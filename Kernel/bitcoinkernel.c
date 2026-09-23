/* btc-verified implementation of the pinned transaction C ABI.
 * Parsing, serialization, hashing, and consensus predicates execute in Lean.
 * This file owns only the C ABI, native snapshots, and runtime registration.
 */
#include <kernel/bitcoinkernel.h>
#include "lean_bridge.h"

#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    unsigned char* data;
    size_t size;
} Bytes;

struct btck_Txid { unsigned char bytes[32]; };
struct btck_ScriptPubkey { Bytes bytes; };
struct btck_WitnessStack { Bytes* items; size_t count; };
struct btck_TransactionOutPoint { btck_Txid txid; uint32_t index; };
struct btck_TransactionInput {
    btck_TransactionOutPoint outpoint;
    uint32_t sequence;
    Bytes script;
    btck_WitnessStack witness;
};
struct btck_TransactionOutput { int64_t amount; btck_ScriptPubkey script; };
struct btck_TxValidationState {
    btck_ValidationMode mode;
    btck_TxValidationResult result;
};
struct btck_Transaction {
    atomic_size_t references;
    Bytes serialization;
    btck_TransactionInput* inputs;
    size_t input_count;
    btck_TransactionOutput* outputs;
    size_t output_count;
    uint32_t locktime;
    bool checks;
    btck_Txid txid;
};

/* No Lean object escapes an API call. Once published, a transaction's native
 * fields are immutable; only its ownership count changes. Its final reference
 * may be released on any thread without entering the Lean runtime.
 */
static pthread_once_t runtime_once = PTHREAD_ONCE_INIT;
static pthread_key_t runtime_thread_key;
static bool runtime_ready;
static const char runtime_thread_tag;

static void finalize_runtime_thread(void* tag)
{
    (void)tag;
    lean_finalize_thread();
}

static void initialize_runtime(void)
{
    if (pthread_key_create(&runtime_thread_key, finalize_runtime_thread) != 0) return;
    /* lean_initialize registers its calling thread as well as the runtime. */
    lean_initialize();
    if (pthread_setspecific(runtime_thread_key, &runtime_thread_tag) != 0) {
        lean_finalize_thread();
        (void)pthread_key_delete(runtime_thread_key);
        return;
    }
    lean_object* result = initialize_btc_x2dverified_Kernel_Transaction(1);
    runtime_ready = !lean_io_result_is_error(result);
    if (!runtime_ready) lean_io_result_show_error(result);
    lean_dec(result);
    lean_io_mark_end_initialization();
    if (!runtime_ready) {
        /* No other caller can use the key until pthread_once returns, and all
         * future callers stop at !runtime_ready. No registration is needed.
         */
        (void)pthread_key_delete(runtime_thread_key);
        lean_finalize_thread();
    }
}

static bool ensure_runtime(void)
{
    /* pthread_once publishes readiness and the key after module initialization,
     * which Lean requires to be serialized. The library stays loaded until exit.
     */
    if (pthread_once(&runtime_once, initialize_runtime) != 0 || !runtime_ready) return false;
    if (pthread_getspecific(runtime_thread_key) == NULL) {
        lean_initialize_thread();
        if (pthread_setspecific(runtime_thread_key, &runtime_thread_tag) != 0) {
            lean_finalize_thread();
            return false;
        }
    }
    return true;
}

/* Every exported Lean object parameter is consuming. Retain borrowed values
 * explicitly at each call site; exported object results must be released.
 */
static lean_object* retain(lean_object* value)
{
    lean_inc(value);
    return value;
}

static void release(lean_object* value)
{
    if (value != NULL) lean_dec(value);
}

static lean_object* lean_bytes(const void* data, size_t size)
{
    assert(data != NULL || size == 0);
    lean_object* result = lean_alloc_sarray(1, size, size);
    if (size != 0) memcpy(lean_sarray_cptr(result), data, size);
    return result;
}

/* Destination buffers start empty. On failure they remain safe to clear. */
static bool bytes_copy(Bytes* destination, const void* data, size_t size)
{
    assert(destination->data == NULL && destination->size == 0);
    assert(data != NULL || size == 0);
    if (size == 0) return true;
    destination->data = malloc(size);
    if (destination->data == NULL) return false;
    memcpy(destination->data, data, size);
    destination->size = size;
    return true;
}

static void bytes_clear(Bytes* bytes)
{
    free(bytes->data);
    *bytes = (Bytes){0};
}

static bool bytes_from_lean(Bytes* destination, lean_object* owned)
{
    const bool ok = bytes_copy(destination, lean_sarray_cptr(owned), lean_sarray_size(owned));
    lean_dec(owned);
    return ok;
}

static bool txid_from_lean(btck_Txid* destination, lean_object* owned)
{
    const bool ok = lean_sarray_size(owned) == sizeof(destination->bytes);
    if (ok) memcpy(destination->bytes, lean_sarray_cptr(owned), sizeof(destination->bytes));
    lean_dec(owned);
    return ok;
}

static void* zero_array(size_t count, size_t element_size)
{
    if (count == 0 || count > SIZE_MAX / element_size) return NULL;
    return calloc(count, element_size);
}

static void witness_clear(btck_WitnessStack* witness)
{
    for (size_t i = 0; i < witness->count; ++i) bytes_clear(&witness->items[i]);
    free(witness->items);
    *witness = (btck_WitnessStack){0};
}

static bool witness_allocate(btck_WitnessStack* witness, size_t count)
{
    if (count != 0) {
        witness->items = zero_array(count, sizeof(*witness->items));
        if (witness->items == NULL) return false;
    }
    witness->count = count;
    return true;
}

static bool witness_copy(btck_WitnessStack* destination, const btck_WitnessStack* source)
{
    if (!witness_allocate(destination, source->count)) return false;
    for (size_t i = 0; i < source->count; ++i) {
        if (!bytes_copy(&destination->items[i], source->items[i].data, source->items[i].size))
            return false;
    }
    return true;
}

static bool witness_from_lean(btck_WitnessStack* destination, lean_object* borrowed)
{
    if (!witness_allocate(destination, lean_array_size(borrowed))) return false;
    for (size_t i = 0; i < destination->count; ++i) {
        lean_object* item = lean_array_get_core(borrowed, i);
        if (!bytes_copy(&destination->items[i], lean_sarray_cptr(item), lean_sarray_size(item)))
            return false;
    }
    return true;
}

static void input_clear(btck_TransactionInput* input)
{
    bytes_clear(&input->script);
    witness_clear(&input->witness);
}

static void transaction_free(btck_Transaction* transaction)
{
    for (size_t i = 0; i < transaction->input_count; ++i) input_clear(&transaction->inputs[i]);
    for (size_t i = 0; i < transaction->output_count; ++i)
        bytes_clear(&transaction->outputs[i].script.bytes);
    free(transaction->inputs);
    free(transaction->outputs);
    bytes_clear(&transaction->serialization);
    free(transaction);
}

static bool transaction_from_lean(btck_Transaction* destination, lean_object* tx)
{
    lean_object* inputs = NULL;
    lean_object* witnesses = NULL;
    lean_object* outputs = NULL;
    bool ok = false;

    if (!bytes_from_lean(&destination->serialization, btcv_kernel_encode(retain(tx)))) goto done;
    /* Compute the immutable txid before publishing the handle. The getter needs
     * neither a lock nor a runtime call, and creation already has a failure value.
     */
    if (!txid_from_lean(&destination->txid,
                       btcv_kernel_hash(btcv_kernel_encode_stripped(retain(tx))))) goto done;
    destination->locktime = btcv_kernel_locktime(retain(tx));
    destination->checks = btcv_kernel_check(retain(tx)) != 0;

    inputs = btcv_kernel_inputs(retain(tx));
    witnesses = btcv_kernel_witnesses(retain(tx));
    const size_t input_count = lean_array_size(inputs);
    if (lean_array_size(witnesses) != input_count) goto done;
    if (input_count != 0) {
        destination->inputs = zero_array(input_count, sizeof(*destination->inputs));
        if (destination->inputs == NULL) goto done;
    }
    destination->input_count = input_count;
    for (size_t i = 0; i < input_count; ++i) {
        lean_object* input = lean_array_get_core(inputs, i);
        btck_TransactionInput* snapshot = &destination->inputs[i];
        if (!txid_from_lean(&snapshot->outpoint.txid, btcv_kernel_input_txid(retain(input)))) goto done;
        snapshot->outpoint.index = btcv_kernel_input_index(retain(input));
        snapshot->sequence = btcv_kernel_input_sequence(retain(input));
        if (!bytes_from_lean(&snapshot->script, btcv_kernel_input_script(retain(input)))) goto done;
        if (!witness_from_lean(&snapshot->witness, lean_array_get_core(witnesses, i))) goto done;
    }

    outputs = btcv_kernel_outputs(retain(tx));
    const size_t output_count = lean_array_size(outputs);
    if (output_count != 0) {
        destination->outputs = zero_array(output_count, sizeof(*destination->outputs));
        if (destination->outputs == NULL) goto done;
    }
    destination->output_count = output_count;
    for (size_t i = 0; i < output_count; ++i) {
        lean_object* output = lean_array_get_core(outputs, i);
        btck_TransactionOutput* snapshot = &destination->outputs[i];
        const uint64_t amount = btcv_kernel_output_amount(retain(output));
        /* Preserve wire bits without an out-of-range unsigned-to-signed cast. */
        memcpy(&snapshot->amount, &amount, sizeof(amount));
        if (!bytes_from_lean(&snapshot->script.bytes, btcv_kernel_output_script(retain(output)))) goto done;
    }
    ok = true;
done:
    release(outputs);
    release(witnesses);
    release(inputs);
    return ok;
}

static int write_bytes(const Bytes* bytes, btck_WriteBytes writer, void* user_data)
{
    assert(writer != NULL);
    /* Callbacks must return normally through the C ABI. Raw-field writers
     * propagate their status; transaction serialization maps nonzero to -1.
     */
    return writer(bytes->data, bytes->size, user_data);
}

btck_Transaction* btck_transaction_create(const void* raw_transaction, size_t raw_transaction_len)
{
    assert(raw_transaction != NULL || raw_transaction_len == 0);
    if (!ensure_runtime()) return NULL;
    lean_object* parsed = btcv_kernel_decode(lean_bytes(raw_transaction, raw_transaction_len));
    if (lean_is_scalar(parsed)) {
        lean_dec(parsed);
        return NULL;
    }
    btck_Transaction* transaction = calloc(1, sizeof(*transaction));
    if (transaction != NULL) {
        atomic_init(&transaction->references, 1);
        if (!transaction_from_lean(transaction, lean_ctor_get(parsed, 0))) {
            transaction_free(transaction);
            transaction = NULL;
        }
    }
    lean_dec(parsed);
    return transaction;
}

btck_Transaction* btck_transaction_copy(const btck_Transaction* transaction)
{
    assert(transaction != NULL);
    btck_Transaction* owned = (btck_Transaction*)transaction;
    size_t count = atomic_load_explicit(&owned->references, memory_order_relaxed);
    do {
        /* A caller must hold a live reference throughout this operation. */
        assert(count != 0);
        if (count == SIZE_MAX) return NULL;
    } while (!atomic_compare_exchange_weak_explicit(&owned->references, &count, count + 1,
                                                   memory_order_relaxed, memory_order_relaxed));
    return owned;
}

void btck_transaction_destroy(btck_Transaction* transaction)
{
    if (transaction == NULL) return;
    if (atomic_fetch_sub_explicit(&transaction->references, 1, memory_order_acq_rel) == 1)
        transaction_free(transaction);
}

int btck_transaction_to_bytes(const btck_Transaction* transaction, btck_WriteBytes writer, void* data)
{
    assert(transaction != NULL);
    return write_bytes(&transaction->serialization, writer, data) == 0 ? 0 : -1;
}

size_t btck_transaction_count_inputs(const btck_Transaction* transaction)
{
    assert(transaction != NULL);
    return transaction->input_count;
}

size_t btck_transaction_count_outputs(const btck_Transaction* transaction)
{
    assert(transaction != NULL);
    return transaction->output_count;
}

const btck_TransactionInput* btck_transaction_get_input_at(const btck_Transaction* transaction, size_t index)
{
    assert(transaction != NULL && index < transaction->input_count);
    return &transaction->inputs[index];
}

const btck_TransactionOutput* btck_transaction_get_output_at(const btck_Transaction* transaction, size_t index)
{
    assert(transaction != NULL && index < transaction->output_count);
    return &transaction->outputs[index];
}

uint32_t btck_transaction_get_locktime(const btck_Transaction* transaction)
{
    assert(transaction != NULL);
    return transaction->locktime;
}

const btck_Txid* btck_transaction_get_txid(const btck_Transaction* transaction)
{
    assert(transaction != NULL);
    return &transaction->txid;
}

btck_TxValidationState* btck_tx_validation_state_create(void)
{
    btck_TxValidationState* state = malloc(sizeof(*state));
    if (state != NULL)
        *state = (btck_TxValidationState){btck_ValidationMode_VALID, btck_TxValidationResult_UNSET};
    return state;
}

void btck_tx_validation_state_destroy(btck_TxValidationState* state) { free(state); }

btck_ValidationMode btck_tx_validation_state_get_validation_mode(const btck_TxValidationState* state)
{
    assert(state != NULL);
    return state->mode;
}

btck_TxValidationResult btck_tx_validation_state_get_tx_validation_result(const btck_TxValidationState* state)
{
    assert(state != NULL);
    return state->result;
}

int btck_transaction_check(const btck_Transaction* tx, btck_TxValidationState* state)
{
    assert(tx != NULL && state != NULL);
    *state = tx->checks
        ? (btck_TxValidationState){btck_ValidationMode_VALID, btck_TxValidationResult_UNSET}
        : (btck_TxValidationState){btck_ValidationMode_INVALID, btck_TxValidationResult_CONSENSUS};
    return tx->checks ? 1 : 0;
}

btck_TransactionInput* btck_transaction_input_copy(const btck_TransactionInput* input)
{
    assert(input != NULL);
    btck_TransactionInput* copy = calloc(1, sizeof(*copy));
    if (copy == NULL) return NULL;
    copy->outpoint = input->outpoint;
    copy->sequence = input->sequence;
    if (!bytes_copy(&copy->script, input->script.data, input->script.size) ||
        !witness_copy(&copy->witness, &input->witness)) {
        btck_transaction_input_destroy(copy);
        return NULL;
    }
    return copy;
}

void btck_transaction_input_destroy(btck_TransactionInput* input)
{
    if (input == NULL) return;
    input_clear(input);
    free(input);
}

const btck_TransactionOutPoint* btck_transaction_input_get_out_point(const btck_TransactionInput* input)
{
    assert(input != NULL);
    return &input->outpoint;
}

uint32_t btck_transaction_input_get_sequence(const btck_TransactionInput* input)
{
    assert(input != NULL);
    return input->sequence;
}

const btck_WitnessStack* btck_transaction_input_get_witness_stack(const btck_TransactionInput* input)
{
    assert(input != NULL);
    return &input->witness;
}

int btck_transaction_input_get_script_sig(const btck_TransactionInput* input, btck_WriteBytes writer, void* data)
{
    assert(input != NULL);
    return write_bytes(&input->script, writer, data);
}

btck_WitnessStack* btck_witness_stack_copy(const btck_WitnessStack* witness)
{
    assert(witness != NULL);
    btck_WitnessStack* copy = calloc(1, sizeof(*copy));
    if (copy == NULL) return NULL;
    if (!witness_copy(copy, witness)) {
        btck_witness_stack_destroy(copy);
        return NULL;
    }
    return copy;
}

void btck_witness_stack_destroy(btck_WitnessStack* witness)
{
    if (witness == NULL) return;
    witness_clear(witness);
    free(witness);
}

size_t btck_witness_stack_count_items(const btck_WitnessStack* witness)
{
    assert(witness != NULL);
    return witness->count;
}

int btck_witness_stack_get_item_at(const btck_WitnessStack* witness, size_t index, btck_WriteBytes writer, void* data)
{
    assert(witness != NULL && index < witness->count);
    return write_bytes(&witness->items[index], writer, data);
}

btck_TransactionOutPoint* btck_transaction_out_point_copy(const btck_TransactionOutPoint* outpoint)
{
    assert(outpoint != NULL);
    btck_TransactionOutPoint* copy = malloc(sizeof(*copy));
    if (copy != NULL) *copy = *outpoint;
    return copy;
}

void btck_transaction_out_point_destroy(btck_TransactionOutPoint* outpoint) { free(outpoint); }

uint32_t btck_transaction_out_point_get_index(const btck_TransactionOutPoint* outpoint)
{
    assert(outpoint != NULL);
    return outpoint->index;
}

const btck_Txid* btck_transaction_out_point_get_txid(const btck_TransactionOutPoint* outpoint)
{
    assert(outpoint != NULL);
    return &outpoint->txid;
}

btck_Txid* btck_txid_copy(const btck_Txid* txid)
{
    assert(txid != NULL);
    btck_Txid* copy = malloc(sizeof(*copy));
    if (copy != NULL) *copy = *txid;
    return copy;
}

void btck_txid_destroy(btck_Txid* txid) { free(txid); }

int btck_txid_equals(const btck_Txid* left, const btck_Txid* right)
{
    assert(left != NULL && right != NULL);
    return memcmp(left->bytes, right->bytes, sizeof(left->bytes)) == 0 ? 1 : 0;
}

void btck_txid_to_bytes(const btck_Txid* txid, unsigned char output[32])
{
    assert(txid != NULL && output != NULL);
    memcpy(output, txid->bytes, sizeof(txid->bytes));
}

btck_ScriptPubkey* btck_script_pubkey_create(const void* bytes, size_t size)
{
    assert(bytes != NULL || size == 0);
    btck_ScriptPubkey* script = calloc(1, sizeof(*script));
    if (script == NULL) return NULL;
    if (!bytes_copy(&script->bytes, bytes, size)) {
        free(script);
        return NULL;
    }
    return script;
}

btck_ScriptPubkey* btck_script_pubkey_copy(const btck_ScriptPubkey* script)
{
    assert(script != NULL);
    return btck_script_pubkey_create(script->bytes.data, script->bytes.size);
}

void btck_script_pubkey_destroy(btck_ScriptPubkey* script)
{
    if (script == NULL) return;
    bytes_clear(&script->bytes);
    free(script);
}

int btck_script_pubkey_to_bytes(const btck_ScriptPubkey* script, btck_WriteBytes writer, void* data)
{
    assert(script != NULL);
    return write_bytes(&script->bytes, writer, data);
}

btck_TransactionOutput* btck_transaction_output_create(const btck_ScriptPubkey* script, int64_t amount)
{
    assert(script != NULL);
    btck_TransactionOutput* output = calloc(1, sizeof(*output));
    if (output == NULL) return NULL;
    if (!bytes_copy(&output->script.bytes, script->bytes.data, script->bytes.size)) {
        free(output);
        return NULL;
    }
    output->amount = amount;
    return output;
}

btck_TransactionOutput* btck_transaction_output_copy(const btck_TransactionOutput* output)
{
    assert(output != NULL);
    return btck_transaction_output_create(&output->script, output->amount);
}

void btck_transaction_output_destroy(btck_TransactionOutput* output)
{
    if (output == NULL) return;
    bytes_clear(&output->script.bytes);
    free(output);
}

const btck_ScriptPubkey* btck_transaction_output_get_script_pubkey(const btck_TransactionOutput* output)
{
    assert(output != NULL);
    return &output->script;
}

int64_t btck_transaction_output_get_amount(const btck_TransactionOutput* output)
{
    assert(output != NULL);
    return output->amount;
}
