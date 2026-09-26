/* The nine-function transaction slice of the pinned upstream C ABI.
 * Lean owns parsing, serialization, and transaction-local semantics. This file
 * owns only runtime entry, immutable native snapshots, and C object lifetimes.
 */
#include <bitcoinkernel.h>
#include "lean_bridge.h"

#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct btck_Transaction {
    atomic_size_t references;
    size_t size;
    bool checks;
    unsigned char bytes[];
};

struct btck_TxValidationState {
    btck_ValidationMode mode;
    btck_TxValidationResult result;
};

/* Module initialization is serialized. Keep this library loaded until process
 * exit; Lean's module constants have process lifetime. Each entering native
 * thread has its own registration, released at thread exit. No Lean object
 * survives transaction_create, so native handles can move between threads.
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
    /* Also registers this first thread with Lean. */
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
        (void)pthread_key_delete(runtime_thread_key);
        lean_finalize_thread();
    }
}

static bool ensure_runtime(void)
{
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

btck_Transaction* btck_transaction_create(const void* raw_transaction, size_t raw_transaction_len)
{
    assert(raw_transaction != NULL || raw_transaction_len == 0);
    if (!ensure_runtime()) return NULL;
    lean_object* bytes = lean_alloc_sarray(1, raw_transaction_len, raw_transaction_len);
    if (raw_transaction_len != 0)
        memcpy(lean_sarray_cptr(bytes), raw_transaction, raw_transaction_len);
    lean_object* parsed = btcv_kernel_decode(bytes); /* Consumes bytes. */
    if (lean_is_scalar(parsed)) return NULL; /* Option.none owns no allocation. */

    lean_object* tx = lean_ctor_get(parsed, 0); /* Borrowed from Option.some. */
    lean_inc(tx);
    lean_object* encoded = btcv_kernel_encode(tx);
    const size_t size = lean_sarray_size(encoded);
    btck_Transaction* snapshot = NULL;
    if (size <= SIZE_MAX - sizeof(*snapshot)) snapshot = malloc(sizeof(*snapshot) + size);
    if (snapshot != NULL) {
        atomic_init(&snapshot->references, 1);
        snapshot->size = size;
        if (size != 0) memcpy(snapshot->bytes, lean_sarray_cptr(encoded), size);
        lean_inc(tx);
        snapshot->checks = btcv_kernel_check(tx);
    }
    lean_dec(encoded);
    lean_dec(parsed);
    return snapshot;
}

btck_Transaction* btck_transaction_copy(const btck_Transaction* transaction)
{
    assert(transaction != NULL);
    btck_Transaction* owned = (btck_Transaction*)transaction;
    size_t count = atomic_load_explicit(&owned->references, memory_order_relaxed);
    do {
        /* The caller must hold a live reference during this operation. */
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
        free(transaction);
}

int btck_transaction_to_bytes(const btck_Transaction* transaction, btck_WriteBytes writer, void* data)
{
    assert(transaction != NULL && writer != NULL);
    /* No runtime lock is held during callbacks; callers may reenter the API.
     * Writer callbacks must return normally through the C ABI.
     */
    return writer(transaction->bytes, transaction->size, data) == 0 ? 0 : -1;
}

btck_TxValidationState* btck_tx_validation_state_create(void)
{
    btck_TxValidationState* state = malloc(sizeof(*state));
    if (state != NULL)
        *state = (btck_TxValidationState){btck_ValidationMode_VALID, btck_TxValidationResult_UNSET};
    return state;
}

void btck_tx_validation_state_destroy(btck_TxValidationState* state)
{
    free(state);
}

btck_ValidationMode btck_tx_validation_state_get_validation_mode(const btck_TxValidationState* state)
{
    assert(state != NULL);
    return state->mode;
}

btck_TxValidationResult btck_tx_validation_state_get_tx_validation_result(
    const btck_TxValidationState* state)
{
    assert(state != NULL);
    return state->result;
}

int btck_transaction_check(const btck_Transaction* tx, btck_TxValidationState* state)
{
    assert(tx != NULL && state != NULL);
    /* The upstream contract overwrites the state, including invalid -> valid. */
    *state = tx->checks
        ? (btck_TxValidationState){btck_ValidationMode_VALID, btck_TxValidationResult_UNSET}
        : (btck_TxValidationState){btck_ValidationMode_INVALID, btck_TxValidationResult_CONSENSUS};
    return tx->checks ? 1 : 0;
}
