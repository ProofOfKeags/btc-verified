#include <kernel/bitcoinkernel.h>

#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define REQUIRE(condition) require_impl((condition), #condition, __FILE__, __LINE__)

enum { WRITER_FAILURE = 73, FIRST_OUTPUT_AMOUNT_OFFSET = 50 };

static const unsigned char LEGACY_TX[] = {
    0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
    0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12,
    0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
    0x1f, 0x03, 0x00, 0x00, 0x00, 0x03, 0xaa, 0xbb, 0xcc, 0xfe, 0xff, 0xff,
    0xff, 0x02, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x51,
    0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x6a, 0x00, 0x44,
    0x33, 0x22, 0x11,
};

static const unsigned char SEGWIT_TX[] = {
    0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4,
    0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf, 0xb0,
    0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xbb, 0xbc,
    0xbd, 0xbe, 0xbf, 0x01, 0x00, 0x00, 0x00, 0x00, 0xfd, 0xff, 0xff, 0xff,
    0x01, 0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x51, 0x51,
    0x02, 0x03, 0x01, 0x02, 0x03, 0x00, 0x04, 0x03, 0x02, 0x01,
};

/* hashlib.sha256(hashlib.sha256(LEGACY_TX).digest()).digest() */
static const unsigned char LEGACY_TXID[] = {
    0xce, 0xa8, 0x7c, 0x70, 0xf8, 0x83, 0x93, 0xfa, 0xd0, 0x9f, 0x4d, 0x61,
    0x03, 0x70, 0xca, 0xc8, 0xca, 0xd0, 0x22, 0x1b, 0x60, 0xe5, 0xc9, 0xbc,
    0xee, 0xa8, 0x77, 0xe3, 0xde, 0x5d, 0x4a, 0x3b,
};

/* Double-SHA-256 of SEGWIT_TX with marker, flag, and witness removed. */
static const unsigned char SEGWIT_TXID[] = {
    0x49, 0x66, 0xa0, 0xb2, 0x0f, 0x26, 0xe5, 0x21, 0xd0, 0xcc, 0x4e, 0x67,
    0x29, 0xd5, 0xd5, 0x63, 0x59, 0x6e, 0x99, 0xae, 0x48, 0xce, 0x62, 0x39,
    0xb9, 0x77, 0xd9, 0x37, 0x45, 0x39, 0x31, 0x6b,
};

static const unsigned char COINBASE_VALID[] = {
    0x01, 0x00, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xff, 0xff, 0xff, 0xff, 0x02, 0x01, 0x01,
    0xff, 0xff, 0xff, 0xff, 0x01,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00,
};

static const unsigned char COINBASE_SHORT_SCRIPT[] = {
    0x01, 0x00, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xff, 0xff, 0xff, 0xff, 0x01, 0x01,
    0xff, 0xff, 0xff, 0xff, 0x01,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00,
};

struct byte_buffer {
    unsigned char bytes[512];
    size_t size;
    size_t calls;
};

struct reentrant_buffer {
    struct byte_buffer output;
    const btck_Transaction* transaction;
    int observed;
};

static void require_impl(int condition, const char* expression, const char* file, int line)
{
    if (condition) return;
    fprintf(stderr, "%s:%d: requirement failed: %s\n", file, line, expression);
    exit(EXIT_FAILURE);
}

static int collect_writer(const void* bytes, size_t size, void* user_data)
{
    struct byte_buffer* output = user_data;
    if (output == NULL || (bytes == NULL && size != 0) ||
        size > sizeof(output->bytes) - output->size) {
        return 91;
    }
    if (size != 0) memcpy(output->bytes + output->size, bytes, size);
    output->size += size;
    output->calls += 1;
    return 0;
}

static int failing_writer(const void* bytes, size_t size, void* user_data)
{
    (void)bytes;
    (void)size;
    (void)user_data;
    return WRITER_FAILURE;
}

static int reentrant_writer(const void* bytes, size_t size, void* user_data)
{
    struct reentrant_buffer* output = user_data;
    if (btck_transaction_count_inputs(output->transaction) != 1 ||
        btck_transaction_get_locktime(output->transaction) != UINT32_C(0x11223344)) {
        return 92;
    }
    output->observed = 1;
    return collect_writer(bytes, size, &output->output);
}

static void require_bytes(const struct byte_buffer* output,
                          const unsigned char* expected, size_t expected_size)
{
    REQUIRE(output->size == expected_size);
    REQUIRE(expected_size == 0 || memcmp(output->bytes, expected, expected_size) == 0);
}

static struct byte_buffer serialize_transaction(const btck_Transaction* transaction)
{
    struct byte_buffer output = {{0}, 0, 0};
    REQUIRE(btck_transaction_to_bytes(transaction, collect_writer, &output) == 0);
    return output;
}

static struct byte_buffer serialize_script(const btck_ScriptPubkey* script)
{
    struct byte_buffer output = {{0}, 0, 0};
    REQUIRE(btck_script_pubkey_to_bytes(script, collect_writer, &output) == 0);
    return output;
}

static void test_destroy_null(void)
{
    btck_transaction_destroy(NULL);
    btck_tx_validation_state_destroy(NULL);
    btck_transaction_input_destroy(NULL);
    btck_witness_stack_destroy(NULL);
    btck_transaction_out_point_destroy(NULL);
    btck_txid_destroy(NULL);
    btck_script_pubkey_destroy(NULL);
    btck_transaction_output_destroy(NULL);
}

static void test_legacy_fields_and_hash(void)
{
    btck_Transaction* transaction = btck_transaction_create(LEGACY_TX, sizeof(LEGACY_TX));
    REQUIRE(transaction != NULL);
    REQUIRE(btck_transaction_count_inputs(transaction) == 1);
    REQUIRE(btck_transaction_count_outputs(transaction) == 2);
    REQUIRE(btck_transaction_get_locktime(transaction) == UINT32_C(0x11223344));

    const btck_TransactionInput* input = btck_transaction_get_input_at(transaction, 0);
    REQUIRE(input != NULL);
    REQUIRE(btck_transaction_input_get_sequence(input) == UINT32_C(0xfffffffe));
    struct byte_buffer script_sig = {{0}, 0, 0};
    REQUIRE(btck_transaction_input_get_script_sig(input, collect_writer, &script_sig) == 0);
    require_bytes(&script_sig, (const unsigned char[]){0xaa, 0xbb, 0xcc}, 3);
    REQUIRE(btck_transaction_input_get_script_sig(input, failing_writer, NULL) == WRITER_FAILURE);

    const btck_WitnessStack* witness = btck_transaction_input_get_witness_stack(input);
    REQUIRE(witness != NULL);
    REQUIRE(btck_witness_stack_count_items(witness) == 0);
    const btck_TransactionOutPoint* outpoint = btck_transaction_input_get_out_point(input);
    REQUIRE(outpoint != NULL);
    REQUIRE(btck_transaction_out_point_get_index(outpoint) == 3);
    unsigned char outpoint_hash[32];
    btck_txid_to_bytes(btck_transaction_out_point_get_txid(outpoint), outpoint_hash);
    REQUIRE(memcmp(outpoint_hash, LEGACY_TX + 5, sizeof(outpoint_hash)) == 0);

    const btck_TransactionOutput* first = btck_transaction_get_output_at(transaction, 0);
    const btck_TransactionOutput* second = btck_transaction_get_output_at(transaction, 1);
    REQUIRE(first != NULL && second != NULL);
    REQUIRE(btck_transaction_output_get_amount(first) == 1);
    REQUIRE(btck_transaction_output_get_amount(second) == 2);
    struct byte_buffer first_script = serialize_script(
        btck_transaction_output_get_script_pubkey(first));
    struct byte_buffer second_script = serialize_script(
        btck_transaction_output_get_script_pubkey(second));
    require_bytes(&first_script, (const unsigned char[]){0x51}, 1);
    require_bytes(&second_script, (const unsigned char[]){0x6a, 0x00}, 2);

    struct byte_buffer serialization = serialize_transaction(transaction);
    require_bytes(&serialization, LEGACY_TX, sizeof(LEGACY_TX));
    REQUIRE(btck_transaction_to_bytes(transaction, failing_writer, NULL) != 0);
    struct reentrant_buffer reentrant = {{{0}, 0, 0}, transaction, 0};
    REQUIRE(btck_transaction_to_bytes(transaction, reentrant_writer, &reentrant) == 0);
    REQUIRE(reentrant.observed == 1);
    require_bytes(&reentrant.output, LEGACY_TX, sizeof(LEGACY_TX));

    const btck_Txid* borrowed_txid = btck_transaction_get_txid(transaction);
    REQUIRE(borrowed_txid != NULL);
    unsigned char txid_bytes[32];
    btck_txid_to_bytes(borrowed_txid, txid_bytes);
    REQUIRE(memcmp(txid_bytes, LEGACY_TXID, sizeof(LEGACY_TXID)) == 0);
    btck_Txid* txid_copy = btck_txid_copy(borrowed_txid);
    REQUIRE(txid_copy != NULL);
    REQUIRE(btck_txid_equals(borrowed_txid, txid_copy) != 0);
    REQUIRE(btck_txid_equals(borrowed_txid,
                              btck_transaction_out_point_get_txid(outpoint)) == 0);

    btck_transaction_destroy(transaction);
    btck_txid_to_bytes(txid_copy, txid_bytes);
    REQUIRE(memcmp(txid_bytes, LEGACY_TXID, sizeof(LEGACY_TXID)) == 0);
    btck_txid_destroy(txid_copy);
}

static void test_segwit_fields(void)
{
    btck_Transaction* transaction = btck_transaction_create(SEGWIT_TX, sizeof(SEGWIT_TX));
    REQUIRE(transaction != NULL);
    REQUIRE(btck_transaction_count_inputs(transaction) == 1);
    REQUIRE(btck_transaction_count_outputs(transaction) == 1);
    REQUIRE(btck_transaction_get_locktime(transaction) == UINT32_C(0x01020304));
    const btck_TransactionInput* input = btck_transaction_get_input_at(transaction, 0);
    REQUIRE(btck_transaction_input_get_sequence(input) == UINT32_C(0xfffffffd));
    struct byte_buffer empty_script = {{0}, 0, 0};
    REQUIRE(btck_transaction_input_get_script_sig(input, collect_writer, &empty_script) == 0);
    require_bytes(&empty_script, NULL, 0);

    const btck_WitnessStack* witness = btck_transaction_input_get_witness_stack(input);
    REQUIRE(btck_witness_stack_count_items(witness) == 2);
    struct byte_buffer first = {{0}, 0, 0};
    struct byte_buffer second = {{0}, 0, 0};
    REQUIRE(btck_witness_stack_get_item_at(witness, 0, collect_writer, &first) == 0);
    REQUIRE(btck_witness_stack_get_item_at(witness, 1, collect_writer, &second) == 0);
    require_bytes(&first, (const unsigned char[]){0x01, 0x02, 0x03}, 3);
    require_bytes(&second, NULL, 0);
    REQUIRE(btck_witness_stack_get_item_at(witness, 0, failing_writer, NULL) == WRITER_FAILURE);

    const btck_TransactionOutput* output = btck_transaction_get_output_at(transaction, 0);
    REQUIRE(btck_transaction_output_get_amount(output) == 42);
    struct byte_buffer script = serialize_script(
        btck_transaction_output_get_script_pubkey(output));
    require_bytes(&script, (const unsigned char[]){0x51, 0x51}, 2);
    struct byte_buffer serialization = serialize_transaction(transaction);
    require_bytes(&serialization, SEGWIT_TX, sizeof(SEGWIT_TX));

    unsigned char txid_bytes[32];
    btck_txid_to_bytes(btck_transaction_get_txid(transaction), txid_bytes);
    REQUIRE(memcmp(txid_bytes, SEGWIT_TXID, sizeof(SEGWIT_TXID)) == 0);

    btck_TxValidationState* state = btck_tx_validation_state_create();
    REQUIRE(state != NULL);
    REQUIRE(btck_transaction_check(transaction, state) == 1);
    REQUIRE(btck_tx_validation_state_get_validation_mode(state) == btck_ValidationMode_VALID);
    REQUIRE(btck_tx_validation_state_get_tx_validation_result(state) ==
            btck_TxValidationResult_UNSET);
    btck_tx_validation_state_destroy(state);
    btck_transaction_destroy(transaction);
}

static void test_prefix_and_malformed_inputs(void)
{
    unsigned char prefixed[sizeof(LEGACY_TX) + 4];
    memcpy(prefixed, LEGACY_TX, sizeof(LEGACY_TX));
    memcpy(prefixed + sizeof(LEGACY_TX), (const unsigned char[]){0xde, 0xad, 0xbe, 0xef}, 4);
    btck_Transaction* transaction = btck_transaction_create(prefixed, sizeof(prefixed));
    REQUIRE(transaction != NULL);
    struct byte_buffer serialization = serialize_transaction(transaction);
    require_bytes(&serialization, LEGACY_TX, sizeof(LEGACY_TX));
    btck_transaction_destroy(transaction);

    const unsigned char byte = 0;
    REQUIRE(btck_transaction_create(NULL, 0) == NULL);
    REQUIRE(btck_transaction_create(&byte, 0) == NULL);
    REQUIRE(btck_transaction_create(&byte, 1) == NULL);
    REQUIRE(btck_transaction_create(LEGACY_TX, sizeof(LEGACY_TX) - 1) == NULL);
}

static void test_validation_state_reset_and_signed_amounts(void)
{
    unsigned char negative_one[sizeof(LEGACY_TX)];
    unsigned char minimum[sizeof(LEGACY_TX)];
    memcpy(negative_one, LEGACY_TX, sizeof(LEGACY_TX));
    memcpy(minimum, LEGACY_TX, sizeof(LEGACY_TX));
    memset(negative_one + FIRST_OUTPUT_AMOUNT_OFFSET, 0xff, 8);
    memset(minimum + FIRST_OUTPUT_AMOUNT_OFFSET, 0x00, 8);
    minimum[FIRST_OUTPUT_AMOUNT_OFFSET + 7] = 0x80;

    btck_Transaction* valid = btck_transaction_create(LEGACY_TX, sizeof(LEGACY_TX));
    btck_Transaction* negative = btck_transaction_create(negative_one, sizeof(negative_one));
    btck_Transaction* min_value = btck_transaction_create(minimum, sizeof(minimum));
    btck_TxValidationState* state = btck_tx_validation_state_create();
    REQUIRE(valid != NULL && negative != NULL && min_value != NULL && state != NULL);
    REQUIRE(btck_tx_validation_state_get_validation_mode(state) == btck_ValidationMode_VALID);
    REQUIRE(btck_tx_validation_state_get_tx_validation_result(state) ==
            btck_TxValidationResult_UNSET);
    REQUIRE(btck_transaction_output_get_amount(
                btck_transaction_get_output_at(negative, 0)) == INT64_C(-1));
    REQUIRE(btck_transaction_output_get_amount(
                btck_transaction_get_output_at(min_value, 0)) == INT64_MIN);

    REQUIRE(btck_transaction_check(valid, state) == 1);
    REQUIRE(btck_tx_validation_state_get_validation_mode(state) == btck_ValidationMode_VALID);
    REQUIRE(btck_tx_validation_state_get_tx_validation_result(state) ==
            btck_TxValidationResult_UNSET);
    REQUIRE(btck_transaction_check(negative, state) == 0);
    REQUIRE(btck_tx_validation_state_get_validation_mode(state) == btck_ValidationMode_INVALID);
    REQUIRE(btck_tx_validation_state_get_tx_validation_result(state) ==
            btck_TxValidationResult_CONSENSUS);
    REQUIRE(btck_transaction_check(min_value, state) == 0);
    REQUIRE(btck_tx_validation_state_get_validation_mode(state) == btck_ValidationMode_INVALID);
    REQUIRE(btck_tx_validation_state_get_tx_validation_result(state) ==
            btck_TxValidationResult_CONSENSUS);
    REQUIRE(btck_transaction_check(valid, state) == 1);
    REQUIRE(btck_tx_validation_state_get_validation_mode(state) == btck_ValidationMode_VALID);
    REQUIRE(btck_tx_validation_state_get_tx_validation_result(state) ==
            btck_TxValidationResult_UNSET);

    btck_tx_validation_state_destroy(state);
    btck_transaction_destroy(min_value);
    btck_transaction_destroy(negative);
    btck_transaction_destroy(valid);
}

static void test_coinbase_branch(void)
{
    btck_Transaction* valid = btck_transaction_create(COINBASE_VALID, sizeof(COINBASE_VALID));
    btck_Transaction* short_script =
        btck_transaction_create(COINBASE_SHORT_SCRIPT, sizeof(COINBASE_SHORT_SCRIPT));
    btck_TxValidationState* state = btck_tx_validation_state_create();
    REQUIRE(valid != NULL && short_script != NULL && state != NULL);
    REQUIRE(btck_transaction_check(valid, state) == 1);
    REQUIRE(btck_tx_validation_state_get_validation_mode(state) == btck_ValidationMode_VALID);
    REQUIRE(btck_tx_validation_state_get_tx_validation_result(state) ==
            btck_TxValidationResult_UNSET);
    REQUIRE(btck_transaction_check(short_script, state) == 0);
    REQUIRE(btck_tx_validation_state_get_validation_mode(state) == btck_ValidationMode_INVALID);
    REQUIRE(btck_tx_validation_state_get_tx_validation_result(state) ==
            btck_TxValidationResult_CONSENSUS);

    btck_tx_validation_state_destroy(state);
    btck_transaction_destroy(short_script);
    btck_transaction_destroy(valid);
}

static void test_owned_copy_lifetimes(void)
{
    btck_Transaction* transaction = btck_transaction_create(SEGWIT_TX, sizeof(SEGWIT_TX));
    REQUIRE(transaction != NULL);
    btck_Transaction* transaction_copy = btck_transaction_copy(transaction);
    const btck_TransactionInput* borrowed_input = btck_transaction_get_input_at(transaction, 0);
    const btck_TransactionOutput* borrowed_output = btck_transaction_get_output_at(transaction, 0);
    btck_TransactionInput* input_copy = btck_transaction_input_copy(borrowed_input);
    btck_TransactionOutput* output_copy = btck_transaction_output_copy(borrowed_output);
    btck_WitnessStack* witness_copy = btck_witness_stack_copy(
        btck_transaction_input_get_witness_stack(borrowed_input));
    btck_TransactionOutPoint* outpoint_copy = btck_transaction_out_point_copy(
        btck_transaction_input_get_out_point(borrowed_input));
    btck_Txid* outpoint_txid_copy = btck_txid_copy(
        btck_transaction_out_point_get_txid(outpoint_copy));
    btck_ScriptPubkey* output_script_copy = btck_script_pubkey_copy(
        btck_transaction_output_get_script_pubkey(borrowed_output));
    REQUIRE(transaction_copy != NULL && input_copy != NULL && output_copy != NULL);
    REQUIRE(witness_copy != NULL && outpoint_copy != NULL && outpoint_txid_copy != NULL);
    REQUIRE(output_script_copy != NULL);

    btck_transaction_destroy(transaction);
    struct byte_buffer serialization = serialize_transaction(transaction_copy);
    require_bytes(&serialization, SEGWIT_TX, sizeof(SEGWIT_TX));
    btck_transaction_destroy(transaction_copy);
    REQUIRE(btck_transaction_input_get_sequence(input_copy) == UINT32_C(0xfffffffd));
    REQUIRE(btck_witness_stack_count_items(witness_copy) == 2);
    REQUIRE(btck_transaction_out_point_get_index(outpoint_copy) == 1);
    REQUIRE(btck_transaction_output_get_amount(output_copy) == 42);
    struct byte_buffer script = serialize_script(output_script_copy);
    require_bytes(&script, (const unsigned char[]){0x51, 0x51}, 2);
    unsigned char hash[32];
    btck_txid_to_bytes(outpoint_txid_copy, hash);
    REQUIRE(memcmp(hash, SEGWIT_TX + 7, sizeof(hash)) == 0);

    btck_transaction_input_destroy(input_copy);
    btck_transaction_output_destroy(output_copy);
    btck_witness_stack_destroy(witness_copy);
    btck_transaction_out_point_destroy(outpoint_copy);
    btck_txid_destroy(outpoint_txid_copy);
    btck_script_pubkey_destroy(output_script_copy);
}

static void test_script_and_output_constructors(void)
{
    static const unsigned char SCRIPT[] = {0x00, 0x51, 0xac};
    btck_ScriptPubkey* empty = btck_script_pubkey_create(NULL, 0);
    btck_ScriptPubkey* script = btck_script_pubkey_create(SCRIPT, sizeof(SCRIPT));
    REQUIRE(empty != NULL && script != NULL);
    struct byte_buffer empty_bytes = serialize_script(empty);
    struct byte_buffer script_bytes = serialize_script(script);
    require_bytes(&empty_bytes, NULL, 0);
    require_bytes(&script_bytes, SCRIPT, sizeof(SCRIPT));
    REQUIRE(btck_script_pubkey_to_bytes(script, failing_writer, NULL) == WRITER_FAILURE);

    btck_ScriptPubkey* script_copy = btck_script_pubkey_copy(script);
    btck_TransactionOutput* minimum = btck_transaction_output_create(script, INT64_MIN);
    btck_TransactionOutput* negative_one = btck_transaction_output_create(script, INT64_C(-1));
    REQUIRE(script_copy != NULL && minimum != NULL && negative_one != NULL);
    REQUIRE(btck_transaction_output_get_amount(minimum) == INT64_MIN);
    REQUIRE(btck_transaction_output_get_amount(negative_one) == INT64_C(-1));
    struct byte_buffer borrowed_script = serialize_script(
        btck_transaction_output_get_script_pubkey(minimum));
    require_bytes(&borrowed_script, SCRIPT, sizeof(SCRIPT));

    btck_TransactionOutput* output_copy = btck_transaction_output_copy(minimum);
    btck_ScriptPubkey* nested_copy = btck_script_pubkey_copy(
        btck_transaction_output_get_script_pubkey(output_copy));
    REQUIRE(output_copy != NULL && nested_copy != NULL);
    btck_script_pubkey_destroy(script);
    btck_transaction_output_destroy(minimum);
    REQUIRE(btck_transaction_output_get_amount(output_copy) == INT64_MIN);
    struct byte_buffer copied_bytes = serialize_script(nested_copy);
    require_bytes(&copied_bytes, SCRIPT, sizeof(SCRIPT));
    struct byte_buffer independent_script = serialize_script(script_copy);
    require_bytes(&independent_script, SCRIPT, sizeof(SCRIPT));

    btck_script_pubkey_destroy(nested_copy);
    btck_transaction_output_destroy(output_copy);
    btck_transaction_output_destroy(negative_one);
    btck_script_pubkey_destroy(script_copy);
    btck_script_pubkey_destroy(empty);
}

int main(void)
{
    test_destroy_null();
    test_legacy_fields_and_hash();
    test_segwit_fields();
    test_prefix_and_malformed_inputs();
    test_validation_state_reset_and_signed_amounts();
    test_coinbase_branch();
    test_owned_copy_lifetimes();
    test_script_and_output_constructors();
    puts("btc-verified kernel ABI lifecycle tests passed");
    return 0;
}
