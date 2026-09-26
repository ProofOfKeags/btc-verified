/* Ordinary C client of the pinned upstream header; no Lean-specific interface. */
#include <bitcoinkernel.h>

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Unlike assert, these checks still execute if a caller defines NDEBUG. */
#define CHECK(condition) do { \
    if (!(condition)) { \
        fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #condition); \
        exit(EXIT_FAILURE); \
    } \
} while (0)

/* Literal wire fixtures, independent of the library's serializer. The legacy
 * input's previous hash is 00..1f; its two output amounts are 1 and 2 satoshis. */
static const unsigned char LEGACY_TX[] = {
    0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
    0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12,
    0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
    0x1f, 0x03, 0x00, 0x00, 0x00, 0x03, 0xaa, 0xbb, 0xcc, 0xfe, 0xff, 0xff,
    0xff, 0x02, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x51,
    0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x6a, 0x00, 0x44,
    0x33, 0x22, 0x11,
};

/* A witness with two items: bytes 01 02 03, then an empty byte string. */
static const unsigned char SEGWIT_TX[] = {
    0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4,
    0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf, 0xb0,
    0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xbb, 0xbc,
    0xbd, 0xbe, 0xbf, 0x01, 0x00, 0x00, 0x00, 0x00, 0xfd, 0xff, 0xff, 0xff,
    0x01, 0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x51, 0x51,
    0x02, 0x03, 0x01, 0x02, 0x03, 0x00, 0x04, 0x03, 0x02, 0x01,
};

/* A single null outpoint and a two-byte scriptSig, with one zero-valued output. */
static const unsigned char COINBASE_TX[] = {
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

/* This decodes, but a one-byte coinbase scriptSig fails the local checks. */
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
    unsigned char bytes[128];
    size_t size;
};

static int collect_writer(const void* bytes, size_t size, void* user_data)
{
    struct byte_buffer* output = user_data;
    CHECK(size <= sizeof(output->bytes) - output->size);
    if (size != 0) memcpy(output->bytes + output->size, bytes, size);
    output->size += size;
    return 0;
}

static void check_serialization(const btck_Transaction* tx,
                                const unsigned char* expected, size_t size)
{
    struct byte_buffer output = {{0}, 0};
    CHECK(btck_transaction_to_bytes(tx, collect_writer, &output) == 0);
    CHECK(output.size == size);
    CHECK(memcmp(output.bytes, expected, size) == 0);
}

static void check_validation(const btck_Transaction* tx, btck_TxValidationState* state,
                             int valid)
{
    CHECK(btck_transaction_check(tx, state) == valid);
    CHECK(btck_tx_validation_state_get_validation_mode(state) ==
          (valid ? btck_ValidationMode_VALID : btck_ValidationMode_INVALID));
    CHECK(btck_tx_validation_state_get_tx_validation_result(state) ==
          (valid ? btck_TxValidationResult_UNSET : btck_TxValidationResult_CONSENSUS));
}

static void test_fixture(const unsigned char* bytes, size_t size, int valid)
{
    btck_Transaction* tx = btck_transaction_create(bytes, size);
    btck_TxValidationState* state = btck_tx_validation_state_create();
    CHECK(tx != NULL && state != NULL);
    check_serialization(tx, bytes, size);
    check_validation(tx, state, valid);

    btck_Transaction* copy = btck_transaction_copy(tx);
    CHECK(copy != NULL);
    btck_transaction_destroy(tx);
    check_serialization(copy, bytes, size);
    check_validation(copy, state, valid);
    btck_transaction_destroy(copy);
    btck_tx_validation_state_destroy(state);
}

static void test_parsing(void)
{
    CHECK(btck_transaction_create(NULL, 0) == NULL);
    for (size_t size = 0; size < sizeof(LEGACY_TX); ++size)
        CHECK(btck_transaction_create(LEGACY_TX, size) == NULL);

    /* Core's create operation consumes a prefix, not necessarily the whole buffer. */
    unsigned char trailing[sizeof(LEGACY_TX) + 2];
    memcpy(trailing, LEGACY_TX, sizeof(LEGACY_TX));
    trailing[sizeof(LEGACY_TX)] = 0xde;
    trailing[sizeof(LEGACY_TX) + 1] = 0xad;
    btck_Transaction* tx = btck_transaction_create(trailing, sizeof(trailing));
    CHECK(tx != NULL);
    check_serialization(tx, LEGACY_TX, sizeof(LEGACY_TX));
    btck_transaction_destroy(tx);

    unsigned char noncanonical[sizeof(LEGACY_TX) + 2];
    memcpy(noncanonical, LEGACY_TX, 4);
    noncanonical[4] = 0xfd;
    noncanonical[5] = 1;
    noncanonical[6] = 0;
    memcpy(noncanonical + 7, LEGACY_TX + 5, sizeof(LEGACY_TX) - 5);
    CHECK(btck_transaction_create(noncanonical, sizeof(noncanonical)) == NULL);

    unsigned char unknown_flags[sizeof(SEGWIT_TX)];
    memcpy(unknown_flags, SEGWIT_TX, sizeof(SEGWIT_TX));
    unknown_flags[5] = 3;
    CHECK(btck_transaction_create(unknown_flags, sizeof(unknown_flags)) == NULL);
}

static void test_input_buffer_lifetime(void)
{
    unsigned char* bytes = malloc(sizeof(LEGACY_TX));
    CHECK(bytes != NULL);
    memcpy(bytes, LEGACY_TX, sizeof(LEGACY_TX));
    btck_Transaction* tx = btck_transaction_create(bytes, sizeof(LEGACY_TX));
    CHECK(tx != NULL);
    memset(bytes, 0, sizeof(LEGACY_TX));
    free(bytes);
    check_serialization(tx, LEGACY_TX, sizeof(LEGACY_TX));
    btck_transaction_destroy(tx);
}

static void test_validation_state_reset(void)
{
    /* The first output amount begins at offset 50; ff..ff is signed -1. */
    unsigned char negative_amount[sizeof(LEGACY_TX)];
    memcpy(negative_amount, LEGACY_TX, sizeof(LEGACY_TX));
    memset(negative_amount + 50, 0xff, 8);
    btck_Transaction* valid = btck_transaction_create(LEGACY_TX, sizeof(LEGACY_TX));
    btck_Transaction* invalid = btck_transaction_create(negative_amount, sizeof(negative_amount));
    btck_TxValidationState* state = btck_tx_validation_state_create();
    CHECK(valid != NULL && invalid != NULL && state != NULL);
    CHECK(btck_tx_validation_state_get_validation_mode(state) == btck_ValidationMode_VALID);
    CHECK(btck_tx_validation_state_get_tx_validation_result(state) == btck_TxValidationResult_UNSET);
    check_serialization(invalid, negative_amount, sizeof(negative_amount));
    check_validation(invalid, state, 0);
    check_validation(valid, state, 1);
    check_validation(invalid, state, 0);
    btck_tx_validation_state_destroy(state);
    btck_transaction_destroy(invalid);
    btck_transaction_destroy(valid);
}

static int failing_writer(const void* bytes, size_t size, void* user_data)
{
    (void)bytes;
    (void)size;
    ++*(size_t*)user_data;
    return 73;
}

struct reentrant_buffer {
    struct byte_buffer output;
    const btck_Transaction* tx;
    size_t calls;
};

static int reentrant_writer(const void* bytes, size_t size, void* user_data)
{
    struct reentrant_buffer* output = user_data;
    btck_Transaction* copy = btck_transaction_copy(output->tx);
    btck_TxValidationState* state = btck_tx_validation_state_create();
    CHECK(copy != NULL && state != NULL);
    check_validation(copy, state, 1);
    check_serialization(copy, LEGACY_TX, sizeof(LEGACY_TX));
    btck_Transaction* fresh = btck_transaction_create(LEGACY_TX, sizeof(LEGACY_TX));
    CHECK(fresh != NULL);
    check_serialization(fresh, LEGACY_TX, sizeof(LEGACY_TX));
    btck_transaction_destroy(fresh);
    btck_tx_validation_state_destroy(state);
    btck_transaction_destroy(copy);
    ++output->calls;
    return collect_writer(bytes, size, &output->output);
}

static void test_writers(void)
{
    btck_Transaction* tx = btck_transaction_create(LEGACY_TX, sizeof(LEGACY_TX));
    CHECK(tx != NULL);
    size_t calls = 0;
    CHECK(btck_transaction_to_bytes(tx, failing_writer, &calls) != 0);
    CHECK(calls == 1);
    struct reentrant_buffer output = {{{0}, 0}, tx, 0};
    CHECK(btck_transaction_to_bytes(tx, reentrant_writer, &output) == 0);
    CHECK(output.calls > 0 && output.output.size == sizeof(LEGACY_TX));
    CHECK(memcmp(output.output.bytes, LEGACY_TX, sizeof(LEGACY_TX)) == 0);
    btck_transaction_destroy(tx);
}

static void* concurrent_client(void* argument)
{
    const btck_Transaction* shared = argument;
    for (size_t i = 0; i < 16; ++i) {
        btck_Transaction* tx = shared != NULL ? btck_transaction_copy(shared) :
            btck_transaction_create(SEGWIT_TX, sizeof(SEGWIT_TX));
        CHECK(tx != NULL);
        btck_Transaction* copy = btck_transaction_copy(tx);
        CHECK(copy != NULL);
        btck_transaction_destroy(tx);
        check_serialization(copy, SEGWIT_TX, sizeof(SEGWIT_TX));
        btck_transaction_destroy(copy);
    }
    return NULL;
}

static void run_clients(btck_Transaction* shared)
{
    pthread_t clients[4];
    for (size_t i = 0; i < 4; ++i)
        CHECK(pthread_create(&clients[i], NULL, concurrent_client, shared) == 0);
    for (size_t i = 0; i < 4; ++i)
        CHECK(pthread_join(clients[i], NULL) == 0);
}

int main(void)
{
    /* First calls enter from foreign threads; initialization is library-owned. */
    run_clients(NULL);
    btck_Transaction* shared = btck_transaction_create(SEGWIT_TX, sizeof(SEGWIT_TX));
    CHECK(shared != NULL);
    run_clients(shared);
    btck_transaction_destroy(shared);

    test_fixture(LEGACY_TX, sizeof(LEGACY_TX), 1);
    test_fixture(SEGWIT_TX, sizeof(SEGWIT_TX), 1);
    test_fixture(COINBASE_TX, sizeof(COINBASE_TX), 1);
    test_fixture(COINBASE_SHORT_SCRIPT, sizeof(COINBASE_SHORT_SCRIPT), 0);
    test_parsing();
    test_input_buffer_lifetime();
    test_validation_state_reset();
    test_writers();
    btck_transaction_destroy(NULL);
    btck_tx_validation_state_destroy(NULL);
    puts("btc-verified transaction C ABI tests passed");
    return 0;
}
