/* Callability smoke test for the Lean-backed kernel's supported C symbols.
 *
 * This is an ordinary C client: it uses only the pinned upstream header and
 * never initializes Lean itself. Run it with `lake run kernel-check`.
 *
 * One fixture supplies the handles needed to call every export in abi.toml.
 * Only handle creation and serialization success are required to complete
 * those calls; bytes, verdicts, and validation-state values are not asserted.
 * Behavior belongs in KernelTests.lean and the forthcoming Core differential
 * suite, not here. This is not evidence of C memory or thread safety.
 */
#include <bitcoinkernel.h>

#include <stdio.h>
#include <stdlib.h>

/* Report setup/call failure even when the client is compiled with NDEBUG. */
#define CHECK(condition) do { \
    if (!(condition)) { \
        fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #condition); \
        exit(EXIT_FAILURE); \
    } \
} while (0)

/* A serialized non-witness transaction used only to obtain a usable handle,
 * not as an expected serialization or validation result. This is synthetic:
 * the outpoint and scripts are arbitrary, not a claim of a spendable transaction.
 * Fields below follow wire order; multibyte integers are little-endian and
 * counts/lengths are single-byte CompactSize values. */
static const unsigned char TRANSACTION[] = {
    0x01, 0x00, 0x00, 0x00,                         /* version: 1 */
    0x01,                                           /* input count: 1 */

    /* Input 0: previous transaction hash (32 raw bytes), then output index. */
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
    0x03, 0x00, 0x00, 0x00,                         /* output index: 3 */
    0x03,                                           /* scriptSig length: 3 */
    0xaa, 0xbb, 0xcc,                               /* scriptSig bytes */
    0xfe, 0xff, 0xff, 0xff,                         /* sequence: 0xfffffffe */

    0x02,                                           /* output count: 2 */
    /* Output 0 */
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, /* value: 1 satoshi */
    0x01,                                           /* scriptPubKey length: 1 */
    0x51,                                           /* scriptPubKey bytes */
    /* Output 1 */
    0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, /* value: 2 satoshis */
    0x02,                                           /* scriptPubKey length: 2 */
    0x6a, 0x00,                                     /* scriptPubKey bytes */

    0x44, 0x33, 0x22, 0x11,                         /* locktime: 0x11223344 */
};

/* The serialization API requires a writer callback. Accept its bytes without
 * inspecting or retaining them; zero tells the kernel the write succeeded. */
static int discard_writer(const void* bytes, size_t size, void* user_data)
{
    (void)bytes;
    (void)size;
    (void)user_data;
    return 0;
}

int main(void)
{
    /* Obtain non-null handles before passing them to the remaining functions. */
    btck_Transaction* tx = btck_transaction_create(TRANSACTION, sizeof(TRANSACTION));
    CHECK(tx != NULL);
    btck_TxValidationState* state = btck_tx_validation_state_create();
    CHECK(state != NULL);
    btck_Transaction* copy = btck_transaction_copy(tx);
    CHECK(copy != NULL);

    /* Exercise the calls, without comparing transaction behavior or results. */
    CHECK(btck_transaction_to_bytes(tx, discard_writer, NULL) == 0);
    (void)btck_transaction_check(tx, state);
    (void)btck_tx_validation_state_get_validation_mode(state);
    (void)btck_tx_validation_state_get_tx_validation_result(state);

    /* Release each acquired handle; no post-destruction lifetime scenario. */
    btck_transaction_destroy(copy);
    btck_transaction_destroy(tx);
    btck_tx_validation_state_destroy(state);
    puts("btc-verified transaction C ABI smoke test passed");
    return 0;
}
