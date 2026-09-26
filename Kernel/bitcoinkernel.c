/* Public API documentation below is reproduced from Bitcoin Core's pinned
 * bitcoinkernel.h. Copyright (c) 2024-present The Bitcoin Core developers.
 * Distributed under the MIT license; see COPYING.bitcoin.
 */

/* C adapter for the nine-function transaction slice of the pinned kernel ABI.
 *
 * Call path: ordinary C client -> this file -> lean_bridge.h declarations ->
 * generated exports from Kernel/Transaction.lean. The upstream bitcoinkernel.h
 * is the public contract; lean_bridge.h is private implementation plumbing.
 * A public transaction handle is an opaque pointer to a retained Lean Tx.
 * Creation decodes in Lean; serialization and checking call Lean when asked.
 * There is no C transaction representation, encoded-byte cache, verdict cache,
 * or separate reference counter. C adapts ownership, buffers, and ABI results.
 *
 * This handwritten boundary is outside the Lean proofs. See README.md for
 * build and ownership details.
 *
 * Each public function starts with the full upstream documentation, adapting
 * parameter names to this definition. "Upstream conventions" makes relevant
 * declaration attributes and header-wide ownership rules explicit;
 * "btc-verified notes" describes our implementation, not additional upstream
 * guarantees. Update these comments and permalinks when retargeting abi.toml.
 * The upstream header remains authoritative:
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h
 * In particular, see lines 34-61 for return-value/non-null attributes and
 * lines 105-121 for pointer ownership and argument lifetimes.
 */
#include <bitcoinkernel.h>
#include "lean_bridge.h"

#include <assert.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

/* The public header leaves btck_Transaction incomplete. We never dereference
 * that pointer as a C struct: cast it back to lean_object before use.
 * Validation state is only the mutable ABI output record, not transaction data.
 */
struct btck_TxValidationState {
    btck_ValidationMode mode;
    btck_TxValidationResult result;
};

/* Two lifetimes, neither of which creates a thread:
 * - pthread_once runs runtime/module initialization once for this library.
 * - The pthread key records registration separately for each calling thread,
 *   and invokes finalize_runtime_thread when a registered thread exits.
 * Keep the library loaded until process exit; module constants live that long.
 */
static pthread_once_t runtime_once = PTHREAD_ONCE_INIT;
static pthread_key_t runtime_thread_key;
static bool runtime_ready;
static const char runtime_thread_tag;

static void finalize_runtime_thread(void* tag)
{
    (void)tag;
    /* Release thread-local runtime resources, not the caller's live handles. */
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
    /* Wait for the one-time initializer, then register this thread if needed.
     * No initialization lock is held while executing transaction operations.
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

/**
 * @brief Create a new transaction from the serialized data.
 *
 * @param[in] raw_transaction     Serialized transaction.
 * @param[in] raw_transaction_len Length of the serialized transaction.
 * @return                        The transaction, or null on error.
 *
 * @par Upstream source
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L589-L597
 *
 * @par Upstream conventions
 * Do not discard the returned owning handle; release it with
 * btck_transaction_destroy. The input buffer need not outlive this call.
 *
 * @par btc-verified notes
 * raw_transaction must address raw_transaction_len readable bytes; it may be
 * NULL only when that length is zero. Prefix decoding may leave trailing bytes
 * unused. Success means decoding succeeded, not that transaction_check passed.
 * Decode or runtime-entry failure returns NULL. Fatal Lean errors, including
 * allocation failure, may terminate the process rather than return an error.
 */
btck_Transaction* btck_transaction_create(const void* raw_transaction, size_t raw_transaction_len)
{
    assert(raw_transaction != NULL || raw_transaction_len == 0);
    if (!ensure_runtime()) return NULL;
    lean_object* bytes = lean_alloc_sarray(1, raw_transaction_len, raw_transaction_len);
    if (raw_transaction_len != 0)
        memcpy(lean_sarray_cptr(bytes), raw_transaction, raw_transaction_len);
    lean_object* parsed = btcv_kernel_decode(bytes); /* Consumes bytes. */
    if (lean_is_scalar(parsed)) return NULL; /* Option.none owns no allocation. */

    /* Take an owned reference out of Option.some before releasing the wrapper. */
    lean_object* tx = lean_ctor_get(parsed, 0);
    lean_inc(tx);
    lean_dec(parsed);
    /* Before publishing the handle, let Lean mark its reachable object graph
     * for multi-threaded reference counting. This does not make it persistent:
     * the last destroy still releases it through Lean's runtime.
     */
    lean_mark_mt(tx);
    return (btck_Transaction*)tx;
}

/**
 * @brief Copy a transaction. Transactions are reference counted, so this just
 * increments the reference count.
 *
 * @param[in] transaction Non-null.
 * @return                The copied transaction.
 *
 * @par Upstream source
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L599-L607
 *
 * @par Upstream conventions
 * The input is borrowed, not consumed. Do not discard the returned owning
 * handle; release that ownership separately with btck_transaction_destroy.
 *
 * @par btc-verified notes
 * Requires a live input handle. Returns the same pointer with an additional
 * Lean reference, not a deep copy. Returns NULL if runtime entry fails.
 */
btck_Transaction* btck_transaction_copy(const btck_Transaction* transaction)
{
    assert(transaction != NULL);
    if (!ensure_runtime()) return NULL;
    /* Copy means another ownership share, not a deep copy. The caller must
     * already hold a live handle while acquiring that share.
     */
    lean_inc((lean_object*)transaction);
    return (btck_Transaction*)transaction;
}

/**
 * Destroy the transaction.
 *
 * @par Upstream source
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L705-L708
 *
 * @par Upstream conventions
 * Releases ownership obtained from transaction_create or transaction_copy.
 * Each acquired reference must be released once; other copies retain theirs.
 *
 * @par btc-verified notes
 * NULL is a no-op. Otherwise releases one Lean reference, reclaiming the
 * transaction when the last reference is gone. Runtime-entry failure is fatal:
 * this void interface cannot return an error. Do not use the released ownership
 * again, even if another owner keeps the same pointer alive.
 */
void btck_transaction_destroy(btck_Transaction* transaction)
{
    if (transaction == NULL) return;
    /* Release may run Lean's allocator on a different thread from creation.
     * This void API cannot report failed runtime entry; do not silently leak.
     */
    if (!ensure_runtime()) abort();
    lean_dec((lean_object*)transaction);
}

/**
 * @brief Serializes the transaction through the passed in callback to bytes.
 * This is consensus serialization that is also used for the P2P network.
 *
 * @param[in] transaction Non-null.
 * @param[in] writer      Non-null, callback to a write bytes function.
 * @param[in] data        Holds a user-defined opaque structure that will be
 *                        passed back through the writer callback.
 * @return                0 on success.
 *
 * @par Upstream source
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L609-L622
 *
 * @par Upstream conventions
 * The transaction is borrowed, not consumed. Do not ignore the return status.
 * The callback type is int (*btck_WriteBytes)(const void* bytes, size_t size,
 * void* userdata); the callback returns 0 to indicate success. The header names
 * our data parameter user_data; it is passed through unchanged and may be NULL.
 * Callback documentation:
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L384-L389
 *
 * @par btc-verified notes
 * Encodes in Lean and calls writer once, synchronously, with the full encoding.
 * The byte buffer is borrowed for the callback's duration; copy it if needed
 * later. The callback may reenter the API, but must return normally through C.
 * A nonzero callback result or runtime-entry failure yields -1; fatal Lean
 * errors may terminate the process. Serialization does not validate the tx.
 */
int btck_transaction_to_bytes(const btck_Transaction* transaction, btck_WriteBytes writer, void* data)
{
    assert(transaction != NULL && writer != NULL);
    if (!ensure_runtime()) return -1;
    /* The export consumes one reference. Supply a temporary ownership share
     * so encoding does not consume the caller's handle.
     */
    lean_object* tx = (lean_object*)transaction;
    lean_inc(tx);
    lean_object* encoded = btcv_kernel_encode(tx);
    /* Keep the Lean ByteArray alive throughout the synchronous callback.
     * No runtime lock is held; reentry is allowed, but the callback must
     * return normally so we can release the encoded bytes afterward.
     */
    const int result = writer(lean_sarray_cptr(encoded), lean_sarray_size(encoded), data);
    lean_dec(encoded);
    return result == 0 ? 0 : -1;
}

/**
 * Create a new btck_TxValidationState.
 *
 * @par Upstream source
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L555-L558
 *
 * @par Upstream conventions
 * Do not discard the returned owning handle; release it with
 * btck_tx_validation_state_destroy.
 *
 * @par btc-verified notes
 * Returns NULL on allocation failure. Otherwise starts with mode VALID and
 * result UNSET; these initial values do not mean a transaction has been checked.
 * Pass this mutable output record to transaction_check, then inspect it through
 * the getters. Concurrent access requires caller synchronization.
 */
btck_TxValidationState* btck_tx_validation_state_create(void)
{
    btck_TxValidationState* state = malloc(sizeof(*state));
    if (state != NULL)
        *state = (btck_TxValidationState){btck_ValidationMode_VALID, btck_TxValidationResult_UNSET};
    return state;
}

/**
 * Destroy the btck_TxValidationState.
 *
 * @par Upstream source
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L577-L580
 *
 * @par Upstream conventions
 * Releases the owning handle returned by btck_tx_validation_state_create.
 * Do not access the state after destruction.
 *
 * @par btc-verified notes
 * NULL is a no-op. A non-null state is freed, not reference-counted; destroy it
 * exactly once, after all operations using it have finished.
 */
void btck_tx_validation_state_destroy(btck_TxValidationState* state)
{
    free(state);
}

/**
 * Returns the validation mode from an opaque btck_TxValidationState pointer.
 *
 * @par Upstream source
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L560-L564
 *
 * @par Upstream conventions
 * state must be non-null and live; it is borrowed, not consumed or modified.
 * btck_ValidationMode distinguishes VALID, INVALID, and INTERNAL_ERROR:
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L391-L399
 *
 * @par btc-verified notes
 * Returns the stored mode without running validation. This slice produces
 * VALID or INVALID; runtime-entry failure in transaction_check is fatal, not
 * returned as INTERNAL_ERROR. Do not read concurrently with a state update.
 */
btck_ValidationMode btck_tx_validation_state_get_validation_mode(const btck_TxValidationState* state)
{
    assert(state != NULL);
    return state->mode;
}

/**
 * Returns the validation result from an opaque btck_TxValidationState pointer.
 *
 * btck_transaction_check currently produces only btck_TxValidationResult_UNSET
 * for valid transactions and btck_TxValidationResult_CONSENSUS for invalid
 * ones. Other values remain exposed for forward compatibility with higher-level
 * validation entry points.
 *
 * @par Upstream source
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L566-L575
 *
 * @par Upstream conventions
 * state must be non-null and live; it is borrowed, not consumed or modified.
 *
 * @par btc-verified notes
 * Returns the stored reason without running validation. CONSENSUS does not
 * identify which individual predicate failed. Do not read concurrently with
 * a state update.
 */
btck_TxValidationResult btck_tx_validation_state_get_tx_validation_result(
    const btck_TxValidationState* state)
{
    assert(state != NULL);
    return state->result;
}

/**
 * @brief Run context-free consensus validation on a btck_Transaction.
 *
 * Performs basic structural consensus checks (consensus/tx_check::CheckTransaction)
 * without requiring blockchain state.
 *
 * @param[in]  tx    Non-null, the transaction to validate.
 * @param[out] state Non-null, previously created with
 *                   btck_tx_validation_state_create.
 *                   Overwritten in-place with the validation
 *                   result.
 * @return           1 if valid, 0 if invalid.
 * @note             Only btck_TxValidationResult_UNSET and
 *                   btck_TxValidationResult_CONSENSUS are
 *                   reachable via this function.
 *
 * @par Upstream source
 * https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L685-L703
 *
 * @par Upstream conventions
 * Neither handle is consumed. The header names our state parameter
 * validation_state. Each call replaces that output, including a prior failure.
 *
 * @par btc-verified notes
 * Calls the Lean checker and writes VALID/UNSET on acceptance or
 * INVALID/CONSENSUS on rejection. This is not script/signature verification,
 * a UTXO lookup, or a verdict that the transaction may appear in a given block.
 * Do not access state concurrently without synchronization. Runtime-entry
 * failure is fatal, never reported as a consensus rejection.
 */
int btck_transaction_check(const btck_Transaction* tx, btck_TxValidationState* state)
{
    assert(tx != NULL && state != NULL);
    /* A runtime-entry failure is not a consensus rejection. This API only
     * reports a transaction verdict, so such infrastructure failure is fatal.
     */
    if (!ensure_runtime()) abort();
    lean_object* transaction = (lean_object*)tx;
    lean_inc(transaction); /* Temporary ownership for the consuming export. */
    const bool valid = btcv_kernel_check(transaction);
    /* The upstream contract overwrites the state, including invalid -> valid. */
    *state = valid
        ? (btck_TxValidationState){btck_ValidationMode_VALID, btck_TxValidationResult_UNSET}
        : (btck_TxValidationState){btck_ValidationMode_INVALID, btck_TxValidationResult_CONSENSUS};
    return valid ? 1 : 0;
}
