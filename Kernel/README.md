# Lean kernel boundary

`Transaction.lean` supplies the pure Lean operations for a future implementation
of Bitcoin Core's `bitcoinkernel.h` interface: packed transaction decoding and
encoding, transaction-local checks, field snapshots, and txid computation.
`Kernel/` is a consumer of the specification in `BtcVerified/`, not another
consensus model or a dependency of the specification.

`nonCoinbaseCheck` evaluates the [six named specification predicates](../BtcVerified/Consensus/README.md#transaction-local-premises).
Only `StrippedSizeLeMaxStrippedTransactionSize` needs a kernel-local implementation:
it measures packed bytes, with agreement established by the transport proof.

`coinbaseCheck` checks the single-null-input coinbase shape, nonempty outputs,
output-value and stripped-size bounds, and the 2–100-byte scriptSig bound.
Its authoritative specification is `Tx.CoinbaseWellFormed` in
[`Consensus/CoinbaseStateless.lean`](../BtcVerified/Consensus/CoinbaseStateless.lean);
`Tx.Coinbase` names the classification alone, including malformed coinbases.
`check` selects between the two checkers using the input shape; placement as
the first transaction is a separate block constraint.

Checked claims:

- `decode_eq_spec`: kernel decoding is specification parsing followed by the
  container-size guard, discarding the unconsumed suffix.
- `decode_encode_append`: encoding then decoding, with any appended suffix,
  returns the original transaction if its containers fit the guard and rejects
  it otherwise.
- `nonCoinbaseCheck_eq_isWellFormed`: packed size measurement preserves the existing
  non-coinbase checker.
- `coinbaseCheck_iff`: the packed coinbase checker accepts exactly when
  `Tx.CoinbaseWellFormed` holds.
- `check_iff`: the main checker accepts exactly the specification selected by
  coinbase classification: `Tx.CoinbaseWellFormed` or `Tx.WellFormed`.
- `witnesses_toList`: witness snapshots preserve the full nested byte lists in
  order, including empty stacks and empty items.
- `witnesses_size_eq_inputs_size`: witness snapshots align with input counts.
- `encodeStripped_toList`: stripped bytes equal the specification encoding.
- `txid_eq_txid`: hashing those bytes returns the specification's txid.

Why it matters: these local transport proofs keep executable kernel operations
connected to the authoritative model before adding a native calling boundary.
The `btcv_kernel_*` exports use Lean's private FFI; they are **not** the public
`btck_*` C API. This increment provides no C shim or shared library.

The source-pinned compatibility guards and coinbase branch are documented in
the module. The container-size guard runs **after** decoding: it restricts
accepted values, not decoding resource usage. Neither these proofs nor the
fixed fixtures establish equivalence to Core or full consensus validity.

The tests separate three kinds of evidence:

- `Tests/TransactionRules.lean` checks named specification predicates on explicit
  Lean transaction values, without invoking a parser or importing the kernel.
- `KernelTests.lean` contains nine assertions across four independently justified
  cases: the first Bitcoin payment's amounts, txid and checker verdict; the SegWit
  activation coinbase's witness, txid and verdict; an unknown flag added to that
  passing coinbase; and the empty object that parses but fails checking. Published
  txids are literal expected answers, not hashes computed through the specification.
- `KernelTests/AxiomAudit.lean` audits the nine universal claims above. General
  decoder, dispatch, witness and refinement contracts are proved once rather
  than sampled repeatedly in the examples.

`Tests/TransactionFixtures.lean` supplies the small specification-rule values;
it does not derive them from our encoder or decoder. The kernel examples reuse
the externally sourced bytes in `Tests/GoldenVectors.lean`, not these values.
The reduced kernel suite is intentionally not an exhaustive malformed-input or
accessor regression catalogue: each retained case explains what independent
expectation it contributes. It does not exercise large container/size boundaries.

`lake build` builds all three groups; `lake lint` checks their default libraries.
No Core checkout, native build, or differential campaign is required. The native
ABI and its future differential consumer remain in the reference work tracked
by PR #56.
