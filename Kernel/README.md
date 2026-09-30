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

- `nonCoinbaseCheck_eq_isWellFormed`: packed size measurement preserves the existing
  non-coinbase checker.
- `coinbaseCheck_iff`: the packed coinbase checker accepts exactly when
  `Tx.CoinbaseWellFormed` holds.
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
- `KernelTests.lean` checks literal wire fixtures, prefix handling, field and
  witness snapshots, and the kernel checker entry points. Parsing, serialization,
  and checker verdicts have separate expectations.
- `KernelTests/AxiomAudit.lean` audits the five universal refinement claims above.

`Tests/TransactionFixtures.lean` supplies the small shared transaction values;
it does not derive them from our encoder or decoder. Raw-wire fixtures remain
independent of that fixture vocabulary.

`lake build` builds all three groups; `lake lint` checks their default libraries.
No Core checkout, native build, or differential campaign is required. The native
ABI and its future differential consumer remain in the reference work tracked
by PR #56.
