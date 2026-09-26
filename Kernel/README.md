# Lean-backed transaction kernel

`Transaction.lean` supplies pure Lean operations for Bitcoin Core's
`bitcoinkernel.h` interface: packed transaction decoding and encoding,
transaction-local checks, field snapshots, and txid computation.
`Kernel/` is a consumer of the specification in `BtcVerified/`, not another
consensus model or a dependency of the specification.

## Public C interface

`bitcoinkernel.c` implements a deliberately small transaction slice of the
unchanged upstream header. `abi.toml` pins the Core commit, header path, and
SHA-256; its `exports` array enumerates the nine public functions:

- `btck_transaction_create`, `copy`, `to_bytes`, `check`, and `destroy`.
- `btck_tx_validation_state_create`, `destroy`, `get_validation_mode`, and
  `get_tx_validation_result`.

The prefixes above apply to every listed suffix. All other functions are
absent, not stubs: a caller using an unsupported symbol must fail to link.
Field, witness, and txid operations exist on the Lean side but are not yet
exposed through this C library. This is not a complete libbitcoinkernel replacement.

Each public function in [`bitcoinkernel.c`](bitcoinkernel.c) reproduces its full
documentation from the [pinned upstream header](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h),
with parameter names adapted to the local definition. Separately labeled
sections spell out upstream declaration/ownership conventions and
btc-verified-specific behavior. The copied documentation carries Bitcoin Core's
MIT notice in [`COPYING.bitcoin`](COPYING.bitcoin). When changing the pin, review
these comments and their source permalinks alongside the implementation.

An ordinary C client includes only the authenticated upstream `bitcoinkernel.h`.
The opaque transaction handle retains the decoded Lean `Tx` itself. Creation
copies the input into Lean and prefix-decodes it; `to_bytes` invokes the Lean
encoder, and `check` invokes the Lean checker on each call. There is no C
transaction representation, serialization/verdict cache, or custom reference
counter. This keeps transaction state and computation in the implementation
connected to the specification, rather than maintaining a parallel C snapshot.

Before exposing a handle, the shim uses the pinned multithreaded Lean runtime's
`lean_mark_mt` to enable atomic reference counting for its reachable objects.
`copy` acquires a Lean reference; `destroy` releases one. Serialization and
checking each give their consuming Lean export a temporary reference, preserving
the caller's ownership. Callers must hold a live handle during use and synchronize publication
between threads. The input buffer may be released after creation.

Serialization retains its Lean output buffer until the writer returns. Callbacks
may reenter the API, but must return normally through C so the buffer can be
released. Validation states remain small, mutable C output records containing
the public ABI's mode/result codes; they must not be accessed concurrently
without caller synchronization. The consensus decision is computed in Lean,
not in that output record.

Lean initialization is internal and serialized; entering foreign threads are
registered and their thread-local resources finalized at thread exit. The library
must stay loaded until process exit: unloading/reloading is not supported.
Lean module constants intentionally have process lifetime; transaction handles
are reference-counted, not made persistent. Every operation that uses or releases
a Lean value enters the runtime on its calling thread. If that entry fails,
creation/copy return null and serialization returns an error; checking and
destruction terminate the process because their interfaces provide no suitable
runtime-error channel. Lean runtime exhaustion or fatal errors can also terminate
the process; this is not a guarantee of recoverable out-of-memory behavior.

The handwritten adapter is C, not C++. Lean owns the generated code and runtime,
including its transitive C++ support. `lean_bridge.h` is private: generated Lean
definitions are type-checked against it during the native build, and its symbols
are hidden from the shared library's public exports.

## Build

```sh
lake build kernel
```

This optional target builds `.lake/build/lib/libbtc_verified_kernel.dylib` on
macOS or `.lake/build/lib/libbtc_verified_kernel.so` on Linux. The authenticated
header is `.lake/build/kernel/include/bitcoinkernel.h`. It downloads only that
header, never configures, builds, links, or executes Core, and requires no Python.
All generated headers, objects, and binaries stay under the ignored `.lake/`.

An existing exact Core checkout can supply the header without a download:

```sh
BTC_VERIFIED_KERNEL_CORE_SOURCE=/path/to/pinned/bitcoin lake build kernel
```

The checkout revision, header Git object, and digest are checked. Otherwise an
authenticated cached header is reused or fetched from the commit-addressed URL.
The build traces sources, pins, headers, export manifest, Lean objects, compiler
version, and flags. `lakefile.lean` replaces the TOML build configuration only
to express these native dependencies; the upstream pin remains TOML data.

Tools: Lean/Lake, a host C11 compiler and linker (`CC`, default `cc`), POSIX
threads, `curl`, and `shasum` (macOS) or `sha256sum` (Linux); `git` is needed for
the local-checkout option. Use an absolute path for a `CC` override: Lake may
prepend Lean's restricted-sysroot compiler to `PATH`. Lean supplies its runtime
link flags. Windows is not supported by this build target.

The library links against the pinned Lean shared runtime, not its
executable-oriented static runtime. Its runtime search paths point into the
local toolchain; clients require its shared libraries at those paths.
Unresolved symbols still fail the library link.

## Native checks

```sh
lake run kernel-check
```

This builds current sources, then compiles and runs `tests/abi.c` as an ordinary
C caller. The smoke test calls every supported symbol in `abi.toml`, using one
transaction fixture to obtain handles and a discard callback for serialization.
It checks only that handle creation and serialization succeed so the calls can
complete. No client includes Lean headers or performs runtime initialization.
When adding an export, add its call to this smoke test.

The test does not compare bytes, verdicts, or validation-state values, or exercise
rejection, lifetime, callback-error, reentry, or threading scenarios. Behavioral
tests belong in `KernelTests.lean`; comparison with Core belongs in the forthcoming
differential suite. Neither covers the handwritten C boundary automatically:
this smoke test claims only basic callability, not behavioral equivalence or C
memory/thread safety. The build still restricts public exports using `abi.toml`;
there is no separate export audit or unsupported-symbol test.

The same command runs in the existing PR CI workflow, reusing the `.lake` and
toolchain cache. Library build diagnostics (including compiler/linker failures)
and client compiler/execution output are saved in `.lake/build/kernel/abi-test.log`
and uploaded as CI diagnostics, never committed. Build diagnostics also remain
visible in the terminal. Native artifacts are generated locally, not stored in Git.

## Lean specification and proofs

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
connected to the authoritative model. The `btcv_kernel_*` names use Lean's
private FFI and are hidden behind the public `btck_*` C interface. The C adapter,
compiler, and runtime remain outside these Lean proofs.

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
No Core checkout, native build, or differential campaign is required for these
Lean checks. Native building is an explicit `kernel` target. Differential
comparison with Core is a subsequent increment; the larger reference
implementation remains in PR #56. Module
organization and deeper witness semantics are tracked in #59 and #60.
