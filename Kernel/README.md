# Lean-backed transaction kernel

`Transaction.lean` supplies pure Lean operations for Bitcoin Core's
`bitcoinkernel.h` interface: packed transaction decoding and encoding,
transaction-local checks, field snapshots, and txid computation.
`Kernel/` is a consumer of the specification in `BtcVerified/`, not another
consensus model or a dependency of the specification.

## Public C interface

`bitcoinkernel.c` implements a deliberately small transaction slice of the
unchanged upstream header. `abi.toml` pins the Core commit, header path, and
SHA-256; `exports.txt` enumerates the nine public functions:

- `btck_transaction_create`, `copy`, `to_bytes`, `check`, and `destroy`.
- `btck_tx_validation_state_create`, `destroy`, `get_validation_mode`, and
  `get_tx_validation_result`.

The prefixes above apply to every listed suffix. All other functions are
absent, not stubs: a caller using an unsupported symbol must fail to link.
Field, witness, and txid operations exist on the Lean side but are not yet
exposed through this C library. This is not a complete libbitcoinkernel replacement.

An ordinary C client includes only the authenticated upstream `bitcoinkernel.h`.
The shim calls Lean for prefix decoding, canonical serialization, and local
checking, then stores immutable native bytes and the verdict. No Lean object
escapes creation. Copies share an atomic reference count; the final destroy
frees the snapshot. Caller input buffers may be released after creation.
Serialization callbacks may reenter the API and must return normally through C.
Each validation state is mutable and must not be accessed concurrently without
caller synchronization; transaction snapshots can be shared with proper ownership.

Lean initialization is internal and serialized; entering foreign threads are
registered and their thread-local resources finalized at thread exit. The library
must stay loaded until process exit: unloading/reloading is not supported.
Lean module constants intentionally have process lifetime. C-owned allocations
are explicitly released, but runtime exhaustion or fatal Lean errors can terminate
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

## Native checks

```sh
lake run kernel-check
```

This builds current sources, checks the exact dynamic export set with `nm`,
compiles and runs `tests/abi.c` as an ordinary C caller, and verifies that
`tests/unsupported.c` compiles but fails to link on the unimplemented locktime
accessor. No test client includes Lean headers or performs runtime initialization.

Fixed fixtures cover legacy, SegWit, and coinbase transactions; parse rejection
and prefix consumption; canonical bytes; parse success with local-check failure;
validation-state overwrite; copy and input-buffer lifetimes; failing/reentrant
callbacks; and foreign-thread initialization and concurrent copies. These are
ABI regression tests, not a differential campaign or a proof of C memory safety.

The same command runs in the existing PR CI workflow, reusing the `.lake` and
toolchain cache. Test, compiler, and negative-link logs plus the observed symbol
list are saved under `.lake/build/kernel/` and uploaded as CI diagnostics, never
committed. Native artifacts are also generated locally, not stored in Git.

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

- `nonCoinbaseCheck_eq_isWellFormed`: packed size measurement preserves the existing
  non-coinbase checker.
- `coinbaseCheck_iff`: the packed coinbase checker accepts exactly when
  `Tx.CoinbaseWellFormed` holds.
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

`lake build` builds the Lean boundary and `KernelTests.lean` (fixed wire fixtures
and axiom audits); `lake lint` checks both default libraries. Native building is
an explicit `kernel` target. Differential comparison with Core is a subsequent
increment; the larger reference implementation remains in PR #56. Module
organization and deeper witness semantics are tracked in #59 and #60.
