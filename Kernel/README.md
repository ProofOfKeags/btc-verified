# Lean-backed transaction kernel ABI

This directory builds an independent btc-verified shared library that implements
the transaction-structure slice of Bitcoin Core's public C ABI. Ordinary C
callers include an authenticated copy of the exact upstream
[`bitcoinkernel.h`](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h)
and link only the btc-verified library. Bitcoin Core is neither linked nor
executed.

The pinned header is explicitly
[unversioned and unstable](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L67-L76).
`fuzz.toml` fixes the Core revision and `Kernel/abi.toml` independently fixes the
header path and SHA-256 digest. The build authenticates and copies that header;
it does not maintain a project-owned substitute.

## Scope

The shared library exports exactly 42 of the pinned header's 136 functions:

- transaction parsing, copying, serialization, field access, destruction, and
  transaction-id access;
- context-free transaction checking and validation-state access;
- input, witness-stack, outpoint, transaction-id, scriptPubKey, and output
  getters plus their copy/create/destroy operations; and
- raw scriptSig, witness-item, and scriptPubKey callback writers.

`Kernel/exports.txt` is the reviewed export allowlist. Script verification,
precomputed transaction data, blocks, chainstate, contexts, logging, and every
other unlisted API are intentionally absent. An ordinary program that references
one of those unsupported symbols must fail to link; the test runner checks that
negative contract. This library is therefore not a complete libbitcoinkernel
replacement.

Opaque handles follow the pinned header's ownership rules: `create` and `copy`
return owned handles, getters return parent-bound borrowed views, and destroy
functions accept null. Transactions are immutable and reference counted;
`btck_transaction_copy` increments the transaction handle's atomic reference
count, and the last destroy releases its snapshot. The subsidiary copy APIs
produce independently owned input, witness, outpoint, transaction-id, script,
and output snapshots that remain valid after their source parent is destroyed.
Callers must not retain a borrowed view past its parent's lifetime. These
conventions track the upstream
[pointer and lifetime contract](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.h#L105-L122).

Parsing, canonical serialization, context-free checking, and transaction-id
hashing execute the Lean implementation during transaction creation. Public
handles then contain copied immutable native snapshots, including the eagerly
computed transaction id; the C shim supplies ABI ownership and lifetime
mechanics rather than reimplementing those semantic operations. Its allocation
and failure paths use explicit cleanup. The handwritten shim and both native
tests are C-only and compile with a C compiler. Generated Lean objects and the
inherited Lean runtime may themselves retain C++ linkage, so this is not a claim
that the transitive shared-library artifact is C++-free.

The library initializes and registers the Lean runtime internally, so callers
must not initialize Lean themselves. Keep the library loaded for the lifetime
of the process: unloading and reloading it is not part of this ABI contract, and
the runtime's process-wide constants intentionally live until process exit.

## Files

- `Kernel/Transaction.lean` is the pure, private semantic bridge and contains
  the checked transport facts used by the native boundary.
- `Kernel/bitcoinkernel.c` implements the public C ABI, immutable native
  snapshots, callbacks, ownership, and process/thread runtime registration.
- `Kernel/lean_bridge.h` declares only the private generated Lean entry points;
  it is neither installed nor exported.
- `Kernel/abi.toml` and `Kernel/exports.txt` pin the header and enumerate the
  exact public slice.
- `lakefile.lean` defines the dependency-tracked `kernel` build target. It
  authenticates the header, compiles the C shim, checks the private Lean
  signatures, and links the library with the reviewed export allowlist.
- `Kernel/Tools/` contains the Lean command options, pure symbol comparison,
  symbol-file/process adapter, and standalone check runner. `KernelCheck.lean`
  exposes these through `lake exe kernel-check`.
- `KernelToolsTests.lean` exercises the tooling's parsers and audit failure
  cases independently of transaction semantics.
- `Kernel/tests/abi.c` and `Kernel/tests/threads.c` are ordinary C clients of
  the pinned public header and shared library. `Kernel/tests/unsupported.c`
  must compile but fail to link against the deliberately incomplete ABI.
- `KernelTests.lean` checks fixed encodings and audits the headline Lean
  theorems without importing fuzz code.

## Build and test

From the repository root:

```sh
lake exe kernel-check --test
```

The same command may be run through the development shell:

```sh
nix develop -c lake exe kernel-check --test
```

`lake build kernel` builds just the native library, including the private
signature check. `lake exe kernel-check` additionally checks the Lean test
targets, audits the exact dynamic exports, and saves a run report; `--test`
also runs the native clients and negative-link control. The build graph tracks
the shim, private/public headers, pins, allowlist, compiler settings, and Lean
objects, so unchanged compilation and linking can be reused.

This path uses Lean/Lake, a C compiler/linker, `git`, `curl` for header-only
downloads, `nm`, and a system SHA-256 tool (`shasum` on macOS or `sha256sum` on
Linux). It does not require Python. The repository's older `Fuzz/` tooling
and its existing CI command still do; they are separate from this migration.
External tools run without inherited `DYLD_LIBRARY_PATH`/`LD_LIBRARY_PATH`,
so Lake's injected Lean runtime paths cannot redirect them to Lean's LLVM.
Native test clients receive only the just-built kernel's library directory.

When the exact pinned Core checkout is unavailable, the builder downloads only
the header from the commit-addressed GitHub URL. The SHA-256 check remains
mandatory. The build never configures, builds, loads, or runs Core.

The checker accepts `--core-source PATH`, `--cc COMPILER`, and `--nm PROGRAM`.
For direct `lake build kernel` use, the corresponding build overrides are
the environment variables `BTC_VERIFIED_KERNEL_CORE_SOURCE` and
`BTC_VERIFIED_KERNEL_CC` (the latter otherwise falls back to `CC`/`PATH`).
These are read when the target runs, so command-line choices cannot be ignored
or retained accidentally by Lake's compiled configuration cache.
The header pins remain TOML data; only the Lake build configuration moved from
`lakefile.toml` to `lakefile.lean` to express custom native targets.

On macOS, `--macos-deployment-target` (or the
`BTC_VERIFIED_KERNEL_MACOS_DEPLOYMENT_TARGET` environment variable) overrides
the host-version default and is recorded in `build.json`. An older target is
valid only when every prebuilt Lean
and dependency object was built compatibly. The builder also has a Linux path;
the current live test evidence is from macOS, and the Linux path has not yet
been exercised.

`--test` first runs `Kernel/tests/threads.c` in a fresh process, concurrently
exercising first-use runtime initialization, eager transaction-id access,
cross-thread copies, and cross-thread destruction. It then runs
`Kernel/tests/abi.c`, which uses self-contained legacy and SegWit fixtures to
check all 42 functions, field bytes, signed amounts, prefix parsing,
empty/malformed inputs, validation-state reset, owned-copy lifetimes, regular
and standalone coinbase-shaped check branches, serialization callback
success/failure, callback reentrancy, and legacy and SegWit transaction ids
independently fixed from Python `hashlib` output. Neither test includes or
invokes the differential-fuzz harness.

Outputs are written below `.lake/kernel/`:

- `libbitcoinkernel.so` on Linux or `libbitcoinkernel.dylib` on macOS;
- `include/kernel/bitcoinkernel.h`, the authenticated public header;
- `native-build.json`, the Lake native-build metadata;
- `build.json`, the check's running/pass/fail status, commands, header
  provenance, library digest, and completed ordinary-client test results;
- `check.log`, the runner's subprocess commands, output, and exit codes; and
- `symbols.json` and `symbols.md`, recording canonical, expected, exported,
  unsupported, missing, and unexpected symbols.

Once the checker starts, it replaces the previous run status before the native
build and updates it on failure; a failed subprocess must not leave a stale
passing report. If Lake cannot compile the checker itself, that failure is
reported by Lake before the runner can write a new report. Reports and native
build products remain ignored under `.lake/`.

## Proof and assurance boundary

`Kernel/Transaction.lean` decodes and encodes with the proved packed transaction
codec. Its checked claims connect packed stripped serialization to the
specification encoding, identify the resulting double-SHA-256 bytes with
`Tx.txid`, align witness snapshots with inputs, and prove that the optimized
regular checker equals `Tx.isWellFormed`. The native adapter additionally covers
the standalone coinbase-shaped branch of pinned Core's
[`CheckTransaction`](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/consensus/tx_check.cpp#L19-L67).

The C tests are executable ABI and lifecycle evidence, not formal proofs
of the shim, not a comparison with Core, and not differential fuzzing. A passing
run does not establish full libbitcoinkernel equivalence, script validity, UTXO
availability, fee or maturity rules, finality, mempool/block admission, state
transitions, memory-leak freedom, or safety for unsupported API functions.
