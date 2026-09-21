# Context-free transaction differential checks

This target compares btc-verified's executable, proved packed transaction
decoder and transaction-local checker with the public C API of the exact
Bitcoin Core revision in [`../fuzz.toml`](../fuzz.toml). It is deliberately
narrower than transaction acceptance in a mempool or block: it uses Core's
`btck_transaction_check`, which wraps `CheckTransaction` and consults neither
chainstate nor script execution.

Within a configured campaign's input domain, both implementations independently
produce a canonical observation or reject parsing, and the harness requires the
results to agree. A successful observation contains:

1. the context-free check verdict;
2. canonical transaction serialization;
3. input count, output count, and locktime;
4. every input's previous txid bytes, output index, sequence, scriptSig, and
   witness items; and
5. every output's signed amount bit pattern and scriptPubKey.

All transcript integers are written independently of the transaction codecs.
This prevents a matching decode/encode mistake, such as using the wrong byte
order in both directions, from cancelling itself out. Core's validation mode
and reason category are also checked for consistency with its boolean result.
The public API does not expose the transaction version as a field; it remains
covered by parsing and reserialization. Transaction-id hashing is outside this
target's structural-check boundary.

Core's generic deserializer rejects CompactSize container lengths above
`0x02000000`, an implementation resource ceiling that btc-verified's protocol
codec does not impose ([pinned `MAX_SIZE`](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/serialize.h#L35),
[range check](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/serialize.h#L333-L363)).
Complete encodings above that length are therefore a known parser-domain
difference. The campaigns documented here stay below that ceiling—the largest
fixed case is 4,000,069 bytes—and make their `-max_len` explicit. This target
does not claim parser equivalence above the stated campaign domain.

## Model boundary

`Tx.isWellFormed` is intentionally the regular-transaction projection of
Core's checker: it rejects every null prevout because coinbase validity is a
block-position rule in the consensus model. The fuzz adapter adds Core's
standalone coinbase branch—exactly one null input and a 2–100 byte scriptSig—so
the two executable observations implement the same `CheckTransaction` predicate
within the stated parser domain. This does not change the consensus model or
claim that a passing transaction can be admitted to a block.

The regular adapter uses the packed transaction-body length in place of the
specification list encoder's length. Its equality to `Tx.isWellFormed` is proved
from `PackedCodec.toList_encode`; this keeps million-byte test cases on the
proved packed implementation instead of overflowing the native stack in the
list-based specification encoder.

## Building and running

From a clean checkout, the complete check is one command:

```sh
nix develop -c python3 -B Fuzz/check.py
```

This requires Nix with flakes enabled. The first Linux invocation needs network
access to realize the development shell, fetch Lean caches, and fetch the
pinned Core and Lean commits. It also performs a substantial source build of
Lean's sanitizer stage 1; later CI runs reuse only an exact-key cache of that
source/build pair.

`Fuzz/check.py` reads the Core revision and campaign bounds from `fuzz.toml`.
It creates or reuses ignored checkouts at the exact Core and Lean revisions,
configures a minimal static kernel build with Clang and libFuzzer, builds the
current Lean and C++ sources, and then runs, in order:

1. the small deterministic controls;
2. the large deterministic controls;
3. a sorted replay of the repository's nine generated transaction seeds;
4. the count-bounded libFuzzer campaign; and
5. a deliberate-mismatch negative control; and
6. on supported Linux ASan builds, a dynamic-Lean-allocation leak control.

The large suite explicitly exercises stripped sizes 999,999, 1,000,000, and
1,000,001 bytes, large witness data that does not count toward that limit, and
CompactSize boundaries. It therefore covers the consensus size boundary even
though the ordinary generated inputs are capped at 4,096 bytes. The default
campaign is fixed at seed 1 and 100,000 executions; all limits remain visible
and reviewable in `fuzz.toml`.

Every invocation writes a fresh directory below `.lake/fuzz/runs/`. Its
`report.json` and `summary.md` identify both source revisions and any local
changes, the Core checkout, toolchain versions, every command and exit status,
campaign limits and observed final statistics, corpus hashes, and failure
artifacts. A fuzz mismatch also records the exact execution count reached before
the failure. Each phase has a separate complete log. The report is finalized
even when checkout, configuration, build, regression, replay, or fuzzing fails.

The semantic negative control first confirms a known transaction agrees normally. It
then alters one byte of the completed Lean observation through an explicitly
test-only environment seam. The child comparison must abort for the expected
semantic-difference reason, save the complete input, and that input must pass
with injection disabled and fail again with injection enabled. An arbitrary
process failure does not satisfy the control. The saved report includes a
portable replay script that resolves an extracted artifact's own directory.

The leak control separately replays the same raw input cleanly, then abandons
exactly one ordinary dynamic `ByteArray` returned by the real Lean observation.
The injected child must exit with the configured LeakSanitizer code, name
`lean_observe` in the allocation stack, and report exactly that one direct
allocation; the saved input must then reproduce both the clean and injected
outcomes. A crash, a C++-only allocation, or an unsymbolized leak report does
not satisfy the control. Unsupported platforms record this check as
unavailable, never passed.

CI executes the same command on every push and pull request to `master`. Lean
dependencies, the exact Core checkout, its minimal CMake build tree, the exact
sanitizer Lean source/stage-1 build, and Core compiler objects are cached
outside Git. The source-build caches are exact-only and keyed by their pinned
revision, runner/workspace identity, Nix toolchain, and build scripts. On an
exact Core cache hit, CMake verifies that `bitcoinkernel` is up to date; the
harness and project-generated Lean C are still rebuilt against current inputs.
The complete run directory is uploaded for 30 days even when the job fails, so
logs and reproducing inputs are available from the workflow run.

Linux CI instruments Core, the harness, every transitive project/dependency C
module, and the pinned Lean stage-1 runtime/libraries with AddressSanitizer.
The stage uses Lean's official `sanitize` preset with `USE_MIMALLOC=OFF`,
`SMALL_ALLOCATOR=OFF`, `BSYMBOLIC=OFF`, and `USE_LAKE=OFF`; it bootstraps from
the exact ordinary toolchain selected by `lean-toolchain`, including that
prefix's `cadical` and `leantar`, and preserves the `rc2` version descriptor.
Ordinary Lake still
elaborates the project and generates C, but those C files are recompiled with
the complete sanitizer-stage `leanc --print-cflags` contract plus
`LEAN_EXPORTING`; both address and undefined sanitizers are required. The final
link names that stage's static Lean archives explicitly. No call scope disables
LeakSanitizer.

Lean's own precise persistent-object transition remains enabled: the pinned
runtime marks the intended process-lifetime object graph and, in an ASan build,
annotates those objects individually for LeakSanitizer. The admission rules,
identified fixed-lifetime allocations, exact source references, and limits of
that evidence are in [`MEMORY.md`](MEMORY.md). Any new unexplained report is a
failure to investigate, not a leak budget or permission to widen suppression.

On macOS, the runner uses libFuzzer without AddressSanitizer because LLVM's
ASan runtime can spin during initialization before `main` on macOS 26. The
report records memory checking as unavailable there. Both platforms retain the
semantic comparisons, corpus replay, bounded campaign, and mismatch control.

## Lower-level commands

The orchestrator uses `Fuzz/build.py` as a separately checkable build boundary.
That helper still requires an existing pinned Core checkout and configured
build, validates them, links the harness, and never executes it. Individual
phases can also be run directly after a successful complete check:

```sh
.lake/fuzz/transaction --regression=small
.lake/fuzz/transaction --regression=large
.lake/fuzz/transaction --replay=.lake/fuzz/runs/<run>/inputs/seeds
```

Generate deterministic cases as raw corpus inputs if desired:

```sh
lake env lean --run Fuzz/SeedCorpus.lean .lake/fuzz/seeds
.lake/fuzz/transaction --regression=large --write-corpus=.lake/fuzz/generated-corpus
```

A successful Linux report means no disagreement was found in the deterministic,
replayed, or generated inputs that invocation executed, the mismatch detector
worked, the ordinary leak replay was clean, and the injected dynamic Lean leak
was detected. It is evidence for these tested boundaries, not proof of
equivalence to Core, complete leak freedom, full transaction validity, or block
validity.
