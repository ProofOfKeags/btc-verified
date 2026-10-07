# Transaction conformance

This tooling compares the two implementations through the public kernel C API,
not through private Lean exports. `Kernel/abi.toml` is the sole Core pin.

## One local / CI check

```sh
nix develop -c lake run transaction-conformance
```

The first run needs network access for Nix, Lean caches, and pinned Core. Later
runs reuse those dependencies, but build current btc-verified and driver sources.
The command replays eight small inputs and three large boundaries, runs a fresh
libFuzzer corpus with `campaign.toml`'s seed and limits, then checks the detector
with a deliberately injected disagreement. An ordinary run must succeed; the
injected child must fail specifically on the changed verdict, save the complete
input and both observations, and reproduce with injection enabled but not without
it. An arbitrary crash cannot satisfy this negative control.

The same C `observe` routine calls each library through its own function table,
typed from the unmodified upstream header. The libraries are loaded locally,
before libFuzzer initializes coverage; all nine entry points must be distinct.
Handles never cross providers and libraries remain loaded until process exit.
No C++ or Python source is added; Core and libFuzzer retain their own C++ runtime
dependencies.

We compare create acceptance, serialization status and canonical bytes, the
context-free check verdict, and validation mode/result. Before each observed
check, the same state is primed with a known-invalid empty transaction; this
also compares the required invalid-to-valid state replacement. Copy and
destruction are exercised to obtain and release the observed transaction, not
exhaustively tested as ownership contracts. A differing rejection category
fails the check as an API disagreement, not automatically as a consensus
disagreement.

`Seeds.lean` reuses external golden bytes for legacy and witness transactions,
alongside malformed inputs and an empty transaction that parses but fails checking.
Its three plain wire constructions are exactly 999,999, 1,000,000, and 1,000,001
stripped bytes. These replay separately: the 4,096-byte mutation cap is a campaign
budget, not a claim about valid transaction sizes. The seed corpus is regenerated
for each run; prior discoveries cannot silently change a seeded campaign.

## Reading or reproducing a result

Each `.lake/conformance/runs/<id>/` contains `report.json`, per-command logs,
generated inputs, the final corpus, and any failure artifacts. Reports record
revisions, dirty status/patch, compiler/Lean/Lake versions, build identity,
instrumentation, campaign settings, binary hashes, and actual execution count.
The build identity and compiler versions are in `logs/`. Dirty runs are useful
locally but are **not reconstructible from revisions alone**; untracked files
and dirty dependencies are not archived. A seed alone does not promise identical
mutation sequences across toolchains. A replay command is recorded only when
its relative input artifact exists; explicit replays execute their archived
`replay.input`, so the report describes the bytes that were actually checked.

On disagreement, `failures/` holds `mismatch.input`, `core.txt`, `verified.txt`,
and each provider's serialized `.bytes` file. Replay a saved input with:

```sh
nix develop -c lake run transaction-conformance --replay /path/to/mismatch.input
```

During mutation, libFuzzer separately saves crashing/timeout inputs; replay them
the same way. Explicit-file replays retain their source under the run directory.
Crashes, resource failures, and build failures fail the run but do not receive
the harness's semantic-mismatch label. Logs identify the failing phase. The
negative control's expected failures live separately under `negative*`, not in
the ordinary failure directory.

Coverage feedback comes from Core, the C driver and boundary, and btc-verified's
generated C. Lake compiles the latter into a separate instrumented build, leaving
ordinary objects and dependency/runtime code untouched; the runner rejects a
verified model object, boundary object, or library without SanitizerCoverage
callbacks, and requires libFuzzer to register the driver plus both providers as
three coverage modules. This increment adds no address/leak sanitizer claims or
suppressions. Agreement on exercised inputs is not a proof of equivalence,
independent decoded-field correctness, full transaction validity, or block
validity. Field-accessor coverage from PR #56 is not ported here.

## Pinned dependency build

`nix develop -c lake exe core-build` builds only Core's kernel shared library,
with libFuzzer coverage instrumentation and at most two compiler workers.
This does not execute a comparison. No generated binaries enter Git.

Sources and builds live under ignored `.lake/conformance/`; a build identity
records the source revision, platform, compiler and build-tool versions, CMake
options, relevant build environment, recipe, Nix flake and lock, and absolute
paths. Repeating a matching build is an up-to-date check. Logs and the identity
are in `.lake/conformance/build-logs/`.

An existing clean pinned checkout may be supplied with
`BTC_VERIFIED_CORE_SOURCE=/absolute/path`. It is never modified. Outside Nix,
provide CMake, Ninja, pkg-config, Boost, and a Clang toolchain with libFuzzer;
`FUZZ_CC` and `FUZZ_CXX` select its compilers. macOS additionally needs its SDK.
