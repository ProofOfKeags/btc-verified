# Kernel conformance

This tooling compares the two implementations through the public kernel C API,
not through private Lean exports. `Kernel/abi.toml` is the sole Core pin.
The current campaign exercises transaction operations.

## Build, then run locally or in CI

```sh
nix develop -c lake build kernel-conformance
nix develop -c lake run kernel-conformance
```

The build command fetches the required caches, builds the pinned Core and current
btc-verified sources, and prepares the comparison harness. The first build needs
network access for Nix, Lean caches, and pinned Core. Later builds reuse matching
dependencies and build output.

The run command executes the last prepared build. It does not fetch Lean caches,
compile code, or invoke CMake. Source edits and changed dependency pins require
another explicit build; they do not change an existing prepared build. Campaign
settings are read from the current `Fuzz/campaign.toml` at execution time, so
changing the seed or run budget does not require rebuilding.

Each successful build saves a snapshot under
`.lake/conformance/prepared/<ID>/`, containing `manifest.json`, `report.json`,
`logs/`, and copies of the harness, driver, and both kernel libraries. The
`.lake/conformance/prepared/current` file selects the default build ID. Select
another retained build explicitly with:

```sh
nix develop -c lake run kernel-conformance --build-id ID
```

Missing or modified prepared artifacts cause an error that points to the build
command. The harness does not silently rebuild them.

CI artifacts preserve the prepared snapshots and reports for later replay.
Restored snapshots still require their Lean/Nix runtime dependencies; these are
not standalone distribution binaries.

The Nix development shell targets macOS 15.0 for local native builds, matching
the minimum of Lean's bundled native libraries. Native objects previously built
for a newer macOS target need rebuilding; the Lean proof cache remains reusable.
Core's kernel build continues to target the host macOS version.

Execution replays eight small inputs and three large boundaries, runs a fresh
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

The build command names each preparation stage. The run command names each check
stage, then shows live fuzzing counters at most once per second and at completion.
The execution percentage measures progress toward the configured run budget. The
other counters mean:

| Counter | Meaning |
| --- | --- |
| Coverage blocks/edges | Instrumented blocks or edges reached so far, not a percentage of all code. |
| Features | Distinct coverage feedback signals used to select interesting executions, such as hit counts. |
| Corpus | Inputs currently retained for further mutation, with their total size. |
| Speed | Executions per second; early updates may show zero before a full second has elapsed. |
| Peak memory | Highest resident memory use observed by libFuzzer. |

Final statistics also count new corpus additions over the whole campaign; this
can exceed the final corpus size as inputs are replaced. Executions can repeat
inputs and include malformed transactions. Neither count measures bugs found.
The complete, unfiltered libFuzzer output is saved in `logs/campaign.log`.

`PASS` means both implementations agreed on the exercised observations and, for
a full campaign, the intentional-mismatch checks passed. A saved-input replay
has its own summary and does not run mutation or the detector checks. `FAIL`
names the stage that stopped, points to the report, and prints a replay command
when an archived input is available. The detector stage deliberately causes
failures to verify that disagreements are caught, saved, and reproducible;
their crash output stays in its separate logs.

Each `.lake/conformance/runs/<id>/` contains `report.json`, per-command logs,
generated inputs, the final corpus, and any failure artifacts. Run reports
identify the prepared build and preserve its saved build provenance separately
from the current run's workspace information, campaign settings, and actual
execution count. Build reports and logs preserve source revisions, dirty
status/patch, compiler/Lean/Lake versions, build identity, instrumentation, and
binary hashes. The workspace revision at execution time is not evidence that
its source was compiled into the selected build.

Builds from dirty worktrees are useful locally but are **not reconstructible
from revisions alone**; untracked files and dirty dependencies are not archived
as source. A seed alone does not promise identical mutation sequences across
toolchains. A replay command is recorded only when its relative input artifact
exists, and pins the original build ID. Explicit replays execute their archived
`replay.input`, so the report describes the bytes that were actually checked.

On disagreement, `failures/` holds `mismatch.input`, `core.txt`, `verified.txt`,
and each provider's serialized `.bytes` file. Replay a saved input with:

```sh
nix develop -c lake run kernel-conformance --build-id ID --replay /path/to/mismatch.input
```

Use the command printed by the failed run to select its original build. Omitting
`--build-id ID` uses the current prepared build, which may have changed since the
failure. When both options are present, `--build-id ID` comes before `--replay`.

During mutation, libFuzzer separately saves crashing/timeout inputs; replay them
the same way. Explicit-file replays retain their source under the run directory.
Crashes and resource failures fail execution; build failures stop preparation.
These do not receive the harness's semantic-mismatch label. Logs identify the
failing phase. The negative control's expected failures live separately under
`negative*`, not in the ordinary failure directory.

Coverage feedback comes from Core, the C driver and boundary, and btc-verified's
generated C. Lake compiles the latter into a separate instrumented build, leaving
ordinary objects and dependency/runtime code untouched; the harness rejects a
verified model object, boundary object, or library without SanitizerCoverage
callbacks during preparation. Execution requires libFuzzer to register the driver
plus both providers as three coverage modules. This increment adds no address/leak
sanitizer claims or suppressions. Agreement on exercised inputs is not a proof of
equivalence, independent decoded-field correctness, full transaction validity,
or block validity. Field-accessor coverage from PR #56 is not ported here.

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
provide CMake, Ninja, Boost, and a Clang toolchain with libFuzzer;
`FUZZ_CC` and `FUZZ_CXX` select its compilers. macOS additionally needs its SDK.
