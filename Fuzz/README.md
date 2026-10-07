# Transaction conformance

This tooling will compare the two implementations through the public kernel C
API, not through private Lean exports. `Kernel/abi.toml` is the sole Core pin.

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
