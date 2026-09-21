#!/usr/bin/env python3
"""Build, but never run, the transaction conformance harness (Python 3.11+).

Requires the pinned Core checkout, an existing instrumented CMake build,
an installed Lean toolchain with local dependency checkouts, and (for ASan)
the completed pinned Lean stage-1 sanitizer build prepared by check.py. No
cloning, configuration, package installation, or cache downloads are done.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / ".lake/fuzz"


def run(*arguments: str | Path, capture: bool = True) -> str:
    """Run an argument-vector command at the repository root, failing loudly."""
    command = [str(argument) for argument in arguments]
    summary = shlex.join(command)
    print(f"+ {summary[:240]}{' ...' if len(summary) > 240 else ''}", file=sys.stderr)
    result = subprocess.run(command, cwd=ROOT, check=True, text=True,
                            stdout=subprocess.PIPE if capture else None)
    return result.stdout.strip() if capture else ""


def require(condition: bool, message: str) -> None:
    """Stop before building if a reproducibility prerequisite is unmet."""
    if not condition:
        raise ValueError(message)


def cmake_cache(path: Path) -> dict[str, str]:
    """Read CMake's KEY:TYPE=VALUE entries without interpreting their values."""
    return {match[1]: match[2] for line in path.read_text().splitlines()
            if (match := re.match(r"^([^/#][^:]*):[^=]+=(.*)$", line))}


def enabled(value: str) -> bool:
    """Recognize the normal affirmative CMake boolean spellings."""
    return value.upper() in {"1", "ON", "TRUE", "YES", "Y"}


def compiler_is(path: str, expected: Path) -> bool:
    """Compare configured compiler paths after resolving store/symlink wrappers."""
    candidate = Path(path)
    return candidate.is_file() and candidate.resolve() == expected.resolve()


def sanitizer_names(flags: list[str]) -> set[str]:
    """Collect every comma-separated sanitizer named by compiler flags."""
    return {
        sanitizer
        for flag in flags if flag.startswith("-fsanitize=")
        for sanitizer in flag.removeprefix("-fsanitize=").split(",")
    }


def validated_sanitizer_prefix(source: Path, build: Path, prefix: Path, cc: Path, cxx: Path,
                               ordinary_prefix: Path, revision: str) -> Path:
    """Validate the exact stage whose allocator/runtime the harness will use."""
    require(prefix == (build / "stage1").resolve(),
            "sanitized Lean prefix must be the selected build's stage1 directory")
    require(run("git", "-C", source, "rev-parse", "HEAD") == revision,
            "sanitized Lean source HEAD differs from fuzz.toml")
    require(not run("git", "-C", source, "status", "--porcelain", "--untracked-files=all"),
            "sanitized Lean source has local files or changes")
    top_cache = cmake_cache(build / "CMakeCache.txt")
    cache = cmake_cache(build / "stage1/CMakeCache.txt")
    require(Path(top_cache["CMAKE_HOME_DIRECTORY"]).resolve() == source,
            "sanitized Lean top-level build uses another source tree")
    require(Path(top_cache["STAGE1_PREV_STAGE"]).resolve() == ordinary_prefix,
            "sanitized Lean top-level build does not override stage1 PREV_STAGE")
    require(Path(cache["CMAKE_HOME_DIRECTORY"]).resolve() == source / "src",
            "sanitized Lean stage1 uses another source tree")
    require(Path(cache["PREV_STAGE"]).resolve() == ordinary_prefix,
            "sanitized Lean stage1 must bootstrap from the selected ordinary toolchain")
    for option in ("USE_MIMALLOC", "SMALL_ALLOCATOR", "BSYMBOLIC", "USE_LAKE"):
        require(not enabled(cache.get(option, "ON")),
                f"sanitized Lean stage1 must configure {option}=OFF")
    require(compiler_is(cache["CMAKE_C_COMPILER"], cc),
            "sanitized Lean and Core must use the same C compiler")
    require(compiler_is(cache["CMAKE_CXX_COMPILER"], cxx),
            "sanitized Lean and Core must use the same C++ compiler")
    require(cache.get("LEAN_SPECIAL_VERSION_DESC") == "rc2",
            "sanitized Lean stage1 must preserve the rc2 version descriptor")
    for executable in ("cadical", "leantar"):
        require(Path(cache[executable.upper()]).resolve() == ordinary_prefix / "bin" / executable,
                f"sanitized Lean stage1 must reuse ordinary {executable}")
    compile_flags = " ".join(cache.get(key, "") for key in (
        "LEAN_EXTRA_CXX_FLAGS", "CMAKE_C_FLAGS", "CMAKE_CXX_FLAGS"))
    link_flags = " ".join(cache.get(key, "") for key in (
        "LEAN_EXTRA_LINKER_FLAGS", "CMAKE_EXE_LINKER_FLAGS"))
    require({"address", "undefined"} <= sanitizer_names(shlex.split(compile_flags)),
            "sanitized Lean stage1 must compile with address and undefined sanitizers")
    require({"address", "undefined"} <= sanitizer_names(shlex.split(link_flags)),
            "sanitized Lean stage1 must link with address and undefined sanitizers")
    leanc = prefix / "bin/leanc"
    lean = prefix / "bin/lean"
    require(leanc.is_file() and lean.is_file(),
            f"sanitized Lean compiler binaries are missing below: {prefix / 'bin'}")
    require(f"commit {revision}" in run(lean, "--version"),
            "sanitized Lean compiler version differs from fuzz.toml")
    for name in ("leancpp", "Init", "Std", "Lean", "leanrt", "Lake"):
        require((prefix / f"lib/lean/lib{name}.a").is_file(),
                f"sanitized Lean archive is missing: lib{name}.a")
    return leanc


def sanitizer_cflags(leanc: Path, prefix: Path, ordinary_prefix: Path) -> list[str]:
    """Use and validate the public flags emitted by this exact sanitizer stage."""
    flags_text = run(leanc, "--print-cflags")
    require(str(ordinary_prefix) not in flags_text,
            "sanitized leanc emitted an ordinary-toolchain compile path")
    flags = shlex.split(flags_text.replace(str(prefix), shlex.quote(str(prefix))))
    require({"address", "undefined"} <= sanitizer_names(flags),
            "sanitized leanc cflags must include address and undefined sanitizers")
    include = str(prefix / "include")
    require(include in flags or f"-I{include}" in flags,
            "sanitized leanc cflags do not select the sanitizer stage headers")
    return flags


def exact_lean_link_flags(prefix: Path, flags_text: str, ordinary_prefix: Path) -> list[str]:
    """Resolve every Lean archive to stage1 so no ordinary archive can win search."""
    flags = shlex.split(flags_text.replace(str(prefix), shlex.quote(str(prefix))))
    require(str(ordinary_prefix) not in flags_text,
            "sanitized leanc emitted an ordinary-toolchain link path")
    require({"address", "undefined"} <= sanitizer_names(flags),
            "sanitized leanc ldflags must include address and undefined sanitizers")
    lean_libraries = {"leancpp", "Init", "Std", "Lean", "leanrt", "Lake"}
    resolved: list[str] = []
    seen: set[str] = set()
    for flag in flags:
        if flag.startswith("-l") and flag[2:] in lean_libraries:
            name = flag[2:]
            resolved.append(str(prefix / f"lib/lean/lib{name}.a"))
            seen.add(name)
        else:
            resolved.append(flag)
    require(seen == lean_libraries,
            f"sanitized leanc link flags omitted Lean archives: {sorted(lean_libraries - seen)}")
    return resolved


def main() -> None:
    """Validate the local inputs, build their objects, and link the harness."""
    os.chdir(ROOT)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core-build", type=Path, required=True,
                        help="existing configured Core build directory")
    parser.add_argument("--core-source", type=Path, default=ARTIFACTS / "core")
    parser.add_argument("--output", type=Path, default=ARTIFACTS / "transaction")
    parser.add_argument("--fuzzer-library", type=Path,
                        help="explicit standalone libFuzzer archive (e.g. for Apple Clang)")
    parser.add_argument("--sanitizers",
                        default="fuzzer" if sys.platform == "darwin" else "fuzzer,address",
                        help="comma-separated Core/link sanitizers; must include fuzzer")
    parser.add_argument("--macos-deployment-target",
                        help="final link minimum macOS version; defaults to Core's cache")
    parser.add_argument("--lean-build", type=Path,
                        help="completed top-level Lean sanitizer build (required with address)")
    parser.add_argument("--lean-source", type=Path,
                        help="exact Lean source checkout (required with address)")
    parser.add_argument("--lean-prefix", type=Path,
                        help="sanitized Lean stage1 prefix (required with address)")
    args = parser.parse_args()
    sanitizers = args.sanitizers.split(",")
    require(all(name in {"fuzzer", "address"} for name in sanitizers),
            "--sanitizers supports only fuzzer and address")
    require("fuzzer" in sanitizers and len(sanitizers) == len(set(sanitizers)),
            "--sanitizers must include fuzzer exactly once and contain no duplicates")
    source, build, output = args.core_source.resolve(), args.core_build.resolve(), args.output.resolve()
    require(output.is_relative_to(ARTIFACTS.resolve()), "--output must be inside .lake/fuzz")
    configuration = tomllib.loads((ROOT / "fuzz.toml").read_text())
    pin = configuration["bitcoinkernel"]["rev"]
    require(isinstance(pin, str) and re.fullmatch(r"[0-9a-fA-F]{40}", pin) is not None,
            "fuzz.toml must contain an exact 40-hex bitcoinkernel.rev")
    require(run("git", "-C", source, "rev-parse", "HEAD") == pin.lower(), "Core HEAD differs from fuzz.toml")
    require(not run("git", "-C", source, "status", "--porcelain", "--untracked-files=all"),
            "Core has local files or changes; use a clean checkout of the pinned revision")
    cache = cmake_cache(build / "CMakeCache.txt")
    require(Path(cache["CMAKE_HOME_DIRECTORY"]).resolve() == source, "Core build uses another source tree")
    require(enabled(cache.get("BUILD_KERNEL_LIB", "")), "Core build must enable BUILD_KERNEL_LIB")
    require(not enabled(cache.get("BUILD_SHARED_LIBS", "OFF")), "Core build must use a static kernel")
    require(not enabled(cache.get("BUILD_FOR_FUZZING", "OFF")), "BUILD_FOR_FUZZING disables the kernel")
    require(set(cache.get("SANITIZERS", "").split(",")) == set(sanitizers),
            f"Core build must set SANITIZERS={args.sanitizers}")
    cc = Path(cache["CMAKE_C_COMPILER"])
    compiler = Path(cache["CMAKE_CXX_COMPILER"])
    require(cc.is_file() and compiler.is_file(), "Configured Core compilers are missing")
    fuzzer = args.fuzzer_library.resolve() if args.fuzzer_library else None
    require(fuzzer is None or fuzzer.is_file(), "Standalone libFuzzer archive does not exist")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        require((ROOT / manifest["packagesDir"] / package["name"]).is_dir(),
                f"Missing local Lean dependency: {package['name']}; prepare dependencies first")
    lean_pin = configuration["lean"]["rev"]
    require(isinstance(lean_pin, str) and re.fullmatch(r"[0-9a-f]{40}", lean_pin) is not None,
            "fuzz.toml must contain an exact lowercase 40-hex lean.rev")
    require(f"commit {lean_pin}" in run("lean", "--version"),
            "ordinary Lean toolchain does not match fuzz.toml lean.rev")
    platform_flags = []
    if sys.platform == "darwin":
        sysroot = cache.get("CMAKE_OSX_SYSROOT", "")
        require(Path(sysroot).is_dir() and bool(sysroot), "Core cache must identify an existing macOS SDK")
        platform_flags += ["-isysroot", sysroot]
        deployment = args.macos_deployment_target or cache.get("CMAKE_OSX_DEPLOYMENT_TARGET", "")
        require(re.fullmatch(r"\d+(\.\d+){0,2}", deployment) is not None, "Invalid macOS deployment target")
        platform_flags += [f"-mmacosx-version-min={deployment}"]
        for arch in filter(None, cache.get("CMAKE_OSX_ARCHITECTURES", "").split(";")):
            platform_flags += ["-arch", arch]
    else:
        require(args.macos_deployment_target is None, "macOS deployment override requires macOS")
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    run("cmake", "--build", build, "--target", "bitcoinkernel", "--parallel", "2", capture=False)
    archive = build / "lib/libbitcoinkernel.a"
    require(archive.is_file(), f"Static kernel archive is missing: {archive}")
    run("lake", "--no-cache", "build", "FuzzTests", capture=False)
    imports = json.loads(run("lake", "--no-cache", "query", "--json", "+Fuzz.Transaction:transImports"))
    require(isinstance(imports, list) and all(isinstance(name, str) for name in imports), "Bad Lake imports JSON")
    modules = list(dict.fromkeys(["Fuzz.Transaction", *imports]))
    ordinary_prefix = Path(run("lean", "--print-prefix")).resolve()
    if "address" in sanitizers:
        require(sys.platform == "linux", "Lean leak instrumentation is currently supported on Linux only")
        require(all(value is not None for value in (
            args.lean_source, args.lean_build, args.lean_prefix)),
            "--lean-source, --lean-build and --lean-prefix are required with AddressSanitizer")
        lean_source = args.lean_source.resolve()
        lean_build, prefix = args.lean_build.resolve(), args.lean_prefix.resolve()
        leanc = validated_sanitizer_prefix(
            lean_source, lean_build, prefix, cc, compiler, ordinary_prefix, lean_pin)
        cflags = sanitizer_cflags(leanc, prefix, ordinary_prefix)
        targets = [f"+{name}:c" for name in modules]
        run("lake", "--no-cache", "build", *targets, capture=False)
        sources_text = run("lake", "--no-cache", "query", "--json", *targets)
        sources = [json.loads(line) for line in sources_text.splitlines() if line.strip()]
        require(len(sources) == len(targets) and
                all(isinstance(source, str) and Path(source).is_file() for source in sources),
                "Lake must return one generated C source per transitive module")
        object_root = ARTIFACTS / "lean-sanitized-objects"
        objects = []
        for module, generated_source in zip(modules, sources, strict=True):
            obj = object_root.joinpath(*module.split(".")).with_suffix(".o")
            obj.parent.mkdir(parents=True, exist_ok=True)
            run(leanc, "-c", *cflags, "-DLEAN_EXPORTING", generated_source,
                "-o", obj, capture=False)
            objects.append(str(obj))
        lean_flags = exact_lean_link_flags(
            prefix, run(leanc, "--print-ldflags"), ordinary_prefix)
    else:
        require(args.lean_source is None and args.lean_build is None and args.lean_prefix is None,
                "sanitized Lean arguments require AddressSanitizer")
        targets = [f"+{name}:o" for name in modules]
        objects_text = run("lake", "--no-cache", "query", "--json", *targets)
        objects = [json.loads(line) for line in objects_text.splitlines() if line.strip()]
        require(len(objects) == len(targets) and
                all(isinstance(obj, str) and Path(obj).is_file() for obj in objects),
                "Lake must return one existing object path per requested target")
        prefix = ordinary_prefix
        flags_text = run("lake", "env", "leanc", "--print-ldflags")
        # leanc prints space-separated flags; protect the known prefix if it contains spaces.
        lean_flags = shlex.split(flags_text.replace(str(prefix), shlex.quote(str(prefix))))
    response = ARTIFACTS / "lean-objects.rsp"
    response.write_text("\n".join(json.dumps(obj) for obj in objects) + "\n")
    link_sanitizers = [
        "fuzzer-no-link" if name == "fuzzer" and fuzzer else name
        for name in sanitizers
    ]
    sanitizer = ",".join(link_sanitizers)
    command = [str(compiler), "-std=c++20", "-O1", "-g", "-fno-omit-frame-pointer",
               f"-fsanitize={sanitizer}", "-DBITCOINKERNEL_STATIC", *platform_flags,
               "-I", str(source / "src"), "-I", str(prefix / "include"),
               "Fuzz/transaction.cpp", f"@{response}", str(archive),
               *([str(fuzzer)] if fuzzer else []), "-L", str(prefix / "lib"), *lean_flags,
               "-o", str(output)]
    output.parent.mkdir(parents=True, exist_ok=True)
    run(*command, capture=False)
    # Record only a completed link. If linking fails, metadata for an older
    # executable remains paired with that older executable.
    (ARTIFACTS / "build.json").write_text(json.dumps({"core_rev": pin, "core_build": str(build),
        "lean_rev": lean_pin,
        "lean_source": str(lean_source) if "address" in sanitizers else None,
        "lean_prefix": str(prefix), "ordinary_lean_prefix": str(ordinary_prefix),
        "lean_generated_source_count": len(modules), "object_count": len(objects),
        "lean_cflags": cflags if "address" in sanitizers else None,
        "lean_exporting": "address" in sanitizers,
        "sanitizers": sanitizers,
        "link_command": command}, indent=2) + "\n")
    print(f"Built {output}; no fuzzing was executed.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        sys.exit(f"build failed: {error}")
