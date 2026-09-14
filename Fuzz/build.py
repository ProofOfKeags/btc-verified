#!/usr/bin/env python3
"""Build, but never run, the transaction conformance harness (Python 3.11+).

Requires the pinned Core checkout, an existing instrumented CMake build,
and an installed Lean toolchain with local dependency checkouts. No cloning,
configuration, package installation, or build-cache downloads are performed.
Lean objects retain their existing instrumentation; this is not an ASan build
of the Lean compiler/runtime or every generated Lean object.
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
    parser.add_argument("--macos-deployment-target",
                        help="final link minimum macOS version; defaults to Core's cache")
    args = parser.parse_args()
    source, build, output = args.core_source.resolve(), args.core_build.resolve(), args.output.resolve()
    require(output.is_relative_to(ARTIFACTS.resolve()), "--output must be inside .lake/fuzz")
    pin = tomllib.loads((ROOT / "fuzz.toml").read_text())["bitcoinkernel"]["rev"]
    require(isinstance(pin, str) and re.fullmatch(r"[0-9a-fA-F]{40}", pin) is not None,
            "fuzz.toml must contain an exact 40-hex bitcoinkernel.rev")
    require(run("git", "-C", source, "rev-parse", "HEAD") == pin.lower(), "Core HEAD differs from fuzz.toml")
    require(not run("git", "-C", source, "status", "--porcelain", "--untracked-files=no"),
            "Core has tracked changes; use a clean checkout of the pinned revision")
    cache = cmake_cache(build / "CMakeCache.txt")
    require(Path(cache["CMAKE_HOME_DIRECTORY"]).resolve() == source, "Core build uses another source tree")
    require(enabled(cache.get("BUILD_KERNEL_LIB", "")), "Core build must enable BUILD_KERNEL_LIB")
    require(not enabled(cache.get("BUILD_SHARED_LIBS", "OFF")), "Core build must use a static kernel")
    require(not enabled(cache.get("BUILD_FOR_FUZZING", "OFF")), "BUILD_FOR_FUZZING disables the kernel")
    require(set(cache.get("SANITIZERS", "").split(",")) == {"fuzzer", "address"},
            "Core build must set SANITIZERS=fuzzer,address")
    compiler = Path(cache["CMAKE_CXX_COMPILER"])
    require(compiler.is_file(), "Configured C++ compiler is missing")
    fuzzer = args.fuzzer_library.resolve() if args.fuzzer_library else None
    require(fuzzer is None or fuzzer.is_file(), "Standalone libFuzzer archive does not exist")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        require((ROOT / manifest["packagesDir"] / package["name"]).is_dir(),
                f"Missing local Lean dependency: {package['name']}; prepare dependencies first")
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
    targets = [f"+{name}:o" for name in dict.fromkeys(["Fuzz.Transaction", *imports])]
    objects_text = run("lake", "--no-cache", "query", "--json", *targets)
    objects = [json.loads(line) for line in objects_text.splitlines() if line.strip()]
    require(len(objects) == len(targets) and all(isinstance(obj, str) and Path(obj).is_file() for obj in objects),
            "Lake must return one existing object path per requested target")
    response = ARTIFACTS / "lean-objects.rsp"
    response.write_text("\n".join(json.dumps(obj) for obj in objects) + "\n")
    prefix = Path(run("lake", "env", "lean", "--print-prefix"))
    flags_text = run("lake", "env", "leanc", "--print-ldflags")
    # leanc prints space-separated flags; protect the known prefix if it contains spaces.
    lean_flags = shlex.split(flags_text.replace(str(prefix), shlex.quote(str(prefix))))
    sanitizer = "fuzzer-no-link,address" if fuzzer else "fuzzer,address"
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
        "lean_prefix": str(prefix), "object_count": len(objects), "link_command": command}, indent=2) + "\n")
    print(f"Built {output}; no fuzzing was executed.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        sys.exit(f"build failed: {error}")
