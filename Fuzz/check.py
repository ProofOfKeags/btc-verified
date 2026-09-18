#!/usr/bin/env python3
"""Build and run the reproducible transaction conformance check (Python 3.11+).

The default invocation provisions the pinned Bitcoin Core source under the
gitignored .lake/fuzz directory, configures its static kernel with Clang and
sanitizers, builds the current Lean/C++ sources, runs deterministic and corpus
checks, executes the bounded campaign from fuzz.toml, and verifies the
deliberate-mismatch negative control. Every phase is recorded under
.lake/fuzz/runs even when the check fails.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import subprocess
import sys
import time
import tomllib
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
FUZZ_ROOT = ROOT / ".lake/fuzz"
INJECT_ENV = "BTC_VERIFIED_INJECT_MISMATCH"
FAILURE_ENV = "BTC_VERIFIED_FAILURE_ARTIFACT"
INJECT_TOKEN = "transaction-observation-v1"


class CheckFailed(RuntimeError):
    """A conformance prerequisite or phase did not satisfy its contract."""


def utc_now() -> str:
    """Return an ISO-8601 UTC timestamp without platform-local ambiguity."""
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def capture(*arguments: str | Path, cwd: Path = ROOT) -> str:
    """Capture a small diagnostic command, returning an empty string on failure."""
    try:
        result = subprocess.run(
            [str(argument) for argument in arguments], cwd=cwd, check=True,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        return result.stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def command_succeeds(*arguments: str | Path, cwd: Path = ROOT) -> bool:
    """Test a command without allowing its output into the evidence log."""
    try:
        return subprocess.run(
            [str(argument) for argument in arguments], cwd=cwd,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    except OSError:
        return False


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def file_manifest(directory: Path, relative_to: Path) -> list[dict[str, Any]]:
    """Describe every regular file below a generated evidence directory."""
    if not directory.is_dir():
        return []
    return [
        {
            "path": str(path.relative_to(relative_to)),
            "size": path.stat().st_size,
            "sha256": sha256_file(path),
        }
        for path in sorted(directory.rglob("*")) if path.is_file()
    ]


def repository_snapshot() -> dict[str, Any]:
    """Record the exact tracked revision and a non-secret description of changes."""
    full_diff = capture("git", "diff", "--binary", "HEAD").encode()
    staged_diff = capture("git", "diff", "--binary", "--cached").encode()
    unstaged_diff = capture("git", "diff", "--binary").encode()
    untracked_files = capture("git", "ls-files", "--others", "--exclude-standard").splitlines()
    untracked_manifest = []
    for name in untracked_files:
        path = ROOT / name
        if path.is_file():
            untracked_manifest.append({
                "path": name,
                "size": path.stat().st_size,
                "sha256": sha256_file(path),
            })
    return {
        "head": capture("git", "rev-parse", "HEAD"),
        "tree": capture("git", "show", "-s", "--format=%T", "HEAD"),
        "branch": capture("git", "branch", "--show-current") or None,
        "status": capture("git", "status", "--porcelain=v1", "--untracked-files=all").splitlines(),
        "changed_files": capture("git", "diff", "--name-status", "HEAD").splitlines(),
        "untracked_files": untracked_files,
        "untracked_manifest": untracked_manifest,
        "diff_sha256": sha256_bytes(full_diff),
        "staged_diff_sha256": sha256_bytes(staged_diff),
        "unstaged_diff_sha256": sha256_bytes(unstaged_diff),
        "github": {
            key.lower(): os.environ[key]
            for key in ("GITHUB_SHA", "GITHUB_HEAD_REF", "GITHUB_BASE_REF")
            if os.environ.get(key)
        },
    }


def first_line(command: list[str]) -> str | None:
    output = capture(*command)
    return output.splitlines()[0] if output else None


class EvidenceRun:
    """Stream child output while maintaining an always-valid JSON run record."""

    def __init__(self, directory: Path, configuration: dict[str, Any]):
        self.directory = directory
        self.logs = directory / "logs"
        self.logs.mkdir(parents=True)
        self.report: dict[str, Any] = {
            "schema": 1,
            "status": "running",
            "started_at": utc_now(),
            "repository": repository_snapshot(),
            "configuration": configuration,
            "campaign": {
                **configuration.get("campaign", {}),
                "executed_units": None,
                "execution_count_source": "not-started",
            },
            "phases": [],
        }
        self.write()

    def relative(self, path: Path) -> str:
        try:
            return str(path.resolve().relative_to(ROOT))
        except ValueError:
            return str(path.resolve())

    def write(self) -> None:
        destination = self.directory / "report.json"
        temporary = destination.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(self.report, indent=2, sort_keys=True) + "\n")
        temporary.replace(destination)

    def phase(self, name: str, command: list[str | Path], *,
              environment: dict[str, str] | None = None,
              expect_success: bool = True) -> int:
        """Run one phase, recording argv, selected environment, duration and output."""
        arguments = [str(argument) for argument in command]
        log = self.logs / f"{len(self.report['phases']) + 1:02d}-{name}.log"
        overrides = environment or {}
        child_environment = os.environ.copy()
        # These test controls must never leak accidentally into ordinary phases.
        child_environment.pop(INJECT_ENV, None)
        child_environment.pop(FAILURE_ENV, None)
        child_environment.update(overrides)
        print(f"\n==> {name}: {shlex.join(arguments)}", flush=True)
        started = time.monotonic()
        started_at = utc_now()
        process: subprocess.Popen[str] | None = None
        interrupted = False
        try:
            with log.open("w", encoding="utf-8") as output:
                output.write(f"$ {shlex.join(arguments)}\n")
                for key, value in sorted(overrides.items()):
                    output.write(f"{key}={value}\n")
                output.flush()
                process = subprocess.Popen(
                    arguments, cwd=ROOT, env=child_environment, text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    errors="replace", bufsize=1)
                assert process.stdout is not None
                for line in process.stdout:
                    sys.stdout.write(line)
                    output.write(line)
                returncode = process.wait()
        except KeyboardInterrupt:
            interrupted = True
            returncode = 130
            if process is not None and process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
            with log.open("a", encoding="utf-8") as output:
                output.write("phase interrupted by user\n")
            print("phase interrupted by user", file=sys.stderr)
        except OSError as error:
            returncode = 127
            with log.open("a", encoding="utf-8") as output:
                output.write(f"could not execute command: {error}\n")
            print(f"could not execute command: {error}", file=sys.stderr)
        matched = (returncode == 0) == expect_success
        self.report["phases"].append({
            "name": name,
            "command": arguments,
            "environment": overrides,
            "expected": "success" if expect_success else "failure",
            "result": "interrupted" if interrupted else ("passed" if matched else "unexpected"),
            "exit_code": returncode,
            "started_at": started_at,
            "duration_seconds": round(time.monotonic() - started, 3),
            "log": self.relative(log),
        })
        self.write()
        if interrupted:
            raise KeyboardInterrupt
        if not matched:
            expectation = "succeed" if expect_success else "fail"
            raise CheckFailed(f"phase {name} did not {expectation}; see {log}")
        return returncode

    def finish(self, status: str, error: str | None = None) -> None:
        self.report["status"] = status
        self.report["finished_at"] = utc_now()
        if error is not None:
            self.report["error"] = error
        self.write()
        self.write_summary()

    def write_summary(self) -> None:
        report = self.report
        repository = report["repository"]
        campaign = report.get("campaign", {})
        lines = [
            "# Transaction conformance run",
            "",
            f"- Status: **{report['status']}**",
            f"- btc-verified: `{repository.get('head')}`",
            f"- Bitcoin Core: `{report.get('core', {}).get('head')}`",
            f"- Started: `{report['started_at']}`",
            f"- Finished: `{report.get('finished_at', 'unfinished')}`",
            f"- Campaign seed: `{campaign.get('seed')}`",
            f"- Requested executions: `{campaign.get('runs')}`",
            f"- Observed executions: `{campaign.get('executed_units')}`",
            f"- Maximum generated input: `{campaign.get('max_len')}` bytes",
            "",
            "## Phases",
            "",
            "| Phase | Expected | Result | Exit | Seconds |",
            "|---|---|---|---:|---:|",
        ]
        for phase in report["phases"]:
            lines.append(
                f"| {phase['name']} | {phase['expected']} | {phase['result']} | "
                f"{phase['exit_code']} | {phase['duration_seconds']} |")
        if repository["status"]:
            lines += ["", "## Local source changes", "", "```text", *repository["status"], "```"]
        if report.get("error"):
            lines += ["", "## Error", "", report["error"]]
        (self.directory / "summary.md").write_text("\n".join(lines) + "\n")


def parse_final_stats(log: Path) -> dict[str, Any]:
    """Extract libFuzzer's stable final-stat labels from a completed log."""
    text = log.read_text(errors="replace")
    labels = {
        "executed_units": "number_of_executed_units",
        "average_exec_per_sec": "average_exec_per_sec",
        "new_units_added": "new_units_added",
        "slowest_unit_time_sec": "slowest_unit_time_sec",
        "peak_rss_mb": "peak_rss_mb",
    }
    values: dict[str, Any] = {}
    for destination, source in labels.items():
        match = re.search(rf"stat::{re.escape(source)}:\s+(\d+)", text)
        if match:
            values[destination] = int(match.group(1))
    if "executed_units" not in values:
        exact = re.search(r"btc-verified fuzz executions before failure:\s+(\d+)", text)
        if exact:
            values["executed_units"] = int(exact.group(1))
            values["execution_count_source"] = "harness-failure-counter"
        else:
            progress = [int(value) for value in re.findall(r"(?m)^#(\d+)\s", text)]
            if progress:
                values["executed_units"] = max(progress)
                values["execution_count_source"] = "last-libfuzzer-progress"
    else:
        values["execution_count_source"] = "libfuzzer-final-stats"
    return values


def validate_campaign(campaign: dict[str, Any]) -> None:
    """Reject settings that could make the nominally bounded check unbounded."""
    for name in ("runs", "max_len", "timeout_seconds", "rss_limit_mb"):
        value = campaign.get(name)
        if type(value) is not int or value <= 0:
            raise CheckFailed(f"campaign.{name} must be a positive integer")
    seed = campaign.get("seed")
    if type(seed) is not int or not 0 <= seed <= 0xFFFFFFFF:
        raise CheckFailed("campaign.seed must be an integer between 0 and 2^32 - 1")
    if type(campaign.get("use_value_profile")) is not bool:
        raise CheckFailed("campaign.use_value_profile must be a boolean")


def ensure_core(run: EvidenceRun, source: Path, repository: str, revision: str) -> None:
    """Create or reuse an ignored checkout, then select the exact configured commit."""
    if not (source / ".git").is_dir():
        if source.exists() and any(source.iterdir()):
            raise CheckFailed(f"Core source path is nonempty but is not a Git checkout: {source}")
        source.mkdir(parents=True, exist_ok=True)
        run.phase("core-init", ["git", "init", source])
    # Do not depend on or rewrite a developer's existing `origin`. This remote
    # belongs to the runner and therefore has one exact configured URL.
    remote = "btc-verified-upstream"
    # Read the literal config value. `git remote get-url` applies a user's
    # url.*.insteadOf transport rewrite (for example HTTPS to SSH), which does
    # not change the configured repository identity.
    remote_url = capture("git", "-C", source, "config", "--get", f"remote.{remote}.url")
    if not remote_url:
        run.phase("core-add-remote", ["git", "-C", source, "remote", "add", remote, repository])
    elif remote_url != repository:
        raise CheckFailed(f"Core {remote} URL is {remote_url!r}, expected {repository!r}")
    if not command_succeeds("git", "-C", source, "cat-file", "-e", f"{revision}^{{commit}}"):
        run.phase("core-fetch", ["git", "-C", source, "fetch", "--depth=1", remote, revision])
    head = capture("git", "-C", source, "rev-parse", "HEAD")
    if head != revision:
        tracked = capture("git", "-C", source, "status", "--porcelain", "--untracked-files=no")
        if tracked:
            raise CheckFailed("Core checkout has tracked changes; refusing to change revisions")
        run.phase("core-checkout", ["git", "-C", source, "checkout", "--detach", revision])
    actual = capture("git", "-C", source, "rev-parse", "HEAD")
    if actual != revision:
        raise CheckFailed(f"Core checkout resolved to {actual}, expected {revision}")
    if capture("git", "-C", source, "status", "--porcelain=v1", "--untracked-files=all"):
        raise CheckFailed("Core checkout has local files or changes; exact pinned source is required")


def toolchain_snapshot(cc: Path, cxx: Path) -> dict[str, Any]:
    return {
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python": platform.python_version(),
        "git": first_line(["git", "--version"]),
        "nix": first_line(["nix", "--version"]),
        "cmake": first_line(["cmake", "--version"]),
        "ninja": first_line(["ninja", "--version"]),
        "ccache": first_line(["ccache", "--version"]),
        "cc": {"path": str(cc), "version": first_line([str(cc), "--version"])},
        "cxx": {"path": str(cxx), "version": first_line([str(cxx), "--version"])},
        "lean": first_line(["lean", "--version"]),
        "lake": first_line(["lake", "--version"]),
    }


def configure_command(source: Path, build: Path, cc: Path, cxx: Path,
                      sanitizers: str) -> list[str]:
    command = [
        "cmake", "-S", str(source), "-B", str(build), "-G", "Ninja",
        f"-DCMAKE_C_COMPILER={cc}", f"-DCMAKE_CXX_COMPILER={cxx}",
        "-DCMAKE_BUILD_TYPE=RelWithDebInfo",
        "-DBUILD_SHARED_LIBS=OFF", "-DBUILD_BITCOIN_BIN=OFF", "-DBUILD_DAEMON=OFF",
        "-DBUILD_GUI=OFF", "-DBUILD_CLI=OFF", "-DBUILD_TESTS=OFF", "-DBUILD_TX=OFF",
        "-DBUILD_UTIL=OFF", "-DBUILD_UTIL_CHAINSTATE=OFF", "-DBUILD_KERNEL_LIB=ON",
        "-DBUILD_KERNEL_TEST=OFF", "-DBUILD_BENCH=OFF", "-DBUILD_FUZZ_BINARY=OFF",
        "-DBUILD_FOR_FUZZING=OFF", "-DENABLE_WALLET=OFF", "-DENABLE_EXTERNAL_SIGNER=OFF",
        "-DENABLE_IPC=OFF", "-DWITH_ZMQ=OFF", "-DWITH_EMBEDDED_ASMAP=OFF",
        "-DWITH_USDT=OFF", "-DWITH_CCACHE=ON", "-DINSTALL_MAN=OFF",
        f"-DSANITIZERS={sanitizers}",
    ]
    if sys.platform == "darwin":
        sdk = capture("xcrun", "--show-sdk-path")
        # This produces a host-local fuzz executable, not a distributable
        # binary. Prefer the host version so it is not lower than the target
        # used by prebuilt Lean objects in the Nix shell.
        deployment = platform.mac_ver()[0] or os.environ.get("MACOSX_DEPLOYMENT_TARGET")
        if not sdk or not deployment:
            raise CheckFailed("macOS requires an SDK and deployment target")
        command += [f"-DCMAKE_OSX_SYSROOT={sdk}", f"-DCMAKE_OSX_DEPLOYMENT_TARGET={deployment}"]
    return command


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core-source", type=Path, default=FUZZ_ROOT / "core")
    parser.add_argument("--core-build", type=Path, default=FUZZ_ROOT / "core-build-ci")
    parser.add_argument("--output", type=Path, default=FUZZ_ROOT / "transaction")
    parser.add_argument("--report-dir", type=Path)
    parser.add_argument("--cc", default="clang")
    parser.add_argument("--cxx", default="clang++")
    parser.add_argument("--fuzzer-library", type=Path)
    parser.add_argument("--skip-lean-cache", action="store_true",
                        help="skip `lake exe cache get` when the cache is already prepared")
    return parser.parse_args()


def main() -> int:
    os.chdir(ROOT)
    args = arguments()
    head = capture("git", "rev-parse", "--short=12", "HEAD") or "unknown"
    if args.report_dir:
        report_directory = args.report_dir.resolve()
    else:
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        report_directory = (FUZZ_ROOT / "runs" / f"{stamp}-{head}").resolve()
        if report_directory.exists():
            report_directory = report_directory.with_name(f"{report_directory.name}-{os.getpid()}")
    report_directory.mkdir(parents=True, exist_ok=False)
    configuration: dict[str, Any] = {}
    configuration_bytes: bytes | None = None
    configuration_error: str | None = None
    try:
        configuration_bytes = (ROOT / "fuzz.toml").read_bytes()
        configuration = tomllib.loads(configuration_bytes.decode())
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as exception:
        configuration_error = f"{type(exception).__name__}: {exception}"
    run = EvidenceRun(report_directory, configuration)
    if configuration_bytes is not None:
        (report_directory / "fuzz.toml").write_bytes(configuration_bytes)
    exit_code = 1
    error: str | None = None
    try:
        if configuration_error is not None:
            raise CheckFailed(f"could not read fuzz.toml: {configuration_error}")
        core_config = configuration["bitcoinkernel"]
        campaign = configuration["campaign"]
        if not isinstance(core_config, dict) or not isinstance(campaign, dict):
            raise CheckFailed("fuzz.toml bitcoinkernel and campaign entries must be tables")
        revision = core_config["rev"]
        repository = core_config["repository"]
        if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
            raise CheckFailed("fuzz.toml must contain an exact lowercase 40-hex bitcoinkernel.rev")
        if not isinstance(repository, str) or not repository:
            raise CheckFailed("fuzz.toml must contain a nonempty bitcoinkernel.repository")
        validate_campaign(campaign)
        source = args.core_source.resolve()
        build = args.core_build.resolve()
        output = args.output.resolve()
        cc_name = shutil.which(args.cc)
        cxx_name = shutil.which(args.cxx)
        if not cc_name or not cxx_name:
            raise CheckFailed("Clang is required; enter the Nix development shell or set --cc/--cxx")
        cc, cxx = Path(cc_name).resolve(), Path(cxx_name).resolve()
        # LLVM's ASan runtime can spin before main on macOS 26. Linux CI keeps
        # ASan coverage; Darwin still runs the complete semantic comparison
        # and negative control with libFuzzer itself.
        sanitizers = "fuzzer" if sys.platform == "darwin" else "fuzzer,address"
        run.report["toolchain"] = toolchain_snapshot(cc, cxx)
        run.report["instrumentation"] = {
            "sanitizers": sanitizers.split(","),
            "address_sanitizer_coverage": sys.platform != "darwin",
        }
        run.write()
        ensure_core(run, source, repository, revision)
        run.report["core"] = {
            "repository": repository,
            "configured_revision": revision,
            "head": capture("git", "-C", source, "rev-parse", "HEAD"),
            "status": capture("git", "-C", source, "status", "--porcelain=v1").splitlines(),
            "source": run.relative(source),
            "build": run.relative(build),
        }
        run.write()

        if not args.skip_lean_cache:
            run.phase("lean-cache", ["lake", "exe", "cache", "get"])
        run.phase("core-configure", configure_command(source, build, cc, cxx, sanitizers))
        build_command: list[str | Path] = [
            sys.executable, "-B", "Fuzz/build.py", "--core-source", source,
            "--core-build", build, "--output", output, "--sanitizers", sanitizers,
        ]
        if args.fuzzer_library:
            build_command += ["--fuzzer-library", args.fuzzer_library.resolve()]
        run.phase("build", build_command)
        build_record = FUZZ_ROOT / "build.json"
        if not build_record.is_file():
            raise CheckFailed("Fuzz/build.py did not produce .lake/fuzz/build.json")
        shutil.copy2(build_record, report_directory / "build.json")

        inputs = report_directory / "inputs"
        seeds = inputs / "seeds"
        failures = report_directory / "failures"
        corpus = report_directory / "campaign/corpus"
        failures.mkdir(parents=True)
        corpus.mkdir(parents=True)
        run.phase("generate-seeds", ["lake", "env", "lean", "--run", "Fuzz/SeedCorpus.lean", seeds])

        def failure_environment(name: str) -> dict[str, str]:
            return {FAILURE_ENV: str(failures / f"{name}.input")}

        run.phase("regression-small", [output, "--regression=small"],
                  environment=failure_environment("regression-small"))
        run.phase("regression-large", [output, "--regression=large"],
                  environment=failure_environment("regression-large"))
        run.phase("replay", [output, f"--replay={seeds}"],
                  environment=failure_environment("replay"))

        fuzz_command: list[str | Path] = [
            output,
            f"-seed={int(campaign['seed'])}",
            f"-runs={int(campaign['runs'])}",
            f"-max_len={int(campaign['max_len'])}",
            f"-timeout={int(campaign['timeout_seconds'])}",
            f"-rss_limit_mb={int(campaign['rss_limit_mb'])}",
            f"-use_value_profile={1 if campaign['use_value_profile'] else 0}",
            "-print_final_stats=1", "-reload=0",
            f"-artifact_prefix={failures}{os.sep}", corpus, seeds,
        ]
        fuzz_log = run.logs / f"{len(run.report['phases']) + 1:02d}-fuzz.log"
        try:
            run.phase("fuzz", fuzz_command, environment=failure_environment("fuzz"))
        finally:
            statistics = parse_final_stats(fuzz_log) if fuzz_log.is_file() else {}
            run.report["campaign"] = {
                **campaign,
                "executed_units": statistics.get("executed_units"),
                "execution_count_source": statistics.get(
                    "execution_count_source", "unavailable"),
                **statistics,
                "seed_manifest": file_manifest(seeds, report_directory),
                "final_corpus_manifest": file_manifest(corpus, report_directory),
            }
            run.write()
        if "executed_units" not in statistics:
            raise CheckFailed(f"libFuzzer did not report its executed-unit count; see {fuzz_log}")
        if file_manifest(failures, report_directory):
            raise CheckFailed("a passing campaign unexpectedly left a failure artifact")
        run.write()

        # Negative control: the input agrees normally, the test-only mutation
        # must fail for the precise comparison reason, and the saved bytes must
        # agree normally again when replayed without injection.
        negative = report_directory / "negative-control"
        negative_corpus = negative / "corpus"
        negative_corpus.mkdir(parents=True)
        control = negative_corpus / "first-payment"
        shutil.copy2(seeds / "first-payment", control)
        run.phase("negative-baseline", [output, f"--replay={negative_corpus}"],
                  environment={FAILURE_ENV: str(negative / "unexpected-baseline.input")})
        reproducer = negative / "injected-mismatch.input"
        injected_exit_code = run.phase(
            "negative-injected", [output, f"--replay={negative_corpus}"],
            environment={INJECT_ENV: INJECT_TOKEN, FAILURE_ENV: str(reproducer)},
            expect_success=False)
        injected_log = run.logs / f"{len(run.report['phases']):02d}-negative-injected.log"
        injected_text = injected_log.read_text(errors="replace")
        required_messages = [
            "btc-verified: deliberate mismatch injection enabled",
            "btc-verified transaction fuzz failure: context-free transaction check differs",
        ]
        if not all(message in injected_text for message in required_messages):
            raise CheckFailed(f"negative control failed for the wrong reason; see {injected_log}")
        if not reproducer.is_file() or reproducer.read_bytes() != control.read_bytes():
            raise CheckFailed("negative control did not preserve the complete triggering input")
        replay_corpus = negative / "replay"
        replay_corpus.mkdir()
        replay_input = replay_corpus / "injected-mismatch.input"
        shutil.copy2(reproducer, replay_input)
        run.phase("negative-reproduce-clean", [output, f"--replay={replay_corpus}"],
                  environment={FAILURE_ENV: str(negative / "unexpected-replay.input")})
        reproduced = negative / "reproduced-mismatch.input"
        run.phase("negative-reproduce-injected", [output, f"--replay={replay_corpus}"],
                  environment={INJECT_ENV: INJECT_TOKEN, FAILURE_ENV: str(reproduced)},
                  expect_success=False)
        reproduced_log = run.logs / f"{len(run.report['phases']):02d}-negative-reproduce-injected.log"
        reproduced_text = reproduced_log.read_text(errors="replace")
        if not all(message in reproduced_text for message in required_messages):
            raise CheckFailed(f"saved negative input failed for the wrong reason; see {reproduced_log}")
        if not reproduced.is_file() or reproduced.read_bytes() != reproducer.read_bytes():
            raise CheckFailed("saved negative input did not reproduce the injected disagreement")
        reproduce_command = "bash \"$BTC_VERIFIED_REPORT_DIR/negative-control/reproduce.sh\""
        reproduce_script = negative / "reproduce.sh"
        reproduce_script.write_text(
            "#!/usr/bin/env bash\n"
            "set -euo pipefail\n"
            "repo_root=\"$(git rev-parse --show-toplevel)\"\n"
            "report_dir=\"$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)\"\n"
            f"export {INJECT_ENV}={INJECT_TOKEN}\n"
            f"unset {FAILURE_ENV}\n"
            "exec \"$repo_root/.lake/fuzz/transaction\" --replay=\"$report_dir/replay\"\n")
        reproduce_script.chmod(0o755)
        run.report["negative_control"] = {
            "status": "passed",
            "injected_exit_code": injected_exit_code,
            "artifacts": file_manifest(negative, report_directory),
            "reproduce_command": reproduce_command,
            "reproduce_requirements": (
                "Set BTC_VERIFIED_REPORT_DIR to this run directory and invoke the command "
                "from a btc-verified checkout after Fuzz/check.py has built "
                ".lake/fuzz/transaction. The script may live in an extracted CI artifact."),
        }
        run.report["failure_artifacts"] = file_manifest(failures, report_directory)
        run.write()
        exit_code = 0
    except (CheckFailed, OSError, ValueError, KeyError, subprocess.SubprocessError,
            KeyboardInterrupt) as exception:
        error = f"{type(exception).__name__}: {exception}"
        print(f"transaction conformance check failed: {exception}", file=sys.stderr)
        run.report["failure_artifacts"] = file_manifest(report_directory / "failures", report_directory)
    finally:
        negative_manifest = file_manifest(report_directory / "negative-control", report_directory)
        if negative_manifest:
            negative_report = run.report.setdefault("negative_control", {"status": "incomplete"})
            negative_report.setdefault("artifacts", negative_manifest)
        run.finish("passed" if exit_code == 0 else "failed", error)
        print(f"transaction conformance report: {report_directory / 'report.json'}")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
