"""Verify that the real Lean observation's dynamic result remains leak-checked.

The control succeeds only when an ordinary replay is clean, deliberately
abandoning one dynamic observation produces a symbolized LeakSanitizer report,
and the saved input reproduces both outcomes. This does not establish that all
possible leaks are detectable or justify any persistent-object exemption.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import re
import shlex
import shutil
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
INJECT_ENV = "BTC_VERIFIED_INJECT_LEAK"
ARTIFACT_ENV = "BTC_VERIFIED_LEAK_ARTIFACT"
INJECT_TOKEN = "transaction-observation-leak-v1"
LEAK_EXIT_CODE = 23
INJECTION_MARKER = "btc-verified: deliberate dynamic Lean observation leak enabled"
# Replace, rather than extend, inherited sanitizer options. In particular,
# user-provided suppressions and detect_leaks=0 cannot validate this control.
SANITIZER_ENVIRONMENT = {
    "ASAN_OPTIONS": (
        "detect_leaks=1:leak_check_at_exit=1:symbolize=1:malloc_context_size=60:"
        "fast_unwind_on_malloc=0:abort_on_error=0"
    ),
    "LSAN_OPTIONS": "exitcode=23:print_suppressions=1",
}


class LeakControlFailed(RuntimeError):
    """The injected ownership error did not satisfy the leak-test contract."""


def validate_injected_log(exit_code: int, text: str) -> None:
    """Reject arbitrary failures, unsymbolized reports, and unrelated leaks."""
    requirements = {
        "LeakSanitizer exit code 23": exit_code == LEAK_EXIT_CODE,
        "one dynamic-result injection": text.count(INJECTION_MARKER) == 1,
        "successful semantic comparison": "replay passed: 1 inputs" in text,
        "LeakSanitizer diagnostic": "ERROR: LeakSanitizer: detected memory leaks" in text,
        "observation allocation stack": re.search(r"(?m)^\s*#\d+.*\blean_observe\b", text),
        "Lean scalar-array allocation stack": re.search(
            r"(?m)^\s*#\d+.*\blean_alloc_(?:object|sarray)\b", text),
        "one direct leaked object": re.search(
            r"Direct leak of [1-9]\d* byte\(s\) in 1 object\(s\) allocated from:", text),
        "exactly one leaked allocation": re.search(
            r"SUMMARY: (?:AddressSanitizer|LeakSanitizer): [1-9]\d* byte\(s\) "
            r"leaked in 1 allocation\(s\)\.", text),
        "no semantic failure": "btc-verified transaction fuzz failure:" not in text,
        "no AddressSanitizer memory error": "ERROR: AddressSanitizer:" not in text,
        "no indirect leaked object": "Indirect leak of" not in text,
    }
    missing = [name for name, satisfied in requirements.items() if not satisfied]
    if missing:
        raise LeakControlFailed("leak control failed its contract: " + ", ".join(missing))


def _manifest(directory: Path, relative_to: Path) -> list[dict[str, Any]]:
    return [{
        "path": str(path.relative_to(relative_to)),
        "size": path.stat().st_size,
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    } for path in sorted(directory.rglob("*")) if path.is_file()]


def run_leak_control(run: Any, output: Path, seed: Path, *, enabled: bool) -> dict[str, Any]:
    """Run recorded phases using check.py's EvidenceRun interface.

    The caller must set enabled only for a Linux ASan build with leak-visible
    Lean allocation. An unavailable platform is recorded explicitly, never
    reported as a passing leak check.
    """
    report: dict[str, Any] = {"status": "running" if enabled else "unavailable"}
    run.report["leak_negative_control"] = report
    if not enabled:
        report["reason"] = "requires a Linux sanitizer build with leak-visible Lean allocation"
        run.write()
        return report

    directory = run.directory / "leak-negative-control"
    corpus = directory / "corpus"
    replay = directory / "replay"
    corpus.mkdir(parents=True)
    replay.mkdir()
    control = corpus / "first-payment"
    shutil.copy2(seed, control)
    reproducer = directory / "injected-leak.input"
    replay_input = replay / "injected-leak.input"
    reproduced = directory / "reproduced-leak.input"
    script = directory / "reproduce.sh"
    binary_relative = output.resolve().relative_to(ROOT)
    script.write_text(
        "#!/usr/bin/env bash\n"
        "set -euo pipefail\n"
        "repo_root=\"$(git rev-parse --show-toplevel)\"\n"
        "report_dir=\"$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)\"\n"
        "unset BTC_VERIFIED_INJECT_MISMATCH BTC_VERIFIED_FAILURE_ARTIFACT\n"
        + "".join(f"export {key}={shlex.quote(value)}\n"
                  for key, value in SANITIZER_ENVIRONMENT.items())
        + f"export {INJECT_ENV}={INJECT_TOKEN}\n"
        + f"export {ARTIFACT_ENV}=\"$report_dir/manual-leak.input\"\n"
        + f"exec \"$repo_root/\"{shlex.quote(str(binary_relative))} "
        "--replay=\"$report_dir/replay\"\n")
    script.chmod(0o755)
    report.update({
        "expected_exit_code": LEAK_EXIT_CODE,
        "sanitizer_environment": SANITIZER_ENVIRONMENT,
        "reproduce_command": 'bash "$BTC_VERIFIED_REPORT_DIR/leak-negative-control/reproduce.sh"',
        "reproduce_requirements": (
            "Set BTC_VERIFIED_REPORT_DIR to this run directory and run from a "
            "btc-verified checkout containing the same Linux sanitizer-built harness. "
            "The script uses the saved raw input and must exit 23 with a LeakSanitizer report."),
    })
    run.write()

    def phase(name: str, source: Path, artifact: Path, *, injected: bool) -> int:
        environment = {
            **SANITIZER_ENVIRONMENT,
            INJECT_ENV: INJECT_TOKEN if injected else "",
            ARTIFACT_ENV: str(artifact),
            "BTC_VERIFIED_INJECT_MISMATCH": "",
            "BTC_VERIFIED_FAILURE_ARTIFACT": str(directory / f"unexpected-{name}.input"),
        }
        exit_code = run.phase(name, [output, f"--replay={source}"],
                              environment=environment, expect_success=not injected)
        log = run.logs / f"{len(run.report['phases']):02d}-{name}.log"
        text = log.read_text(errors="replace")
        if injected:
            validate_injected_log(exit_code, text)
            if not artifact.is_file() or artifact.read_bytes() != control.read_bytes():
                raise LeakControlFailed("leak control did not preserve the complete raw input")
        elif (artifact.exists() or INJECTION_MARKER in text or
              "ERROR: LeakSanitizer:" in text or "replay passed: 1 inputs" not in text):
            raise LeakControlFailed("clean leak-control replay was not clean")
        if (directory / f"unexpected-{name}.input").exists():
            raise LeakControlFailed("leak control unexpectedly produced a semantic failure artifact")
        return exit_code

    try:
        phase("leak-baseline", corpus, directory / "unexpected-baseline-leak.input", injected=False)
        report["injected_exit_code"] = phase(
            "leak-injected", corpus, reproducer, injected=True)
        shutil.copy2(reproducer, replay_input)
        phase("leak-reproduce-clean", replay, directory / "unexpected-replay-leak.input", injected=False)
        report["reproduced_exit_code"] = phase(
            "leak-reproduce-injected", replay, reproduced, injected=True)
        report["status"] = "passed"
    except Exception:
        report["status"] = "failed"
        raise
    finally:
        report["artifacts"] = _manifest(directory, run.directory)
        run.write()
    return report
