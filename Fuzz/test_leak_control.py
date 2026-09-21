"""Fast tests of leak-control evidence validation; no native build required."""

from pathlib import Path
import tempfile
import unittest

from leak_control import (
    ARTIFACT_ENV, INJECT_ENV, INJECTION_MARKER, INJECT_TOKEN, LEAK_EXIT_CODE,
    ROOT, LeakControlFailed, run_leak_control, validate_injected_log,
)


LEAK_LOG = f"""{INJECTION_MARKER}
replay passed: 1 inputs
==123==ERROR: LeakSanitizer: detected memory leaks

Direct leak of 512 byte(s) in 1 object(s) allocated from:
    #0 0x123 in malloc
    #1 0x124 in lean_alloc_sarray
    #2 0x125 in (anonymous namespace)::lean_observe(std::span<unsigned char const>)

SUMMARY: AddressSanitizer: 512 byte(s) leaked in 1 allocation(s).
"""


class FakeRun:
    """Exercise evidence plumbing without claiming to test the actual allocator."""

    def __init__(self, directory: Path):
        self.directory = directory
        self.logs = directory / "logs"
        self.logs.mkdir()
        self.report = {"phases": []}

    def write(self):
        pass

    def phase(self, name, command, *, environment, expect_success):
        injected = environment[INJECT_ENV] == INJECT_TOKEN
        if injected:
            corpus = Path(str(command[1]).removeprefix("--replay="))
            data = next(corpus.iterdir()).read_bytes()
            Path(environment[ARTIFACT_ENV]).write_bytes(data)
        self.report["phases"].append({"name": name, "environment": environment})
        log = self.logs / f"{len(self.report['phases']):02d}-{name}.log"
        log.write_text(LEAK_LOG if injected else "replay passed: 1 inputs\n")
        return LEAK_EXIT_CODE if injected else 0


class LeakControlTests(unittest.TestCase):
    def test_accepts_precise_diagnostic(self):
        validate_injected_log(LEAK_EXIT_CODE, LEAK_LOG)

    def test_rejects_wrong_failures_and_missing_evidence(self):
        invalid = [
            (0, LEAK_LOG),
            (-6, LEAK_LOG),
            (LEAK_EXIT_CODE, LEAK_LOG.replace(INJECTION_MARKER, "")),
            (LEAK_EXIT_CODE, LEAK_LOG.replace("lean_observe", "unrelated_function")),
            (LEAK_EXIT_CODE, LEAK_LOG.replace("lean_alloc_sarray", "malloc_again")),
            (LEAK_EXIT_CODE, LEAK_LOG.replace("replay passed: 1 inputs", "")),
            (LEAK_EXIT_CODE, LEAK_LOG.replace("1 allocation(s)", "2 allocation(s)")),
            (LEAK_EXIT_CODE, LEAK_LOG + "ERROR: AddressSanitizer: heap-use-after-free\n"),
            (LEAK_EXIT_CODE, LEAK_LOG + "Indirect leak of 8 byte(s) in 1 object(s)\n"),
            (LEAK_EXIT_CODE, LEAK_LOG + "btc-verified transaction fuzz failure: disagreement\n"),
            (LEAK_EXIT_CODE, LEAK_LOG + INJECTION_MARKER),
        ]
        for exit_code, text in invalid:
            with self.subTest(exit_code=exit_code, text=text):
                with self.assertRaises(LeakControlFailed):
                    validate_injected_log(exit_code, text)

    def test_roundtrip_keeps_complete_input_and_reproducer(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            seed = directory / "seed"
            data = bytes(range(256)) * 5
            seed.write_bytes(data)
            run = FakeRun(directory)
            report = run_leak_control(run, ROOT / ".lake/fuzz/transaction", seed, enabled=True)
            self.assertEqual(report["status"], "passed")
            self.assertEqual(len(run.report["phases"]), 4)
            evidence = directory / "leak-negative-control"
            self.assertEqual((evidence / "injected-leak.input").read_bytes(), data)
            self.assertEqual((evidence / "reproduced-leak.input").read_bytes(), data)
            self.assertEqual((evidence / "replay/injected-leak.input").read_bytes(), data)
            self.assertIn("detect_leaks=1", (evidence / "reproduce.sh").read_text())
            self.assertTrue(report["artifacts"])

    def test_unavailable_is_not_a_pass(self):
        with tempfile.TemporaryDirectory() as temporary:
            run = FakeRun(Path(temporary))
            report = run_leak_control(run, ROOT / ".lake/fuzz/transaction", Path("absent"),
                                      enabled=False)
            self.assertEqual(report["status"], "unavailable")
            self.assertEqual(run.report["phases"], [])


if __name__ == "__main__":
    unittest.main()
