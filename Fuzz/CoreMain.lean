import Fuzz.Build

/-! # Build-only entry point for the pinned, coverage-instrumented Core kernel. -/

/-- Build Core without running any comparisons. -/
def main : IO Unit := do
  IO.println (← Conformance.buildCore ".lake/conformance/build-logs")
