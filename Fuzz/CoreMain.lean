import Fuzz.Build

/-! # Build-only entry point for the pinned, coverage-instrumented Core kernel. -/

/-- Build Core without running any comparisons. -/
def main : IO Unit := do
  IO.eprintln "Building pinned Bitcoin Core (reuses a matching build; first build can take minutes)..."
  (← IO.getStderr).flush
  IO.println (← Conformance.buildCore ".lake/conformance/build-logs")
