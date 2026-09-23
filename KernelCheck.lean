import Kernel.Tools.Check
/-!
  # Kernel build and ABI check entry point

  Run `lake exe kernel-check --test` from the repository root. The executable
  is Lean tooling, not part of the public kernel library.
-/

/-- Run the standalone kernel check with the provided command-line options. -/
def main (args : List String) : IO UInt32 :=
  Kernel.Tools.runCheck args
