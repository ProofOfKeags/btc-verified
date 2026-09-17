import Lean
import BtcVerified
import ModuleAudit
/-!
  # The module-discipline audit executable

  `lake exe module-audit` imports the built library at runtime (the same
  posture as batteries' `runLinter`) and applies the policy in
  `ModuleAudit.lean`. Violations print with their module and the executable
  exits nonzero, failing CI alongside `lake build`/`lake test`/`lake lint`.

  The static `import BtcVerified` makes the built library a compile-time
  prerequisite of this executable, so `lake exe module-audit` rebuilds stale
  `.olean`s before loading them into a runtime environment. The checker in
  `ModuleAudit` is independent of the audited library.
-/

open Lean Meta

/-- Import the built library and audit it. -/
unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := ModuleAudit.btcVerifiedPolicy.libraryPrefix }] {}
    (trustLevel := 1024) (loadExts := true)
  let (code, _) ← (ModuleAudit.run ModuleAudit.btcVerifiedPolicy env).toIO
    { fileName := "<module-audit>", fileMap := default } { env }
  return code
