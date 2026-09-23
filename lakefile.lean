import Lake

open Lake DSL

package «btc-verified» where
  version := v!"0.1.0"
  license := "Apache-2.0"
  testDriver := "tests"
  lintDriver := "batteries/runLinter"
  leanOptions := #[⟨`weak.linter.mathlibStandardSet, true⟩]

require "leanprover-community" / "mathlib"

@[default_target] lean_lib BtcVerified
@[default_target] lean_lib ModuleAudit
@[default_target] lean_lib Tests
lean_lib Fuzz where
  roots := #[`Fuzz.Transaction]
@[default_target] lean_lib FuzzTests

lean_exe tests where
  root := `TestsMain
lean_exe «module-audit» where
  root := `ModuleAuditMain
  supportInterpreter := true
lean_exe bench where
  root := `BenchMain
