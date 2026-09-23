import Lean
/-!
  # Kernel check command options

  The command-line configuration is independent of the kernel implementation.
  Parsing is pure; the check runner owns filesystem and process effects.
-/

namespace Kernel.Tools

/-- Options for the standalone kernel build, symbol audit, and C ABI tests. -/
structure Options where
  /-- Run the ordinary C clients and the unsupported-symbol negative control. -/
  test : Bool := false
  /-- Print usage without building anything. -/
  help : Bool := false
  /-- Optional checkout used only to obtain the authenticated public header. -/
  coreSource : Option String := none
  /-- C compiler used for the shim, linker, and native clients. -/
  compiler : Option String := none
  /-- Symbol inspection program. -/
  nm : String := "nm"
  /-- Optional minimum macOS deployment version. -/
  macosDeploymentTarget : Option String := none
  deriving BEq

private def setValue (options : Options) (key value : String) : Except String Options := do
  if value.isEmpty || value.startsWith "--" then
    throw s!"{key} requires a nonempty value"
  match key with
  | "--core-source" => return { options with coreSource := some value }
  | "--cc" => return { options with compiler := some value }
  | "--nm" => return { options with nm := value }
  | "--macos-deployment-target" => return { options with macosDeploymentTarget := some value }
  | _ => throw s!"unknown argument: {key}"

/-- Parse the kernel command's flags, rejecting missing values and unknown options. -/
def Options.parse (args : List String) (options : Options := {}) : Except String Options :=
  match args with
  | [] => .ok options
  | "--test" :: rest => parse rest { options with test := true }
  | "--help" :: rest | "-h" :: rest => parse rest { options with help := true }
  | flag :: rest => do
      let (key, inlineValue) := match flag.splitOn "=" with
        | [key] => (key, none)
        | key :: parts => (key, some (String.intercalate "=" parts))
        | [] => (flag, none)
      unless ["--core-source", "--cc", "--nm", "--macos-deployment-target"].contains key do
        throw s!"unknown argument: {flag}"
      match inlineValue with
      | some value => parse rest (← setValue options key value)
      | none => match rest with
        | value :: remaining => parse remaining (← setValue options key value)
        | [] => throw s!"{key} requires a value"

/-- The dependency-tracked targets required by the standalone check. -/
def Options.lakeArgs : Array String :=
  #["build", "kernel", "KernelTests", "KernelToolsTests"]

/-- Pass overrides at target execution time, without Lake's persistent `-K` configuration cache. -/
def Options.buildEnvironment (options : Options) : Array (String × Option String) :=
  #[ ("BTC_VERIFIED_KERNEL_CORE_SOURCE", options.coreSource),
     ("BTC_VERIFIED_KERNEL_CC", options.compiler),
     ("BTC_VERIFIED_KERNEL_MACOS_DEPLOYMENT_TARGET", options.macosDeploymentTarget) ]
    |>.filter (·.2.isSome)

/-- User-facing command synopsis. -/
def Options.usage : String := String.intercalate "\n" [
  "Usage: lake exe kernel-check [--test] [--core-source PATH] [--cc COMPILER]",
  "       [--nm PROGRAM] [--macos-deployment-target VERSION]", "",
  "Builds the Lean-backed kernel, authenticates the pinned Core header, audits",
  "exact public exports, and saves reports under .lake/kernel/. With --test,",
  "also runs standalone C ABI/lifecycle tests and an expected link failure.",
  "Never builds or executes Bitcoin Core or the differential harness.", ""]

end Kernel.Tools
