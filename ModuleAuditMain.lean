import Lean
import BtcVerified
/-!
  # The module-discipline audit

  `lake exe module-audit` — the whole-codebase counterpart of
  `Tests/AxiomAudit.lean`: where that audit guards what each theorem
  *depends on*, this one guards where declarations *live*. It imports the
  built library at runtime (the same posture as batteries' `runLinter`),
  walks `Lean.Environment`, and enforces the module discipline CLAUDE.md
  states in prose:

  1. **One type per module** — a `BtcVerified` module declares at most one
     `structure`/`inductive`. Sum-type arm-record clusters may be
     allowlisted in `armRecordClusters` (none today).
  2. **Instances live with their type** — an `instance` of a class this
     library defines targets a type declared in the instance's own module;
     explicitly allowlisted instances for Core/dependency targets live with
     the *class* instead (`instCodecUInt8…64`, `instCodecBitVec256`, and
     `instCodecProd` in `Serialize/Codec.lean`).

  The walk is over elaborated declarations, not source syntax, so renames,
  re-exports, and `abbrev`s cannot fool it; `abbrev`-defined types
  (`CountedList`, `Hash256`) keep their own constant in stored types, so
  they audit like any other. Only attribute-marked instances are checked —
  a deliberately unregistered worked codec (`compactSizeCodec`) is exempt
  by design, matching the issue-#9 wording "every `instance`".

  Violations print with their module and the audit exits nonzero, failing
  CI, which runs it alongside `lake build`/`lake test`/`lake lint`.

  The `import BtcVerified` above is not used by the code — it makes the
  built library a compile-time prerequisite of this executable, so
  `lake exe module-audit` always audits fresh `.olean`s; without it, the
  runtime `importModules` would silently read whatever stale build is on
  disk.
-/

open Lean Meta

namespace ModuleAudit

/-- The module-discipline rules for one audited library. -/
structure Policy where
  /-- Module prefix whose declarations are audited. -/
  libraryPrefix : Name
  /-- Modules permitted to declare a tightly coupled arm-record cluster. -/
  armRecordClusters : List Name := []
  /-- Library instances permitted to target Core/dependency types. -/
  dependencyInstances : List Name := []

/-- The library the production audit applies to. -/
def libraryPrefix : Name := `BtcVerified

/-- Rule-1 allowlist: modules permitted more than one type because they
hold a sum type's arm records that never appear in an outside signature.
Empty today — `SegwitInput` appears in `Tx`'s signature, so it earns its
own module rather than an entry here. -/
def armRecordClusters : List Name := []

/-- Rule-2 allowlist: the intentional instances of `Codec` for
Core/dependency types. Every other dependency-targeting instance is rejected,
even when it lives with the class. -/
def dependencyInstances : List Name := [
  `BtcVerified.Serialize.instCodecProd,
  `BtcVerified.Serialize.instCodecUInt8,
  `BtcVerified.Serialize.instCodecUInt16,
  `BtcVerified.Serialize.instCodecUInt32,
  `BtcVerified.Serialize.instCodecUInt64,
  `BtcVerified.Serialize.instCodecBitVec256
]

/-- The production policy for `btc-verified`. -/
def btcVerifiedPolicy : Policy where
  libraryPrefix := libraryPrefix
  armRecordClusters := armRecordClusters
  dependencyInstances := dependencyInstances

/-- The module a declaration was compiled in, when it is imported. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- Whether a module name belongs to the library selected by `policy`. -/
def inLibrary (policy : Policy) (m : Name) : Bool :=
  policy.libraryPrefix.isPrefixOf m

/-- Every audited-library module paired with the `structure`/`inductive`
constants it declares (classes and private declarations included). -/
def typesByModule (policy : Policy) (env : Environment) : Std.HashMap Name (Array Name) :=
  env.constants.fold (init := {}) fun acc n info =>
    match info with
    | .inductInfo _ =>
      match moduleOf env n with
      | some m => if inLibrary policy m then acc.insert m ((acc.getD m #[]).push n) else acc
      | none => acc
    | _ => acc

/-- Rule 1: no audited module declares two or more types unless
allowlisted as an arm-record cluster. Returns one message per violating
module. -/
def rule1Violations (policy : Policy) (env : Environment) : Array String :=
  typesByModule policy env |>.fold (init := #[]) fun acc m types =>
    if types.size ≥ 2 && !policy.armRecordClusters.contains m then
      acc.push s!"{m}: declares {types.size} types ({", ".intercalate
        (types.map toString).toList}); one type per module, or allowlist an \
        arm-record cluster in ModuleAuditMain.lean"
    else acc

/-- The classes the audited library defines — the classes whose instances
rule 2 constrains. -/
def libraryClasses (policy : Policy) (env : Environment) : Std.HashMap Name Name :=
  env.constants.fold (init := {}) fun acc n _ =>
    if isClass env n then
      match moduleOf env n with
      | some m => if inLibrary policy m then acc.insert n m else acc
      | none => acc
    else acc

/-- Enforce the explicit allowlist and class-module location for an instance
whose target is not a type declared by the audited library. -/
def dependencyInstanceViolation (policy : Policy) (className classModule : Name)
    (instName instModule : Name) (target : String) : Option String :=
  if !policy.dependencyInstances.contains instName then
    some s!"{instName}: instance of {className} for the Core/dependency target \
      {target} is not allowlisted in ModuleAuditMain.lean"
  else if instModule = classModule then none
  else some s!"{instName}: allowlisted instance of {className} for the \
    Core/dependency target {target} lives in {instModule}; such instances \
    live with the class ({classModule})"

/-- Rule 2, for one marked instance: if it instantiates a library class,
its target type's head constant decides where it must live — the target's
module for a library type, the class's module for a Core/dependency type.
Returns a violation message, or `none` when the rule is satisfied or does
not apply. -/
def rule2Violation (policy : Policy) (env : Environment)
    (classes : Std.HashMap Name Name) (instName : Name) (instType : Expr) : Option String := do
  let classApp := instType.getForallBody
  let some className := classApp.getAppFn.constName? | none
  let some classModule := classes.get? className | none
  let some instModule := moduleOf env instName | none
  guard (inLibrary policy instModule)
  let some target := classApp.getAppArgs.back?
    | return s!"{instName}: instance of {className} has no target argument; \
        configure the audit before adding this class"
  match target.getAppFn with
  | .const targetName _ =>
    match moduleOf env targetName with
    | some tm =>
      if inLibrary policy tm then
        if instModule = tm then none
        else some s!"{instName}: instance of {className} for {targetName} \
          (declared in {tm}) lives in {instModule}; a library type's \
          instances live in its module"
      else
        dependencyInstanceViolation policy className classModule instName instModule
          (toString targetName)
    | none =>
      dependencyInstanceViolation policy className classModule instName instModule
        (toString targetName)
  | _ =>
    dependencyInstanceViolation policy className classModule instName instModule
      (toString target)

/-- Rule 2 over the whole environment: check every attribute-marked
instance against `rule2Violation`. -/
def rule2Violations (policy : Policy) (env : Environment) : MetaM (Array String) := do
  let classes := libraryClasses policy env
  let mut acc := #[]
  for (n, info) in env.constants.toList do
    if ← isInstance n then
      if let some v := rule2Violation policy env classes n info.type then
        acc := acc.push v
  return acc

/-- Run both rules and report: violations to stderr with exit code 1, a
one-line summary to stdout with exit code 0. -/
def run (policy : Policy) (env : Environment) : MetaM UInt32 := do
  let types := typesByModule policy env
  let violations := rule1Violations policy env ++ (← rule2Violations policy env)
  if violations.isEmpty then
    let typeCount := types.fold (init := 0) fun n _ ts => n + ts.size
    IO.println s!"module discipline: {types.size} type-declaring modules, \
      {typeCount} types, instances of {(libraryClasses policy env).size} library \
      classes checked; no violations"
    return 0
  else
    for v in violations do
      IO.eprintln s!"module discipline violation — {v}"
    return 1

end ModuleAudit

/-- Import the built library and audit it. -/
unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := ModuleAudit.btcVerifiedPolicy.libraryPrefix }] {}
    (trustLevel := 1024) (loadExts := true)
  let (code, _) ← (ModuleAudit.run ModuleAudit.btcVerifiedPolicy env).toIO
    { fileName := "<module-audit>", fileMap := default } { env }
  return code
