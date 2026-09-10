import Lean
/-!
  # Module-discipline audit policy and checker

  The whole-codebase counterpart of `Tests/AxiomAudit.lean`: where that audit
  guards what each theorem *depends on*, this one guards where declarations
  *live*. It walks `Lean.Environment` and enforces the module discipline
  CLAUDE.md states in prose:

  1. **One type per module** — a `BtcVerified` module declares at most one
     `structure`/`inductive`. Sum-type arm-record clusters may be
     allowlisted in `armRecordClusters` (none today).
  2. **Instances live with their type** — an `instance` of a class this
     library defines targets a type declared in the instance's own module;
     instances for Core/dependency targets live with the *class* instead.

  The walk is over elaborated declarations, not source names. A class must
  have exactly one type argument; value arguments and class dictionaries do
  not select the target. The target's stored head constant identifies its
  module without unfolding aliases such as `CountedList` or `Bytes`.
  Unsupported class signatures and targets without a constant head fail
  closed. Global and scoped instance registrations are checked even when a
  scope is unopened. Only registered instances are checked —
  a deliberately unregistered worked codec (`compactSizeCodec`) is exempt
  by design, matching the issue-#9 wording "every `instance`".

-/

open Lean Meta

namespace ModuleAudit

/-- The module-discipline rules for one audited library. -/
structure Policy where
  /-- Module prefix whose declarations are audited. -/
  libraryPrefix : Name
  /-- Modules permitted to declare a tightly coupled arm-record cluster. -/
  armRecordClusters : List Name := []

/-- The library the production audit applies to. -/
def libraryPrefix : Name := `BtcVerified

/-- Rule-1 allowlist: modules permitted more than one type because they
hold a sum type's arm records that never appear in an outside signature.
Empty today — `SegwitInput` appears in `Tx`'s signature, so it earns its
own module rather than an entry here. -/
def armRecordClusters : List Name := []

/-- The production policy for `btc-verified`. -/
def btcVerifiedPolicy : Policy where
  libraryPrefix := libraryPrefix
  armRecordClusters := armRecordClusters

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
        arm-record cluster in ModuleAudit.lean"
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

/-- Core/dependency targets place their instances in the class's module. -/
def dependencyInstanceViolation (className classModule : Name)
    (instName instModule : Name) (target : String) : Option String :=
  if instModule = classModule then none
  else some s!"{instName}: instance of {className} for the \
    Core/dependency target {target} lives in {instModule}; such instances \
    live with the class ({classModule})"

/-- Select the unique type argument of a class application. The arguments'
types are inspected in the instance's local context, so generic parameters
are valid inputs. Only those inferred types are reduced: the selected target
keeps its declared head constant, including an `abbrev` name. -/
def instanceTarget (className : Name) (classApp : Expr) : MetaM (Except String Expr) := do
  let typeArgs ← classApp.getAppArgs.filterM fun arg => do
    return (← whnf (← inferType arg)).isSort
  match typeArgs.toList with
  | [target] => return .ok target
  | _ => return .error s!"class {className} has {typeArgs.size} type arguments; \
      the module audit requires exactly one target type"

/-- Rule 2, for one marked instance: if it instantiates a library class,
its target type's head constant decides where it must live — the target's
module for a library type, the class's module for a Core/dependency type.
The outer class application is reduced so an alias cannot hide a library
class; its target argument remains unreduced. Returns a violation message,
or `none` when the rule is satisfied or does not apply. Unsupported target
selection is a violation, not an exemption. -/
def rule2Violation (policy : Policy) (env : Environment)
    (classes : Std.HashMap Name Name) (instName : Name) (instType : Expr) :
    MetaM (Option String) := do
  let some instModule := moduleOf env instName | return none
  if !inLibrary policy instModule then return none
  forallTelescopeReducing instType (whnfType := true) fun _ classApp => do
    let some className := classApp.getAppFn.constName? | return none
    let some classModule := classes.get? className | return none
    match ← instanceTarget className classApp with
    | .error reason => return some s!"{instName}: {reason}"
    | .ok target =>
      let some targetName := target.getAppFn.constName?
        | return some s!"{instName}: target of {className} has no constant head \
            ({← ppExpr target}); the module audit cannot determine its home"
      let some targetModule := moduleOf env targetName
        | return some s!"{instName}: cannot determine the defining module of \
            target {targetName} for {className}"
      if inLibrary policy targetModule then
        if instModule = targetModule then return none
        else return some s!"{instName}: instance of {className} for {targetName} \
          (declared in {targetModule}) lives in {instModule}; a library type's \
          instances live in its module"
      else
        return dependencyInstanceViolation className classModule instName instModule
          (toString targetName)

/-- Registered instance names, including unopened scopes. Reading the scoped
registrations directly avoids changing which instances are active in the
audited environment. Names already present in the active registry are
deduplicated, and explicit erasures in that registry are respected. -/
def registeredInstanceNames (env : Environment) : NameSet :=
  let active := instanceExtension.getState env
  let names := active.instanceNames.foldl (fun names name _ => names.insert name) {}
  let scopedEntries := (instanceExtension.ext.getState env).scopedEntries.map
  scopedEntries.fold (init := names) fun names _ entries =>
    entries.foldl (init := names) fun names entry =>
      match entry.globalName? with
      | some name => if active.erased.contains name then names else names.insert name
      | none => names

/-- Rule 2 over the whole environment: check global and scoped instance
registrations against `rule2Violation`, regardless of active scopes. -/
def rule2Violations (policy : Policy) (env : Environment) : MetaM (Array String) := do
  let classes := libraryClasses policy env
  let instances := registeredInstanceNames env
  let mut acc := #[]
  for (n, info) in env.constants.toList do
    if instances.contains n then
      if let some v ← rule2Violation policy env classes n info.type then
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
