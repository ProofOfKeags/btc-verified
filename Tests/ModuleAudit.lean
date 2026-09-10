import ModuleAudit
import Tests.ModuleAuditFixtures.PrivateTypes
import Tests.ModuleAuditFixtures.Misplaced
import Tests.ModuleAuditFixtures.AmbiguousClass
import Tests.ModuleAuditFixtures.MissingTargetClass
import Batteries.Data.String.Matcher
import Mathlib.Tactic.Linter.HashCommandLinter
/-!
  # Module-audit regression tests

  Fixtures exercise module placement, generic abbreviations, trailing class
  dictionaries, and value indices. Unsupported target shapes fail closed.
  The assertions run while `lake build Tests` elaborates this module.
-/

open Lean Elab Command

namespace Tests.ModuleAudit

set_option linter.hashCommand false

/-- Audit policy scoped to the deliberately invalid fixture modules. -/
def fixturePolicy : _root_.ModuleAudit.Policy where
  libraryPrefix := `Tests.ModuleAuditFixtures

/-- Check that every deliberately invalid fixture is rejected, while the
correctly placed fixtures remain clean without instance-name allowlists. -/
elab "#assert_module_audit_fixtures" : command => do
  let env ← getEnv
  let types := _root_.ModuleAudit.typesByModule fixturePolicy env
  let privateTypes := types.getD `Tests.ModuleAuditFixtures.PrivateTypes #[]
  unless privateTypes.size = 2 do
    throwError "expected the public and private fixture types; got {privateTypes.toList}"
  let rule1 := _root_.ModuleAudit.rule1Violations fixturePolicy env
  unless rule1.size = 1 do
    throwError "expected exactly one Rule-1 fixture violation; got {rule1.toList}"
  let allowedClusters := { fixturePolicy with
    armRecordClusters := [`Tests.ModuleAuditFixtures.PrivateTypes] }
  unless (_root_.ModuleAudit.rule1Violations allowedClusters env).isEmpty do
    throwError "the explicitly allowed type cluster was rejected"
  for name in [`Tests.ModuleAuditFixtures.Unopened.instFixtureClassBool,
      `Tests.ModuleAuditFixtures.ScopedHome.instFixtureClassBool] do
    if Meta.isInstanceCore env name then
      throwError "the scope for fixture {name} must remain unopened"
  let rule2 ← liftTermElabM <|
    _root_.ModuleAudit.rule2Violations fixturePolicy env
  let expected := [
    (`Tests.ModuleAuditFixtures.instHiddenClassMisplaced, "live with the class"),
    (`Tests.ModuleAuditFixtures.Unopened.instFixtureClassBool, "live with the class"),
    (`Tests.ModuleAuditFixtures.instFixtureClassBoolMisplaced, "live with the class"),
    (`Tests.ModuleAuditFixtures.instFixtureClassFunction, "no constant head"),
    (`Tests.ModuleAuditFixtures.instFixtureClassPublicTypeMisplaced,
      "instances live in its module"),
    (`Tests.ModuleAuditFixtures.instRefinedClassPublicTypeMisplaced,
      "instances live in its module"),
    (`Tests.ModuleAuditFixtures.instRefinedClassBoxMisplaced, "instances live in its module"),
    (`Tests.ModuleAuditFixtures.instFixtureClassOpen, "no constant head"),
    (`Tests.ModuleAuditFixtures.instAmbiguousClassUnitBool, "has 2 type arguments"),
    (`Tests.ModuleAuditFixtures.instMissingTargetClass, "has 0 type arguments")
  ]
  for (name, reason) in expected do
    unless rule2.any (fun violation =>
        violation.containsSubstr name.toString && violation.containsSubstr reason) do
      throwError "expected a Rule-2 violation for {name} containing {reason}; got {rule2.toList}"
  unless rule2.size = expected.length do
    throwError "expected exactly {expected.length} Rule-2 fixture violations; \
      got {rule2.toList}"
  let accepted := [
    `Tests.ModuleAuditFixtures.instFixtureClassPUnit,
    `Tests.ModuleAuditFixtures.instFixtureClassUnit,
    `Tests.ModuleAuditFixtures.ScopedHome.instFixtureClassBool,
    `Tests.ModuleAuditFixtures.instRefinedClassUnit,
    `Tests.ModuleAuditFixtures.instIndexedClassUnit,
    `Tests.ModuleAuditFixtures.instFixtureClassPublicType,
    `Tests.ModuleAuditFixtures.instRefinedClassPublicType,
    `Tests.ModuleAuditFixtures.instIndexedClassPublicType,
    `Tests.ModuleAuditFixtures.instFixtureClassBox,
    `Tests.ModuleAuditFixtures.instRefinedClassBox,
    `Tests.ModuleAuditFixtures.instInhabitedPublicTypeElsewhere
  ]
  for name in accepted do
    -- Match the declaration prefix, so a longer deliberately misplaced name
    -- cannot be confused with its correctly placed counterpart.
    if rule2.any (fun violation => violation.startsWith s!"{name}:") then
      throwError "the correctly placed instance {name} was rejected"

#assert_module_audit_fixtures

end Tests.ModuleAudit
