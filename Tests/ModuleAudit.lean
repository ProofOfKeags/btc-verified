import ModuleAuditMain
import Tests.ModuleAuditFixtures.PrivateTypes
import Tests.ModuleAuditFixtures.Misplaced
import Batteries.Data.String.Matcher
/-!
  # Module-audit regression tests

  Negative fixtures verify the audit fails closed for private types, opaque
  instances, unallowlisted dependency instances, and targets without a head
  constant. The assertions run while `lake build Tests` elaborates this module.
-/

open Lean Elab Command

namespace Tests.ModuleAudit

set_option linter.hashCommand false

/-- Audit policy scoped to the deliberately invalid fixture modules. -/
def fixturePolicy : _root_.ModuleAudit.Policy where
  libraryPrefix := `Tests.ModuleAuditFixtures
  dependencyInstances := [`Tests.ModuleAuditFixtures.allowedPUnit]

/-- Whether an audit message identifies `name`. -/
def hasViolation (violations : Array String) (name : Name) : Bool :=
  violations.any fun violation => violation.containsSubstr name.toString

/-- Check that every deliberately invalid fixture is rejected, while the
explicitly allowed and correctly placed fixtures remain clean. -/
elab "#assert_module_audit_fixtures" : command => do
  let env ← getEnv
  let types := _root_.ModuleAudit.typesByModule fixturePolicy env
  let privateTypes := types.getD `Tests.ModuleAuditFixtures.PrivateTypes #[]
  unless privateTypes.size = 2 do
    throwError "expected the public and private fixture types; got {privateTypes.toList}"
  let rule1 := _root_.ModuleAudit.rule1Violations fixturePolicy env
  unless rule1.size = 1 do
    throwError "expected exactly one Rule-1 fixture violation; got {rule1.toList}"
  let rule2 ← liftTermElabM <|
    _root_.ModuleAudit.rule2Violations fixturePolicy env
  let expected := [
    `Tests.ModuleAuditFixtures.unallowlistedUnit,
    `Tests.ModuleAuditFixtures.misplacedOpaque,
    `Tests.ModuleAuditFixtures.misplacedFunction
  ]
  for name in expected do
    unless hasViolation rule2 name do
      throwError "expected a Rule-2 violation for {name}; got {rule2.toList}"
  unless rule2.size = expected.length do
    throwError "expected exactly {expected.length} Rule-2 fixture violations; \
      got {rule2.toList}"
  if hasViolation rule2 `Tests.ModuleAuditFixtures.allowedPUnit then
    throwError "the explicitly allowlisted dependency instance was rejected"
  if hasViolation rule2 `Tests.ModuleAuditFixtures.instFixtureClassPublicType then
    throwError "the correctly placed library-type instance was rejected"

#assert_module_audit_fixtures

end Tests.ModuleAudit
