import Tests.ModuleAuditFixtures.ClassHome
/-!
  # Private-type module-audit fixture

  A public and a private structure deliberately share this module. Rule 1 must
  see both declarations and reject the module.
-/

namespace Tests.ModuleAuditFixtures

/-- The public half of the deliberate two-type violation. -/
structure PublicType where
  /-- Arbitrary fixture data. -/
  value : Nat

/-- A correctly placed instance for a fixture-library type. -/
instance instFixtureClassPublicType : FixtureClass PublicType where
  witness := trivial

private structure HiddenType where
  value : Nat

end Tests.ModuleAuditFixtures
