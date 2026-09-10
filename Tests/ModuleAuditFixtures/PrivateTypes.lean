import Tests.ModuleAuditFixtures.RefinedClass
import Tests.ModuleAuditFixtures.IndexedClass
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

/-- A trailing class dictionary leaves the library target's home unchanged. -/
instance instRefinedClassPublicType : RefinedClass PublicType where
  witness := trivial

/-- A value index leaves the library target's home unchanged. -/
instance instIndexedClassPublicType (index : Nat) : IndexedClass PublicType index where
  witness := trivial

private structure HiddenType where
  value : Nat

end Tests.ModuleAuditFixtures
