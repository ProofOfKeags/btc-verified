/-!
  # Module-audit fixture class

  A minimal library-defined class with two dependency instances beside it.
  Neither needs an allowlist. These declarations are imported only by the audit's
  regression test, never by `BtcVerified`.
-/

namespace Tests.ModuleAuditFixtures

/-- A trivial class used to exercise instance placement. -/
class FixtureClass (α : Type) : Prop where
  /-- The fixture carries no behavior. -/
  witness : True

/-- A dependency instance belongs beside its class without an allowlist. -/
instance instFixtureClassPUnit : FixtureClass PUnit where
  witness := trivial

/-- A second dependency target is accepted by the same placement rule. -/
instance instFixtureClassUnit : FixtureClass Unit where
  witness := trivial

namespace ScopedHome

/-- A scoped dependency instance is valid beside its class. -/
scoped instance instFixtureClassBool : FixtureClass Bool where
  witness := trivial

end ScopedHome

end Tests.ModuleAuditFixtures
