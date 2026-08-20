/-!
  # Module-audit fixture class

  A minimal library-defined class with one allowed and one unallowlisted
  dependency instance. These declarations are imported only by the audit's
  regression test, never by `BtcVerified`.
-/

namespace Tests.ModuleAuditFixtures

/-- A trivial class used to exercise instance placement. -/
class FixtureClass (α : Type) : Prop where
  /-- The fixture carries no behavior. -/
  witness : True

/-- The one dependency instance explicitly allowed by the fixture policy. -/
instance allowedPUnit : FixtureClass PUnit where
  witness := trivial

/-- A dependency instance the fixture policy must reject despite its correct
location beside the class. -/
instance unallowlistedUnit : FixtureClass Unit where
  witness := trivial

end Tests.ModuleAuditFixtures
