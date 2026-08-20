import Tests.ModuleAuditFixtures.ClassHome
/-!
  # Misplaced-instance module-audit fixtures

  Both declarations below must be found by Rule 2: one is opaque, and the
  other's target has no head constant.
-/

namespace Tests.ModuleAuditFixtures

/-- An opaque, attribute-marked dependency instance outside the class module. -/
@[instance] opaque misplacedOpaque : FixtureClass Bool := {
  witness := trivial
}

/-- A regular misplaced instance whose function target has no head constant. -/
instance misplacedFunction : FixtureClass (Unit → Unit) where
  witness := trivial

end Tests.ModuleAuditFixtures
