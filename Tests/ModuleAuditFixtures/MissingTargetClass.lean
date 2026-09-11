/-!
  # An unsupported class without a target type

  Its natural-number argument is a value, so the audit cannot assign a type home.
-/

namespace Tests.ModuleAuditFixtures

/-- A class with a value index but no type argument. -/
class MissingTargetClass (index : Nat) : Prop where
  /-- The fixture carries no behavior. -/
  witness : True

/-- A value-only class application must be diagnosed as missing a target. -/
instance instMissingTargetClass (index : Nat) : MissingTargetClass index where
  witness := trivial

end Tests.ModuleAuditFixtures
