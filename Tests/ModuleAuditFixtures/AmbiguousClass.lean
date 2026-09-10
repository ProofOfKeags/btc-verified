/-!
  # An unsupported class with two target types

  The audit must report ambiguity rather than choose either type by position.
-/

namespace Tests.ModuleAuditFixtures

/-- A class whose two type arguments do not identify a unique target. -/
class AmbiguousClass (α β : Type) : Prop where
  /-- The fixture carries no behavior. -/
  witness : True

/-- Even placement beside the class cannot resolve its ambiguous target. -/
instance instAmbiguousClassUnitBool : AmbiguousClass Unit Bool where
  witness := trivial

end Tests.ModuleAuditFixtures
