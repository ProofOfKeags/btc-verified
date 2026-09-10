import Tests.ModuleAuditFixtures.ClassHome
/-!
  # A class with a trailing dictionary

  The same parameter shape as `PackedCodec`: the target type comes before
  an implicit instance argument. The dictionary does not determine the home.
-/

namespace Tests.ModuleAuditFixtures

/-- A refinement class whose second argument is a supporting instance. -/
class RefinedClass (α : Type) [FixtureClass α] : Prop where
  /-- The fixture carries no behavior. -/
  witness : True

/-- Dependency targets remain valid beside the refinement class. -/
instance instRefinedClassUnit : RefinedClass Unit where
  witness := trivial

end Tests.ModuleAuditFixtures
