import Tests.ModuleAuditFixtures.RefinedClass
/-!
  # A generic target declared by abbreviation

  Like `CountedList`, the target must retain its own module despite reducing
  to a dependency type. Opening the instance binders is necessary to inspect it.
-/

namespace Tests.ModuleAuditFixtures

/-- A generic library target whose representation is a subtype of lists. -/
abbrev Box (α : Type) := { values : List α // values = values }

/-- A library abbreviation's instance lives with that abbreviation. -/
instance instFixtureClassBox {α : Type} [FixtureClass α] : FixtureClass (Box α) where
  witness := trivial

/-- A generic target remains the target despite a trailing dictionary. -/
instance instRefinedClassBox {α : Type} [FixtureClass α] : RefinedClass (Box α) where
  witness := trivial

end Tests.ModuleAuditFixtures
