import Tests.ModuleAuditFixtures.PrivateTypes
import Tests.ModuleAuditFixtures.Box
/-!
  # Misplaced-instance module-audit fixtures

  Rule 2 must distinguish a target type's module from a supporting instance's
  module, and must reject targets with no identifiable constant head.
-/

namespace Tests.ModuleAuditFixtures

/-- Dependency-defined classes are outside this audit's placement rule. -/
instance instInhabitedPublicTypeElsewhere : Inhabited PublicType where
  default := ⟨0⟩

/-- A reducible alias must not hide a library class from the audit. -/
abbrev HiddenClass := FixtureClass Bool

/-- An attribute-marked instance remains misplaced through a class alias. -/
@[instance] opaque instHiddenClassMisplaced : HiddenClass := ⟨trivial⟩

namespace Unopened

/-- An unopened scope does not exempt a misplaced dependency instance. -/
scoped instance instFixtureClassBool : FixtureClass Bool where
  witness := trivial

end Unopened

/-- An opaque, attribute-marked dependency instance outside the class module. -/
@[instance] opaque instFixtureClassBoolMisplaced : FixtureClass Bool := {
  witness := trivial
}

/-- A regular misplaced instance whose function target has no head constant. -/
instance instFixtureClassFunction : FixtureClass (Unit → Unit) where
  witness := trivial

/-- A deliberately misplaced support instance for the next fixture. -/
instance instFixtureClassPublicTypeMisplaced : FixtureClass PublicType where
  witness := trivial

/-- Reading the last class argument would incorrectly accept this instance:
its supporting dictionary lives here, but the target type does not. -/
instance instRefinedClassPublicTypeMisplaced :
    @RefinedClass PublicType instFixtureClassPublicTypeMisplaced where
  witness := trivial

/-- An abbreviation keeps its own home even in a generic instance. -/
instance instRefinedClassBoxMisplaced {α : Type} [FixtureClass α] :
    RefinedClass (Box α) where
  witness := trivial

/-- An open target type has no declaring module and must fail closed. -/
instance instFixtureClassOpen (α : Type) : FixtureClass α where
  witness := trivial

end Tests.ModuleAuditFixtures
