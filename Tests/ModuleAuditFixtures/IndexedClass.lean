/-!
  # A class with a value parameter

  A trailing natural number is an index, not another candidate target type.
-/

namespace Tests.ModuleAuditFixtures

/-- A class with one target type and one value index. -/
class IndexedClass (α : Type) (index : Nat) : Prop where
  /-- The fixture carries no behavior. -/
  witness : True

/-- A generic value index does not obscure the external target type. -/
instance instIndexedClassUnit (index : Nat) : IndexedClass Unit index where
  witness := trivial

end Tests.ModuleAuditFixtures
