import BtcVerified.Crypto.Merkle
import BtcVerified.Transaction.Txid
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Vector
/-!
  # Collision-scope regressions

  A global SHA-256d collision exists by the pigeonhole principle, independently
  of any compared commitments. Such existence must not suffice for the binding
  theorems' collision alternative. Singleton Merkle trees have no node
  preimages at all; their scoped collision alternative is false even though
  the global collision proposition is true.

  Checked claims:

  * `global_collision_exists`: SHA-256d has a collision on finite byte lists.
  * `global_collision_does_not_supply_scoped_collision`: a global collision
    exists while a singleton tree cannot supply any node collision.
  * `txid_body_eq_of_no_relevant_collision`: equal txids identify bodies when
    their two encodings do not collide; no global collision-freedom premise.
-/

namespace Tests.CollisionScope

open BtcVerified BtcVerified.Serialize

/-- SHA-256d has distinct finite byte-list inputs with the same digest. -/
theorem global_collision_exists : Sha256.Collision := by
  letI : Finite UInt8 := Finite.of_injective UInt8.toFin (by
    intro a b h
    exact UInt8.toFin_inj.mp h)
  letI : Fintype UInt8 := Fintype.ofFinite UInt8
  let f : Nat → List.Vector UInt8 32 := fun n =>
    ⟨Sha256.sha256d (List.replicate n 0), Sha256.sha256d_length _⟩
  obtain ⟨a, b, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  refine ⟨List.replicate a 0, List.replicate b 0, ?_, ?_⟩
  · intro h
    apply hne
    simpa using congrArg List.length h
  · exact congrArg Subtype.val heq

/-- A global collision exists, but a singleton tree has no node preimages
with which to witness a scoped collision, even against an arbitrary other tree. -/
theorem global_collision_does_not_supply_scoped_collision (h : Hash256)
    (ys : List Hash256) :
    Sha256.Collision ∧ ¬ Sha256.CollisionBetween
      (Merkle.hashPreimages [h]) (Merkle.hashPreimages ys) := by
  refine ⟨global_collision_exists, ?_⟩
  simp [Sha256.CollisionBetween, Merkle.hashPreimages, Merkle.tree, Merkle.ofList,
    Merkle.Tree.hashPreimages, Nat.clog]

/-- Equal txids identify the bodies if their own two encodings do not collide. -/
theorem txid_body_eq_of_no_relevant_collision {t₁ t₂ : Tx}
    (hid : t₁.txid = t₂.txid)
    (hlocal : ¬ Sha256.Collides (Codec.encode t₁.body) (Codec.encode t₂.body)) :
    t₁.body = t₂.body :=
  (Tx.txid_binding hid).resolve_right hlocal

end Tests.CollisionScope
