import BtcVerified.Crypto.Merkle
import BtcVerified.Transaction.Txid
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Vector
/-!
  # Collision-scope regressions

  A global SHA-256d collision exists by the pigeonhole principle, independently
  of any compared commitments. Such existence must not suffice for the binding
  theorems' collision alternative. Singleton Merkle trees have no interior
  positions; their collision alternative is false even though a global
  collision exists. Even a run containing colliding inputs at different
  positions cannot collide with itself at a common position.

  Checked claims:

  * `global_collision_exists`: SHA-256d has a collision on finite byte lists.
  * `global_collision_does_not_supply_scoped_collision`: a global collision
    exists while a singleton tree cannot supply any node collision.
  * `global_collision_does_not_supply_same_position_collision`: a run can
    contain colliding inputs without a collision at corresponding positions
    when compared with itself.
  * `txid_body_eq_of_no_relevant_collision`: equal txids identify bodies when
    their two encodings do not collide.
-/

namespace Tests.CollisionScope

open BtcVerified BtcVerified.Serialize

/-- SHA-256d has distinct finite byte-list inputs with the same digest. -/
theorem global_collision_exists : ∃ a b, Sha256.Collision a b := by
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

/-- A global collision exists, but a singleton tree has no interior position
at which to collide with another tree. -/
theorem global_collision_does_not_supply_scoped_collision (h : Hash256)
    (ys : List Hash256) :
    (∃ a b, Sha256.Collision a b) ∧ ¬ CollisionAt Sha256.sha256d
      (fun p : {p : List Bool // p.length < Nat.clog 2 [h].length} =>
        (Merkle.tree [h]).inputAt p.1)
      (fun p => (Merkle.tree ys).inputAt p.1) := by
  refine ⟨global_collision_exists, ?_⟩
  rintro ⟨⟨p, hp⟩, _⟩
  simp [Nat.clog] at hp

/-- A run can contain distinct colliding inputs at different positions while
having no collision at a common position when compared with itself. -/
theorem global_collision_does_not_supply_same_position_collision :
    ∃ f : Bool → List UInt8,
      Sha256.Collision (f false) (f true) ∧ ¬ CollisionAt Sha256.sha256d f f := by
  obtain ⟨a, b, hc⟩ := global_collision_exists
  refine ⟨(fun i => if i then b else a), ?_, ?_⟩
  · simpa using hc
  · rintro ⟨i, hne, _⟩
    exact hne rfl

/-- Equal txids identify the bodies if their own two encodings do not collide. -/
theorem txid_body_eq_of_no_relevant_collision {t₁ t₂ : Tx}
    (hid : t₁.txid = t₂.txid)
    (hlocal : ¬ Sha256.Collision (Codec.encode t₁.body) (Codec.encode t₂.body)) :
    t₁.body = t₂.body :=
  (Tx.txid_binding hid).resolve_right hlocal

end Tests.CollisionScope
