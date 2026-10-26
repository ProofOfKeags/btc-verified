import Mathlib.Logic.Basic
/-!
  # Collisions on specified inputs and mathematical collision freedom

  `Collides h a b` names the two inputs of a collision. `CollisionBetween h
  left right` requires one preimage from each supplied list, so binding results
  retain the connection between a collision and the objects being compared.
  An unrelated existential collision cannot discharge that conclusion.

  `Collision` and `CollisionFree` retain the global mathematical vocabulary.
  Collision freedom means injectivity, not computational collision resistance;
  it is false for hashes from an infinite domain to a finite range. No concrete
  hash is assumed collision-free. The scoped binding results do not depend on
  such an assumption and do not assert computational security or work bounds.

  Checked claims:

  * `CollisionBetween.mono`: enlarging the two preimage lists preserves a
    collision already witnessed between them.
  * `collisionBetween_singletons`: singleton lists collide exactly when their
    specified elements do.
  * `not_collisionBetween_nil_left` / `not_collisionBetween_nil_right`: no
    collision can be witnessed when either supplied list is empty.
  * `CollisionFree.injective`: collision freedom implies injectivity.
  * `Collision.comp`: a composite collision yields a collision in one factor.
  * `CollisionFree.comp`: collision freedom composes.
-/

namespace BtcVerified

/-- A collision in `h`: two distinct inputs sharing an image. -/
def Collision {α β : Type*} (h : α → β) : Prop := ∃ a b : α, a ≠ b ∧ h a = h b

/-- The specified distinct inputs have the same image under `h`. -/
def Collides {α β : Type*} (h : α → β) (a b : α) : Prop :=
  a ≠ b ∧ h a = h b

/-- A collision has one preimage from each of the supplied lists. -/
def CollisionBetween {α β : Type*} (h : α → β) (left right : List α) : Prop :=
  ∃ a ∈ left, ∃ b ∈ right, Collides h a b

/-- A collision on specified inputs also witnesses global collision existence. -/
theorem Collides.collision {α β : Type*} {h : α → β} {a b : α}
    (hc : Collides h a b) : Collision h :=
  ⟨a, b, hc⟩

/-- Specified colliding inputs in the two lists witness a collision between them. -/
theorem CollisionBetween.of_collides {α β : Type*} {h : α → β}
    {left right : List α} {a b : α} (ha : a ∈ left) (hb : b ∈ right)
    (hc : Collides h a b) : CollisionBetween h left right :=
  ⟨a, ha, b, hb, hc⟩

/-- Enlarging either supplied list preserves a collision between their inputs. -/
theorem CollisionBetween.mono {α β : Type*} {h : α → β}
    {left right left' right' : List α} (hc : CollisionBetween h left right)
    (hl : left ⊆ left') (hr : right ⊆ right') : CollisionBetween h left' right' := by
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  exact ⟨a, hl ha, b, hr hb, hab⟩

/-- A collision between supplied lists also witnesses global collision existence. -/
theorem CollisionBetween.collision {α β : Type*} {h : α → β}
    {left right : List α} (hc : CollisionBetween h left right) : Collision h := by
  obtain ⟨a, _, b, _, hab⟩ := hc
  exact hab.collision

/-- Singleton lists collide exactly when their specified inputs collide. -/
@[simp] theorem collisionBetween_singletons {α β : Type*} (h : α → β) (a b : α) :
    CollisionBetween h [a] [b] ↔ Collides h a b := by
  simp [CollisionBetween]

/-- An empty left list cannot supply a collision preimage. -/
@[simp] theorem not_collisionBetween_nil_left {α β : Type*} (h : α → β)
    (right : List α) : ¬ CollisionBetween h [] right := by
  simp [CollisionBetween]

/-- An empty right list cannot supply a collision preimage. -/
@[simp] theorem not_collisionBetween_nil_right {α β : Type*} (h : α → β)
    (left : List α) : ¬ CollisionBetween h left [] := by
  simp [CollisionBetween]

/-- Mathematical collision freedom: no distinct inputs have the same image.
This is not a computational hardness property. -/
def CollisionFree {α β : Type*} (h : α → β) : Prop := ¬ Collision h

/-- A collision-free function is injective: equal images force equal
inputs. This is a mathematical property of the entire function, not a
computational security assumption. -/
theorem CollisionFree.injective {α β : Type*} {h : α → β}
    (hcr : CollisionFree h) {a b : α} (hab : h a = h b) : a = b := by
  by_cases hne : a = b
  · exact hne
  · exact absurd ⟨a, b, hne, hab⟩ hcr

/-- A collision in `g ∘ f` is a collision in `f` (its inputs already collide
under `f`) or in `g` (their distinct `f`-images collide under `g`). -/
theorem Collision.comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (hc : Collision (g ∘ f)) : Collision f ∨ Collision g := by
  match hc with
  | ⟨a, b, hab, h⟩ =>
    by_cases hf : f a = f b
    · exact Or.inl ⟨a, b, hab, hf⟩
    · exact Or.inr ⟨f a, f b, hf, h⟩

/-- Collision freedom composes: if `f` and `g` are each collision-free,
so is `g ∘ f`. -/
theorem CollisionFree.comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : CollisionFree f) (hg : CollisionFree g) :
    CollisionFree (g ∘ f) :=
  fun hc => (Collision.comp hc).elim hf hg

/-- A collision in the inner function lifts to a collision in the composite:
the colliding inputs already agree under `f`, hence under `g ∘ f`. -/
theorem Collision.comp_inner {α β γ : Type*} {f : α → β} {g : β → γ}
    (hc : Collision f) : Collision (g ∘ f) := by
  match hc with
  | ⟨a, b, hab, h⟩ => exact ⟨a, b, hab, congrArg g h⟩

/-- The partial dual of `CollisionFree.comp`: collision freedom of `g ∘ f` forces
collision freedom of the *inner* `f` (a collision in `f` would lift to one in the
composite). It does **not** force collision freedom of the outer `g` — `g` may collide
on values outside the range of `f`, where no composite input reaches. -/
theorem CollisionFree.of_comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (h : CollisionFree (g ∘ f)) : CollisionFree f :=
  fun hc => h hc.comp_inner

end BtcVerified
