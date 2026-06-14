import Mathlib.Logic.Basic
/-!
  # Collisions and collision resistance of a function

  The collision vocabulary, stated over an arbitrary function rather than any
  particular hash. A collision is two distinct inputs with the same image;
  collision resistance is the absence of one. Both are interesting independent
  of which function appears — `sha256d`, a merkle node combiner, an abstract
  commitment hash — so they live here once and specialize where needed.

  Collision resistance is never an axiom over a concrete function (it is
  provably false there by pigeonhole). It enters as a *hypothesis*, and from it
  injectivity follows: a collision-resistant function is injective on the nose.
  Composition is the other load-bearing fact — a collision in `g ∘ f` is a
  collision in `f` or in `g` — which is exactly what carries collision
  resistance through Bitcoin's double hashing.

  Checked claims:

  * `CollisionResistant.injective`: a collision-resistant function is injective.
  * `Collision.comp`: a collision in `g ∘ f` yields a collision in `f` or `g`.
  * `CollisionResistant.comp`: collision resistance of `f` and `g` gives
    collision resistance of `g ∘ f`.
-/

namespace BtcVerified

/-- A collision in `h`: two distinct inputs sharing an image. -/
def Collision {α β : Type*} (h : α → β) : Prop := ∃ a b : α, a ≠ b ∧ h a = h b

/-- `h` is collision-resistant when it has no collision. For a concrete function
this is a hypothesis a caller supplies, never an axiom — it is provably false
for any function out of an infinite domain into a finite one. -/
def CollisionResistant {α β : Type*} (h : α → β) : Prop := ¬ Collision h

/-- A collision-resistant function is injective: equal images force equal
inputs. This is the bridge that turns the `… ∨ Collision` disjunct of the
hashing faithfulness theorems into outright injectivity under a resistance
hypothesis. -/
theorem CollisionResistant.injective {α β : Type*} {h : α → β}
    (hcr : CollisionResistant h) {a b : α} (hab : h a = h b) : a = b := by
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

/-- Collision resistance composes: if `f` and `g` are each collision-resistant,
so is `g ∘ f`. -/
theorem CollisionResistant.comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : CollisionResistant f) (hg : CollisionResistant g) :
    CollisionResistant (g ∘ f) :=
  fun hc => (Collision.comp hc).elim hf hg

end BtcVerified
