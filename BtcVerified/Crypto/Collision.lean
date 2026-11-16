import Mathlib.Logic.Basic
/-!
  # Collisions and collision resistance of a function

  `Collision h a b` retains the two distinct inputs with the same image.
  `CollisionAt h f g` compares two runs of a hashing procedure at a common
  position, so a binding theorem's collision must arise from corresponding
  hash applications. An unrelated existential collision cannot discharge it.

  Collision resistance is never an axiom over a concrete function (it is
  provably false there by pigeonhole). It enters as a *hypothesis*, and from it
  injectivity follows: a collision-resistant function is injective on the nose.
  Composition is the other load-bearing fact — a collision in `g ∘ f` is a
  collision in `f` or in `g` — which is exactly what carries collision
  resistance through Bitcoin's double hashing.

  Checked claims:

  * `CollisionResistant.injective`: a collision-resistant function is injective.
  * `Collision.comp`: a specified composite collision yields a collision in
    the inner function on those inputs or the outer function on their images.
  * `Collision.comp_inner`: an inner collision persists through composition.
  * `CollisionResistant.comp`: collision resistance of `f` and `g` gives
    collision resistance of `g ∘ f`.
-/

namespace BtcVerified

/-- The two specified inputs are distinct and have the same image under `h`. -/
def Collision {α β : Type*} (h : α → β) (a b : α) : Prop :=
  a ≠ b ∧ h a = h b

/-- Two runs of one hashing procedure, given as their hash inputs indexed by
position, collide at a common position. -/
def CollisionAt {ι α β : Type*} (h : α → β) (f g : ι → α) : Prop :=
  ∃ i, Collision h (f i) (g i)

/-- `h` is collision-resistant when it has no collision. For a concrete function
this is a hypothesis a caller supplies, never an axiom — it is provably false
for any function out of an infinite domain into a finite one. -/
def CollisionResistant {α β : Type*} (h : α → β) : Prop :=
  ∀ a b, ¬ Collision h a b

/-- A collision-resistant function is injective: equal images force equal
inputs. This is the bridge that turns the `… ∨ Collision` disjunct of the
hashing binding theorems into outright injectivity under a resistance
hypothesis. -/
theorem CollisionResistant.injective {α β : Type*} {h : α → β}
    (hcr : CollisionResistant h) {a b : α} (hab : h a = h b) : a = b := by
  by_cases hne : a = b
  · exact hne
  · exact absurd ⟨hne, hab⟩ (hcr a b)

/-- A collision in `g ∘ f` on `a` and `b` is a collision in `f` on those
inputs or a collision in `g` on their `f`-images. -/
theorem Collision.comp {α β γ : Type*} {f : α → β} {g : β → γ} {a b : α}
    (hc : Collision (g ∘ f) a b) : Collision f a b ∨ Collision g (f a) (f b) := by
  by_cases hf : f a = f b
  · exact Or.inl ⟨hc.1, hf⟩
  · exact Or.inr ⟨hf, hc.2⟩

/-- Collision resistance composes: if `f` and `g` are each collision-resistant,
so is `g ∘ f`. -/
theorem CollisionResistant.comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : CollisionResistant f) (hg : CollisionResistant g) :
    CollisionResistant (g ∘ f) :=
  fun a b hc => (Collision.comp hc).elim (hf a b) (hg (f a) (f b))

/-- A collision in `f` on `a` and `b` is also a collision in `g ∘ f` on
those same inputs. -/
theorem Collision.comp_inner {α β γ : Type*} {f : α → β} {g : β → γ} {a b : α}
    (hc : Collision f a b) : Collision (g ∘ f) a b :=
  ⟨hc.1, congrArg g hc.2⟩

/-- The partial dual of `CollisionResistant.comp`: resistance of `g ∘ f` forces
resistance of the *inner* `f` (a collision in `f` would lift to one in the
composite). It does **not** force resistance of the outer `g` — `g` may collide
on values outside the range of `f`, where no composite input reaches. -/
theorem CollisionResistant.of_comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (h : CollisionResistant (g ∘ f)) : CollisionResistant f :=
  fun a b hc => h a b hc.comp_inner

end BtcVerified
