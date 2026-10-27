import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
/-!
  # Executable consensus requirements

  A rule pairs its semantic requirement with an executable checker and the
  proof that they agree. The input type determines its scope: a transaction,
  a block, or an object together with the context its requirement needs.
  Deployment choices belong to the combinators that assemble these rules.

  Checked claims:

  * `Rule.ofDecidable`: its checker decides the supplied predicate.
  * `Rule.when`: its checker decides conditional enforcement.
  * `Rule.ext`: equivalent requirements determine equal checked rules.
  * `instPartialOrderRule`: implication orders rules, with stronger rules below weaker ones.
  * `instSemilatticeInfRule`: conjunction is the meet of two requirements.
  * `instOrderTopRule`: the greatest rule accepts every input.
-/

namespace BtcVerified.Consensus

/-- A requirement together with an executable decision of that requirement. -/
structure Rule (α : Type*) where
  /-- The semantic requirement on an input. -/
  Holds : α → Prop
  /-- The executable acceptance decision. -/
  check : α → Bool
  /-- The checker accepts exactly the inputs satisfying the requirement. -/
  check_iff : ∀ input, check input = true ↔ Holds input

/-- Pointwise equivalent requirements determine equal checked rules. -/
@[ext] theorem Rule.ext {left right : Rule α}
    (h : ∀ input, left.Holds input ↔ right.Holds input) : left = right := by
  have holds_eq : left.Holds = right.Holds := funext fun input => propext (h input)
  have check_eq : left.check = right.check := by
    funext input
    apply Bool.eq_iff_iff.mpr
    rw [left.check_iff, right.check_iff]
    exact h input
  cases left
  cases right
  cases holds_eq
  cases check_eq
  rfl

/-- Order rules by implication between their requirements. -/
instance instPartialOrderRule : PartialOrder (Rule α) :=
  PartialOrder.lift Rule.Holds fun _ _ h => Rule.ext fun input => by rw [h]

/-- Package a decidable predicate as an executable rule. -/
def Rule.ofDecidable (predicate : α → Prop) [DecidablePred predicate] : Rule α where
  Holds := predicate
  check input := decide (predicate input)
  check_iff _ := by simp

/-- Enforce a requirement only on inputs satisfying the applicability rule. -/
def Rule.when (applicable requirement : Rule α) : Rule α where
  Holds input := applicable.Holds input → requirement.Holds input
  check input := !applicable.check input || requirement.check input
  check_iff input := by
    rw [← applicable.check_iff input, ← requirement.check_iff input]
    cases applicable.check input <;> simp

/-- Require both rules on the same candidate and context. -/
def Rule.and (left right : Rule α) : Rule α where
  Holds x := left.Holds x ∧ right.Holds x
  check x := left.check x && right.check x
  check_iff x := by simp [left.check_iff, right.check_iff]

/-- Conjunction is the greatest rule that implies both operands. -/
instance instSemilatticeInfRule : SemilatticeInf (Rule α) where
  __ := instPartialOrderRule
  inf := Rule.and
  inf_le_left _ _ _ h := h.1
  inf_le_right _ _ _ h := h.2
  le_inf _ _ _ left right input h := ⟨left input h, right input h⟩

/-- The greatest rule accepts every input. -/
instance instOrderTopRule : OrderTop (Rule α) where
  top := Rule.ofDecidable fun _ => True
  le_top _ _ _ := True.intro

end BtcVerified.Consensus
