import BtcVerified.Consensus.Rule
/-!
  # Explicit requirement selection

  Selection replaces one requirement with another on a checked condition.
  Only the selected requirement is enforced. This operation makes no claim
  that replacement preserves or strengthens the original meaning; such a
  relation must be proved for the particular requirements and input domain.

-/

namespace BtcVerified.Consensus

/-- Enforce the first requirement when the condition holds, and the second otherwise. -/
def Rule.choose (condition yes no : Rule α) : Rule α where
  Holds input := (condition.Holds input → yes.Holds input) ∧
    (¬ condition.Holds input → no.Holds input)
  check input := if condition.check input then yes.check input else no.check input
  check_iff input := by
    rw [← condition.check_iff input, ← yes.check_iff input, ← no.check_iff input]
    cases condition.check input <;> simp

/-- When the condition holds, selection requires exactly the first requirement. -/
theorem Rule.choose_holds_iff_of_condition {condition yes no : Rule α}
    {input : α} (h : condition.Holds input) :
    (condition.choose yes no).Holds input ↔ yes.Holds input := by
  simp [choose, h]

/-- When the condition fails, selection requires exactly the second requirement. -/
theorem Rule.choose_holds_iff_of_not_condition {condition yes no : Rule α}
    {input : α} (h : ¬ condition.Holds input) :
    (condition.choose yes no).Holds input ↔ no.Holds input := by
  simp [choose, h]

/-- A satisfied condition selects exactly the first requirement's checker. -/
theorem Rule.check_choose_of_condition {condition yes no : Rule α}
    {input : α} (h : condition.Holds input) :
    (condition.choose yes no).check input = yes.check input := by
  simp [choose, (condition.check_iff input).mpr h]

end BtcVerified.Consensus
