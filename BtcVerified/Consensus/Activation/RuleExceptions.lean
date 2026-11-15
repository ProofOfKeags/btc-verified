import BtcVerified.Consensus.Rule
/-!
  # Exceptions to a requirement

  An exception suspends one named requirement on precisely the inputs that
  satisfy its own checked predicate. Other requirements remain the caller's
  responsibility; suspending one requirement does not accept an entire block.

  Checked claims:

  * `Rule.unless_holds_of_exception`: an applicable exception discharges the
    selected requirement.
  * `Rule.unless_holds_iff_of_not_exception`: elsewhere its meaning is unchanged.
  * `Rule.check_unless_of_exception` and `Rule.check_unless_of_not_exception`:
    the executable decision follows the same two cases.
-/

namespace BtcVerified.Consensus

/-- Enforce a requirement unless the checked exception applies to the input. -/
def Rule.unless (exception requirement : Rule α) : Rule α where
  Holds input := ¬ exception.Holds input → requirement.Holds input
  check input := exception.check input || requirement.check input
  check_iff input := by
    rw [← exception.check_iff input, ← requirement.check_iff input]
    cases exception.check input <;> simp

/-- An applicable exception discharges precisely the selected requirement. -/
theorem Rule.unless_holds_of_exception {exception requirement : Rule α}
    {input : α} (h : exception.Holds input) :
    (exception.unless requirement).Holds input := by
  simp [Rule.unless, h]

/-- Outside its exception, a suspended requirement keeps its original meaning. -/
theorem Rule.unless_holds_iff_of_not_exception {exception requirement : Rule α}
    {input : α} (h : ¬ exception.Holds input) :
    (exception.unless requirement).Holds input ↔ requirement.Holds input := by
  simp [Rule.unless, h]

/-- The checker accepts its selected requirement when the exception applies. -/
theorem Rule.check_unless_of_exception {exception requirement : Rule α}
    {input : α} (h : exception.Holds input) :
    (exception.unless requirement).check input = true := by
  simp [Rule.unless, (exception.check_iff input).mpr h]

/-- Outside its exception, the checker makes the original requirement's decision. -/
theorem Rule.check_unless_of_not_exception {exception requirement : Rule α}
    {input : α} (h : ¬ exception.Holds input) :
    (exception.unless requirement).check input = requirement.check input := by
  have hfalse : exception.check input = false := by
    cases hc : exception.check input with
    | false => rfl
    | true => exact False.elim (h ((exception.check_iff input).mp hc))
  simp [Rule.unless, hfalse]

end BtcVerified.Consensus
