import BtcVerified.Consensus.Rule
/-!
  # Exceptions to a requirement

  An exception suspends one named requirement on precisely the inputs that
  satisfy its own checked predicate. Other requirements remain the caller's
  responsibility; suspending one requirement does not accept an entire block.

-/

namespace BtcVerified.Consensus

/-- Enforce a requirement unless the checked exception applies to the input. -/
def Rule.unless (exception requirement : Rule α) : Rule α where
  Holds input := ¬ exception.Holds input → requirement.Holds input
  check input := exception.check input || requirement.check input
  check_iff input := by
    rw [← exception.check_iff input, ← requirement.check_iff input]
    cases exception.check input <;> simp

end BtcVerified.Consensus
