import BtcVerified.Consensus.Rule
/-!
  # Activation at an established height

  A known activation height selects a requirement without changing that
  requirement's meaning. The caller supplies the height projection and the
  historical threshold; this module does not establish a network's history.
  At the threshold itself the requirement is already enforced.

  Checked claims:

  * `Rule.atHeight_check_before`: earlier heights impose no requirement.
  * `Rule.atHeight_check_of_le`: the threshold and later heights use the rule.
-/

namespace BtcVerified.Consensus

/-- Enforce a rule starting at `firstHeight`, using the input's candidate height. -/
def Rule.atHeight (height : α → Nat) (firstHeight : Nat) (requirement : Rule α) : Rule α :=
  .when (.ofDecidable fun input => firstHeight ≤ height input) requirement

/-- Before the activation height, the gated checker accepts every input. -/
theorem Rule.atHeight_check_before (height : α → Nat) (firstHeight : Nat)
    (requirement : Rule α) (input : α) (h : height input < firstHeight) :
    (requirement.atHeight height firstHeight).check input = true := by
  simp [atHeight, when, ofDecidable, Nat.not_le.mpr h]

/-- At or above the activation height, the gated checker is the underlying checker. -/
theorem Rule.atHeight_check_of_le (height : α → Nat) (firstHeight : Nat)
    (requirement : Rule α) (input : α) (h : firstHeight ≤ height input) :
    (requirement.atHeight height firstHeight).check input = requirement.check input := by
  simp [atHeight, when, ofDecidable, h]

end BtcVerified.Consensus
