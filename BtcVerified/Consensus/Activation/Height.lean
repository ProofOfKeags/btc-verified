import BtcVerified.Consensus.Rule
/-!
  # Activation at an established height

  A known activation height selects a requirement without changing that
  requirement's meaning. The caller supplies the height projection and the
  historical threshold; this module does not establish a network's history.
  At the threshold itself the requirement is already enforced.

-/

namespace BtcVerified.Consensus

/-- Enforce a rule starting at `firstHeight`, using the input's candidate height. -/
def Rule.atHeight (height : α → Nat) (firstHeight : Nat) (requirement : Rule α) : Rule α :=
  .when (.ofDecidable fun input => firstHeight ≤ height input) requirement

end BtcVerified.Consensus
