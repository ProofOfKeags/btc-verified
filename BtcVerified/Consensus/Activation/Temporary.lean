import BtcVerified.Consensus.Activation.VersionBitsState
/-!
  # Temporary consensus obligations

  A time window and a set of deployment states restrict when one checked
  requirement applies. Window endpoints are inclusive; a reversed window is
  empty. The caller supplies the clock and deployment state explicitly.
  These selectors do not compute history or establish a deployment's rules.

-/

namespace BtcVerified.Consensus

/-- Enforce a requirement when the supplied clock lies within inclusive endpoints. -/
def Rule.during (clock : α → Nat) (first last : Nat) (requirement : Rule α) : Rule α :=
  Rule.when (Rule.ofDecidable fun input => first ≤ clock input ∧ clock input ≤ last)
    requirement

/-- Enforce a requirement in precisely the listed deployment states. -/
def Rule.inStates (state : α → VersionBitsState) (states : List VersionBitsState)
    (requirement : Rule α) : Rule α :=
  Rule.when (Rule.ofDecidable fun input => state input ∈ states) requirement

end BtcVerified.Consensus
