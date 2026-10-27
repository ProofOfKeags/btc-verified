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

/-- A windowed checker enforces its requirement exactly within its inclusive window. -/
theorem Rule.during_check_iff (clock : α → Nat) (first last : Nat)
    (requirement : Rule α) (input : α) :
    (Rule.during clock first last requirement).check input = true ↔
      (first ≤ clock input ∧ clock input ≤ last → requirement.Holds input) :=
  (Rule.during clock first last requirement).check_iff input

/-- Within its window, a checker returns exactly the requirement's decision. -/
theorem Rule.check_during_of_mem {clock : α → Nat} {first last : Nat}
    {requirement : Rule α} {input : α}
    (h : first ≤ clock input ∧ clock input ≤ last) :
    (Rule.during clock first last requirement).check input = requirement.check input := by
  simp [during, when, ofDecidable, h]

/-- Outside its window, an obligation imposes no requirement on the input. -/
theorem Rule.check_during_of_not_mem {clock : α → Nat} {first last : Nat}
    {requirement : Rule α} {input : α}
    (h : ¬ (first ≤ clock input ∧ clock input ≤ last)) :
    (Rule.during clock first last requirement).check input = true :=
  (during_check_iff clock first last requirement input).mpr fun bounds => (h bounds).elim

end BtcVerified.Consensus
