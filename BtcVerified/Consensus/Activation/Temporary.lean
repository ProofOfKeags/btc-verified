import BtcVerified.Consensus.Activation.VersionBitsState
/-!
  # Temporary consensus obligations

  A time window and a set of deployment states restrict when one checked
  requirement applies. Window endpoints are inclusive; a reversed window is
  empty. The caller supplies the clock and deployment state explicitly.
  These selectors do not compute history or establish a deployment's rules.

  Checked claims:

  * `Rule.during_check_iff` and `Rule.inStates_check_iff`: each selector enforces
    precisely the requirement on its specified domain.
  * `Rule.check_during_of_mem` and `Rule.check_during_of_not_mem`: the window
    selects the requirement's decision or imposes no obligation.
  * `Rule.check_inStates_of_mem` and `Rule.check_inStates_of_not_mem`: a listed
    state selects the requirement's decision; other states impose no obligation.
  * `Rule.check_during_of_reversed`: reversed endpoints impose no obligation.
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

/-- Reversed window endpoints leave the requirement unenforced on every input. -/
theorem Rule.check_during_of_reversed {clock : α → Nat} {first last : Nat}
    {requirement : Rule α} (h : last < first) (input : α) :
    (Rule.during clock first last requirement).check input = true :=
  check_during_of_not_mem fun bounds =>
    (Nat.not_le_of_lt h) (Nat.le_trans bounds.1 bounds.2)

/-- A state-selected checker enforces its requirement exactly in a listed state. -/
theorem Rule.inStates_check_iff (state : α → VersionBitsState)
    (states : List VersionBitsState) (requirement : Rule α) (input : α) :
    (Rule.inStates state states requirement).check input = true ↔
      (state input ∈ states → requirement.Holds input) :=
  (Rule.inStates state states requirement).check_iff input

/-- In a listed state, the checker returns exactly the requirement's decision. -/
theorem Rule.check_inStates_of_mem {state : α → VersionBitsState}
    {states : List VersionBitsState} {requirement : Rule α} {input : α}
    (h : state input ∈ states) :
    (Rule.inStates state states requirement).check input = requirement.check input := by
  simp [inStates, when, ofDecidable, h]

/-- A state absent from the list leaves the requirement unenforced. -/
theorem Rule.check_inStates_of_not_mem {state : α → VersionBitsState}
    {states : List VersionBitsState} {requirement : Rule α} {input : α}
    (h : state input ∉ states) :
    (Rule.inStates state states requirement).check input = true := by
  simp [inStates, when, ofDecidable, h]

end BtcVerified.Consensus
