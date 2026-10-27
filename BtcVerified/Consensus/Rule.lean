import Mathlib.Data.Bool.Basic
/-!
  # Executable consensus requirements

  A rule pairs its semantic requirement with an executable checker and the
  proof that they agree. The input type determines its scope: a transaction,
  a block, or an object together with the context its requirement needs.
  Deployment choices belong to the combinators that assemble these rules.
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

/-- Package a decidable predicate as an executable rule. -/
def Rule.ofDecidable (predicate : α → Prop) [DecidablePred predicate] : Rule α where
  Holds := predicate
  check input := decide (predicate input)
  check_iff _ := by simp

end BtcVerified.Consensus
