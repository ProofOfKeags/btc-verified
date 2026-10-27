import BtcVerified.Consensus.Activation.Height
/-!
  # Composition of consensus requirements

  Bundles share an input domain and require every member. Projection supplies
  a smaller rule with exactly the context it reads. Implication is semantic;
  no equality or registry of predicate-valued rule records is required.

-/

namespace BtcVerified.Consensus.Rule

/-- Require both rules on the same candidate and context. -/
def and (left right : Rule α) : Rule α where
  Holds x := left.Holds x ∧ right.Holds x
  check x := left.check x && right.check x
  check_iff x := by simp [left.check_iff, right.check_iff]

/-- Require every rule in a finite bundle, accepting the empty bundle. -/
def all (rules : List (Rule α)) : Rule α where
  Holds x := ∀ rule ∈ rules, rule.Holds x
  check x := rules.all fun rule => rule.check x
  check_iff x := by simp [List.all_eq_true, Rule.check_iff]

/-- Supply a rule with the part of the context it needs. -/
def contramap (project : β → α) (rule : Rule α) : Rule β where
  Holds x := rule.Holds (project x)
  check x := rule.check (project x)
  check_iff x := rule.check_iff (project x)

/-- Every input satisfying the stronger rule satisfies the weaker rule. -/
def Refines (stronger weaker : Rule α) : Prop :=
  ∀ x, stronger.Holds x → weaker.Holds x

end BtcVerified.Consensus.Rule
