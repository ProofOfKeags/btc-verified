import BtcVerified.Consensus.Activation.Height
import Mathlib.Order.Hom.BoundedLattice
/-!
  # Composition of consensus requirements

  Bundles share an input domain and require every member. Projection supplies
  a smaller rule with exactly the context it reads. The standard implication
  order places stronger requirements below weaker ones.

  Checked claims:

  * `Rule.all_le_of_mem`: accepting a bundle establishes each member.
  * `Rule.all_append`: appending bundles conjoins their requirements.
  * `Rule.map_all`: finite-meet homomorphisms preserve executable bundles.
  * `Rule.inf_atHeight_holds_iff_left`: an inactive addition has no effect.
-/

namespace BtcVerified.Consensus.Rule

/-- Require every rule in a finite bundle, accepting the empty bundle. -/
def all (rules : List (Rule α)) : Rule α where
  Holds x := ∀ rule ∈ rules, rule.Holds x
  check x := rules.all fun rule => rule.check x
  check_iff x := by simp [List.all_eq_true, Rule.check_iff]

/-- Project inputs into a rule's context, preserving conjunction and the accepting rule. -/
def contramap (project : β → α) : InfTopHom (Rule α) (Rule β) where
  toFun rule :=
    { Holds := fun input => rule.Holds (project input)
      check := fun input => rule.check (project input)
      check_iff := fun input => rule.check_iff (project input) }
  map_inf' _ _ := rfl
  map_top' := rfl

/-! ## Behavioral laws -/

/-- A bundle implies each rule occurring in it. -/
theorem all_le_of_mem {rules : List (Rule α)} {rule : Rule α}
    (h : rule ∈ rules) : all rules ≤ rule :=
  fun _ accepted => accepted rule h

/-- The empty bundle is the rule accepting every input. -/
@[simp] theorem all_nil : all ([] : List (Rule α)) = ⊤ := by
  apply Rule.ext
  intro input
  simp [all]

/-- Prepending a requirement takes its meet with the existing bundle. -/
@[simp] theorem all_cons (rule : Rule α) (rules : List (Rule α)) :
    all (rule :: rules) = rule ⊓ all rules := by
  apply Rule.ext
  intro input
  simp [all]

/-- Appending bundles takes the meet of their requirements. -/
theorem all_append (left right : List (Rule α)) :
    all (left ++ right) = all left ⊓ all right := by
  apply Rule.ext
  intro input
  simp [all, or_imp, forall_and]

/-- Any map preserving finite meets and top commutes with executable bundles. -/
theorem map_all (f : InfTopHom (Rule α) (Rule β)) (rules : List (Rule α)) :
    f (all rules) = all (rules.map f) := by
  induction rules with
  | nil => simp
  | cons rule rules ih => simp [ih]

/-- Before activation, adjoining a scheduled rule leaves the existing requirement unchanged. -/
theorem inf_atHeight_holds_iff_left (height : α → Nat) (firstHeight : Nat)
    (left right : Rule α) (input : α) (before : height input < firstHeight) :
    (left ⊓ right.atHeight height firstHeight).Holds input ↔ left.Holds input := by
  have inactive : (right.atHeight height firstHeight).Holds input :=
    ((right.atHeight height firstHeight).check_iff input).mp
      (atHeight_check_before height firstHeight right input before)
  simp [inactive]

end BtcVerified.Consensus.Rule
