import BtcVerified.Consensus.Activation.Height
/-!
  # Composition of consensus requirements

  Bundles share an input domain and require every member. Projection supplies
  a smaller rule with exactly the context it reads. The standard implication
  order places stronger requirements below weaker ones.

  Checked claims:

  * `Rule.all_le_of_mem`: accepting a bundle establishes each member.
  * `Rule.all_append_holds`: appending bundles conjoins their requirements.
  * `Rule.and_atHeight_holds_iff_left`: an inactive addition has no effect.
-/

namespace BtcVerified.Consensus.Rule

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

/-! ## Behavioral laws -/

/-- A bundle implies each rule occurring in it. -/
theorem all_le_of_mem {rules : List (Rule α)} {rule : Rule α}
    (h : rule ∈ rules) : all rules ≤ rule :=
  fun _ accepted => accepted rule h

/-- Every input satisfies the empty bundle. -/
@[simp] theorem all_nil_holds (x : α) : (all []).Holds x := by
  simp [all]

/-- A prepended bundle holds exactly when its new rule and old bundle hold. -/
@[simp] theorem all_cons_holds (rule : Rule α) (rules : List (Rule α)) (x : α) :
    (all (rule :: rules)).Holds x ↔ rule.Holds x ∧ (all rules).Holds x := by
  simp [all]

/-- Appending bundles requires exactly the requirements of both bundles. -/
theorem all_append_holds (left right : List (Rule α)) (x : α) :
    (all (left ++ right)).Holds x ↔ (all left).Holds x ∧ (all right).Holds x := by
  simp [all, or_imp, forall_and]

/-- Appended bundles accept exactly when each separate bundle accepts. -/
theorem all_append_check (left right : List (Rule α)) (x : α) :
    (all (left ++ right)).check x = ((all left).check x && (all right).check x) := by
  simp [all]

/-- Projecting context for a bundle equals projecting it for every member. -/
theorem contramap_all_holds (project : β → α) (rules : List (Rule α)) (x : β) :
    (contramap project (all rules)).Holds x ↔
      (all (rules.map (contramap project))).Holds x := by
  simp [contramap, all]

/-- An inactive guarded conjunct leaves the other rule's requirement unchanged. -/
theorem and_when_holds_iff_left (left condition right : Rule α) (x : α)
    (inactive : ¬condition.Holds x) :
    (and left (when condition right)).Holds x ↔ left.Holds x := by
  simp [and, when, inactive]

/-- A scheduled conjunct leaves the other rule unchanged before activation. -/
theorem and_atHeight_holds_iff_left (height : α → Nat) (firstHeight : Nat)
    (left right : Rule α) (x : α) (before : height x < firstHeight) :
    (and left (atHeight height firstHeight right)).Holds x ↔ left.Holds x := by
  exact and_when_holds_iff_left left _ right x (Nat.not_le_of_lt before)

end BtcVerified.Consensus.Rule
