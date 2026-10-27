import BtcVerified.Consensus.Activation.Height
/-!
  # Composition of consensus requirements

  Bundles share an input domain and require every member. Projection supplies
  a smaller rule with exactly the context it reads. Implication is semantic;
  no equality or registry of predicate-valued rule records is required.

  Checked claims:

  * `Rule.all_refines_of_mem`: accepting a bundle establishes each member.
  * `Rule.all_append_holds`: appending bundles conjoins their requirements.
  * `Rule.and_check_eq_left_of_refines`: an implied check can be omitted.
  * `Rule.and_atHeight_holds_iff_left`: an inactive addition has no effect.
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

/-! ## Behavioral laws -/

/-- Every rule implies itself. -/
theorem refines_refl (rule : Rule α) : rule.Refines rule :=
  fun _ h => h

/-- Rule implication is transitive. -/
theorem Refines.trans {first second third : Rule α}
    (h₁ : first.Refines second) (h₂ : second.Refines third) :
    first.Refines third :=
  fun x h => h₂ x (h₁ x h)

/-- A conjunction implies its left rule. -/
theorem and_refines_left (left right : Rule α) :
    (and left right).Refines left :=
  fun _ h => h.1

/-- A conjunction implies its right rule. -/
theorem and_refines_right (left right : Rule α) :
    (and left right).Refines right :=
  fun _ h => h.2

/-- A bundle implies each rule occurring in it. -/
theorem all_refines_of_mem {rules : List (Rule α)} {rule : Rule α}
    (h : rule ∈ rules) : (all rules).Refines rule :=
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

/-- A rule that implies another is unchanged semantically by adding it. -/
theorem and_holds_iff_left_of_refines {stronger weaker : Rule α}
    (h : stronger.Refines weaker) (x : α) :
    (and stronger weaker).Holds x ↔ stronger.Holds x :=
  ⟨And.left, fun accepted => ⟨accepted, h x accepted⟩⟩

/-- An implied requirement can be omitted without changing acceptance. -/
theorem and_check_eq_left_of_refines {stronger weaker : Rule α}
    (h : stronger.Refines weaker) (x : α) :
    (and stronger weaker).check x = stronger.check x := by
  apply Bool.eq_iff_iff.mpr
  rw [(and stronger weaker).check_iff, stronger.check_iff]
  exact and_holds_iff_left_of_refines h x

/-- A bundle is unchanged semantically by adding a requirement it implies. -/
theorem all_cons_holds_iff_of_refines {rules : List (Rule α)} {rule : Rule α}
    (h : (all rules).Refines rule) (x : α) :
    (all (rule :: rules)).Holds x ↔ (all rules).Holds x := by
  rw [all_cons_holds]
  exact ⟨And.right, fun accepted => ⟨h x accepted, accepted⟩⟩

/-- Projecting contexts preserves implication between rules. -/
theorem Refines.contramap {stronger weaker : Rule α}
    (h : stronger.Refines weaker) (project : β → α) :
    (contramap project stronger).Refines (contramap project weaker) :=
  fun x accepted => h (project x) accepted

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
