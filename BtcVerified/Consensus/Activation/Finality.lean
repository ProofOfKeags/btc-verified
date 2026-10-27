import BtcVerified.Consensus.Activation.LockTime
import BtcVerified.Consensus.Rule.Composition

/-!
  # Cumulative finality requirements

  The existing absolute-lock rule is always required under the block clock.
  From the supplied activation height, median-time-past finality is also
  required. The latter subsumes the former only when the supplied clocks are
  ordered; arbitrary `TxContext` values do not establish that invariant.

  Checked claims:
  * Median-time-past finality implies block-time finality under clock order.
  * Before activation the bundle is exactly block-time finality.
  * From activation the bundle is exactly MTP finality under clock order.
-/

namespace BtcVerified

/-! ## Definitions -/

/-- Require block-time finality and, from the threshold, MTP finality. -/
def TxBody.finalityRules (firstHeight : Nat) : Consensus.Rule (TxContext × TxBody) :=
  (lockTimeRule .blockTime).and
    ((lockTimeRule .medianTimePast).atHeight (fun input => input.1.height) firstHeight)

/-! ## Behavioral laws -/

/-- MTP finality implies block-time finality when MTP is no later than block time. -/
theorem TxBody.lockTimeSatisfied_blockTime_of_medianTimePast
    (body : TxBody) (ctx : TxContext) (clockOrder : ctx.medianTimePast ≤ ctx.blockTime)
    (accepted : body.LockTimeSatisfied .medianTimePast ctx) :
    body.LockTimeSatisfied .blockTime ctx := by
  rcases accepted with past | final
  · left
    cases hlock : body.interpretedLockTime <;>
      simp only [hlock, Consensus.LockTime.Past, TxContext.timeFor] at past ⊢
    · exact past
    · exact lt_of_lt_of_le past clockOrder
  · exact .inr final

/-- Before activation, the combined requirement is exactly block-time finality. -/
theorem TxBody.finalityRules_holds_before (firstHeight : Nat) (body : TxBody)
    (ctx : TxContext) (before : ctx.height < firstHeight) :
    (finalityRules firstHeight).Holds (ctx, body) ↔
      body.LockTimeSatisfied .blockTime ctx := by
  simp [finalityRules, Consensus.Rule.and, Consensus.Rule.atHeight,
    Consensus.Rule.when, Consensus.Rule.ofDecidable, lockTimeRule, Nat.not_le.mpr before]

/-- After activation, the combined requirement is exactly MTP finality under clock order. -/
theorem TxBody.finalityRules_holds_of_le (firstHeight : Nat) (body : TxBody)
    (ctx : TxContext) (active : firstHeight ≤ ctx.height)
    (clockOrder : ctx.medianTimePast ≤ ctx.blockTime) :
    (finalityRules firstHeight).Holds (ctx, body) ↔
      body.LockTimeSatisfied .medianTimePast ctx := by
  change (body.LockTimeSatisfied .blockTime ctx ∧
    (firstHeight ≤ ctx.height → body.LockTimeSatisfied .medianTimePast ctx)) ↔ _
  exact ⟨fun accepted => accepted.2 active, fun accepted =>
    ⟨lockTimeSatisfied_blockTime_of_medianTimePast body ctx clockOrder accepted,
      fun _ => accepted⟩⟩

/-- Before activation, the combined checker returns the block-time checker's result. -/
theorem TxBody.finalityRules_check_before (firstHeight : Nat) (body : TxBody)
    (ctx : TxContext) (before : ctx.height < firstHeight) :
    (finalityRules firstHeight).check (ctx, body) =
      body.isLockTimeSatisfied .blockTime ctx := by
  apply Bool.eq_iff_iff.mpr
  rw [(finalityRules firstHeight).check_iff, isLockTimeSatisfied_iff]
  exact finalityRules_holds_before firstHeight body ctx before

/-- After activation, the combined checker returns the MTP checker's result under clock order. -/
theorem TxBody.finalityRules_check_of_le (firstHeight : Nat) (body : TxBody)
    (ctx : TxContext) (active : firstHeight ≤ ctx.height)
    (clockOrder : ctx.medianTimePast ≤ ctx.blockTime) :
    (finalityRules firstHeight).check (ctx, body) =
      body.isLockTimeSatisfied .medianTimePast ctx := by
  apply Bool.eq_iff_iff.mpr
  rw [(finalityRules firstHeight).check_iff, isLockTimeSatisfied_iff]
  exact finalityRules_holds_of_le firstHeight body ctx active clockOrder

end BtcVerified
