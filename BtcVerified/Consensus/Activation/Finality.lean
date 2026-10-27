import BtcVerified.Consensus.Activation.LockTime
import BtcVerified.Consensus.Rule.Composition

/-!
  # Cumulative finality requirements

  The existing absolute-lock rule is always required under the block clock.
  From the supplied activation height, median-time-past finality is also
  required. The latter subsumes the former only when the supplied clocks are
  ordered; arbitrary `TxContext` values do not establish that invariant.

-/

namespace BtcVerified


/-- Require block-time finality and, from the threshold, MTP finality. -/
def TxBody.finalityRules (firstHeight : Nat) : Consensus.Rule (TxContext × TxBody) :=
  (lockTimeRule .blockTime).and
    ((lockTimeRule .medianTimePast).atHeight (fun input => input.1.height) firstHeight)

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

end BtcVerified
