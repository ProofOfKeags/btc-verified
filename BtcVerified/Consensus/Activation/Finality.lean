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

end BtcVerified
