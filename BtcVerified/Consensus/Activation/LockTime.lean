import BtcVerified.Consensus.Activation.Height
import BtcVerified.Consensus.TxContextual
/-!
  # Absolute finality as a composable rule

  Package the existing lock-time checker without changing its predicate or
  its clock selection. A deployment can gate the MTP requirement at its
  activation height. This adapter is one requirement, not a transaction
  validator or a claim that independently supplied clocks are coherent.

  Checked claims:

  * `TxBody.lockTimeRule`: its checker enforces the existing absolute-finality
    predicate, using `TxBody.isLockTimeSatisfied_iff`.
-/

namespace BtcVerified

/-- Absolute finality on a context and transaction body under the named clock. -/
def TxBody.lockTimeRule (clock : LockTimeClock) : Consensus.Rule (TxContext × TxBody) where
  Holds input := input.2.LockTimeSatisfied clock input.1
  check input := input.2.isLockTimeSatisfied clock input.1
  check_iff _ := TxBody.isLockTimeSatisfied_iff

end BtcVerified
