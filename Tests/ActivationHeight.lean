import BtcVerified.Consensus.Activation.LockTime
import Tests.TransactionFixtures
/-!
  # Height activation through absolute finality

  A timestamp lock has passed according to the header but not according to
  parent MTP. Gate the existing MTP rule around a synthetic activation height,
  including equality, without changing the transaction or either clock.
  These are finite checker examples, not historical activation evidence.
-/

namespace Tests.ActivationHeight

open BtcVerified Consensus Tests.TransactionFixtures

set_option linter.hashCommand false

private def lockedBody : TxBody :=
  { legacyExample.body with lockTime := 500000100 }

private def context (height : Nat) : TxContext :=
  ⟨height, 500000200, 500000050⟩

private def deployed :=
  (TxBody.lockTimeRule .medianTimePast).atHeight (fun input => input.1.height) 100

end Tests.ActivationHeight
