import BtcVerified.Consensus.Activation.Finality
import Tests.TransactionFixtures
/-!
  # Combined requirements and clock refinement examples

  Exercise shared activation, context projection, and cumulative absolute
  finality. The incoherent-clock counterexample demonstrates why the
  refinement theorem explicitly requires clock order.
-/

namespace Tests.ActivationBundles

open BtcVerified Consensus Tests.TransactionFixtures

set_option linter.hashCommand false

private def lowerBound : Rule Nat := .ofDecidable fun amount => 3 ≤ amount
private def upperBound : Rule Nat := .ofDecidable fun amount => amount ≤ 10
private def deployed : Rule (Nat × Nat) :=
  (Rule.all [lowerBound, upperBound]).contramap Prod.snd |>.atHeight Prod.fst 100

#guard deployed.check (99, 2)
#guard !deployed.check (100, 2)
#guard !deployed.check (100, 20)
#guard deployed.check (100, 10)

private def lockedBody : TxBody := { legacyExample.body with lockTime := 500000100 }
private def context (height : Nat) : TxContext := ⟨height, 500000200, 500000050⟩

#guard (TxBody.finalityRules 100).check (context 99, lockedBody)
#guard !(TxBody.finalityRules 100).check (context 100, lockedBody)

end Tests.ActivationBundles
