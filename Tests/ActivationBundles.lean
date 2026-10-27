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

end Tests.ActivationBundles
