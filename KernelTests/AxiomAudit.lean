import Kernel.Transaction
import Tests.AxiomAudit
/-!
  # Kernel refinement axiom audit

  Reject unexpected axioms in the universal decoder and checker refinements,
  witness contents and count, stripped encoding, and txid agreement. This is a
  proof-dependency audit, not a collection of transaction examples. The allowed
  assumptions and audit command are defined in Tests.AxiomAudit.
-/

set_option linter.hashCommand false

#assert_axioms BtcVerified.Kernel.decode_eq_spec
#assert_axioms BtcVerified.Kernel.decode_encode_append
#assert_axioms BtcVerified.Kernel.nonCoinbaseCheck_eq_isWellFormed
#assert_axioms BtcVerified.Kernel.coinbaseCheck_iff
#assert_axioms BtcVerified.Kernel.check_iff
#assert_axioms BtcVerified.Kernel.witnesses_toList
#assert_axioms BtcVerified.Kernel.witnesses_size_eq_inputs_size
#assert_axioms BtcVerified.Kernel.encodeStripped_toList
#assert_axioms BtcVerified.Kernel.txid_eq_txid
