import Kernel.Transaction
import Tests.AxiomAudit
/-!
  # Native transaction boundary tests

  These elaboration-time checks exercise fixed, small transaction encodings and
  audit the boundary's headline transport proofs. They do not run a differential
  harness or import any fuzz module.
-/

namespace KernelTests

open BtcVerified

set_option linter.hashCommand false

private def regularBytes : ByteArray :=
  (([0x01, 0x00, 0x00, 0x00, 0x01] : List UInt8)
    ++ List.replicate 32 (0x01 : UInt8)
    ++ [0x00, 0x00, 0x00, 0x00]
    ++ [0x00]
    ++ [0xff, 0xff, 0xff, 0xff]
    ++ [0x01]
    ++ List.replicate 8 (0x00 : UInt8)
    ++ [0x00]
    ++ [0x00, 0x00, 0x00, 0x00]).toByteArray

private def emptyBytes : ByteArray :=
  ([0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] :
    List UInt8).toByteArray

#assert_axioms BtcVerified.Kernel.regularCheck_eq_isWellFormed
#assert_axioms BtcVerified.Kernel.witnesses_size_eq_inputs_size
#assert_axioms BtcVerified.Kernel.encodeStripped_toList
#assert_axioms BtcVerified.Kernel.txid_eq_txid

#guard match Kernel.decode regularBytes with
  | some tx => Kernel.encode tx == regularBytes && Kernel.check tx
  | none => false

#guard match Kernel.decode regularBytes with
  | some tx =>
      match (Kernel.inputs tx).toList, (Kernel.outputs tx).toList,
          (Kernel.witnesses tx).toList with
      | [input], [output], [witness] =>
          Kernel.inputTxid input == (List.replicate 32 (0x01 : UInt8)).toByteArray
            && Kernel.inputIndex input == 0
            && Kernel.inputSequence input == 0xffffffff
            && Kernel.inputScript input == ByteArray.empty
            && Kernel.outputAmount output == 0
            && Kernel.outputScript output == ByteArray.empty
            && witness.isEmpty
      | _, _, _ => false
  | none => false

#guard match Kernel.decode emptyBytes with
  | some tx =>
      !Kernel.check tx
        && (Kernel.inputs tx).isEmpty
        && (Kernel.outputs tx).isEmpty
        && (Kernel.witnesses tx).isEmpty
        && Kernel.locktime tx == 0
  | none => false

#guard match Kernel.decode regularBytes with
  | some tx => Kernel.txid tx == tx.txid.val.toByteArray
  | none => false

#guard Kernel.decode
  ([0x01, 0x00, 0x00, 0x00, 0x00] : List UInt8).toByteArray |>.isNone

end KernelTests
