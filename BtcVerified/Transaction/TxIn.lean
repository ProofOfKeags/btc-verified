import BtcVerified.Transaction.OutPoint
import BtcVerified.Script.Script
/-!
  # Transaction inputs

  A transaction input spends one previous output: the outpoint it consumes,
  the unlocking script, and the sequence number. The script is a `Script` —
  raw program bytes, tokenized only at execution time — and the codec comes
  by composition over the fields in wire order.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- A transaction input: the output it spends, the unlocking script, and the
input sequence number. -/
structure TxIn where
  /-- The previous output this input spends. -/
  prevout : OutPoint
  /-- The unlocking script (`scriptSig`). -/
  scriptSig : Script
  /-- The input sequence number (used for relative timelocks / RBF signalling). -/
  sequence : UInt32
  deriving DecidableEq

/-- A `TxIn` is its previous output, its unlocking script, and its sequence
number, in that order. -/
def TxIn.equivProd : TxIn ≃ (OutPoint × Script × UInt32) where
  toFun i := (i.prevout, i.scriptSig, i.sequence)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Serializes a `TxIn` as its `OutPoint`, then its length-prefixed `scriptSig`,
then its little-endian sequence number. -/
instance instCodecTxIn : Codec TxIn :=
  Codec.ofEquiv TxIn.equivProd inferInstance

end BtcVerified
