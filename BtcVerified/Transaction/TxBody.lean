import BtcVerified.Transaction.TxIn
import BtcVerified.Transaction.TxOut
/-!
  # The transaction body

  The witness-free core of a transaction — version, inputs, outputs, lock
  time — one object in three roles: the txid preimage, the legacy wire
  serialization, and the witness-stripped form a SegWit transaction presents
  to non-upgraded nodes. Its codec comes by composition over the fields in
  wire order, and *is* the legacy transaction serialization.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- The witness-free body of a transaction: version, inputs, outputs, and lock
time. This is exactly what a txid commits to, exactly the legacy (pre-SegWit)
wire serialization, and exactly the witness-stripped form a SegWit transaction
presents to non-upgraded nodes — one object in three roles. -/
structure TxBody where
  /-- Transaction version (serialized as a 4-byte little-endian word). -/
  version : UInt32
  /-- The transaction inputs, in order. -/
  inputs : CountedList TxIn
  /-- The transaction outputs, in order. -/
  outputs : CountedList TxOut
  /-- The transaction lock time. -/
  lockTime : UInt32
  deriving DecidableEq

/-- A `TxBody` is its version, inputs, outputs, and lock time, in that order. -/
def TxBody.equivProd :
    TxBody ≃ (UInt32 × CountedList TxIn × CountedList TxOut × UInt32) where
  toFun b := (b.version, b.inputs, b.outputs, b.lockTime)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Serializes a `TxBody` — equivalently, a legacy transaction — as its
little-endian version, its length-prefixed input and output vectors, and its
little-endian lock time. This is exactly the txid preimage. -/
instance instCodecTxBody : Codec TxBody :=
  Codec.ofEquiv TxBody.equivProd inferInstance

end BtcVerified
