import BtcVerified.Script.Script
/-!
  # Transaction outputs

  A transaction output is an amount in satoshis and the locking script that
  must be satisfied to spend it. The script is a `Script` — raw program bytes,
  tokenized only at execution time — and the codec comes by composition over
  the two fields in wire order.

  ## Packed codec

  The packed `TxOut` codec (issue #52): the same field-product transport as
  the spec codec, so agreement with `instCodecTxOut` holds by construction.

  Checked claims:

  * `instPackedCodecTxOut`: the packed codec agrees with the
    specification encoder and decoder on every input.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- A transaction output: the amount in satoshis and the locking script that must
be satisfied to spend it. -/
structure TxOut where
  /-- The output amount in satoshis. -/
  value : UInt64
  /-- The locking script (`scriptPubKey`). -/
  scriptPubKey : Script
  deriving DecidableEq

/-- A `TxOut` is its amount followed by its locking script. -/
def TxOut.equivProd : TxOut ≃ (UInt64 × Script) where
  toFun o := (o.value, o.scriptPubKey)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Serializes a `TxOut` as its little-endian 8-byte amount followed by its
length-prefixed `scriptPubKey`. -/
instance instCodecTxOut : Codec TxOut :=
  Codec.ofEquiv TxOut.equivProd inferInstance

end BtcVerified

/-! ## Packed codec -/

namespace BtcVerified.Packed

open BtcVerified.Serialize BtcVerified

/-- The packed `TxOut` codec, agreeing with `instCodecTxOut` by transport
over the same field product. -/
instance instPackedCodecTxOut : PackedCodec TxOut :=
  PackedCodec.ofEquiv TxOut.equivProd inferInstance inferInstance

end BtcVerified.Packed
