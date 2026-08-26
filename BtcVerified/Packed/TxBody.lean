import BtcVerified.Transaction.TxBody
import BtcVerified.Packed.TxIn
import BtcVerified.Packed.TxOut
/-!
  # Packed transaction bodies

  The packed `TxBody` codec (issue #52): the same field-product transport as
  the spec codec, so agreement with `instCodecTxBody` — and hence with the
  legacy transaction serialization and the txid preimage — holds by
  construction.
-/

namespace BtcVerified.Packed

open BtcVerified.Serialize BtcVerified

/-- The packed `TxBody` codec, agreeing with `instCodecTxBody` by transport
over the same field product. -/
instance instPackedCodecTxBody : PackedCodec TxBody :=
  PackedCodec.ofEquiv TxBody.equivProd inferInstance inferInstance

end BtcVerified.Packed
