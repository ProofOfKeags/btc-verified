import BtcVerified.Transaction.TxOut
import BtcVerified.Packed.Script
/-!
  # Packed transaction outputs

  The packed `TxOut` codec (issue #52): the same field-product transport as
  the spec codec, so agreement with `instCodecTxOut` holds by construction.
-/

namespace BtcVerified.Packed

open BtcVerified.Serialize BtcVerified

/-- The packed `TxOut` codec, agreeing with `instCodecTxOut` by transport
over the same field product. -/
instance instPackedCodecTxOut : PackedCodec TxOut :=
  PackedCodec.ofEquiv TxOut.equivProd inferInstance inferInstance

end BtcVerified.Packed
