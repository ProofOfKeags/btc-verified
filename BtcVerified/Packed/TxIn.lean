import BtcVerified.Transaction.TxIn
import BtcVerified.Packed.OutPoint
import BtcVerified.Packed.Script
/-!
  # Packed transaction inputs

  The packed `TxIn` codec (issue #52): the same field-product transport as
  the spec codec, so agreement with `instCodecTxIn` holds by construction.
-/

namespace BtcVerified.Packed

open BtcVerified.Serialize BtcVerified

/-- The packed `TxIn` codec, agreeing with `instCodecTxIn` by transport over
the same field product. -/
instance instPackedCodecTxIn : PackedCodec TxIn :=
  PackedCodec.ofEquiv TxIn.equivProd inferInstance inferInstance

end BtcVerified.Packed
