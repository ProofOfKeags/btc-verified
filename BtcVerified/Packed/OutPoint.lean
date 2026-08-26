import BtcVerified.Transaction.OutPoint
import BtcVerified.Packed.Bytes
/-!
  # Packed outpoints

  The packed `OutPoint` codec (issue #52). The spec codec is `Codec.ofEquiv`
  over the field product in wire order; the packed codec is the same
  transport applied to the packed field codecs, so agreement with
  `instCodecOutPoint` holds by construction, with no hand-written proof.
-/

namespace BtcVerified.Packed

open BtcVerified.Serialize BtcVerified

/-- The packed `OutPoint` codec, agreeing with `instCodecOutPoint` by
transport over the same field product. -/
instance instPackedCodecOutPoint : PackedCodec OutPoint :=
  PackedCodec.ofEquiv OutPoint.equivProd inferInstance inferInstance

end BtcVerified.Packed
