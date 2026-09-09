import BtcVerified.Block.BlockHeader
import BtcVerified.Packed.Bytes
/-!
  # Packed block headers

  The packed `BlockHeader` codec (issue #52): the same field-product
  transport as the spec codec, so agreement with `instCodecBlockHeader` —
  the 80-byte proof-of-work preimage — holds by construction.
-/

namespace BtcVerified.Packed

open BtcVerified.Serialize BtcVerified

/-- The packed `BlockHeader` codec, agreeing with `instCodecBlockHeader` by
transport over the same field product. -/
instance instPackedCodecBlockHeader : PackedCodec BlockHeader :=
  PackedCodec.ofEquiv BlockHeader.equivProd inferInstance inferInstance

end BtcVerified.Packed
