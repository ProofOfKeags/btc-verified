import BtcVerified.Block.Block
import BtcVerified.Impl.Packed.BlockHeader
import BtcVerified.Impl.Packed.Tx
/-!
  # Packed blocks

  The packed `Block` codec (issue #52): the same field-product transport as
  the spec codec — header, then CompactSize-counted transactions — so
  agreement with `instCodecBlock` holds by construction. This closes the
  packed hierarchy: every byte of a block can be parsed and re-serialized
  through the packed codecs, and every such run agrees with the verified
  spec codecs.
-/

namespace BtcVerified.Impl.Packed

open BtcVerified.Serialize BtcVerified

/-- The packed `Block` codec, agreeing with `instCodecBlock` by transport
over the same field product. -/
instance instPackedCodecBlock : PackedCodec Block :=
  PackedCodec.ofEquiv Block.equivProd inferInstance inferInstance

/-- End-to-end decode agreement at the block level: parsing any byte string
with the packed block codec, read through the abstraction, is the spec
block parse — same acceptance, same block, same unconsumed remainder. -/
theorem abstractParse_decodeBlock (bs : List UInt8) :
    abstractParse (PackedCodec.decode (α := Block) bs.toByteArray)
      = Codec.decode (α := Block) bs :=
  PackedCodec.abstractParse_decode_toByteArray bs

/-- End-to-end encode agreement at the block level: the packed encoding of
a block is byte-for-byte its spec encoding. -/
theorem toList_encodeBlock (b : Block) :
    (PackedCodec.encode b).toList = Codec.encode b :=
  PackedCodec.toList_encode b

end BtcVerified.Impl.Packed
