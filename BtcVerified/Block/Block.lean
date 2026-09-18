import BtcVerified.Block.BlockHeader
import BtcVerified.Transaction.Tx
/-!
  # The block

  A header together with its ordered transactions — the unit fork choice
  weighs and consensus validity judges. The transaction list is
  CompactSize-counted on the wire, hence a `CountedList`. That the header's
  merkle root actually commits to `txs` is a consensus-validity fact, stated
  at the layer where hashing becomes concrete, not a structural invariant
  here.

  On the wire a block is its 80-byte header followed by its
  CompactSize-counted transactions — exactly the model's field order — so the
  codec comes by composition (`Codec.ofEquiv`), with no hand-written proofs.
  This closes the syntactic hierarchy: every byte of a block is now parsed by
  a verified codec, from CompactSize counts up through transactions to the
  block itself.

  ## Packed codec

  The packed `Block` codec (issue #52): the same field-product transport as
  the spec codec — header, then CompactSize-counted transactions — so
  agreement with `instCodecBlock` holds by construction. This closes the
  packed hierarchy: every byte of a block can be parsed and re-serialized
  through the packed codecs, and every such run agrees with the verified
  spec codecs.

  Checked claims:

  * `instPackedCodecBlock`: the packed codec agrees with the
    specification encoder and decoder on every input.
  * `abstractParse_decodeBlock` / `toList_encodeBlock`: whole-block packed
    decoding and encoding agree with the specification byte for byte.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- A block: its header together with the ordered list of transactions. -/
structure Block where
  /-- The block header. -/
  header : BlockHeader
  /-- The block's transactions, in order (the first is the coinbase). -/
  txs : CountedList Tx
  deriving DecidableEq

/-- A `Block` is its header and its transaction list, in that order. -/
def Block.equivProd : Block ≃ (BlockHeader × CountedList Tx) where
  toFun b := (b.header, b.txs)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Serializes a `Block` as its 80-byte header followed by its
CompactSize-counted transactions. -/
instance instCodecBlock : Codec Block :=
  Codec.ofEquiv Block.equivProd inferInstance

end BtcVerified

/-! ## Packed codec -/

namespace BtcVerified.Packed

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

end BtcVerified.Packed
