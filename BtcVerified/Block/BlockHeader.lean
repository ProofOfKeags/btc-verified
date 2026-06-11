import BtcVerified.Crypto.Hash256
import BtcVerified.Serialize.Codec
/-!
  # The block header

  The 80 bytes proof of work covers: version, previous-header hash, merkle
  root, time, the compact target encoding, and the nonce. The two hash fields
  are where chain structure and the transaction commitment enter the model —
  `prevBlockHash` is what makes blocks a tree, `merkleRoot` is what ties a
  header to its transactions. Interpreting `bits` as a 256-bit target and
  checking the header hash against it belongs to the proof-of-work layer, not
  this module.

  The wire format and the model agree on field order, so the codec comes by
  composition over the fields (`Codec.ofEquiv`), with no hand-written proofs.

  Checked claims:

  * `instCodecBlockHeader`: the header codec satisfies round-trip and
    canonicality, inherited field by field.
  * `BlockHeader.encode_length`: every header encodes to exactly 80 bytes —
    the fixed proof-of-work preimage size.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- An 80-byte Bitcoin block header: the fields covered by proof of work.

`bits` is the compact (`nBits`) encoding of the target; decoding it to a
256-bit target and checking the block hash against it is the proof-of-work
layer's job, not this module's. -/
structure BlockHeader where
  /-- Block version. -/
  version : UInt32
  /-- The hash of the previous block's header. -/
  prevBlockHash : Hash256
  /-- The merkle root committing to the block's transactions. -/
  merkleRoot : Hash256
  /-- The block time (Unix epoch seconds). -/
  time : UInt32
  /-- The compact (`nBits`) encoding of the proof-of-work target. -/
  bits : UInt32
  /-- The proof-of-work nonce. -/
  nonce : UInt32
  deriving DecidableEq

/-- A `BlockHeader` is its version, previous-header hash, merkle root, time,
compact target, and nonce, in that order. -/
def BlockHeader.equivProd :
    BlockHeader ≃ (UInt32 × Hash256 × Hash256 × UInt32 × UInt32 × UInt32) where
  toFun h := (h.version, h.prevBlockHash, h.merkleRoot, h.time, h.bits, h.nonce)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Serializes a `BlockHeader` as its four little-endian 4-byte words and two
32-byte hashes, in wire order: version, previous-header hash, merkle root,
time, compact target, nonce. -/
instance instCodecBlockHeader : Codec BlockHeader :=
  Codec.ofEquiv BlockHeader.equivProd inferInstance

/-- A block header encodes to exactly 80 bytes: the fixed size of the
proof-of-work preimage. -/
theorem BlockHeader.encode_length (h : BlockHeader) : (Codec.encode h).length = 80 := by
  simp [Codec.encode, List.length_append, encodeBitVecLE_length]

end BtcVerified
