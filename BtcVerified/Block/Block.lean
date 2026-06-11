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
