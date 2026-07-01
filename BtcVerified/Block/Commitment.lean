import BtcVerified.Block.Block
import BtcVerified.Transaction.Txid
import BtcVerified.Crypto.Merkle
/-!
  # The block's merkle commitment

  The validity condition tying a block's header to its body: the transaction
  ids form a canonical list whose merkle root is the header's `merkleRoot`.
  Root equality alone is not enough — the padding ambiguity (CVE-2012-2459)
  lets a non-canonical list share a canonical list's root — so consensus
  demands canonicality of the list itself.

  The SegWit witness commitment — the wtxid merkle root committed in the
  coinbase — is the next leaf, not this one.

  Checked claims:

  * `Block.merkleCommits` is decidable, so real blocks are checked against it
    in the golden vectors and the `lake test` fixture.
-/

namespace BtcVerified

/-- The merkle commitment a consensus-valid block satisfies: its transaction
ids form a canonical list whose merkle root is the header's. With
`Merkle.root_inj_of_canonical`, two such blocks sharing a header agree on
their txid lists — or exhibit a concrete double-SHA-256 collision. -/
def Block.merkleCommits (b : Block) : Prop :=
  Merkle.Canonical (b.txs.val.map Tx.txid)
    ∧ Merkle.computeRoot (b.txs.val.map Tx.txid) = b.header.merkleRoot

instance : DecidablePred Block.merkleCommits := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

end BtcVerified
