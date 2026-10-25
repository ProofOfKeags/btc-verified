import BtcVerified.Block.Block
import BtcVerified.Transaction.Txid
import BtcVerified.Crypto.Merkle
/-!
  # The block's merkle commitment

  The validity condition tying a block's header to its body: the transaction
  ids form a canonical list whose merkle root is the header's `merkleRoot`.
  Root equality alone is not enough — the padding ambiguity (CVE-2012-2459)
  lets a non-canonical list share a canonical list's root — so consensus
  demands canonicality of the list itself. The binding theorem also requires
  both transaction lists to be nonempty and to have equal enclosing widths;
  neither condition follows from `merkleCommits` alone.

  The SegWit witness commitment — the wtxid merkle root committed in the
  coinbase — is `WitnessCommitment.lean`, the sibling leaf built on the
  same pattern.

  Checked claims:

  * `Block.merkleCommits` is decidable, so real blocks are checked against it
    in the golden vectors and the `lake test` fixture.
-/

namespace BtcVerified

/-- The transaction ids form a canonical list whose merkle root is the header's.
For two such blocks sharing a header, `Merkle.root_binding_of_canonical` also
requires nonempty txid lists of equal enclosing width: their lists are then equal,
or node preimages from their two merkle trees collide under double-SHA-256. -/
def Block.merkleCommits (b : Block) : Prop :=
  Merkle.Canonical (b.txs.val.map Tx.txid)
    ∧ Merkle.root (b.txs.val.map Tx.txid) = b.header.merkleRoot

/-- Decide whether a block's transaction ids satisfy its merkle commitment. -/
instance instDecidableMerkleCommits : DecidablePred Block.merkleCommits := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

end BtcVerified
