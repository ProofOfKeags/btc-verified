import BtcVerified.Block.BlockHeader
import BtcVerified.Crypto.Sha256
/-!
  # Block header hashes

  The block hash: the double-SHA-256 of a header's 80-byte encoding, the same
  digest proof-of-work targets and `prevBlockHash` links commit to. Promoted
  from the ad hoc `Sha256.sha256d (Codec.encode b.header)` expression the
  fixture tests computed inline into the library — the same move `Tx.txid`
  made for transactions.

  As with `Tx.txid_faithful`, the faithfulness theorem here is the
  collision-disjunct idiom: equal hashes force equal headers, or the two
  encodings exhibit a concrete double-SHA-256 collision. Collision resistance
  is never assumed for the concrete hash — only ever a hypothesis a caller
  supplies over the abstract `Sha256.Collision` vocabulary.

  Checked claims:

  * `BlockHeader.hash_faithful`: equal block hashes mean equal headers — or a
    concrete double-SHA-256 collision.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- The block hash: the double-SHA-256 of the header's 80-byte encoding. This
is the digest `prevBlockHash` links commit to, and the digest a proof-of-work
target is checked against (the target check itself belongs to the
proof-of-work layer, not this module). -/
def BlockHeader.hash (h : BlockHeader) : Hash256 :=
  ⟨Sha256.sha256d (Codec.encode h), Sha256.sha256d_length _⟩

/-- Equal block hashes mean equal headers — or two concrete byte strings
witnessing a double-SHA-256 collision. -/
theorem BlockHeader.hash_faithful {h₁ h₂ : BlockHeader} (h : h₁.hash = h₂.hash) :
    h₁ = h₂ ∨ Sha256.Collision := by
  by_cases he : h₁ = h₂
  · exact Or.inl he
  · exact Or.inr ⟨Codec.encode h₁, Codec.encode h₂,
      fun hc => he (encode_injective hc), congrArg Subtype.val h⟩

end BtcVerified
