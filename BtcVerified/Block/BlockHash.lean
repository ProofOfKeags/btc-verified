import BtcVerified.Block.BlockHeader
import BtcVerified.Crypto.Sha256
/-!
  # Block header hashes

  The block hash: the double-SHA-256 of a header's 80-byte encoding, the same
  digest proof-of-work targets and `prevBlockHash` links commit to. Promoted
  from the ad hoc `Sha256.sha256d (Codec.encode b.header)` expression the
  fixture tests computed inline into the library — the same move `Tx.txid`
  made for transactions.

  As with `Tx.txid_binding`, equal hashes imply equal headers or a
  double-SHA-256 collision between the two specified 80-byte header encodings.
  The collision must involve those two header encodings; an unrelated
  collision cannot satisfy the conclusion. No global collision freedom or
  computational security assumption is made.

  Checked claims:

  * `BlockHeader.hash_binding`: equal block hashes imply equal headers, or
    the two specified header encodings collide under double-SHA-256.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- The block hash: the double-SHA-256 of the header's 80-byte encoding. This
is the digest `prevBlockHash` links commit to, and the digest a proof-of-work
target is checked against (the target check itself belongs to the
proof-of-work layer, not this module). -/
def BlockHeader.hash (h : BlockHeader) : Hash256 :=
  ⟨Sha256.sha256d (Codec.encode h), Sha256.sha256d_length _⟩

/-- Equal block hashes mean equal headers — or their two encodings
collide under double-SHA-256. -/
theorem BlockHeader.hash_binding {h₁ h₂ : BlockHeader} (h : h₁.hash = h₂.hash) :
    h₁ = h₂ ∨ Sha256.Collides (Codec.encode h₁) (Codec.encode h₂) := by
  by_cases he : h₁ = h₂
  · exact Or.inl he
  · exact Or.inr ⟨fun hc => he (encode_injective hc), congrArg Subtype.val h⟩

end BtcVerified
