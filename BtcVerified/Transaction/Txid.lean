import BtcVerified.Transaction.Tx
import BtcVerified.Crypto.Sha256
import BtcVerified.Crypto.Hash256
/-!
  # Transaction ids

  The txid is the double-SHA-256 of the witness-free `TxBody` serialization,
  read little-endian; the wtxid (BIP141) is the same over the full
  serialization, witness included. Witness data never affects a txid — that
  is the non-malleability SegWit exists to provide — and for a legacy
  transaction the two ids coincide definitionally.

  A hash of an encoding only identifies anything because the encoding is
  injective — `encode_injective`, a consequence of the codec round-trip law.
  The faithfulness theorems here are exactly that observation: equal txids
  mean equal bodies, and equal wtxids mean equal transactions, or in either
  case there are two concrete byte strings witnessing a double-SHA-256
  collision (`Sha256.Collision`). The collision appears as a constructed
  disjunct, never as an assumed-absent axiom.

  Checked claims:

  * `Tx.txid_faithful`: equal txids imply equal witness-free bodies, or a
    concrete `sha256d` collision.
  * `Tx.wtxid_faithful`: equal wtxids imply equal transactions (witnesses
    included), or a concrete `sha256d` collision.
  * `Tx.wtxid_legacy`: a legacy transaction's wtxid is its txid.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- The transaction id: double-SHA-256 of the witness-free `TxBody`
serialization, read little-endian (the displayed hex is the digest bytes
reversed). Both constructors hash only the body, so witness data never
affects a txid. -/
def Tx.txid (tx : Tx) : Hash256 :=
  Hash256.ofBytesLE (Sha256.sha256d (Codec.encode tx.body))

/-- The witness transaction id (BIP141): double-SHA-256 of the full
serialization, witness included for the SegWit form. -/
def Tx.wtxid (tx : Tx) : Hash256 :=
  Hash256.ofBytesLE (Sha256.sha256d (Codec.encode tx))

/-- A legacy transaction's wtxid is its txid: its full serialization is its
body's serialization. -/
theorem Tx.wtxid_legacy (body : TxBody) (h : body.inputs.val ≠ []) :
    (Tx.legacy body h).wtxid = (Tx.legacy body h).txid := rfl

/-- Equal hash-of-digest values force the digests themselves equal, because a
full digest round-trips through its 32-byte encoding. -/
private theorem digest_eq_of_hash_eq {a b : List UInt8}
    (h : Hash256.ofBytesLE (Sha256.sha256d a) = Hash256.ofBytesLE (Sha256.sha256d b)) :
    Sha256.sha256d a = Sha256.sha256d b := by
  rw [← Hash256.encode_ofBytesLE (Sha256.sha256d_length a),
    ← Hash256.encode_ofBytesLE (Sha256.sha256d_length b), h]

/-- Equal txids mean equal witness-free bodies — or two concrete byte strings
witnessing a double-SHA-256 collision. -/
theorem Tx.txid_faithful {t₁ t₂ : Tx} (h : t₁.txid = t₂.txid) :
    t₁.body = t₂.body ∨ Sha256.Collision := by
  by_cases hb : t₁.body = t₂.body
  · exact Or.inl hb
  · exact Or.inr ⟨Codec.encode t₁.body, Codec.encode t₂.body,
      fun he => hb (encode_injective he), digest_eq_of_hash_eq h⟩

/-- Equal wtxids mean equal transactions, witnesses included — or two
concrete byte strings witnessing a double-SHA-256 collision. -/
theorem Tx.wtxid_faithful {t₁ t₂ : Tx} (h : t₁.wtxid = t₂.wtxid) :
    t₁ = t₂ ∨ Sha256.Collision := by
  by_cases ht : t₁ = t₂
  · exact Or.inl ht
  · exact Or.inr ⟨Codec.encode t₁, Codec.encode t₂,
      fun he => ht (encode_injective he), digest_eq_of_hash_eq h⟩

end BtcVerified
