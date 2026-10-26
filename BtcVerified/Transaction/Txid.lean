import BtcVerified.Transaction.Tx
import BtcVerified.Crypto.Sha256
import BtcVerified.Crypto.Hash256
/-!
  # Transaction ids

  The txid is the double-SHA-256 of the witness-free `TxBody` serialization,
  as its raw 32 digest bytes; the wtxid (BIP141) is the same over the full
  serialization, witness included. Witness data never affects a txid — that
  is the non-malleability SegWit exists to provide — and for a legacy
  transaction the two ids coincide definitionally.

  A hash of an encoding only identifies anything because the encoding is
  injective — `encode_injective`, a consequence of the codec round-trip law.
  The binding theorems here are exactly that observation: equal txids
  mean equal bodies, and equal wtxids mean equal transactions, or in either
  case there are two concrete byte strings witnessing a double-SHA-256
  collision between the encodings of the compared objects. The conclusion
  names those inputs, so an unrelated collision cannot satisfy it. No
  computational hardness claim or global collision-freedom axiom is used.

  Checked claims:

  * `Tx.txid_binding`: equal txids imply equal witness-free bodies, or their
    two encodings collide under `sha256d`.
  * `Tx.wtxid_binding`: equal wtxids imply equal transactions (witnesses
    included), or their two full encodings collide.
  * `Tx.map_wtxid_binding`: equal wtxid lists imply equal transaction lists,
    or a collision between transaction encodings from the two lists.
  * `Tx.wtxid_legacy`: a legacy transaction's wtxid is its txid.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- The transaction id of a witness-free body: the double-SHA-256 of the
`TxBody` serialization, as its raw 32 digest bytes (the displayed hex is these
bytes reversed). The body alone determines the txid — this is the form the
UTXO layer uses to key a transaction's outputs. -/
def TxBody.txid (body : TxBody) : Hash256 :=
  ⟨Sha256.sha256d (Codec.encode body), Sha256.sha256d_length _⟩

/-- The transaction id: the txid of the witness-free body. Both constructors
hash only the body, so witness data never affects a txid. -/
def Tx.txid (tx : Tx) : Hash256 :=
  tx.body.txid

/-- The witness transaction id (BIP141): the double-SHA-256 of the full
serialization, witness included for the SegWit form. -/
def Tx.wtxid (tx : Tx) : Hash256 :=
  ⟨Sha256.sha256d (Codec.encode tx), Sha256.sha256d_length _⟩

/-- A legacy transaction's wtxid is its txid: its full serialization is its
body's serialization. -/
theorem Tx.wtxid_legacy (body : TxBody) (h : body.inputs.val ≠ []) :
    (Tx.legacy body h).wtxid = (Tx.legacy body h).txid := rfl

/-- The degenerate empty transaction is also witness-free, so its wtxid is
its txid. -/
theorem Tx.wtxid_empty (version lockTime : UInt32) :
    (Tx.empty version lockTime).wtxid = (Tx.empty version lockTime).txid := rfl

/-- Equal txids mean equal witness-free bodies — or two serialized bodies
colliding under double-SHA-256. -/
theorem Tx.txid_binding {t₁ t₂ : Tx} (h : t₁.txid = t₂.txid) :
    t₁.body = t₂.body ∨ Sha256.Collides (Codec.encode t₁.body) (Codec.encode t₂.body) := by
  by_cases hb : t₁.body = t₂.body
  · exact Or.inl hb
  · exact Or.inr ⟨fun he => hb (encode_injective he), congrArg Subtype.val h⟩

/-- Equal wtxids mean equal transactions, witnesses included — or two
full transaction encodings colliding under double-SHA-256. -/
theorem Tx.wtxid_binding {t₁ t₂ : Tx} (h : t₁.wtxid = t₂.wtxid) :
    t₁ = t₂ ∨ Sha256.Collides (Codec.encode t₁) (Codec.encode t₂) := by
  by_cases ht : t₁ = t₂
  · exact Or.inl ht
  · exact Or.inr ⟨fun he => ht (encode_injective he), congrArg Subtype.val h⟩

/-- Equal wtxid lists mean equal transaction lists, witnesses included — or
a collision between an encoding from each list.
`Tx.wtxid_binding` lifted pointwise, in the form the witness commitment's
binding theorem carries through the merkle layer. -/
theorem Tx.map_wtxid_binding {l₁ l₂ : List Tx}
    (h : l₁.map Tx.wtxid = l₂.map Tx.wtxid) :
    l₁ = l₂ ∨ Sha256.CollisionBetween (l₁.map Codec.encode) (l₂.map Codec.encode) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact Or.inl rfl
    | cons t r => exact absurd h (by simp)
  | cons t₁ r₁ ih =>
    cases l₂ with
    | nil => exact absurd h (by simp)
    | cons t₂ r₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      rcases Tx.wtxid_binding h.1 with ht | c
      · rcases ih h.2 with hr | c
        · exact Or.inl (by rw [ht, hr])
        · exact Or.inr (c.mono
            (by intro x hx; exact List.mem_cons_of_mem _ hx)
            (by intro x hx; exact List.mem_cons_of_mem _ hx))
      · exact Or.inr (CollisionBetween.of_collides (by simp) (by simp) c)

end BtcVerified
