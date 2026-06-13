import BtcVerified.BitVM.BitCommitment.Bit
/-!
  # Openings and the commitment function

  An opening reveals the bit and the nonce behind a commitment. The commitment
  itself is a digest produced by hashing the bit with the nonce, and an opening
  verifies when recomputing that digest reproduces the commitment.
-/

namespace BtcVerified.BitVM.BitCommitment

/-- An opening reveals both the committed bit and the nonce used to commit it. -/
structure Opening (Nonce : Type) where
  /-- The bit revealed by the opening. -/
  bit : Bit
  /-- The nonce paired with the revealed bit. -/
  nonce : Nonce

/-- If two openings reveal different bits, then the openings themselves are
different. This is the small structural fact that turns equivocation into a
collision witness. -/
theorem openings_with_distinct_bits_are_distinct {Nonce : Type}
    (left right : Opening Nonce)
    (hdiff : left.bit ≠ right.bit) : left ≠ right := by
  exact mt (congrArg Opening.bit) hdiff

/-- A commitment is just a digest value at this abstraction level. -/
abbrev Commitment (Digest : Type) := Digest

/-- Commits to a bit by hashing the bit together with a nonce. -/
def commit
    (hash : Bit → Nonce → Digest)
    (bit : Bit)
    (nonce : Nonce) :
    Commitment Digest :=
  hash bit nonce

/-- An opening verifies when recomputing the commitment yields the same digest. -/
def Verifies
    (hash : Bit → Nonce → Digest)
    (c : Commitment Digest)
    (opening : Opening Nonce) :
    Prop :=
  commit hash opening.bit opening.nonce = c

/-- The opening used to create a commitment verifies for that commitment. -/
theorem commitment_verifies_against_original_opening
    (hash : Bit → Nonce → Digest)
    (bit : Bit)
    (nonce : Nonce) :
    Verifies hash (commit hash bit nonce) ⟨bit, nonce⟩ := by
  rfl

end BtcVerified.BitVM.BitCommitment
