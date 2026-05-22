namespace BtcVerified.BitVM.BitCommitment

/--
  A bit-level commitment primitive for the BitVM verification track.

  This file intentionally keeps the hash function abstract. The first useful
  proof surface is the protocol shape: opening one commitment to both bits is
  exactly a collision/equivocation witness for the commitment hash.
-/

inductive Bit where
  | zero
  | one
  deriving DecidableEq, Repr

structure Opening (Nonce : Type) where
  bit : Bit
  nonce : Nonce

theorem diff_bits_diff_openings {Nonce: Type}
  (left right : Opening Nonce)
  (hdiff : left.bit ≠ right.bit) : left ≠ right := by
    exact mt (congrArg Opening.bit) hdiff

abbrev Commitment (Digest : Type) := Digest

def commit (hash : Bit → Nonce → Digest) (bit : Bit) (nonce : Nonce) : Commitment Digest :=
  hash bit nonce

def verifies (hash : Bit → Nonce → Digest) (c : Commitment Digest)
    (opening : Opening Nonce) : Prop :=
  commit hash opening.bit opening.nonce = c

theorem commit_verifies_identity
    (hash : Bit → Nonce → Digest) (bit : Bit) (nonce : Nonce) :
    verifies hash (commit hash bit nonce) ⟨bit, nonce⟩ := by
  rfl

structure ValidOpening (hash : Bit → Nonce → Digest) (c : Commitment Digest) where
  opening : Opening Nonce
  valid: verifies hash c opening

structure Equivocation (hash : Bit → Nonce → Digest) where
  commitment : Commitment Digest
  left : ValidOpening hash commitment
  right : ValidOpening hash commitment
  bits_distinct : left.opening.bit ≠ right.opening.bit

structure Collision (hash : Bit → Nonce → Digest) where
  left : Opening Nonce
  right : Opening Nonce
  distinct : left ≠ right
  same_digest : commit hash left.bit left.nonce = commit hash right.bit right.nonce

def collisionFromEquivocation
    (hash : Bit → Nonce → Digest)
    (equivocation : Equivocation hash) :
    Collision hash := by
    rcases equivocation with ⟨c, left, right, diff_bits⟩
    apply Collision.mk
    apply diff_bits_diff_openings
    exact diff_bits
    rw [left.valid, right.valid]

theorem equivocation_implies_collision
    (hash : Bit → Nonce → Digest)
    (equivocation : Equivocation hash) :
    Nonempty (Collision hash) := by
  exact ⟨collisionFromEquivocation hash equivocation⟩

def CollisionResistant (hash : Bit → Nonce → Digest) : Prop := Collision hash → False

def Binding (hash : Bit → Nonce → Digest) : Prop :=
  ∀ (c : Commitment Digest) (left right : ValidOpening hash c),
    left.opening.bit = right.opening.bit

theorem collision_resistant_hashes_are_binding
    (hash : Bit → Nonce → Digest)
    (hcr : CollisionResistant hash) :
    Binding hash := by
    intro c left right
    by_cases same_bits : left.opening.bit = right.opening.bit
    · exact same_bits
    · let equivocation : Equivocation hash := ⟨c, left, right, same_bits⟩
      let collision : Collision hash := collisionFromEquivocation hash equivocation
      exact (False.elim (hcr collision))

end BtcVerified.BitVM.BitCommitment
