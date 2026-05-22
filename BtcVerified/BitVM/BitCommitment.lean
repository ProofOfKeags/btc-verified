/-!
  # Abstract BitVM bit commitments

  This module models the smallest useful commitment primitive for the BitVM
  verification track. The hash function is intentionally abstract: the point of
  this leaf is not to verify SHA-256 or any concrete compression function, but
  to state the protocol-level shape that any collision-resistant commitment
  hash must satisfy.

  A commitment is produced by hashing a bit together with a nonce. An
  equivocation is a single commitment with two valid openings to distinct bits.
  The checked proof spine is:

  * distinct opened bits imply distinct openings;
  * an equivocation therefore gives two distinct openings with the same digest,
    i.e. a collision;
  * if collisions are impossible, every pair of valid openings for a commitment
    must open to the same bit.

  This is deliberately tiny, but it fixes the vocabulary for later BitVM proof
  packets: openings, equivocation, collision resistance, and binding.
-/

namespace BtcVerified.BitVM.BitCommitment

/-- The committed payload is a bit. -/
inductive Bit where
  | zero
  | one
  deriving DecidableEq, Repr

/-- An opening reveals both the committed bit and the nonce used to commit it. -/
structure Opening (Nonce : Type) where
  bit : Bit
  nonce : Nonce

/--
  If two openings reveal different bits, then the openings themselves are
  different. This is the small structural fact that turns equivocation into a
  collision witness.
-/
theorem diff_bits_diff_openings {Nonce: Type}
  (left right : Opening Nonce)
  (hdiff : left.bit ≠ right.bit) : left ≠ right := by
    exact mt (congrArg Opening.bit) hdiff

/-- A commitment is just a digest value at this abstraction level. -/
abbrev Commitment (Digest : Type) := Digest

/-- Commits to a bit by hashing the bit together with a nonce. -/
def commit (hash : Bit → Nonce → Digest) (bit : Bit) (nonce : Nonce) : Commitment Digest :=
  hash bit nonce

/-- An opening verifies when recomputing the commitment yields the same digest. -/
def verifies (hash : Bit → Nonce → Digest) (c : Commitment Digest)
    (opening : Opening Nonce) : Prop :=
  commit hash opening.bit opening.nonce = c

/-- The opening used to create a commitment verifies for that commitment. -/
theorem commit_verifies_identity
    (hash : Bit → Nonce → Digest) (bit : Bit) (nonce : Nonce) :
    verifies hash (commit hash bit nonce) ⟨bit, nonce⟩ := by
  rfl

/-- A valid opening packages an opening together with its verification proof. -/
structure ValidOpening (hash : Bit → Nonce → Digest) (c : Commitment Digest) where
  opening : Opening Nonce
  valid: verifies hash c opening

/--
  Equivocation means one commitment has two valid openings whose revealed bits
  are distinct.
-/
structure Equivocation (hash : Bit → Nonce → Digest) where
  commitment : Commitment Digest
  left : ValidOpening hash commitment
  right : ValidOpening hash commitment
  bits_distinct : left.opening.bit ≠ right.opening.bit

/--
  A collision is two distinct openings that produce the same commitment digest
  under the abstract hash.
-/
structure Collision (hash : Bit → Nonce → Digest) where
  left : Opening Nonce
  right : Opening Nonce
  distinct : left ≠ right
  same_digest : commit hash left.bit left.nonce = commit hash right.bit right.nonce

/--
  Extracts the concrete collision witness contained in an equivocation.

  The two openings are distinct because they reveal different bits, and their
  digests are equal because both verify against the same commitment.
-/
def collisionFromEquivocation
    (hash : Bit → Nonce → Digest)
    (equivocation : Equivocation hash) :
    Collision hash := by
    rcases equivocation with ⟨c, left, right, diff_bits⟩
    apply Collision.mk
    apply diff_bits_diff_openings
    exact diff_bits
    rw [left.valid, right.valid]

/-- Every equivocation gives evidence that a collision exists. -/
theorem equivocation_implies_collision
    (hash : Bit → Nonce → Digest)
    (equivocation : Equivocation hash) :
    Nonempty (Collision hash) := by
  exact ⟨collisionFromEquivocation hash equivocation⟩

/-- Collision resistance says there are no collision witnesses for this hash. -/
def CollisionResistant (hash : Bit → Nonce → Digest) : Prop := Collision hash → False

/--
  Binding says that any two valid openings for the same commitment must reveal
  the same bit.
-/
def Binding (hash : Bit → Nonce → Digest) : Prop :=
  ∀ (c : Commitment Digest) (left right : ValidOpening hash c),
    left.opening.bit = right.opening.bit

/--
  Collision resistance implies binding for this abstract commitment scheme.

  If two valid openings for one commitment revealed different bits, they would
  form an equivocation, hence a collision. Collision resistance rules that out.
-/
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
