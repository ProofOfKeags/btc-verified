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
  * any equivocation refutes collision resistance;
  * collision resistance gives non-equivocation;
  * non-equivocation makes the induced commitments binding.

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
  /-- The bit revealed by the opening. -/
  bit : Bit
  /-- The nonce paired with the revealed bit. -/
  nonce : Nonce

/--
  If two openings reveal different bits, then the openings themselves are
  different. This is the small structural fact that turns equivocation into a
  collision witness.
-/
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
def verifies
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
    verifies hash (commit hash bit nonce) ⟨bit, nonce⟩ := by
  rfl

/-- A valid opening packages an opening together with its verification proof. -/
structure ValidOpening (hash : Bit → Nonce → Digest) (c : Commitment Digest) where
  /-- The concrete opening being validated. -/
  opening : Opening Nonce
  /-- Evidence that the opening recomputes to the target commitment. -/
  valid : verifies hash c opening

/--
  Equivocation means one commitment has two valid openings whose revealed bits
  are distinct.
-/
structure Equivocation (hash : Bit → Nonce → Digest) where
  /-- The commitment that admits two distinct valid openings. -/
  commitment : Commitment Digest
  /-- One valid opening for the commitment. -/
  left : ValidOpening hash commitment
  /-- Another valid opening for the same commitment. -/
  right : ValidOpening hash commitment
  /-- Evidence that the two openings reveal different bits. -/
  bits_distinct : left.opening.bit ≠ right.opening.bit

/--
  A collision is two distinct openings that produce the same commitment digest
  under the abstract hash.
-/
structure Collision (hash : Bit → Nonce → Digest) where
  /-- One opening in the collision pair. -/
  left : Opening Nonce
  /-- The other opening in the collision pair. -/
  right : Opening Nonce
  /-- Evidence that the two openings are not the same opening. -/
  distinct : left ≠ right
  /-- Evidence that the two openings hash to the same digest. -/
  same_digest : commit hash left.bit left.nonce = commit hash right.bit right.nonce

/--
  Extracts the concrete collision witness contained in an equivocation.

  The two openings are distinct because they reveal different bits, and their
  digests are equal because both verify against the same commitment.
-/
def collisionFromEquivocation
    (hash : Bit → Nonce → Digest)
    (equivocation : Equivocation hash) :
    Collision hash :=
  let ⟨_commitment, left, right, bits_distinct⟩ := equivocation
  { left := left.opening
    right := right.opening
    distinct := openings_with_distinct_bits_are_distinct left.opening right.opening bits_distinct
    same_digest := by rw [left.valid, right.valid] }

/--
  `collisionResistance` says that the bundled commitment function admits no
  collision witnesses.
-/
def collisionResistance (hash : Bit → Nonce → Digest) : Prop := Collision hash → False

/--
  Any equivocation refutes collision resistance, because the equivocation can
  be converted into a concrete collision.
-/
theorem equivocation_refutes_collision_resistance
    (hash : Bit → Nonce → Digest)
    (equivocation : Equivocation hash) :
    ¬ collisionResistance hash := by
  intro resistance
  apply resistance
  apply collisionFromEquivocation
  exact equivocation

/--
  `nonEquivocation` says that the bundled commitment function admits no
  equivocation witnesses.
-/
def nonEquivocation (hash : Bit → Nonce → Digest) : Prop := Equivocation hash → False

/--
  Collision resistance gives non-equivocation: an equivocation witness would
  produce the collision witness that collision resistance rules out.
-/
theorem collision_resistance_gives_non_equivocation
    (hash : Bit → Nonce → Digest) :
    collisionResistance hash → nonEquivocation hash := by
  intros resistance equivocation
  apply resistance
  exact collisionFromEquivocation hash equivocation

/-- `binding` says that any two valid openings reveal the same bit. -/
def binding (hash : Bit → Nonce → Digest) : Prop :=
  ∀ (c : Commitment Digest) (left right : ValidOpening hash c),
    left.opening.bit = right.opening.bit

/--
  If equivocation is impossible, then two valid openings for the same commitment
  must reveal the same bit.
-/
theorem non_equivocation_makes_commitments_binding
    (hash : Bit → Nonce → Digest)
    (hashForbidsEquivocation : nonEquivocation hash) :
    binding hash := by
  intros commitment left right
  by_cases same_bits : left.opening.bit = right.opening.bit
  · exact same_bits
  · apply False.elim
    apply hashForbidsEquivocation
    constructor
    exact same_bits

/--
  Collision resistance makes the induced commitments binding.

  Collision resistance gives non-equivocation, and non-equivocation rules out
  pairs of valid openings that reveal different bits.
-/
theorem collision_resistance_makes_commitments_binding
    (hash : Bit → Nonce → Digest)
    (resistance : collisionResistance hash) :
    binding hash := by
  apply non_equivocation_makes_commitments_binding hash
  apply collision_resistance_gives_non_equivocation hash
  exact resistance

end BtcVerified.BitVM.BitCommitment
