import BtcVerified.BitVM.BitCommitment.Opening
/-!
  # Collisions and collision resistance

  A collision is two distinct openings that hash to the same commitment digest.
  Collision resistance says no such witness exists — the abstract hypothesis the
  binding of the commitment scheme will rest on.
-/

namespace BtcVerified.BitVM.BitCommitment

/-- A collision is two distinct openings that produce the same commitment digest
under the abstract hash. -/
structure Collision (hash : Bit → Nonce → Digest) where
  /-- One opening in the collision pair. -/
  left : Opening Nonce
  /-- The other opening in the collision pair. -/
  right : Opening Nonce
  /-- Evidence that the two openings are not the same opening. -/
  distinct : left ≠ right
  /-- Evidence that the two openings hash to the same digest. -/
  same_digest : commit hash left.bit left.nonce = commit hash right.bit right.nonce

/-- `CollisionResistance` says that the bundled commitment function admits no
collision witnesses. -/
def CollisionResistance (hash : Bit → Nonce → Digest) : Prop := Collision hash → False

end BtcVerified.BitVM.BitCommitment
