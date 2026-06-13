import BtcVerified.BitVM.BitCommitment.Opening
/-!
  # Valid openings and binding

  A valid opening bundles an opening with its verification proof. `Binding` is
  the property the whole leaf is aiming at: any two valid openings of one
  commitment reveal the same bit.
-/

namespace BtcVerified.BitVM.BitCommitment

/-- A valid opening packages an opening together with its verification proof. -/
structure ValidOpening (hash : Bit → Nonce → Digest) (c : Commitment Digest) where
  /-- The concrete opening being validated. -/
  opening : Opening Nonce
  /-- Evidence that the opening recomputes to the target commitment. -/
  valid : Verifies hash c opening

/-- `Binding` says that any two valid openings reveal the same bit. -/
def Binding (hash : Bit → Nonce → Digest) : Prop :=
  ∀ (c : Commitment Digest) (left right : ValidOpening hash c),
    left.opening.bit = right.opening.bit

end BtcVerified.BitVM.BitCommitment
