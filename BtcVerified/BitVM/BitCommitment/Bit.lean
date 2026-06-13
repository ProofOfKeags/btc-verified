/-!
  # The committed bit

  The payload a BitVM bit commitment commits to: a single bit.
-/

namespace BtcVerified.BitVM.BitCommitment

/-- The committed payload is a bit. -/
inductive Bit where
  | zero
  | one
  deriving DecidableEq, Repr

end BtcVerified.BitVM.BitCommitment
