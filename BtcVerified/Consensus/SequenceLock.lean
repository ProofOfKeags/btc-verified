import BtcVerified.Consensus.Limits
/-!
  # Relative input lock times

  An input sequence encodes a disabled lock, a block delay, or a delay in
  seconds. The transaction version and active rules decide whether this
  interpretation is enforced. Keeping the selected unit in the type avoids
  mixing height and time when the contextual rules compare coin ages.

  The wire interpretation follows the pinned
  [Core sequence constants](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/primitives/transaction.h#L84-L114).
-/

namespace BtcVerified.Consensus

/-- The relative delay encoded by one input's sequence field. -/
inductive SequenceLock where
  /-- The input imposes no relative lock. -/
  | disabled
  /-- The input requires this many blocks since its coin's creation. -/
  | blocks (delay : Nat)
  /-- The input requires this many seconds since its coin's time anchor. -/
  | seconds (delay : Nat)
  deriving DecidableEq

end BtcVerified.Consensus
