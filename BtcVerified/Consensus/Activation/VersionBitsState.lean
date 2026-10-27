import BtcVerified.Consensus.Rule
/-!
  # Versionbits deployment state

  These are the five states used by Bitcoin Core fc6923cec5b440b611700f6629d8c6a61c6f11bd.
  The model states the forward transition table; it does not model Core's cache.

-/

namespace BtcVerified.Consensus

/-- The deployment state shared by every block in one signaling period. -/
inductive VersionBitsState where
  /-- Signaling has not started. -/
  | defined
  /-- Signaling counts toward the threshold. -/
  | started
  /-- The threshold was reached; activation awaits a later period boundary. -/
  | lockedIn
  /-- The deployment's rules apply. -/
  | active
  /-- The deployment timed out before lock-in. -/
  | failed
  deriving DecidableEq

/-- Enforce a requirement exactly when this deployment state is active. -/
def VersionBitsState.enforce (state : VersionBitsState) (requirement : Rule α) : Rule α :=
  Rule.when (Rule.ofDecidable fun _ : α => state = .active) requirement

end BtcVerified.Consensus
