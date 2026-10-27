import BtcVerified.Consensus.Activation.VersionBitsState
import BtcVerified.Consensus.Activation.VersionBitsParams
/-!
  # Period-boundary versionbits transitions

  [Pinned Core](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/versionbits.cpp#L76-L111)
  specifies this transition table. Threshold attainment takes precedence
  over timeout; a defined deployment only checks start time.

-/

namespace BtcVerified.Consensus

/-- Advance the state at a completed period, given the next period's first height,
the completed period's final MTP, and the signals counted in that period. -/
def VersionBitsState.atPeriodEnd (state : VersionBitsState) (params : VersionBitsParams)
    (nextHeight medianTimePast signals : Nat) : VersionBitsState :=
  match state with
  | .defined => if params.startTime ≤ medianTimePast then .started else .defined
  | .started =>
    if params.threshold ≤ signals then .lockedIn
    else if params.timeout ≤ medianTimePast then .failed else .started
  | .lockedIn => if params.minActivationHeight ≤ nextHeight then .active else .lockedIn
  | .active => .active
  | .failed => .failed

end BtcVerified.Consensus
