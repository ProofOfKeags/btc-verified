import Mathlib.Data.Bool.Basic
/-!
  # Parameters for an in-flight versionbits deployment

  Positive signaling periods and bounded thresholds are structural. Constant
  always-active/never-active deployment choices belong to the outer selector.
-/

namespace BtcVerified.Consensus

/-- The parameters of one timed deployment, excluding Core's special sentinel times. -/
structure VersionBitsParams where
  /-- The signaling bit below the three versionbits prefix bits. -/
  bit : Fin 29
  /-- Number of consecutive block heights sharing a deployment state. -/
  period : Nat
  /-- Period alignment and the completed window require a positive period. -/
  periodPositive : 0 < period
  /-- Minimum signaling blocks in a completed period; zero is permitted. -/
  threshold : Nat
  /-- The requested signaling count is attainable within one period. -/
  thresholdBound : threshold ≤ period
  /-- First boundary MTP at which the deployment enters the started state. -/
  startTime : Nat
  /-- Boundary MTP at which a started deployment without enough signals fails. -/
  timeout : Nat
  /-- Minimum height of the first block of an active period. -/
  minActivationHeight : Nat

/-- A raw header version signals only when its top three bits are 001 and its
selected deployment bit is set; negative signed header versions do not signal
([pinned Core](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/versionbits_impl.h#L77-L81)). -/
def VersionBitsParams.signals (params : VersionBitsParams) (version : UInt32) : Bool :=
  (version &&& 0xe0000000) == 0x20000000 && version.toNat.testBit params.bit.val

end BtcVerified.Consensus
