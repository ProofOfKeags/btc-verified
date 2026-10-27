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

end BtcVerified.Consensus
