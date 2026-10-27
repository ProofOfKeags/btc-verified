import BtcVerified.Block.BlockHeader
import BtcVerified.Consensus.Activation.Temporary
import BtcVerified.Consensus.Activation.VersionBitsParams
/-!
  # Temporary signaling examples

  These synthetic inputs carry candidate MTP, parent deployment state and an
  actual header. They require bit 1 with the versionbits 001 prefix only in
  `.started` and within inclusive times. The window resembles BIP148, but its
  historical guard excludes locked-in/active rather than selecting only started;
  this example deliberately does not claim exact BIP148 or BIP91 validation.
  No header history, proof of work or Bitcoin Core execution is checked here.
-/

namespace Tests.TemporaryExamples

open BtcVerified BtcVerified.Consensus

set_option linter.hashCommand false

private abbrev Input := Nat × VersionBitsState × BlockHeader

-- Only the selected bit is consumed by `signals`; other parameters are fixtures.
private def signalParams : VersionBitsParams where
  bit := ⟨1, by decide⟩
  period := 1
  periodPositive := by decide
  threshold := 1
  thresholdBound := by decide
  startTime := 0
  timeout := 1
  minActivationHeight := 0

private def header (version : UInt32) : BlockHeader :=
  ⟨version, 0, 0, 0, 0, 0⟩

private def signals : Rule Input := Rule.ofDecidable fun input =>
  signalParams.signals input.2.2.version = true

private def inStarted : Rule Input := Rule.inStates (fun input => input.2.1) [.started] signals

private def temporary : Rule Input := Rule.during Prod.fst 1501545600 1510704000 inStarted

-- Inclusive first boundary; prefix and selected bit are independent requirements.
#guard temporary.check (1501545599, .started, header 0)
#guard temporary.check (1501545600, .started, header 0x20000002)
#guard !temporary.check (1501545600, .started, header 0x20000000)
#guard !temporary.check (1501545600, .started, header 0x40000002)
-- Inclusive last boundary, followed by cessation even for a non-signaling header.
#guard temporary.check (1510704000, .started, header 0x20000002)
#guard !temporary.check (1510704000, .started, header 0x20000000)

end Tests.TemporaryExamples
