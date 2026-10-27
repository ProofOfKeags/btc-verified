import BtcVerified.Consensus.Activation.VersionBitsBoundary
/-!
  # Versionbits history and continuation examples

  Two hash-linked branches share the same prefix and height but have different
  signaling counts. Their timestamps are synthetic and deployment parameters
  use four-block periods and increasing timestamps to expose the transitions compactly.
-/

namespace Tests.ActivationHistory

open BtcVerified BtcVerified.Consensus

set_option linter.hashCommand false

private def params : VersionBitsParams :=
  ⟨⟨2, by decide⟩, 4, by decide, 3, by decide, 10, 20, 0⟩

private def header (version time : UInt32) : BlockHeader :=
  ⟨version, 0, 0, time, 0, 0⟩

private def linked (anchor : Hash256) (headers : List BlockHeader) :
    Σ tip : Hash256, Chain anchor tip :=
  headers.foldl (fun ⟨tip, chain⟩ template =>
    let next := { template with prevBlockHash := tip }
    ⟨next.hash, .extend next chain⟩) ⟨anchor, .nil⟩

private def commonHistory := linked 0
  ([10, 11, 12, 13].map (header 0x20000000) ++ [20, 21].map (header 0x20000004))
private def startBoundary := (VersionBitsBoundary.initial params).extend commonHistory.2
private def waitingPeriod := [24, 25, 26, 27].map (header 0x20000000)
private def successfulBranch := linked commonHistory.1
  ([header 0x20000004 22, header 0x20000000 23] ++ waitingPeriod)
private def failingBranch := linked commonHistory.1
  ([22, 23].map (header 0x20000000) ++ waitingPeriod)

#guard startBoundary.progress.state == .started
#guard startBoundary.progress.nextHeight == 6
#guard startBoundary.progress.periodSignals == 2
#guard (startBoundary.extend successfulBranch.2).progress.state == .active
#guard (startBoundary.extend failingBranch.2).progress.state == .failed
#guard (startBoundary.extend successfulBranch.2).progress.nextHeight == 12
#guard (startBoundary.extend failingBranch.2).progress.nextHeight == 12
#guard ((VersionBitsBoundary.initial params).extend
  (successfulBranch.2.append commonHistory.2)).progress.state == .active

end Tests.ActivationHistory
