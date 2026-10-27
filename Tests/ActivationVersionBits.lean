import BtcVerified.Consensus.Activation.VersionBitsProgress
/-!
  # Header-derived deployment progress

  Chronological synthetic headers exercise partial periods, count reset,
  the MTP window, and minimum-height activation at period boundaries.
-/

namespace Tests.ActivationVersionBits

open BtcVerified BtcVerified.Consensus

set_option linter.hashCommand false

private def params : VersionBitsParams :=
  ⟨⟨2, by decide⟩, 4, by decide, 3, by decide, 10, 20, 0⟩

private def header (version time : UInt32) : BlockHeader :=
  ⟨version, 0, 0, time, 0, 0⟩

#guard VersionBitsProgress.medianTimePast [9, 1] == 9
#guard VersionBitsProgress.medianTimePast [1, 9, 5] == 5
#guard (VersionBitsProgress.initial.consume params
  ([1, 2, 3, 100].map (header 0x20000004))).state == .defined
private def firstPeriod : List BlockHeader := List.replicate 4 (header 0x20000004 10)
private def signalingPeriod : List BlockHeader :=
  List.replicate 3 (header 0x20000004 20) ++ [header 0x20000000 20]
private def waitingPeriod : List BlockHeader := List.replicate 4 (header 0x20000000 20)
private def afterFirst := VersionBitsProgress.initial.consume params firstPeriod
private def afterSecond := afterFirst.consume params signalingPeriod

#guard VersionBitsProgress.initial.state == .defined
#guard (VersionBitsProgress.initial.consume params (firstPeriod.take 3)).state == .defined
#guard afterFirst.state == .started

end Tests.ActivationVersionBits
