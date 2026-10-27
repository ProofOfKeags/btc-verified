import BtcVerified.Block.BlockHeader
import BtcVerified.Consensus.Activation.VersionBitsTransition
/-!
  # Incremental versionbits evaluation

  The forward table follows Core fc6923cec5b440b611700f6629d8c6a61c6f11bd,
  src/versionbits.cpp lines 76–111. Threshold attainment precedes timeout;
  defined checks only start time. State changes occur only at period boundaries.
  Core's backwards cache shortcut additionally relies on timestamp-valid ancestry;
  no equivalence with that optimized algorithm is claimed for arbitrary headers.

-/

namespace BtcVerified.Consensus

/-- Sufficient history to continue one deployment immediately after an assumed prefix.
Manually supplied values are assumptions about that prefix, not validated history. -/
structure VersionBitsProgress where
  /-- Absolute height of the next header to consume. -/
  nextHeight : Nat
  /-- State applying to the next header's signaling period. -/
  state : VersionBitsState
  /-- Signals already consumed within that period, zero at a period boundary. -/
  periodSignals : Nat
  /-- Up to eleven consumed timestamps, newest first and contiguous with the prefix tip. -/
  recentTimes : List UInt32

/-- Before genesis, height zero has no signals or preceding timestamps and is defined. -/
def VersionBitsProgress.initial : VersionBitsProgress :=
  ⟨0, .defined, 0, []⟩

/-- Select the upper middle timestamp after sorting; empty history has no measured
MTP and returns zero, which the boundary transition never reads from initial state.
The ordering follows [pinned Core](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/chain.h#L231-L244). -/
def VersionBitsProgress.medianTimePast (times : List UInt32) : Nat :=
  ((times.map UInt32.toNat).mergeSort (· ≤ ·))[times.length / 2]?.getD 0

/-- Consume one chronological header, deriving its signal and the new MTP window;
only a completed period changes the state or clears the signal count. -/
def VersionBitsProgress.advance (params : VersionBitsParams) (progress : VersionBitsProgress)
    (header : BlockHeader) : VersionBitsProgress :=
  let height := progress.nextHeight + 1
  let times := (header.time :: progress.recentTimes).take 11
  let signals := progress.periodSignals + if params.signals header.version then 1 else 0
  let boundary := height % params.period = 0
  { nextHeight := height
    state := if boundary then progress.state.atPeriodEnd params height (medianTimePast times) signals
      else progress.state
    periodSignals := if boundary then 0 else signals
    recentTimes := times }

/-- Consume headers oldest first, preserving the explicitly supplied starting summary. -/
def VersionBitsProgress.consume (params : VersionBitsParams) (progress : VersionBitsProgress)
    (headers : List BlockHeader) : VersionBitsProgress :=
  headers.foldl (advance params) progress

end BtcVerified.Consensus
