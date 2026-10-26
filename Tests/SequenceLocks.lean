import BtcVerified.Consensus.SequenceLock
/-!
  # Relative sequence-lock interpretation examples

  Literal wire fields exercise interpretation and both relative-lock comparisons
  at their exact boundaries. Each axis ignores locks measured on the other axis.
  These finite examples do not establish Core correspondence.
-/

namespace Tests.SequenceLocks

open BtcVerified.Consensus

/-! ## Interpretation: disable takes priority, and only masked delay bits count -/

#guard SequenceLock.ofUInt32 0 == .blocks 0
#guard SequenceLock.ofUInt32 0xffff == .blocks 65535
#guard SequenceLock.ofUInt32 0x00010005 == .blocks 5
#guard SequenceLock.ofUInt32 0x00400000 == .seconds 0
#guard SequenceLock.ofUInt32 0x00400001 == .seconds 512
#guard SequenceLock.ofUInt32 0x0040ffff == .seconds 33553920
#guard SequenceLock.ofUInt32 0x80000000 == .disabled
#guard SequenceLock.ofUInt32 0xffffffff == .disabled

/-! ## First-valid heights include equality, including zero at genesis -/

#guard !(SequenceLock.blocks 5).isHeightSatisfied 100 104
#guard (SequenceLock.blocks 5).isHeightSatisfied 100 105
#guard !(SequenceLock.blocks 0).isHeightSatisfied 100 99
#guard (SequenceLock.blocks 0).isHeightSatisfied 100 100
#guard (SequenceLock.blocks 0).isHeightSatisfied 0 0
#guard !(SequenceLock.blocks 65535).isHeightSatisfied 100 65634
#guard (SequenceLock.blocks 65535).isHeightSatisfied 100 65635
#guard SequenceLock.disabled.isHeightSatisfied 100 0
#guard (SequenceLock.ofUInt32 0x0040ffff).isHeightSatisfied 100 0

/-! ## First-valid times include equality and use the full seconds delay -/

#guard !(SequenceLock.seconds 512).isTimeSatisfied 1000 1511
#guard (SequenceLock.seconds 512).isTimeSatisfied 1000 1512
#guard !(SequenceLock.seconds 0).isTimeSatisfied 1000 999
#guard (SequenceLock.seconds 0).isTimeSatisfied 1000 1000
#guard (SequenceLock.seconds 0).isTimeSatisfied 0 0
#guard !(SequenceLock.seconds 33553920).isTimeSatisfied 1000 33554919
#guard (SequenceLock.seconds 33553920).isTimeSatisfied 1000 33554920
#guard SequenceLock.disabled.isTimeSatisfied 1000 0
#guard (SequenceLock.blocks 65535).isTimeSatisfied 1000 0

end Tests.SequenceLocks
