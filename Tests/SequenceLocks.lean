import BtcVerified.Consensus.SequenceLock
/-!
  # Relative sequence-lock interpretation examples

  Literal wire fields exercise interpretation and the height-relative comparison
  at its exact boundaries. Time-valued sequences impose no height constraint.
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

end Tests.SequenceLocks
