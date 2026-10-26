import Tests.SequenceLockFixtures
/-!
  # Contextual time-lock examples

  Distinct historical MTP values expose predecessor-height lookup, genesis
  clamping, and comparison against the candidate parent's MTP. These examples
  use synthetic history, not a proof that a chain produced those MTP values.
-/

namespace Tests.TimeLocks

open BtcVerified Tests.TransactionFixtures Tests.SequenceLockFixtures

set_option linter.hashCommand false

/-! ## The predecessor of the birth block supplies the time baseline -/

#guard (spend 2 0x00400001).body.isTimeLocksSatisfied coins timeContext
#guard !(spend 2 0x00400001).body.isTimeLocksSatisfied coins
  { timeContext with medianTimePast := 1511, blockTime := 1000000 }
#guard (spend 2 0x00400001).body.isTimeLocksSatisfied coins
  { timeContext with blockTime := 0 }
#guard !(spend 2 0x00400000).body.isTimeLocksSatisfied coins
  { timeContext with medianTimePast := 999 }
#guard (spend 2 0x00400000).body.isTimeLocksSatisfied coins
  { timeContext with medianTimePast := 1000 }

/-! ## Genesis uses its historical MTP rather than inventing time zero -/

private def genesisCoins : UtxoSet :=
  UtxoSet.create ∅ [(ordinaryInput.prevout, ⟨oneSatoshiOutput, ⟨0, false⟩⟩)]

#guard !(spend 2 0x00400001).body.isTimeLocksSatisfied genesisCoins
  { timeContext with medianTimePast := 911 }
#guard (spend 2 0x00400001).body.isTimeLocksSatisfied genesisCoins
  { timeContext with medianTimePast := 912 }

/-! ## Only explicit activation, low versions, and the disable bit bypass time -/

#guard (spend 2 0x0040ffff).body.isTimeLocksSatisfied coins
  { timeContext with sequenceLocksActive := false, medianTimePast := 0 }
#guard ([0, 1] : List UInt32).all fun version =>
  (spend version 0x00400001).body.isTimeLocksSatisfied coins
    { timeContext with medianTimePast := 1511 }
#guard ([2, 0x7fffffff, 0x80000000, 0xffffffff] : List UInt32).all fun version =>
  !(spend version 0x00400001).body.isTimeLocksSatisfied coins
    { timeContext with medianTimePast := 1511 }
#guard (spend 2 0x8040ffff).body.isTimeLocksSatisfied coins
  { timeContext with medianTimePast := 0 }

end Tests.TimeLocks
