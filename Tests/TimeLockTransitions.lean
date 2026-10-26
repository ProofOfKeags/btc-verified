import Tests.SequenceLockFixtures
/-!
  # Time locks in guarded transaction application

  Mixed inputs require both relative-lock axes independently. Single-input
  examples check the accepting and rejecting guarded state transitions while
  varying the clock selected for absolute locks.
-/

namespace Tests.TimeLockTransitions

open BtcVerified Tests.TransactionFixtures Tests.SequenceLockFixtures

set_option linter.hashCommand false

private def mixedSpend : Tx :=
  .legacy
    { (spend 2 5).body with
      inputs := ⟨[{ ordinaryInput with sequence := 5 },
        { laterInput with sequence := 0x00400001 }], by simp⟩ }
    (by simp)

private def mixedContext : TxContext :=
  { timeContext with
    medianTimePast := 2512
    medianTimePastAt := fun height => if height = 103 then 2000 else 9000 }

#guard mixedSpend.isAdmissible (fun _ _ _ => true) twoCoins .blockTime mixedContext
#guard !mixedSpend.isAdmissible (fun _ _ _ => true) twoCoins .blockTime
  { mixedContext with height := 104 }
#guard !mixedSpend.isAdmissible (fun _ _ _ => true) twoCoins .blockTime
  { mixedContext with medianTimePast := 2511 }

#guard ([.blockTime, .medianTimePast] : List LockTimeClock).all fun clock =>
  (spend 2 0x00400001).isAdmissible (fun _ _ _ => true) coins clock timeContext
#guard (coins.applyChecked (fun _ _ _ => true) .blockTime
  { timeContext with medianTimePast := 1511 } (spend 2 0x00400001)).isNone
#guard match coins.applyChecked (fun _ _ _ => true) .blockTime timeContext
    (spend 2 0x00400001) with
  | none => false
  | some next =>
    (next.lookup ordinaryInput.prevout).isNone
      && ((next.lookup ⟨(spend 2 0x00400001).txid, 0⟩).map (·.provenance))
        == some ⟨105, false⟩
      && next.totalValue == 1

end Tests.TimeLockTransitions
