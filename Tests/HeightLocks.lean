import Tests.SequenceLockFixtures
/-!
  # Contextual height-lock examples

  Explicit activation and coin heights exercise the height-relative premise
  and its enforcement in guarded application. `TimeLocks` and
  `TimeLockTransitions` cover the time component separately. These finite
  examples do not establish Core correspondence.
-/

namespace Tests.HeightLocks

open BtcVerified Tests.TransactionFixtures Tests.SequenceLockFixtures

set_option linter.hashCommand false

/-! ## Activation is explicit; the raw version word is compared unsigned -/

#guard (spend 2 5).body.isHeightLocksSatisfied coins context
#guard !(spend 2 6).body.isHeightLocksSatisfied coins context
#guard (spend 2 6).body.isHeightLocksSatisfied coins
  { context with sequenceLocksActive := false }
#guard ([0, 1] : List UInt32).all fun version =>
  (spend version 6).body.isHeightLocksSatisfied coins context
#guard ([2, 0x7fffffff, 0x80000000, 0xffffffff] : List UInt32).all fun version =>
  !(spend version 6).body.isHeightLocksSatisfied coins context
#guard (spend 2 0x80000006).body.isHeightLocksSatisfied coins context

/-! ## Every input uses its own coin, independently of input order -/

#guard ![false, true].any fun reverse =>
  (twoInputs reverse).isHeightLocksSatisfied twoCoins context
#guard [false, true].all fun reverse =>
  (twoInputs reverse).isHeightLocksSatisfied twoCoins { context with height := 106 }

/-! ## Admission and application enforce the new guard and preserve other guards -/

#guard (spend 2 5).isAdmissible (fun _ _ _ => true) coins .blockTime context
#guard !(spend 2 6).isAdmissible (fun _ _ _ => true) coins .blockTime context
#guard !(spend 2 5).isAdmissible (fun _ _ _ => true) ∅ .blockTime context
#guard !(spend 2 5).isAdmissible (fun _ _ _ => false) coins .blockTime context
#guard (coins.applyChecked (fun _ _ _ => true) .blockTime context (spend 2 6)).isNone
#guard match coins.applyChecked (fun _ _ _ => true) .blockTime context (spend 2 5) with
  | none => false
  | some next =>
    (next.lookup ordinaryInput.prevout).isNone
      && ((next.lookup ⟨(spend 2 5).txid, 0⟩).map (·.provenance)) == some ⟨105, false⟩
      && next.totalValue == 1

end Tests.HeightLocks
