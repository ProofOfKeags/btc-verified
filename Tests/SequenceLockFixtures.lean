import BtcVerified.Consensus.ApplyChecked
import Tests.TransactionFixtures
/-!
  # Sequence-lock transaction and chainstate fixtures

  Concrete heights, outpoints, and wire fields support contextual examples
  independently of the checkers. The script bytes remain opaque.
-/

namespace Tests.SequenceLockFixtures

open BtcVerified Tests.TransactionFixtures

/-- Admit transactions at height 105 with sequence-lock enforcement active. -/
def context : TxContext :=
  { height := 105, blockTime := 2000, medianTimePast := 1500
    sequenceLocksActive := true
    medianTimePastAt := fun _ => 0 }

/-- Spend the ordinary outpoint into one satoshi, using the given raw version
and sequence words and no absolute lock. -/
def spend (version sequence : UInt32) : Tx :=
  .legacy
    { version := version
      inputs := ⟨[{ ordinaryInput with sequence := sequence }], by simp⟩
      outputs := ⟨[oneSatoshiOutput], by decide⟩
      lockTime := 0 }
    (by simp)

/-- The ordinary outpoint holds ten satoshis created outside coinbase at height 100. -/
def coins : UtxoSet :=
  UtxoSet.create ∅
    [(ordinaryInput.prevout, ⟨{ oneSatoshiOutput with value := 10 }, ⟨100, false⟩⟩)]

/-- A distinct outpoint carries a two-block relative delay. -/
def laterInput : TxIn :=
  { ordinaryInput with prevout := { ordinaryInput.prevout with vout := 0 }
                       sequence := 2 }

/-- Add a one-satoshi non-coinbase coin born at height 104 to the height-100 coin. -/
def twoCoins : UtxoSet :=
  UtxoSet.create coins
    [(laterInput.prevout, ⟨oneSatoshiOutput, ⟨104, false⟩⟩)]

/-- Spend both outpoints with five- and two-block delays, optionally reversing
input order while retaining each input's own sequence. -/
def twoInputs (reverse : Bool) : TxBody :=
  let first := { ordinaryInput with sequence := 5 }
  { (spend 2 5).body with
    inputs := ⟨if reverse then [laterInput, first] else [first, laterInput],
      by split <;> decide⟩ }

/-- The height-99 MTP is 1000, genesis MTP is 400, and all other historical
heights deliberately differ; a one-unit lock on the height-100 coin expires at 1512. -/
def timeContext : TxContext :=
  { context with
    medianTimePast := 1512
    medianTimePastAt := fun height =>
      if height = 99 then 1000 else if height = 0 then 400 else 9000 }

end Tests.SequenceLockFixtures
