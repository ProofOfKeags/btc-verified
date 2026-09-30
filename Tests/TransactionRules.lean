import BtcVerified.Consensus.CoinbaseStateless
import Tests.TransactionFixtures
/-!
  # Transaction-local specification examples

  These examples check the intended meaning of named predicates on explicit
  transaction values. Each guard has one expected proposition, so a failure
  points to a particular rule rather than a parser or a combined Boolean.

  The fixtures fix concrete amounts, outpoints, and script lengths independent
  of the checked predicate. They are examples and counterexamples, not proofs
  over all transactions. No parser or kernel implementation is called here;
  the stripped-size predicate still measures the specification's encoding.
  Checker refinement and wire compatibility have separate tests.
  Script execution, contextual validity, and the million-byte stripped-size
  boundary are not established by these small transaction-local examples.
-/

namespace Tests.TransactionRules

open BtcVerified Tests.TransactionFixtures

set_option linter.hashCommand false

/-! ## Ordinary premises: witness data does not change the body-level examples

  Each form has one non-null input, one small output, and a tiny stripped body.
  Check every named premise separately for both serialization forms.
-/

#guard decide legacyExample.InputsNonempty
#guard decide legacyExample.OutputsNonempty
#guard decide legacyExample.AllInputOutpointsDistinct
#guard decide legacyExample.AllInputOutpointsNeNull
#guard decide legacyExample.TotalOutputValueLeMaxMoney
#guard decide legacyExample.StrippedSizeLeMaxStrippedTransactionSize

#guard decide segwitExample.InputsNonempty
#guard decide segwitExample.OutputsNonempty
#guard decide segwitExample.AllInputOutpointsDistinct
#guard decide segwitExample.AllInputOutpointsNeNull
#guard decide segwitExample.TotalOutputValueLeMaxMoney
#guard decide segwitExample.StrippedSizeLeMaxStrippedTransactionSize

/-! ## The empty object lacks both lists and cannot be coinbase

  A universal script-length property could hold vacuously on an empty list.
  Coinbase well-formedness must also require the single-null-input shape.
-/

#guard !decide emptyTx.InputsNonempty
#guard !decide emptyTx.OutputsNonempty
#guard !decide emptyTx.Coinbase
#guard !decide emptyTx.CoinbaseWellFormed

/-! ## Coinbase classification is independent of its script's length

  Every fixture below has exactly one null prevout. The inclusive 2–100-byte
  scriptSig bounds belong to well-formedness, not to that classification.
-/

-- Empty script: classified coinbase, but below the minimum.
#guard decide (coinbaseTx 0).Coinbase
#guard !decide (coinbaseTx 0).CoinbaseWellFormed
-- Immediately below the minimum.
#guard decide (coinbaseTx 1).Coinbase
#guard !decide (coinbaseTx 1).CoinbaseWellFormed
-- Both endpoints are included.
#guard decide (coinbaseTx 2).Coinbase
#guard decide (coinbaseTx 2).CoinbaseWellFormed
#guard decide (coinbaseTx 100).Coinbase
#guard decide (coinbaseTx 100).CoinbaseWellFormed
-- Immediately above the maximum.
#guard decide (coinbaseTx 101).Coinbase
#guard !decide (coinbaseTx 101).CoinbaseWellFormed

/-! ## Exactly one null input, not merely any null input

  A non-null singleton and a pair of null inputs must both fail coinbase shape.
  The valid singleton with a two-byte script is the positive control above.
-/

private def ordinarySingleton : Tx := legacyTx [ordinaryInput] [ordinaryOutput]
private def twoNullInputs : Tx :=
  legacyTx [coinbaseInput 2, coinbaseInput 2] [ordinaryOutput]

#guard !decide ordinarySingleton.Coinbase
#guard !decide ordinarySingleton.CoinbaseWellFormed
#guard !decide twoNullInputs.Coinbase
#guard !decide twoNullInputs.CoinbaseWellFormed

/-! ## Distinctness compares outpoints, not complete input records -/

-- Replacing the high sequence byte 05 by 00 gives 0x00060708. These inputs
-- differ as records but still spend exactly the same previous output.
private def repeatedOutpoint : Tx :=
  legacyTx [ordinaryInput, { ordinaryInput with sequence := 0x00060708 }]
    [ordinaryOutput]

#guard !decide repeatedOutpoint.AllInputOutpointsDistinct
-- Null is permitted by coinbase shape, but prohibited by the ordinary rule.
#guard !decide (coinbaseTx 2).AllInputOutpointsNeNull

/-! ## The money bound includes equality and applies to the total

  A second individually small output must not evade an aggregate bound.
-/

private def atMaxMoney : Tx := legacyTx [ordinaryInput] [maxMoneyOutput]
private def aboveMaxMoney : Tx :=
  legacyTx [ordinaryInput] [maxMoneyOutput, oneSatoshiOutput]

#guard decide atMaxMoney.TotalOutputValueLeMaxMoney
#guard !decide aboveMaxMoney.TotalOutputValueLeMaxMoney

/-! ## Bad outputs do not change coinbase classification

  Both transactions keep the passing two-byte script. Removing the outputs or
  exceeding maxMoney must reject well-formedness without changing their shape.
-/

private def coinbaseWithoutOutputs : Tx := legacyTx [coinbaseInput 2] []
private def coinbaseAboveMaxMoney : Tx :=
  legacyTx [coinbaseInput 2] [maxMoneyOutput, oneSatoshiOutput]

#guard decide coinbaseWithoutOutputs.Coinbase
#guard !decide coinbaseWithoutOutputs.CoinbaseWellFormed
#guard decide coinbaseAboveMaxMoney.Coinbase
#guard !decide coinbaseAboveMaxMoney.CoinbaseWellFormed

end Tests.TransactionRules
