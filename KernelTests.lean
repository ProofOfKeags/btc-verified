import Kernel.Transaction
import Tests.AxiomAudit
import Tests.GoldenVectors
/-!
  # Lean transaction kernel tests

  Fixed wire fixtures exercise the boundary; axiom audits cover its transport
  proofs. These checks neither execute Core nor establish native ABI conformance.
-/

namespace KernelTests

open BtcVerified Tests.GoldenVectors

set_option linter.hashCommand false

#assert_axioms Kernel.nonCoinbaseCheck_eq_isWellFormed
#assert_axioms Kernel.coinbaseCheck_iff
#assert_axioms Kernel.witnesses_size_eq_inputs_size
#assert_axioms Kernel.encodeStripped_toList
#assert_axioms Kernel.txid_eq_txid

private def fixtureChecks (hex : String) (accepted : Bool) : Bool :=
  match hexBytes? hex with
  | none => false
  | some bytes =>
    [bytes, bytes ++ [0xde, 0xad]].all fun input =>
      match Kernel.decode input.toByteArray with
      | none => false
      | some tx => Kernel.encode tx == bytes.toByteArray && Kernel.check tx == accepted

-- Real legacy, SegWit, and coinbase fixtures; trailing bytes are left unread.
#guard fixtureChecks firstBitcoinPaymentHex true
#guard fixtureChecks firstSegwitSpendHex true
#guard fixtureChecks segwitCoinbaseHex true
#guard fixtureChecks coreEmptyTxHex false
#guard match hexBytes? superfluousWitnessHex with
  | some bytes => (Kernel.decode bytes.toByteArray).isNone
  | none => false

private def previousHash : List UInt8 := (List.range 32).map UInt8.ofNat
private def inputBytes : List UInt8 :=
  previousHash ++ [4, 3, 2, 1, 2, 0x51, 0xab, 8, 7, 6, 5]
private def outputBytes : List UInt8 := [6, 5, 4, 3, 2, 1, 0, 0, 3, 0, 0x6a, 0xff]
private def lockTimeBytes : List UInt8 := [12, 11, 10, 9]
private def legacyBytes : List UInt8 :=
  [1, 0, 0, 0, 1] ++ inputBytes ++ [1] ++ outputBytes ++ lockTimeBytes
private def witnessedBytes : List UInt8 :=
  [1, 0, 0, 0, 0, 1, 1] ++ inputBytes ++ [1] ++ outputBytes
    ++ [2, 0, 3, 0xaa, 0xbb, 0xcc] ++ lockTimeBytes

-- Nonzero fields distinguish byte order; an empty item is not an empty stack.
#guard [legacyBytes, witnessedBytes].all fun bytes =>
  match Kernel.decode bytes.toByteArray with
  | none => false
  | some tx =>
    match (Kernel.inputs tx).toList, (Kernel.outputs tx).toList with
    | [input], [output] =>
        Kernel.locktime tx == 0x090a0b0c
          && Kernel.inputTxid input == previousHash.toByteArray
          && Kernel.inputIndex input == 0x01020304
          && Kernel.inputSequence input == 0x05060708
          && Kernel.inputScript input == ([0x51, 0xab] : List UInt8).toByteArray
          && Kernel.outputAmount output == 0x010203040506
          && Kernel.outputScript output == ([0, 0x6a, 0xff] : List UInt8).toByteArray
          && Kernel.encodeStripped tx == legacyBytes.toByteArray
          && Kernel.txid tx == tx.txid.val.toByteArray
          && decide tx.InputsNonempty
          && decide tx.OutputsNonempty
          && decide tx.AllInputOutpointsDistinct
          && decide tx.AllInputOutpointsNeNull
          && decide tx.TotalOutputValueLeMaxMoney
          && decide tx.StrippedSizeLeMaxStrippedTransactionSize
    | _, _ => false

#guard match Kernel.decode legacyBytes.toByteArray with
  | some tx => Kernel.witnesses tx == #[#[]]
  | none => false
#guard match Kernel.decode witnessedBytes.toByteArray with
  | some tx => Kernel.witnesses tx ==
      #[#[ByteArray.empty, ([0xaa, 0xbb, 0xcc] : List UInt8).toByteArray]]
  | none => false
#guard match hexBytes? coreEmptyTxHex >>= (Kernel.decode ·.toByteArray) with
  | some tx => (Kernel.inputs tx).isEmpty && (Kernel.outputs tx).isEmpty
      && (Kernel.witnesses tx).isEmpty && Kernel.locktime tx == 0
      && !decide tx.InputsNonempty && !decide tx.OutputsNonempty
  | none => false

-- Truncation, unknown witness flags, and a noncanonical CompactSize input count.
#guard [[], [1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2], legacyBytes.dropLast,
    [1, 0, 0, 0, 0, 3] ++ witnessedBytes.drop 6,
    [1, 0, 0, 0, 0xfd, 1, 0] ++ inputBytes ++ [1] ++ outputBytes ++ lockTimeBytes].all
  fun bytes => (Kernel.decode bytes.toByteArray).isNone

-- Small fixtures use literal one-byte counts, independently of our encoder.
private def smallTransaction (inputs outputs : List (List UInt8)) : ByteArray :=
  ([1, 0, 0, 0, UInt8.ofNat inputs.length] ++ inputs.flatten
    ++ [UInt8.ofNat outputs.length] ++ outputs.flatten ++ [0, 0, 0, 0]).toByteArray
private def coinbaseInput (scriptLength : Nat) : List UInt8 :=
  List.replicate 32 0 ++ [0xff, 0xff, 0xff, 0xff, UInt8.ofNat scriptLength]
    ++ List.replicate scriptLength 0 ++ [0xff, 0xff, 0xff, 0xff]
private def hasCheckResult (bytes : ByteArray) (expected : Bool) : Bool :=
  match Kernel.decode bytes with
  | some tx => Kernel.check tx == expected
  | none => false

#guard [0, 1, 2, 100, 101].all fun n =>
  match Kernel.decode (smallTransaction [coinbaseInput n] [outputBytes]) with
  | some tx =>
      let expected := 2 ≤ n && n ≤ 100
      decide tx.Coinbase && decide tx.CoinbaseWellFormed == expected
        && Kernel.check tx == expected
  | none => false
#guard hasCheckResult (smallTransaction [coinbaseInput 2] []) false
#guard hasCheckResult (smallTransaction [inputBytes] []) false
#guard hasCheckResult (smallTransaction [inputBytes, inputBytes] [outputBytes]) false
#guard hasCheckResult (smallTransaction [inputBytes, coinbaseInput 2] [outputBytes]) false

-- The extracted checker rejects non-coinbase shapes when called directly.
#guard [([coinbaseInput 2], true), ([inputBytes], false),
    ([coinbaseInput 2, coinbaseInput 2], false)].all fun (inputs, expected) =>
  match Kernel.decode (smallTransaction inputs [outputBytes]) with
  | some tx => decide tx.Coinbase == expected
      && decide tx.CoinbaseWellFormed == expected && Kernel.coinbaseCheck tx == expected
  | none => false

-- Exercise named predicates independently of the combined checker.
private def predicateResult (predicate : Tx → Prop) [DecidablePred predicate]
    (bytes : ByteArray) (expected : Bool) : Bool :=
  match Kernel.decode bytes with
  | some tx => decide (predicate tx) == expected
  | none => false

#guard predicateResult Tx.AllInputOutpointsDistinct
  (smallTransaction [inputBytes, inputBytes.dropLast ++ [0]] [outputBytes]) false
#guard predicateResult Tx.AllInputOutpointsNeNull
  (smallTransaction [coinbaseInput 2] [outputBytes]) false
private def maxMoneyBytes : List UInt8 := [0, 0x40, 7, 0x5a, 0xf0, 0x75, 7, 0]

-- Bad outputs do not change coinbase classification, but fail well-formedness.
#guard [[], [maxMoneyBytes ++ [0], [1, 0, 0, 0, 0, 0, 0, 0, 0]]].all fun outputs =>
  match Kernel.decode (smallTransaction [coinbaseInput 2] outputs) with
  | some tx => decide tx.Coinbase && !decide tx.CoinbaseWellFormed && !Kernel.coinbaseCheck tx
  | none => false
#guard predicateResult Tx.Coinbase (smallTransaction [] []) false
#guard predicateResult Tx.CoinbaseWellFormed (smallTransaction [] []) false

#guard predicateResult Tx.TotalOutputValueLeMaxMoney
  (smallTransaction [inputBytes] [maxMoneyBytes ++ [0]]) true
#guard predicateResult Tx.TotalOutputValueLeMaxMoney
  (smallTransaction [inputBytes] [maxMoneyBytes ++ [0], [1, 0, 0, 0, 0, 0, 0, 0, 0]]) false

-- Signed-negative wire amounts retain their bits and fail the natural-value bound.
#guard match Kernel.decode
    (smallTransaction [inputBytes] [List.replicate 8 0xff ++ [0]]) with
  | some tx => !Kernel.check tx &&
      (Kernel.outputs tx).toList.map Kernel.outputAmount == [0xffffffffffffffff]
  | none => false

end KernelTests
