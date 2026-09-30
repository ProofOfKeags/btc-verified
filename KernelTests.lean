import Kernel.Transaction
import KernelTests.AxiomAudit
import Tests.GoldenVectors
import Tests.TransactionFixtures
/-!
  # Lean kernel boundary regressions

  These examples exercise the adapter: prefix decoding, byte preservation,
  field/witness snapshots, and checker dispatch. Raw fixtures are independent
  of our encoder; their layouts and expected results are documented below.
  Each guard checks one observable result, including successful decoding
  wherever an observation is expected.

  Specification examples on transaction values live in `Tests.TransactionRules`.
  Universal refinement claims are audited separately in `KernelTests.AxiomAudit`.
  Neither those proofs nor these examples establish Core equivalence, native
  ABI conformance, script validity, or block validity. The million-byte
  stripped-size and Core container-length boundaries are not exercised here.
-/

namespace KernelTests

open BtcVerified Tests.GoldenVectors Tests.TransactionFixtures

set_option linter.hashCommand false

/-! ## Prefix decoding and byte preservation

  Re-encoding must reproduce the transaction bytes, excluding any suffix.
  Checker observations are separate: parse success is not rule acceptance.
  The mainnet fixtures and the empty encoding are documented in GoldenVectors.
-/

private def decodeHex (hex : String) (suffix : List UInt8 := []) : Option Tx :=
  (hexBytes? hex).bind fun bytes => Kernel.decode (bytes ++ suffix).toByteArray

private def roundtrips (hex : String) (suffix : List UInt8 := []) : Bool :=
  match hexBytes? hex with
  | some bytes => (decodeHex hex suffix).map Kernel.encode == some bytes.toByteArray
  | none => false

-- Legacy spend.
#guard roundtrips firstBitcoinPaymentHex
#guard roundtrips firstBitcoinPaymentHex [0xde, 0xad]
#guard (decodeHex firstBitcoinPaymentHex).map Kernel.check == some true
#guard (decodeHex firstBitcoinPaymentHex [0xde, 0xad]).map Kernel.check == some true

-- SegWit spend.
#guard roundtrips firstSegwitSpendHex
#guard roundtrips firstSegwitSpendHex [0xde, 0xad]
#guard (decodeHex firstSegwitSpendHex).map Kernel.check == some true
#guard (decodeHex firstSegwitSpendHex [0xde, 0xad]).map Kernel.check == some true

-- SegWit coinbase.
#guard roundtrips segwitCoinbaseHex
#guard roundtrips segwitCoinbaseHex [0xde, 0xad]
#guard (decodeHex segwitCoinbaseHex).map Kernel.check == some true
#guard (decodeHex segwitCoinbaseHex [0xde, 0xad]).map Kernel.check == some true

-- The empty object parses but fails transaction-local checks.
#guard roundtrips coreEmptyTxHex
#guard roundtrips coreEmptyTxHex [0xde, 0xad]
#guard (decodeHex coreEmptyTxHex).map Kernel.check == some false
#guard (decodeHex coreEmptyTxHex [0xde, 0xad]).map Kernel.check == some false

/-! ## Literal wire layout

  Recognizable fields distinguish byte order and field boundaries. These bytes
  are written independently of the structured fixtures used by the rule tests.
  Script contents remain opaque; no claim about script execution is made.
-/

-- Recognizable raw txid bytes: 00 01 ... 1f, not display-order hexadecimal.
private def previousHash : List UInt8 := (List.range 32).map UInt8.ofNat
private def inputBytes : List UInt8 :=
  previousHash ++ [4, 3, 2, 1]  -- vout = 0x01020304, little-endian
    ++ [2, 0x51, 0xab]         -- scriptSig: length 2, then two opaque bytes
    ++ [8, 7, 6, 5]            -- sequence = 0x05060708, little-endian
private def outputBytes : List UInt8 :=
  [6, 5, 4, 3, 2, 1, 0, 0]    -- value = 0x010203040506, below maxMoney
    ++ [3, 0, 0x6a, 0xff]      -- scriptPubKey: length 3, then three opaque bytes
-- lockTime = 0x090a0b0c, little-endian.
private def lockTimeBytes : List UInt8 := [12, 11, 10, 9]
private def legacyBytes : List UInt8 :=
  -- Version 1, one input, one output, then lockTime.
  [1, 0, 0, 0, 1] ++ inputBytes ++ [1] ++ outputBytes ++ lockTimeBytes
private def witnessedBytes : List UInt8 :=
  -- Same body, with marker/flag 00 01 and one witness stack before lockTime.
  [1, 0, 0, 0, 0, 1, 1] ++ inputBytes ++ [1] ++ outputBytes
    -- Two witness items: an empty byte string, then aa bb cc.
    ++ [2, 0, 3, 0xaa, 0xbb, 0xcc] ++ lockTimeBytes

/-! ## Malformed encodings

  These must fail parsing, unlike the successfully decoded but rejected empty
  transaction above. Malformed syntax cannot be represented by a typed `Tx`.
-/

-- Witness marker/flag with no nonempty witness stack.
#guard match hexBytes? superfluousWitnessHex with
  | some bytes => (Kernel.decode bytes.toByteArray).isNone
  | none => false

-- No version; version plus marker but no flag; short unsupported-flag header.
#guard (Kernel.decode ByteArray.empty).isNone
#guard (Kernel.decode ([1, 0, 0, 0, 0] : List UInt8).toByteArray).isNone
#guard (Kernel.decode ([1, 0, 0, 0, 0, 2] : List UInt8).toByteArray).isNone
-- Removing the last byte leaves an incomplete four-byte lockTime.
#guard (Kernel.decode legacyBytes.dropLast.toByteArray).isNone
-- Replace only flag 01 with 03 in an otherwise complete witnessed fixture:
-- bit 02 is unknown, so accepting the recognized witness bit is not enough.
#guard (Kernel.decode
  (([1, 0, 0, 0, 0, 3] : List UInt8) ++ witnessedBytes.drop 6).toByteArray).isNone
-- fd 01 00 represents count 1 noncanonically; the canonical count is just 01.
#guard (Kernel.decode
  (([1, 0, 0, 0, 0xfd, 1, 0] : List UInt8) ++ inputBytes
    ++ [1] ++ outputBytes ++ lockTimeBytes).toByteArray).isNone

/-! ## Field and witness snapshots

  Both encodings carry the body annotated above. Each array expectation also
  checks that exactly one input or output is returned, in addition to its value.
-/

private def decodedLegacy : Option Tx := Kernel.decode legacyBytes.toByteArray
private def decodedWitnessed : Option Tx := Kernel.decode witnessedBytes.toByteArray

#guard decodedLegacy.map Kernel.locktime == some 0x090a0b0c
#guard decodedWitnessed.map Kernel.locktime == some 0x090a0b0c

#guard decodedLegacy.map (fun tx => (Kernel.inputs tx).map Kernel.inputTxid) ==
  some #[previousHash.toByteArray]
#guard decodedWitnessed.map (fun tx => (Kernel.inputs tx).map Kernel.inputTxid) ==
  some #[previousHash.toByteArray]

#guard decodedLegacy.map (fun tx => (Kernel.inputs tx).map Kernel.inputIndex) ==
  some #[0x01020304]
#guard decodedWitnessed.map (fun tx => (Kernel.inputs tx).map Kernel.inputIndex) ==
  some #[0x01020304]

#guard decodedLegacy.map (fun tx => (Kernel.inputs tx).map Kernel.inputSequence) ==
  some #[0x05060708]
#guard decodedWitnessed.map (fun tx => (Kernel.inputs tx).map Kernel.inputSequence) ==
  some #[0x05060708]

#guard decodedLegacy.map (fun tx => (Kernel.inputs tx).map Kernel.inputScript) ==
  some #[([0x51, 0xab] : List UInt8).toByteArray]
#guard decodedWitnessed.map (fun tx => (Kernel.inputs tx).map Kernel.inputScript) ==
  some #[([0x51, 0xab] : List UInt8).toByteArray]

#guard decodedLegacy.map (fun tx => (Kernel.outputs tx).map Kernel.outputAmount) ==
  some #[0x010203040506]
#guard decodedWitnessed.map (fun tx => (Kernel.outputs tx).map Kernel.outputAmount) ==
  some #[0x010203040506]

#guard decodedLegacy.map (fun tx => (Kernel.outputs tx).map Kernel.outputScript) ==
  some #[([0, 0x6a, 0xff] : List UInt8).toByteArray]
#guard decodedWitnessed.map (fun tx => (Kernel.outputs tx).map Kernel.outputScript) ==
  some #[([0, 0x6a, 0xff] : List UInt8).toByteArray]

-- Stripping removes witness data but retains the complete body.
#guard decodedLegacy.map Kernel.encodeStripped == some legacyBytes.toByteArray
#guard decodedWitnessed.map Kernel.encodeStripped == some legacyBytes.toByteArray

-- These retain the previous concrete refinement checks, not an independent
-- hash oracle: both the adapter and specification share SHA-256.
#guard decodedLegacy.map (fun tx => Kernel.txid tx == tx.txid.val.toByteArray) == some true
#guard decodedWitnessed.map (fun tx => Kernel.txid tx == tx.txid.val.toByteArray) == some true

-- A legacy input has an empty stack; an empty ITEM within a SegWit stack stays.
#guard decodedLegacy.map Kernel.witnesses == some #[#[]]
#guard decodedWitnessed.map Kernel.witnesses ==
  some #[#[ByteArray.empty, ([0xaa, 0xbb, 0xcc] : List UInt8).toByteArray]]

private def decodedEmpty : Option Tx := decodeHex coreEmptyTxHex

#guard decodedEmpty.map Kernel.inputs == some #[]
#guard decodedEmpty.map Kernel.outputs == some #[]
#guard decodedEmpty.map Kernel.witnesses == some #[]
#guard decodedEmpty.map Kernel.locktime == some 0

/-! ## Wire amount bits versus checker verdict

  All-one bits represent -1 as signed 64-bit data. Lean's UInt64 accessor must
  preserve those bits, while checking rejects the resulting out-of-range value.
  This intentionally spans parsing and checking; an unexpected parse failure
  cannot satisfy either `some` expectation.
-/

private def negativeAmountBytes : ByteArray :=
  -- Version 1, one ordinary input, one output with eight ff amount bytes and
  -- an empty scriptPubKey, then lockTime 0.
  ([1, 0, 0, 0, 1] ++ inputBytes ++ [1]
    ++ List.replicate 8 0xff ++ [0] ++ [0, 0, 0, 0]).toByteArray

#guard (Kernel.decode negativeAmountBytes).map
  (fun tx => (Kernel.outputs tx).map Kernel.outputAmount) == some #[0xffffffffffffffff]
#guard (Kernel.decode negativeAmountBytes).map Kernel.check == some false

/-! ## Checker entry points

  These are calls on already constructed transactions, not parser tests.
  The predicates' examples are in Tests.TransactionRules; here literal expected
  verdicts retain the dispatch and direct-checker observations from this suite.
-/

-- Coinbase dispatch at each scriptSig boundary.
#guard Kernel.check (coinbaseTx 0) == false
#guard Kernel.check (coinbaseTx 1) == false
#guard Kernel.check (coinbaseTx 2) == true
#guard Kernel.check (coinbaseTx 100) == true
#guard Kernel.check (coinbaseTx 101) == false

-- Missing outputs on either branch; duplicate and mixed-null non-coinbase inputs.
#guard Kernel.check (legacyTx [coinbaseInput 2] []) == false
#guard Kernel.check (legacyTx [ordinaryInput] []) == false
#guard Kernel.check (legacyTx [ordinaryInput, ordinaryInput] [ordinaryOutput]) == false
#guard Kernel.check (legacyTx [ordinaryInput, coinbaseInput 2] [ordinaryOutput]) == false

-- Calling the coinbase checker directly must still enforce its input shape.
#guard Kernel.coinbaseCheck (coinbaseTx 2) == true
#guard Kernel.coinbaseCheck (legacyTx [ordinaryInput] [ordinaryOutput]) == false
#guard Kernel.coinbaseCheck
  (legacyTx [coinbaseInput 2, coinbaseInput 2] [ordinaryOutput]) == false

-- Coinbase shape alone does not excuse missing outputs or an excessive total.
#guard Kernel.coinbaseCheck (legacyTx [coinbaseInput 2] []) == false
#guard Kernel.coinbaseCheck
  (legacyTx [coinbaseInput 2] [maxMoneyOutput, oneSatoshiOutput]) == false

end KernelTests
