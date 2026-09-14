import Fuzz.Transaction
import Tests.AxiomAudit
import Tests.GoldenVectors
/-!
  # Native transaction-codec boundary tests

  These tests check the adapter's status tagging and prefix semantics on
  fixed byte strings. They include both published transaction vectors
  already used by the repository, malformed inputs, and the degenerate
  empty-input/empty-output transaction form. They are executable checks,
  not an equivalence proof against an external implementation.
-/

namespace FuzzTests

open BtcVerified.Fuzz Tests.GoldenVectors

set_option linter.hashCommand false

private def rejected : ByteArray := ByteArray.empty.push 0

private def succeedsWith (input expected : List UInt8) : Bool :=
  transactionRoundtrip input.toByteArray == (1 :: expected).toByteArray

private def vectorChecksOut (hex : String) : Bool :=
  match hexBytes? hex with
  | none => false
  | some bytes =>
    succeedsWith bytes bytes && succeedsWith (bytes ++ [0xde, 0xad]) bytes

-- Missing version and truncated marker/flag paths must reject.
#guard transactionRoundtrip ByteArray.empty == rejected
#guard transactionRoundtrip ([1, 0, 0, 0, 0] : List UInt8).toByteArray == rejected
#guard transactionRoundtrip ([1, 0, 0, 0, 0, 2] : List UInt8).toByteArray == rejected

-- This is syntactically decodable, even though consensus rejects the transaction.
#guard succeedsWith [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard succeedsWith [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255]
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

#guard vectorChecksOut firstBitcoinPaymentHex
#guard vectorChecksOut segwitCoinbaseHex

/-! ## The independent field transcript -/

-- Small fixed lengths are written literally here, independently of the
-- observation's bit-shift writer and the transaction's CompactSize codec.
private def smallLength (value : UInt8) : List UInt8 := [value, 0, 0, 0, 0, 0, 0, 0]

private def previousHash : List UInt8 := (List.range 32).map UInt8.ofNat
private def indexBytes : List UInt8 := [4, 3, 2, 1]
private def sequenceBytes : List UInt8 := [8, 7, 6, 5]
private def lockTimeBytes : List UInt8 := [12, 11, 10, 9]
private def amountBytes : List UInt8 := [6, 5, 4, 3, 2, 1, 0, 0]
private def inputBytes : List UInt8 :=
  previousHash ++ indexBytes ++ [2, 0x51, 0xab] ++ sequenceBytes
private def outputBytes : List UInt8 := amountBytes ++ [3, 0x00, 0x6a, 0xff]
private def legacyBytes : List UInt8 :=
  [4, 3, 2, 1, 1] ++ inputBytes ++ [1] ++ outputBytes ++ lockTimeBytes
private def witnessedBytes : List UInt8 :=
  [4, 3, 2, 1, 0, 1, 1] ++ inputBytes ++ [1] ++ outputBytes
    ++ [2, 0, 3, 0xaa, 0xbb, 0xcc] ++ lockTimeBytes

private def fieldPrefix : List UInt8 :=
  smallLength 1 ++ smallLength 1 ++ lockTimeBytes
    ++ previousHash ++ indexBytes ++ sequenceBytes
    ++ smallLength 2 ++ [0x51, 0xab]
private def outputFields : List UInt8 :=
  amountBytes ++ smallLength 3 ++ [0x00, 0x6a, 0xff]
private def legacyObservation : List UInt8 :=
  [1, 1] ++ smallLength 65 ++ legacyBytes ++ fieldPrefix
    ++ smallLength 0 ++ outputFields
private def witnessedObservation : List UInt8 :=
  [1, 1] ++ smallLength 73 ++ witnessedBytes ++ fieldPrefix
    ++ smallLength 2 ++ smallLength 0 ++ smallLength 3 ++ [0xaa, 0xbb, 0xcc]
    ++ outputFields

-- These full expected transcripts check field order, integer byte order,
-- witness regrouping, empty witness items, byte-region lengths, and suffixes.
#guard legacyBytes.length == 65
#guard witnessedBytes.length == 73
#guard transactionObserve legacyBytes.toByteArray == legacyObservation.toByteArray
#guard transactionObserve witnessedBytes.toByteArray == witnessedObservation.toByteArray
#guard transactionObserve (legacyBytes ++ [0xde, 0xad]).toByteArray
  == legacyObservation.toByteArray
#guard transactionObserve (witnessedBytes ++ [0xde, 0xad]).toByteArray
  == witnessedObservation.toByteArray
#guard transactionObserve ByteArray.empty == rejected
#guard transactionObserve (legacyBytes.dropLast.toByteArray) == rejected
#guard transactionObserve ([1, 0, 0, 0, 0, 2] : List UInt8).toByteArray == rejected
#guard match hexBytes? superfluousWitnessHex with
  | some bytes => transactionObserve bytes.toByteArray == rejected
  | none => false

-- The degenerate empty transaction parses, fails the check, and has no fields
-- beyond the two zero counts and locktime.
private def emptyBytes : List UInt8 := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#guard transactionObserve emptyBytes.toByteArray ==
  ([1, 0] ++ smallLength 10 ++ emptyBytes ++ smallLength 0 ++ smallLength 0
    ++ [0, 0, 0, 0]).toByteArray

/-! ## Context-free acceptance, separate from parsing -/

private def hasCheckResult (bytes : List UInt8) (expected : Bool) : Bool :=
  (transactionObserve bytes.toByteArray).toList.take 2 == [1, if expected then 1 else 0]

-- The fixtures below contain fewer than 253 inputs, outputs, or script bytes,
-- so their one-byte CompactSize prefixes are literal wire-format values.
private def smallTransaction (inputs outputs : List (List UInt8)) : List UInt8 :=
  [1, 0, 0, 0, UInt8.ofNat inputs.length] ++ inputs.flatten
    ++ [UInt8.ofNat outputs.length] ++ outputs.flatten ++ [0, 0, 0, 0]
private def regularInput : List UInt8 :=
  List.replicate 32 1 ++ [0, 0, 0, 0, 0, 0xff, 0xff, 0xff, 0xff]
private def coinbaseInput (scriptLength : Nat) : List UInt8 :=
  List.replicate 32 0 ++ [0xff, 0xff, 0xff, 0xff, UInt8.ofNat scriptLength]
    ++ List.replicate scriptLength 0 ++ [0xff, 0xff, 0xff, 0xff]
private def amountOutput (amount : List UInt8) : List UInt8 := amount ++ [0]
private def zeroOutput : List UInt8 := amountOutput (smallLength 0)
private def maximumMoney : List UInt8 := [0x00, 0x40, 0x07, 0x5a, 0xf0, 0x75, 0x07, 0x00]

#guard hasCheckResult (smallTransaction [regularInput] [zeroOutput]) true
#guard hasCheckResult (smallTransaction [regularInput] []) false
#guard hasCheckResult (smallTransaction [regularInput, regularInput] [zeroOutput]) false
#guard hasCheckResult (smallTransaction [regularInput, coinbaseInput 2] [zeroOutput]) false
#guard hasCheckResult (smallTransaction [coinbaseInput 2, coinbaseInput 2] [zeroOutput]) false
-- Both components must match the null outpoint; either component alone is legal.
#guard hasCheckResult (smallTransaction
  [List.replicate 32 0 ++ [0, 0, 0, 0, 0, 0xff, 0xff, 0xff, 0xff]]
  [zeroOutput]) true
#guard hasCheckResult (smallTransaction
  [List.replicate 32 1 ++ [0xff, 0xff, 0xff, 0xff, 0, 0xff, 0xff, 0xff, 0xff]]
  [zeroOutput]) true
-- Different output indexes are distinct spends even with the same txid.
#guard hasCheckResult (smallTransaction
  [regularInput, List.replicate 32 1 ++ [1, 0, 0, 0, 0, 0xff, 0xff, 0xff, 0xff]]
  [zeroOutput]) true

-- Coinbase shape is exactly one null prevout, with inclusive scriptSig bounds.
#guard hasCheckResult (smallTransaction [coinbaseInput 0] [zeroOutput]) false
#guard hasCheckResult (smallTransaction [coinbaseInput 1] [zeroOutput]) false
#guard hasCheckResult (smallTransaction [coinbaseInput 2] [zeroOutput]) true
#guard hasCheckResult (smallTransaction [coinbaseInput 100] [zeroOutput]) true
#guard hasCheckResult (smallTransaction [coinbaseInput 101] [zeroOutput]) false
#guard hasCheckResult (smallTransaction [coinbaseInput 2] []) false

-- An individual output or aggregate may equal maxMoney, but not exceed it.
#guard hasCheckResult (smallTransaction [regularInput] [amountOutput maximumMoney]) true
#guard hasCheckResult (smallTransaction [regularInput]
  [amountOutput maximumMoney, zeroOutput]) true
#guard hasCheckResult (smallTransaction [regularInput]
  [amountOutput maximumMoney, amountOutput (smallLength 1)]) false
#guard hasCheckResult (smallTransaction [regularInput]
  [amountOutput [0x01, 0x40, 0x07, 0x5a, 0xf0, 0x75, 0x07, 0x00]]) false

-- Keep signed-negative Core wire amounts in the domain: their UInt64 values
-- exceed maxMoney, and the transcript retains their exact 64-bit patterns.
#guard hasCheckResult (smallTransaction [regularInput]
  [amountOutput [0, 0, 0, 0, 0, 0, 0, 0x80]]) false
#guard hasCheckResult (smallTransaction [regularInput]
  [amountOutput (List.replicate 8 0xff)]) false
#guard hasCheckResult (smallTransaction [coinbaseInput 2]
  [amountOutput (List.replicate 8 0xff)]) false
#guard let observation := transactionObserve (smallTransaction [regularInput]
    [amountOutput [0, 0, 0, 0, 0, 0, 0, 0x80]]).toByteArray
  observation.toList.drop (observation.size - 16)
    == [0, 0, 0, 0, 0, 0, 0, 0x80] ++ smallLength 0

#guard match hexBytes? firstBitcoinPaymentHex with
  | some bytes => hasCheckResult bytes true
  | none => false
#guard match hexBytes? segwitCoinbaseHex with
  | some bytes => hasCheckResult bytes true
  | none => false
#guard match hexBytes? firstSegwitSpendHex with
  | some bytes => hasCheckResult bytes true
  | none => false

end FuzzTests

namespace Tests.AxiomAudit

set_option linter.hashCommand false

#assert_axioms BtcVerified.Fuzz.regularCheck_eq_isWellFormed

end Tests.AxiomAudit
