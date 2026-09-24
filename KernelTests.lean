import Kernel.Transaction
import Tests.AxiomAudit
import Tests.GoldenVectors
/-!
  # Lean transaction kernel tests

  This file checks the pure Lean adapter, not the C ABI. Read it in four parts:

  1. Axiom audits protect the general proofs connecting the adapter to the spec.
  2. Wire fixtures check parsing and re-encoding, including malformed encodings.
  3. Accessor fixtures check field values, witness shape, and stripped bytes.
  4. Transaction-local fixtures distinguish successful parsing from passing rules.

  `#guard` evaluates a concrete Boolean and fails the build unless it is true.
  It is a regression test, not a theorem over all inputs. Expected answers come
  from documented mainnet fixtures or the hand-written wire layouts and named
  specification rules below, never from running Core. Synthetic test bytes are
  deliberately constructed without our encoder.

  These cases do not establish Core equivalence, native ABI conformance, script
  validity, or block validity. The txid comparison below checks spec agreement,
  not an independent hash oracle. The million-byte stripped-size boundary and
  Core container-length boundary are not exercised by these small fixtures.
-/

namespace KernelTests

open BtcVerified Tests.GoldenVectors

set_option linter.hashCommand false

/-! ## 1. Proof dependencies

  These are not fixture tests. Reject unexpected axioms (including `sorryAx`)
  in the checker refinement, witness-count equality, stripped encoding,
  and txid agreement. The allowed assumptions are defined in `Tests.AxiomAudit`.
-/

#assert_axioms Kernel.regularCheck_eq_isWellFormed
#assert_axioms Kernel.witnesses_size_eq_inputs_size
#assert_axioms Kernel.encodeStripped_toList
#assert_axioms Kernel.txid_eq_txid

/-! ## 2. Parsing and serialization

  A transaction can parse successfully yet fail transaction-local checks.
  Malformed wire bytes, by contrast, must fail before a checker is called.
-/

/-- Require decoding to succeed before inspecting its result. An unexpected
parse failure cannot satisfy a test expecting checker rejection. -/
private def decodedSatisfies (bytes : ByteArray) (expect : Tx → Bool) : Bool :=
  match Kernel.decode bytes with
  | some tx => expect tx
  | none => false

/-- Require a fixture to parse, re-encode to its original bytes, and produce the
specified checker result. Repeat with a suffix: decoding consumes a transaction
prefix, so the suffix must not become part of the re-encoded transaction. -/
private def roundtripsWithCheckResult (hex : String) (expectedCheck : Bool) : Bool :=
  match hexBytes? hex with
  | none => false
  | some bytes =>
    [bytes, bytes ++ [0xde, 0xad]].all fun input =>
      decodedSatisfies input.toByteArray fun tx =>
        Kernel.encode tx == bytes.toByteArray && Kernel.check tx == expectedCheck

-- Sources and layouts are documented in Tests.GoldenVectors. The three mainnet
-- transactions exercise legacy, SegWit, and coinbase paths; each passes the local
-- rules. Re-encoding must preserve the original transaction, not its suffix.
#guard roundtripsWithCheckResult firstBitcoinPaymentHex true
#guard roundtripsWithCheckResult firstSegwitSpendHex true
#guard roundtripsWithCheckResult segwitCoinbaseHex true
-- The empty object is decodable but lacks the inputs and outputs needed to pass.
#guard roundtripsWithCheckResult coreEmptyTxHex false

-- An encoding with a witness marker but no nonempty witness stack is superfluous:
-- there is no witness data to justify that form. Decoding must reject it.
#guard match hexBytes? superfluousWitnessHex with
  | some bytes => (Kernel.decode bytes.toByteArray).isNone
  | none => false

/-! ### Hand-written wire ingredients

  Distinct nonzero bytes make endianness and field-boundary mistakes observable.
  Scripts are opaque bytes here: no test claims they execute successfully.
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

/-! ### Malformed bytes must fail decoding

  Unlike the rejected transactions in section 4, these inputs do not describe
  an accepted transaction encoding. Separate guards identify the failing case.
-/

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

/-! ## 3. Field and witness accessors

  Both synthetic encodings have the same body. Expected values below are read
  directly from the annotated byte layout, independently of the decoder.
-/

private def fieldsMatchWireLayout (tx : Tx) : Bool :=
  match (Kernel.inputs tx).toList, (Kernel.outputs tx).toList with
  | [input], [output] =>
      Kernel.locktime tx == 0x090a0b0c
        && Kernel.inputTxid input == previousHash.toByteArray
        && Kernel.inputIndex input == 0x01020304
        && Kernel.inputSequence input == 0x05060708
        && Kernel.inputScript input == ([0x51, 0xab] : List UInt8).toByteArray
        && Kernel.outputAmount output == 0x010203040506
        && Kernel.outputScript output == ([0, 0x6a, 0xff] : List UInt8).toByteArray
  | _, _ => false

#guard decodedSatisfies legacyBytes.toByteArray fieldsMatchWireLayout
#guard decodedSatisfies witnessedBytes.toByteArray fieldsMatchWireLayout

-- Stripping removes the marker/flag and witness but retains the whole body.
-- Txid agreement checks the adapter's composition with the spec; both sides
-- share SHA-256, so this is not an independent hash correctness test.
private def strippedEncodingAndTxidAgree (tx : Tx) : Bool :=
  Kernel.encodeStripped tx == legacyBytes.toByteArray
    && Kernel.txid tx == tx.txid.val.toByteArray

#guard decodedSatisfies legacyBytes.toByteArray strippedEncodingAndTxidAgree
#guard decodedSatisfies witnessedBytes.toByteArray strippedEncodingAndTxidAgree

-- The outer array follows inputs; each inner array is that input's stack.
-- A legacy input gets one empty stack. An empty witness ITEM must be retained
-- inside its nonempty stack, rather than dropping or shifting it.
#guard decodedSatisfies legacyBytes.toByteArray fun tx => Kernel.witnesses tx == #[#[]]
#guard decodedSatisfies witnessedBytes.toByteArray fun tx =>
  Kernel.witnesses tx == #[#[ByteArray.empty, ([0xaa, 0xbb, 0xcc] : List UInt8).toByteArray]]

-- Zero inputs means zero stacks, not one empty stack. This empty object's
-- lockTime is zero, and both named nonemptiness predicates must be false.
#guard match hexBytes? coreEmptyTxHex >>= (Kernel.decode ·.toByteArray) with
  | some tx => (Kernel.inputs tx).isEmpty && (Kernel.outputs tx).isEmpty
      && (Kernel.witnesses tx).isEmpty && Kernel.locktime tx == 0
      && !decide tx.InputsNonempty && !decide tx.OutputsNonempty
  | none => false

/-! ## 4. Transaction-local rules on successfully decoded values

  Every transaction-local test below requires decoding to succeed. A false
  checker expectation cannot accidentally pass because a fixture was malformed.
  These cases check rule decisions and branch selection, not spendability or
  block inclusion.
-/

-- Positive controls: one non-null input gives nonemptiness and distinctness;
-- the single positive output is below maxMoney and the stripped body is tiny.
private def ordinaryPremisesHold (tx : Tx) : Bool :=
  decide tx.InputsNonempty && decide tx.OutputsNonempty
    && decide tx.AllInputOutpointsDistinct && decide tx.AllInputOutpointsNeNull
    && decide tx.TotalOutputValueLeMaxMoney
    && decide tx.StrippedSizeLeMaxStrippedTransactionSize

#guard decodedSatisfies legacyBytes.toByteArray ordinaryPremisesHold
#guard decodedSatisfies witnessedBytes.toByteArray ordinaryPremisesHold

/-- Assemble version-1, lockTime-0 fixtures from already serialized inputs and
outputs. All counts used here are below 253, so their CompactSize prefix is one
literal byte. This is a small-fixture builder, not a general transaction codec. -/
private def smallTransaction (inputs outputs : List (List UInt8)) : ByteArray :=
  ([1, 0, 0, 0, UInt8.ofNat inputs.length] ++ inputs.flatten
    ++ [UInt8.ofNat outputs.length] ++ outputs.flatten ++ [0, 0, 0, 0]).toByteArray
-- Null prevout = 32 zero bytes plus index ffffffff. All lengths used below are
-- below 253. Zero script bytes suffice because only their length is checked.
private def coinbaseInput (scriptLength : Nat) : List UInt8 :=
  List.replicate 32 0 ++ [0xff, 0xff, 0xff, 0xff, UInt8.ofNat scriptLength]
    ++ List.replicate scriptLength 0 ++ [0xff, 0xff, 0xff, 0xff]
private def hasCheckResult (bytes : ByteArray) (expected : Bool) : Bool :=
  decodedSatisfies bytes fun tx => Kernel.check tx == expected

/-! ### Coinbase scriptSig length boundaries

  A single null-prevout input selects the coinbase branch of the checker.
  That branch requires inclusive 2–100-byte scriptSig bounds. Vary only that
  length, with otherwise passing local fields.
-/

private def coinbaseLengthHasResult (scriptLength : Nat) (expected : Bool) : Bool :=
  hasCheckResult (smallTransaction [coinbaseInput scriptLength] [outputBytes]) expected

#guard coinbaseLengthHasResult 0 false    -- Empty script: below the minimum.
#guard coinbaseLengthHasResult 1 false    -- Immediately below the minimum.
#guard coinbaseLengthHasResult 2 true     -- Minimum is inclusive.
#guard coinbaseLengthHasResult 100 true   -- Maximum is inclusive.
#guard coinbaseLengthHasResult 101 false  -- Immediately above the maximum.

-- The dispatcher rejects missing outputs on either branch.
#guard hasCheckResult (smallTransaction [coinbaseInput 2] []) false
#guard hasCheckResult (smallTransaction [inputBytes] []) false
-- Identical inputs repeat an outpoint.
#guard hasCheckResult (smallTransaction [inputBytes, inputBytes] [outputBytes]) false
-- Two inputs are not coinbase-shaped; the null prevout is therefore prohibited.
#guard hasCheckResult (smallTransaction [inputBytes, coinbaseInput 2] [outputBytes]) false

/-- Evaluate one named specification predicate after successful decoding. -/
private def predicateResult (predicate : Tx → Prop) [DecidablePred predicate]
    (bytes : ByteArray) (expected : Bool) : Bool :=
  decodedSatisfies bytes fun tx => decide (predicate tx) == expected

/-! ### Input outpoints, not entire input records, must be distinct -/

-- Change only the last sequence byte. The inputs differ as records but still
-- spend the same outpoint, so the distinctness predicate must remain false.
#guard predicateResult Tx.AllInputOutpointsDistinct
  (smallTransaction [inputBytes, inputBytes.dropLast ++ [0]] [outputBytes]) false
-- The null prevout is exactly what makes the preceding coinbase fixtures fail
-- the non-coinbase specification's non-null-input rule.
#guard predicateResult Tx.AllInputOutpointsNeNull
  (smallTransaction [coinbaseInput 2] [outputBytes]) false

/-! ### Money bounds -/

-- 2,100,000,000,000,000 satoshis (maxMoney), eight little-endian bytes.
private def maxMoneyBytes : List UInt8 := [0, 0x40, 7, 0x5a, 0xf0, 0x75, 7, 0]
-- Each output appends a zero-length scriptPubKey to its eight-byte value.
private def maxMoneyOutput : List UInt8 := maxMoneyBytes ++ [0]
private def oneSatoshiOutput : List UInt8 := [1, 0, 0, 0, 0, 0, 0, 0, 0]

-- Equality is allowed. Adding a second, individually small output exceeds the
-- aggregate bound: checking each output alone would miss this rejection.
#guard predicateResult Tx.TotalOutputValueLeMaxMoney
  (smallTransaction [inputBytes] [maxMoneyOutput]) true
#guard predicateResult Tx.TotalOutputValueLeMaxMoney
  (smallTransaction [inputBytes] [maxMoneyOutput, oneSatoshiOutput]) false

-- All-one amount bits represent -1 as signed 64-bit data. Our UInt64 field must
-- preserve those bits, while its natural value exceeds maxMoney. Thus parsing
-- succeeds, the amount accessor is lossless, and checking rejects.
#guard match Kernel.decode
    (smallTransaction [inputBytes] [List.replicate 8 0xff ++ [0]]) with
  | some tx => !Kernel.check tx &&
      (Kernel.outputs tx).toList.map Kernel.outputAmount == [0xffffffffffffffff]
  | none => false

end KernelTests
