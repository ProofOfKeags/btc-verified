import BtcVerified.Transaction.Tx
/-!
  # Transaction values for regression examples

  These small fixtures describe fields directly as Lean values, without an
  encoder or decoder. Specification examples can therefore express amounts,
  outpoints, and script lengths without depending on a wire-format test first.
  Kernel boundary examples instead use independently sourced wire bytes.
  Scripts are opaque data, not claims about spendability.

  Construction requires the model's shape and length proofs. A bad fixture
  cannot silently become a default transaction.
-/

namespace Tests.TransactionFixtures

open BtcVerified

/-- One non-null input with recognizable raw hash bytes `00 01 ... 1f`, index
`0x01020304`, scriptSig `51 ab`, and sequence `0x05060708`. The hash is in raw
byte order, not the reversed order used to display a txid. -/
def ordinaryInput : TxIn :=
  { prevout :=
      { txid := ⟨(List.range 32).map UInt8.ofNat, by simp⟩
        vout := 0x01020304 }
    scriptSig := ⟨⟨[0x51, 0xab], by decide⟩⟩
    sequence := 0x05060708 }

/-- One output below maxMoney, with amount `0x010203040506` satoshis and
opaque scriptPubKey bytes `00 6a ff`. -/
def ordinaryOutput : TxOut :=
  { value := 0x010203040506
    scriptPubKey := ⟨⟨[0, 0x6a, 0xff], by decide⟩⟩ }

/-- A version-1, witness-free transaction with the given fields. Proof arguments
are discharged for the literal lists at each use; zero-input fixtures must use
`Tx.empty` explicitly rather than masquerading as legacy transactions. -/
def legacyTx (inputs : List TxIn) (outputs : List TxOut) (lockTime : UInt32 := 0)
    (inputsNonempty : inputs ≠ [] := by decide)
    (inputsBound : inputs.length < 2 ^ 64 := by decide)
    (outputsBound : outputs.length < 2 ^ 64 := by decide) : Tx :=
  .legacy
    { version := 1
      inputs := ⟨inputs, inputsBound⟩
      outputs := ⟨outputs, outputsBound⟩
      lockTime := lockTime }
    inputsNonempty

/-- One null-prevout input with an all-zero scriptSig of the requested length
and the final sequence `0xffffffff`. Only script length matters in these
transaction-local coinbase examples. -/
def coinbaseInput (scriptLength : Nat) (bound : scriptLength < 2 ^ 64 := by decide) :
    TxIn :=
  { prevout := OutPoint.null
    scriptSig := ⟨⟨List.replicate scriptLength 0, by simpa using bound⟩⟩
    sequence := 0xffffffff }

/-- A single-null-input transaction with the ordinary output and zero lockTime.
Its classification is coinbase for every script length; well-formedness is what
the script-length examples test separately. -/
def coinbaseTx (scriptLength : Nat) (bound : scriptLength < 2 ^ 64 := by decide) : Tx :=
  legacyTx [coinbaseInput scriptLength bound] [ordinaryOutput]
    (inputsNonempty := by simp) (inputsBound := by simp)

/-- The ordinary input and output, with recognizable lockTime `0x090a0b0c`.
This supplies a small transaction for the specification-rule examples. -/
def legacyExample : Tx :=
  legacyTx [ordinaryInput] [ordinaryOutput] 0x090a0b0c

/-- The same body as `legacyExample`, carrying one witness stack whose items
are an empty byte string and `aa bb cc`. An empty item is not an empty stack. -/
def segwitExample : Tx :=
  let input : SegwitInput :=
    { input := ordinaryInput
      witness := ⟨[⟨[], by decide⟩, ⟨[0xaa, 0xbb, 0xcc], by decide⟩], by decide⟩ }
  .segwit 1 ⟨[input], by decide⟩ ⟨[ordinaryOutput], by decide⟩ 0x090a0b0c
    (by exact ⟨input, by simp, by decide⟩)

/-- Version 1 and zero lockTime, with no inputs or outputs. This is a distinct
constructor in the model, not a failed construction of an ordinary transaction. -/
def emptyTx : Tx := .empty 1 0

/-- Exactly 21 million BTC expressed as satoshis, with an empty scriptPubKey.
The literal is independent of `Consensus.maxMoney`, so changing that limit can
change the expected result instead of silently changing the test input. -/
def maxMoneyOutput : TxOut :=
  { value := 2_100_000_000_000_000
    scriptPubKey := ⟨⟨[], by decide⟩⟩ }

/-- One satoshi, with an empty scriptPubKey; adding it to `maxMoneyOutput`
crosses the aggregate money boundary without making either output too large. -/
def oneSatoshiOutput : TxOut :=
  { value := 1
    scriptPubKey := ⟨⟨[], by decide⟩⟩ }

end Tests.TransactionFixtures
