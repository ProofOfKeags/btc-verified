import BtcVerified.Packed.Tx
import BtcVerified.Consensus.TxStateless
/-!
  # Native transaction conformance boundary

  This module exposes the existing packed transaction codec through a pure
  byte-array function. Its C symbol uses Lean's native object ABI: the host
  initializes this module once, supplies a `ByteArray`, and receives an
  owned `ByteArray` result.

  The original roundtrip result's first byte is a status tag: `0` means parsing failed; `1`
  precedes the packed serialization of the decoded transaction. A
  successful prefix parse deliberately ignores the remaining input bytes.
  The additional observation includes a context-free structural-check result
  and explicit decoded fields. Its fixed-width transcript writer is independent
  of the transaction's integer codecs, so decoding and re-encoding an integer
  with the same wrong endianness cannot hide that field disagreement.

  The underlying packed decoder and encoder already have their agreement
  proofs in `PackedCodec.abstractParse_decode` and
  `PackedCodec.toList_encode`. Neither export adds a parser restriction;
  campaign resource limits belong to the native harness.

  Regular transactions use a checker proved equal to `Tx.isWellFormed`, with
  the size measured through the packed encoder to avoid allocating the
  specification's serialized byte list. The
  coinbase-shaped branch is an adapter for Core's standalone `CheckTransaction`
  boundary, not a change to the regular-position consensus model and not a
  theorem of equivalence to Core. Neither branch establishes script validity,
  input availability, fees, maturity, finality, or block-extension validity.
  Reference: https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/consensus/tx_check.cpp#L19-L67

  Checked claims:

  * `regularCheck_eq_isWellFormed`: the packed-size regular checker computes
    exactly the existing regular-position consensus checker.
-/

namespace BtcVerified.Fuzz

open BtcVerified.Packed

/-- Return `0` on a failed packed transaction parse, or `1` followed by the
packed encoding of the parsed transaction, ignoring trailing input bytes.
The exported C symbol consumes its input Lean `ByteArray` object and returns
an owned Lean `ByteArray` object. -/
@[export btc_verified_transaction_roundtrip]
def transactionRoundtrip (input : ByteArray) : ByteArray :=
  match PackedCodec.decode (α := Tx) input with
  | none => ByteArray.empty.push 0
  | some (tx, _) => PackedCodec.encodeInto tx (ByteArray.empty.push 1)

private theorem packed_stripped_size_eq (tx : Tx) :
    (PackedCodec.encode tx.body).size = tx.strippedSize := by
  have h := congrArg List.length (PackedCodec.toList_encode tx.body)
  simpa only [ByteArray.toList_eq_data_toList, ByteArray.size,
    Array.length_toList, Tx.strippedSize] using h

/-- The existing regular-position transaction checker, with the same premises
but a packed encoding for the stripped-size measurement. This avoids the
specification encoder's recursive per-byte list construction on large scripts. -/
def regularCheck (tx : Tx) : Bool :=
  decide (tx.body.inputs.val ≠ [])
    && decide (tx.body.outputs.val ≠ [])
    && decide tx.body.spends.Nodup
    && tx.body.spends.all (· != OutPoint.null)
    && decide ((tx.body.outputs.val.map fun output => output.value.toNat).sum
        ≤ Consensus.maxMoney)
    && decide ((PackedCodec.encode tx.body).size ≤ Consensus.maxLegacySerializedSize)

/-- Measuring stripped size with the packed encoder leaves the existing
regular-position transaction checker unchanged on every transaction. -/
theorem regularCheck_eq_isWellFormed (tx : Tx) :
    regularCheck tx = tx.isWellFormed := by
  simp only [regularCheck, Tx.isWellFormed, packed_stripped_size_eq]

private def contextFreeCheck (tx : Tx) : Bool :=
  match tx.body.inputs.val with
  | [input] =>
    if input.prevout == OutPoint.null then
      !tx.body.outputs.val.isEmpty
        && decide ((tx.body.outputs.val.map fun output => output.value.toNat).sum
          ≤ Consensus.maxMoney)
        -- PackedCodec.toList_encode identifies this size with the spec's
        -- stripped serialization size, without constructing its byte list.
        && decide ((PackedCodec.encode tx.body).size ≤ Consensus.maxLegacySerializedSize)
        && decide (2 ≤ input.scriptSig.code.val.length)
        && decide (input.scriptSig.code.val.length ≤ 100)
    else regularCheck tx
  | _ => regularCheck tx

-- This is an observation format, not a second transaction codec. In particular,
-- do not use PackedCodec.encodeInto to encode the observed integer values.
private def pushWord (width : Nat) (value : UInt64) (acc : ByteArray) : ByteArray :=
  (List.range width).foldl
    (fun bytes i => bytes.push ((value >>> UInt64.ofNat (8 * i)).toUInt8)) acc

private def pushLength (length : Nat) (acc : ByteArray) : ByteArray :=
  pushWord 8 (UInt64.ofNat length) acc

private def pushRegion (bytes : List UInt8) (acc : ByteArray) : ByteArray :=
  pushBytes bytes (pushLength bytes.length acc)

private def pushWitness (witness : List (List UInt8)) (acc : ByteArray) : ByteArray :=
  witness.foldl (fun bytes item => pushRegion item bytes) (pushLength witness.length acc)

private def pushInputObservation (input : TxIn) (witness : List (List UInt8))
    (acc : ByteArray) : ByteArray :=
  let acc := pushBytes input.prevout.txid.val acc
  let acc := pushWord 4 input.prevout.vout.toUInt64 acc
  let acc := pushWord 4 input.sequence.toUInt64 acc
  pushWitness witness (pushRegion input.scriptSig.code.val acc)

private def pushInputObservations (tx : Tx) (acc : ByteArray) : ByteArray :=
  match tx with
  | .legacy body _ =>
    body.inputs.val.foldl (fun bytes input => pushInputObservation input [] bytes) acc
  | .empty .. => acc
  | .segwit _ inputs .. =>
    inputs.val.foldl (fun bytes input =>
      pushInputObservation input.input (input.witness.val.map Subtype.val) bytes) acc

private def pushOutputObservation (output : TxOut) (acc : ByteArray) : ByteArray :=
  -- Preserve all 64 amount bits, including encodings Core reads as negative.
  -- Their UInt64.toNat values exceed maxMoney, so the check still rejects them.
  pushRegion output.scriptPubKey.code.val (pushWord 8 output.value acc)

/-- Observe a parsed transaction and its context-free structural-check result.
Returns `[0]` on parsing failure. Otherwise returns `[1, check]`, the `u64LE`
serialization length and serialization, then `u64LE` input/output counts and
`u32LE` locktime. Each input contributes its raw 32-byte prevout hash, `u32LE`
index and sequence, length-prefixed scriptSig, and witness stack; each output
contributes the amount's `u64LE` bit pattern and length-prefixed scriptPubKey.
Transcript byte-region lengths and witness counts are `u64LE`. Trailing input
bytes are ignored. The C export consumes its input and returns an owned result. -/
@[export btc_verified_transaction_observe]
def transactionObserve (input : ByteArray) : ByteArray :=
  match PackedCodec.decode (α := Tx) input with
  | none => ByteArray.empty.push 0
  | some (tx, _) =>
    let serialization := PackedCodec.encode tx
    let body := tx.body
    let acc := (ByteArray.empty.push 1).push (if contextFreeCheck tx then 1 else 0)
    let acc := pushLength serialization.size acc ++ serialization
    let acc := pushLength body.inputs.val.length acc
    let acc := pushLength body.outputs.val.length acc
    let acc := pushWord 4 body.lockTime.toUInt64 acc
    let acc := pushInputObservations tx acc
    body.outputs.val.foldl (fun bytes output => pushOutputObservation output bytes) acc

end BtcVerified.Fuzz
