import BtcVerified.Consensus.TxStateless
import BtcVerified.Transaction.Txid
/-!
  # Lean transaction kernel boundary

  This module supplies the pure Lean operations for a future
  `libbitcoinkernel` compatibility shim. It decodes and encodes with the proved
  packed transaction codec, exposes immutable field snapshots, and computes the
  transaction-local `CheckTransaction` projection without importing the fuzz
  harness.

  Decoding retains the protocol codec's prefix-consuming semantics, then rejects
  decoded values whose CompactSize-prefixed containers exceed Core's generic
  `0x02000000` allocation ceiling. The compatibility guard covers input and
  output vectors, scripts, witness-stack vectors, and witness items; it does not
  impose a raw total-input-size cap or change the protocol codec. This is a
  post-decode domain restriction, not an allocation or work limit on decoding.
  References: pinned Core's
  [`MAX_SIZE`](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/serialize.h#L35)
  and [`ReadCompactSize` range check](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/serialize.h#L333-L363).

  The `btcv_kernel_*` exports are private Lean FFI entry points, not the public
  `btck_*` interface. Their generated wrappers consume object arguments and
  return owned object results. A borrowing caller must increment an object
  before passing it to an export. No C shim or shared library is provided here.
  The proofs below relate these operations to our Lean specification; they do
  not establish equivalence to Core or full consensus validity.

  Checked claims:

  * `regularCheck_eq_isWellFormed`: the packed-size regular checker computes the
    existing regular-position consensus checker.
  * `witnesses_size_eq_inputs_size`: every exported witness snapshot is aligned
    one-for-one with the exported inputs.
  * `encodeStripped_toList`: the native stripped encoding is exactly the
    specification encoding of the transaction body.
  * `txid_eq_txid`: hashing that native stripped encoding returns `Tx.txid`'s
    raw bytes.
-/

namespace BtcVerified.Kernel

open BtcVerified.Packed BtcVerified.Serialize

private def coreCompactSizeLimit : Nat := 0x02000000

private def lengthWithinCoreLimit {α : Type} (values : List α) : Bool :=
  decide (values.length ≤ coreCompactSizeLimit)

private def inputWithinCoreLimit (input : TxIn) : Bool :=
  lengthWithinCoreLimit input.scriptSig.code.val

private def outputWithinCoreLimit (output : TxOut) : Bool :=
  lengthWithinCoreLimit output.scriptPubKey.code.val

private def witnessWithinCoreLimit (witness : WitnessStack) : Bool :=
  lengthWithinCoreLimit witness.val
    && witness.val.all fun item => lengthWithinCoreLimit item.val

/-- Whether every CompactSize-prefixed container in a decoded transaction fits
Core's generic `0x02000000` deserialization allocation ceiling. This is a native
compatibility-domain guard, not a protocol-validity predicate or total-size cap. -/
def compactSizeCompatible (tx : Tx) : Bool :=
  let body := tx.body
  lengthWithinCoreLimit body.inputs.val
    && lengthWithinCoreLimit body.outputs.val
    && body.inputs.val.all inputWithinCoreLimit
    && body.outputs.val.all outputWithinCoreLimit
    && (match tx with
      | .segwit _ txInputs _ _ _ =>
          txInputs.val.all fun input => witnessWithinCoreLimit input.witness
      | .legacy .. | .empty .. => true)

/-- Prefix-decode a transaction with the proved packed codec, then restrict the
result to Core's generic CompactSize allocation domain. The input object is
owned by the generated C wrapper. -/
@[export btcv_kernel_decode]
def decode (input : ByteArray) : Option Tx :=
  match PackedCodec.decode (α := Tx) input with
  | none => none
  | some (tx, _) => if compactSizeCompatible tx then some tx else none

/-- Encode a transaction in its canonical legacy, empty, or SegWit wire form. -/
@[export btcv_kernel_encode]
def encode (tx : Tx) : ByteArray :=
  PackedCodec.encode tx

/-- Encode the transaction's witness-stripped body, which is the txid preimage. -/
@[export btcv_kernel_encode_stripped]
def encodeStripped (tx : Tx) : ByteArray :=
  PackedCodec.encode tx.body

-- The packed implementation of `Tx.StrippedSizeLeMaxStrippedTransactionSize`;
-- `regularCheck_eq_isWellFormed` transports this measurement to the spec.
private def checkStrippedSizeLeMaxStrippedTransactionSize (tx : Tx) : Bool :=
  decide ((PackedCodec.encode tx.body).size ≤ Consensus.maxStrippedTransactionSize)

/-- Decide the regular-position transaction-local premises while measuring
stripped size through the packed encoder. -/
def regularCheck (tx : Tx) : Bool :=
  decide tx.ExistsInput
    && decide tx.ExistsOutput
    && decide tx.AllInputOutpointsDistinct
    && decide tx.AllInputOutpointsNeNull
    && decide tx.TotalOutputValueLeMaxMoney
    && checkStrippedSizeLeMaxStrippedTransactionSize tx

/-- Measuring stripped size with the packed encoder leaves the existing
regular-position transaction checker unchanged on every transaction. -/
theorem regularCheck_eq_isWellFormed (tx : Tx) :
    regularCheck tx = tx.isWellFormed := by
  have hsize : (PackedCodec.encode tx.body).size = tx.strippedSize := by
    have h := congrArg List.length (PackedCodec.toList_encode tx.body)
    simpa only [ByteArray.toList_eq_data_toList, ByteArray.size,
      Array.length_toList, Tx.strippedSize] using h
  apply Bool.eq_iff_iff.mpr
  simp only [regularCheck, Tx.isWellFormed, checkStrippedSizeLeMaxStrippedTransactionSize,
    Bool.and_eq_true, decide_eq_true_eq, Tx.StrippedSizeLeMaxStrippedTransactionSize, hsize]

/-- The standalone transaction-local adapter: the regular checker plus a
single-null-input coinbase branch with scriptSig length bounds. This follows
pinned Core's [`CheckTransaction`](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/consensus/tx_check.cpp#L19-L67);
no theorem of Core equivalence or full consensus validity is claimed. -/
@[export btcv_kernel_check]
def check (tx : Tx) : Bool :=
  match tx.body.inputs.val with
  | [input] =>
    if input.prevout == OutPoint.null then
      decide tx.ExistsOutput
        && decide tx.TotalOutputValueLeMaxMoney
        && checkStrippedSizeLeMaxStrippedTransactionSize tx
        && decide (2 ≤ input.scriptSig.code.val.length)
        && decide (input.scriptSig.code.val.length ≤ 100)
    else regularCheck tx
  | _ => regularCheck tx

/-- Return the transaction locktime. -/
@[export btcv_kernel_locktime]
def locktime (tx : Tx) : UInt32 :=
  tx.body.lockTime

/-- Materialize the transaction inputs in wire order. -/
@[export btcv_kernel_inputs]
def inputs (tx : Tx) : Array TxIn :=
  tx.body.inputs.val.toArray

/-- Materialize the transaction outputs in wire order. -/
@[export btcv_kernel_outputs]
def outputs (tx : Tx) : Array TxOut :=
  tx.body.outputs.val.toArray

/-- Materialize witness items as byte arrays aligned one-for-one with the
transaction inputs. Legacy inputs receive empty witness arrays. -/
@[export btcv_kernel_witnesses]
def witnesses (tx : Tx) : Array (Array ByteArray) :=
  match tx with
  | .legacy body _ =>
      (body.inputs.val.map fun _ => (#[] : Array ByteArray)).toArray
  | .empty .. => #[]
  | .segwit _ txInputs _ _ _ =>
      (txInputs.val.map fun input =>
        (input.witness.val.map fun item => item.val.toByteArray).toArray).toArray

/-- The witness snapshot contains exactly one stack for each input. -/
theorem witnesses_size_eq_inputs_size (tx : Tx) :
    (witnesses tx).size = (inputs tx).size := by
  cases tx with
  | legacy body inputsNonempty =>
      simp [witnesses, inputs]
      rfl
  | empty version lockTime =>
      simp [witnesses, inputs]
      rfl
  | segwit version txInputs txOutputs lockTime hWitness =>
      simp only [witnesses, Nat.reducePow, List.map_subtype, List.size_toArray,
        List.length_map, inputs]
      change txInputs.val.length = (txInputs.val.map SegwitInput.input).length
      simp only [List.length_map]

/-- Return an input's previous transaction id as its 32 raw wire bytes. -/
@[export btcv_kernel_input_txid]
def inputTxid (input : TxIn) : ByteArray :=
  input.prevout.txid.val.toByteArray

/-- Return an input's previous-output index. -/
@[export btcv_kernel_input_index]
def inputIndex (input : TxIn) : UInt32 :=
  input.prevout.vout

/-- Return an input's sequence number. -/
@[export btcv_kernel_input_sequence]
def inputSequence (input : TxIn) : UInt32 :=
  input.sequence

/-- Return an input's raw scriptSig bytes. -/
@[export btcv_kernel_input_script]
def inputScript (input : TxIn) : ByteArray :=
  input.scriptSig.code.val.toByteArray

/-- Return all 64 output-amount wire bits. -/
@[export btcv_kernel_output_amount]
def outputAmount (output : TxOut) : UInt64 :=
  output.value

/-- Return an output's raw scriptPubKey bytes. -/
@[export btcv_kernel_output_script]
def outputScript (output : TxOut) : ByteArray :=
  output.scriptPubKey.code.val.toByteArray

/-- Double-SHA-256 arbitrary owned bytes and return the 32 raw digest bytes. -/
@[export btcv_kernel_hash]
def hash (bytes : ByteArray) : ByteArray :=
  (Sha256.sha256d bytes.toList).toByteArray

/-- The native stripped encoding is byte-for-byte the specification encoding
of the transaction body. -/
theorem encodeStripped_toList (tx : Tx) :
    (encodeStripped tx).toList = Codec.encode tx.body :=
  PackedCodec.toList_encode tx.body

/-- Compute a transaction id by hashing the native stripped encoding. -/
def txid (tx : Tx) : ByteArray :=
  hash (encodeStripped tx)

/-- Hashing the native stripped encoding returns exactly `Tx.txid`'s 32 raw
bytes. -/
theorem txid_eq_txid (tx : Tx) :
    txid tx = tx.txid.val.toByteArray := by
  simp only [txid, hash, encodeStripped, Tx.txid, TxBody.txid,
    PackedCodec.toList_encode]

end BtcVerified.Kernel
