import BtcVerified.Transaction.OutPoint
import BtcVerified.Script.Script
/-!
  # Transaction inputs

  A transaction input spends one previous output: the outpoint it consumes,
  the unlocking script, and the sequence number. The script is a `Script` —
  raw program bytes, tokenized only at execution time — and the codec comes
  by composition over the fields in wire order.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- A transaction input: the output it spends, the unlocking script, and the
input sequence number. -/
structure TxIn where
  /-- The previous output this input spends. -/
  prevout : OutPoint
  /-- The unlocking script (`scriptSig`). -/
  scriptSig : Script
  /-- The input sequence number (used for relative timelocks / RBF signalling). -/
  sequence : UInt32
  deriving DecidableEq

/-- A `TxIn` is its previous output, its unlocking script, and its sequence
number, in that order. -/
def TxIn.equivProd : TxIn ≃ (OutPoint × Script × UInt32) where
  toFun i := (i.prevout, i.scriptSig, i.sequence)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Serializes a `TxIn` as its `OutPoint`, then its length-prefixed `scriptSig`,
then its little-endian sequence number. -/
instance instCodecTxIn : Codec TxIn :=
  Codec.ofEquiv TxIn.equivProd inferInstance

/-- A transaction input with a short scriptSig encodes to 41 bytes plus the
scriptSig length: a 36-byte outpoint, the script (one-byte prefix + bytes), and a
4-byte sequence. -/
theorem encode_txin_length {i : TxIn} (h : i.scriptSig.code.val.length < 253) :
    (Codec.encode i).length = 41 + i.scriptSig.code.val.length := by
  change (Codec.encode i.prevout
    ++ (Codec.encode i.scriptSig ++ Codec.encode i.sequence)).length = _
  rw [List.length_append, List.length_append, encode_outpoint_length,
    encode_script_length_lt_253 h, encode_uint32_length]
  omega

/-- An input's length with the scriptSig factored out (no size assumption). -/
theorem encode_txin_length_eq (i : TxIn) :
    (Codec.encode i).length = 40 + (Codec.encode i.scriptSig).length := by
  change (Codec.encode i.prevout
    ++ (Codec.encode i.scriptSig ++ Codec.encode i.sequence)).length = _
  rw [List.length_append, List.length_append, encode_outpoint_length, encode_uint32_length]
  omega

/-- Every transaction input is at least 41 bytes (a 36-byte outpoint, a nonempty
script prefix, and a 4-byte sequence). -/
theorem encode_txin_length_ge (i : TxIn) : 41 ≤ (Codec.encode i).length := by
  rw [encode_txin_length_eq, encode_script_length_eq]
  have := CompactSize.encode_length_ge_one (UInt64.ofNat i.scriptSig.code.val.length)
  omega

/-- The byte layout of an input: outpoint, scriptSig, sequence. -/
theorem encode_txin_eq (i : TxIn) :
    Codec.encode i
      = Codec.encode i.prevout ++ Codec.encode i.scriptSig ++ Codec.encode i.sequence := by
  change Codec.encode i.prevout
    ++ (Codec.encode i.scriptSig ++ Codec.encode i.sequence) = _
  simp only [List.append_assoc]

/-- An input sequence is at least 41 bytes per input. -/
theorem encodeElems_txin_length_ge (xs : List TxIn) :
    41 * xs.length ≤ (encodeElems xs).length := by
  induction xs with
  | nil => simp [encodeElems]
  | cons x xs ih =>
    simp only [encodeElems, List.length_append, List.length_cons]
    have := encode_txin_length_ge x
    omega

end BtcVerified
