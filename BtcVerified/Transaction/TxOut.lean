import BtcVerified.Script.Script
/-!
  # Transaction outputs

  A transaction output is an amount in satoshis and the locking script that
  must be satisfied to spend it. The script is a `Script` — raw program bytes,
  tokenized only at execution time — and the codec comes by composition over
  the two fields in wire order.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- A transaction output: the amount in satoshis and the locking script that must
be satisfied to spend it. -/
structure TxOut where
  /-- The output amount in satoshis. -/
  value : UInt64
  /-- The locking script (`scriptPubKey`). -/
  scriptPubKey : Script
  deriving DecidableEq

/-- A `TxOut` is its amount followed by its locking script. -/
def TxOut.equivProd : TxOut ≃ (UInt64 × Script) where
  toFun o := (o.value, o.scriptPubKey)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Serializes a `TxOut` as its little-endian 8-byte amount followed by its
length-prefixed `scriptPubKey`. -/
instance instCodecTxOut : Codec TxOut :=
  Codec.ofEquiv TxOut.equivProd inferInstance

/-- A transaction output with a short scriptPubKey encodes to 9 bytes plus the
scriptPubKey length: an 8-byte value and the script (one-byte prefix + bytes). -/
theorem encode_txout_length {o : TxOut} (h : o.scriptPubKey.code.val.length < 253) :
    (Codec.encode o).length = 9 + o.scriptPubKey.code.val.length := by
  change (Codec.encode o.value ++ Codec.encode o.scriptPubKey).length = _
  rw [List.length_append, encode_uint64_length, encode_script_length_lt_253 h]
  omega

/-- An output's length with the scriptPubKey factored out (no size assumption). -/
theorem encode_txout_length_eq (o : TxOut) :
    (Codec.encode o).length = 8 + (Codec.encode o.scriptPubKey).length := by
  change (Codec.encode o.value ++ Codec.encode o.scriptPubKey).length = _
  rw [List.length_append, encode_uint64_length]

/-- Every transaction output is at least 9 bytes (an 8-byte value and a nonempty
script prefix). -/
theorem encode_txout_length_ge (o : TxOut) : 9 ≤ (Codec.encode o).length := by
  rw [encode_txout_length_eq, encode_script_length_eq]
  have := CompactSize.encode_length_ge_one (UInt64.ofNat o.scriptPubKey.code.val.length)
  omega

/-- The byte layout of an output: value, scriptPubKey. -/
theorem encode_txout_eq (o : TxOut) :
    Codec.encode o = Codec.encode o.value ++ Codec.encode o.scriptPubKey := by
  rfl

/-- An output sequence is at least 9 bytes per output. -/
theorem encodeElems_txout_length_ge (xs : List TxOut) :
    9 * xs.length ≤ (encodeElems xs).length := by
  induction xs with
  | nil => simp [encodeElems]
  | cons x xs ih =>
    simp only [encodeElems, List.length_append, List.length_cons]
    have := encode_txout_length_ge x
    omega

end BtcVerified
