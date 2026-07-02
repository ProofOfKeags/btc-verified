import BtcVerified.Serialize.CountedList
/-!
  # The script type

  A `Script` is a Bitcoin Script program as it exists on the wire: raw bytes.
  This module gives programs their own type — a `scriptSig` or `scriptPubKey`
  is a *program*, not an anonymous byte string like a witness item — without
  giving them any internal structure yet.

  Keeping the program text raw is a protocol fact, not a simplification.
  Bitcoin tokenizes a script only at execution time (`GetScriptOp` runs inside
  `EvalScript`); (de)serialization treats every script field as an opaque byte
  vector, and consensus never requires the bytes to tokenize. Mainnet relies
  on this: most current coinbase scriptSigs do not tokenize (pool tags whose
  bytes read as truncated pushes), and an output script that fails to tokenize
  is merely unspendable, not invalid. So tokenization is the first stage of
  the execution layer, where it can fail — deserialization must accept every
  byte string, and does.

  On the wire a script field is CompactSize-length-prefixed, so the program
  bytes are a `CountedList UInt8` and the codec comes by transport
  (`Codec.ofEquiv`) with no hand-written proofs.

  Checked claims:

  * `instCodecScript`: the script codec satisfies round-trip and canonicality,
    inherited from the counted byte list.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- A Bitcoin Script program as it exists on the wire: raw,
CompactSize-length-prefixed bytes. The bytes are uninterpreted here because
that is the protocol's own posture — tokenization happens at execution time
and may fail (an output that fails to tokenize is unspendable, a coinbase
scriptSig is never tokenized at all), so every byte string is a syntactically
valid program text. -/
structure Script where
  /-- The program bytes, uninterpreted at this layer. -/
  code : CountedList UInt8
  deriving DecidableEq

/-- A `Script` is its program bytes. -/
def Script.equivCode : Script ≃ CountedList UInt8 where
  toFun s := s.code
  invFun c := ⟨c⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Serializes a `Script` as its CompactSize-length-prefixed program bytes. -/
instance instCodecScript : Codec Script :=
  Codec.ofEquiv Script.equivCode inferInstance

/-- A short script (program length below 253) encodes to a one-byte length prefix
plus its program bytes. -/
theorem encode_script_length_lt_253 {s : Script} (h : s.code.val.length < 253) :
    (Codec.encode s).length = 1 + s.code.val.length := by
  change (encodeCountedList s.code).length = 1 + s.code.val.length
  unfold encodeCountedList
  rw [List.length_append, encodeElems_uint8_length, CompactSize.encode_length_ofNat_lt_253 h]

/-- The general script length: a CompactSize length prefix plus the program bytes
(no size assumption). -/
theorem encode_script_length_eq (s : Script) :
    (Codec.encode s).length
      = (CompactSize.encode (UInt64.ofNat s.code.val.length)).length + s.code.val.length := by
  change (encodeCountedList s.code).length = _
  unfold encodeCountedList
  rw [List.length_append, encodeElems_uint8_length]

/-- The byte layout of a script: its CompactSize length prefix then its bytes. -/
theorem encode_script_eq (s : Script) :
    Codec.encode s
      = CompactSize.encode (UInt64.ofNat s.code.val.length) ++ s.code.val := by
  change encodeCountedList s.code = _
  unfold encodeCountedList
  rw [encodeElems_uint8_eq]

end BtcVerified
