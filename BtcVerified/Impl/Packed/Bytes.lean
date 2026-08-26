import BtcVerified.Serialize.Bytes
import BtcVerified.Impl.Packed.Codec
/-!
  # Packed width-indexed byte strings

  The packed counterpart of the `Bytes n` codec (issue #52). Decoding takes
  the width off the front of the slice — the remainder stays zero-copy, and
  only the `n` bytes of the value itself are materialized into the
  specification representation. Encoding appends the value's bytes onto the
  output buffer one push at a time, which the runtime performs in place on
  an unshared buffer.

  Checked claims:

  * `abstractParse_readBytes` / `toList_pushBytes`: the packed forms agree with
    `decodeBytes` and the identity encoder, packaged as
    `instPackedCodecBytes` — which, at width 32, is the packed `Hash256`
    codec.
-/

namespace BtcVerified.Impl.Packed

open BtcVerified.Serialize

/-- Append a byte list onto the output buffer: the builder for raw byte
contents (hashes, script bytes, witness items). -/
def pushBytes (bs : List UInt8) (acc : ByteArray) : ByteArray :=
  bs.foldl ByteArray.push acc

/-- Appending a byte list appends exactly those bytes. -/
theorem toList_pushBytes (bs : List UInt8) (acc : ByteArray) :
    (pushBytes bs acc).toList = acc.toList ++ bs := by
  induction bs generalizing acc with
  | nil => simp [pushBytes]
  | cons b bs ih =>
    change (pushBytes bs (acc.push b)).toList = _
    rw [ih, ByteArray.toList_push, List.append_assoc, List.singleton_append]

/-- Read exactly `n` bytes off the front of a slice: the packed mirror of
`decodeBytes`. The value's bytes are materialized; the remainder slice is
zero-copy. -/
def readBytes (n : Nat) (s : ByteSlice) : Option (Bytes n × ByteSlice) :=
  if h : n ≤ s.size then
    some (⟨(s.take n).toList, by
      rw [ByteSlice.length_toList, ByteSlice.size_take, Nat.min_eq_left h]⟩,
      s.drop n)
  else none

/-- The packed width read, through the abstraction, is the spec's. -/
theorem abstractParse_readBytes (n : Nat) (s : ByteSlice) :
    abstractParse (readBytes n s) = decodeBytes n s.toList := by
  rw [readBytes, decodeBytes]
  by_cases h : n ≤ s.size
  · rw [dif_pos h, dif_pos (by rw [ByteSlice.length_toList]; exact h), abstractParse_some]
    simp [ByteSlice.toList_take, ByteSlice.toList_drop]
  · rw [dif_neg h, dif_neg (by rw [ByteSlice.length_toList]; exact h), abstractParse_none]

/-- The packed codec for width-indexed bytes, agreeing with
`instCodecBytes n`. At width 32 this is the packed `Hash256` codec. -/
instance instPackedCodecBytes (n : Nat) : PackedCodec (Bytes n) where
  encodeInto bs acc := pushBytes bs.1 acc
  decodeSlice := readBytes n
  toList_encodeInto bs acc := toList_pushBytes bs.1 acc
  abstractParse_decodeSlice := abstractParse_readBytes n

end BtcVerified.Impl.Packed
