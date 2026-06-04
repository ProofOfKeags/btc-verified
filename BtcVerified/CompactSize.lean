import Std.Tactic.BVDecide
import Mathlib.Tactic.SplitIfs
import BtcVerified.Serialize.Codec
import BtcVerified.Serialize.WidthCast
/-!
  # Bitcoin CompactSize encoding

  This module formalizes Bitcoin's CompactSize variable-length integer
  encoding over `UInt64`. CompactSize is the count prefix used throughout
  Bitcoin serialization (number of inputs, outputs, transactions, …), so it is
  a small but load-bearing leaf.

  The encoder chooses one of four canonical forms:

  * `n < 253`: one byte, `[n]`
  * `n < 2^16`: marker `0xFD` followed by a little-endian `UInt16`
  * `n < 2^32`: marker `0xFE` followed by a little-endian `UInt32`
  * otherwise: marker `0xFF` followed by a little-endian `UInt64`

  The fixed-width payloads are not open-coded here: they are the little-endian
  `Codec` instances from `BtcVerified.Serialize`, so this leaf sits on the same
  byte-level serialization spine as the rest of the block model and only adds
  CompactSize's own concern — marker dispatch and shortest-form (minimality).

  The decoder rejects non-canonical encodings, so values must appear in the
  shortest applicable form. The main checked claims are:

  * `decode_encode`: encoding and then decoding returns the original value,
    preserving any following bytes as the unconsumed tail.
  * `encode_length_le`: every canonical CompactSize encoding is at most
    nine bytes.
  * `decode_canonical`: every accepted byte string has a consumed prefix equal
    to `encode n`, which rules out accepted non-canonical encodings.
-/

namespace BtcVerified.CompactSize

open BtcVerified.Serialize

private theorem uint16_to_uint64_lt_two_pow_16 (n : UInt16) : n.toUInt64 < 2^16 := by
  simpa [UInt64.lt_iff_toNat_lt] using UInt16.toNat_lt n

private theorem uint32_to_uint64_lt_two_pow_32 (n : UInt32) : n.toUInt64 < 2^32 := by
  simpa [UInt64.lt_iff_toNat_lt] using UInt32.toNat_lt n

private theorem not_to_uint16_lt_253 {n : UInt64}
    (h253 : 253 ≤ n) (h16 : n < 2^16) : 0xFD ≤ n.toUInt16 := by
  apply UInt16.toUInt64_le.mp
  have e : n.toUInt16.toUInt64 = n := by narrow_widen h16
  simpa [e] using h253

private theorem not_to_uint32_lt_two_pow_16 {n : UInt64}
    (h16 : ¬ n < 2^16) (h32 : n < 2^32) :
    ¬ n.toUInt32 < 2^16 := by
  intro h
  exact h16 (by
    have h64 := UInt32.toUInt64_lt.mpr h
    have e : n.toUInt32.toUInt64 = n := by narrow_widen h32
    simpa [e] using h64)

/--
  Canonically encodes a `UInt64` as Bitcoin CompactSize bytes.

  The branch conditions implement the shortest-form rule: marker bytes are used
  only when the value cannot fit in a shorter CompactSize form. The fixed-width
  payloads are the little-endian `Codec` encodings from `BtcVerified.Serialize`.
-/
def encode (n : UInt64) : List UInt8 :=
  if n < 253 then
    [n.toUInt8]
  else if n < 2 ^ 16 then
    0xFD :: Codec.encode n.toUInt16
  else if n < 2 ^ 32 then
    0xFE :: Codec.encode n.toUInt32
  else
    0xFF :: Codec.encode n

/--
  Decodes a CompactSize value from the front of a byte list.

  On success, the result contains the decoded value and the unconsumed tail.
  Non-canonical forms (a value encoded in a longer-than-necessary marker) and
  incomplete inputs return `none`.
-/
def decode (bs : List UInt8) : Option (UInt64 × List UInt8) :=
  match bs with
  | [] => none
  | h :: t =>
    if h < 0xFD then
      some (h.toUInt64, t)
    else if h = 0xFD then
      match Codec.decode (α := UInt16) t with
      | none => none
      | some (w, rest) => if w < 0xFD then none else some (w.toUInt64, rest)
    else if h = 0xFE then
      match Codec.decode (α := UInt32) t with
      | none => none
      | some (w, rest) => if w < 2 ^ 16 then none else some (w.toUInt64, rest)
    else if h = 0xFF then
      match Codec.decode (α := UInt64) t with
      | none => none
      | some (w, rest) => if w < 2 ^ 32 then none else some (w, rest)
    else
      none

/--
  Round-trip correctness for canonical encodings.

  Encoding `n` and appending arbitrary trailing bytes always decodes back to
  `n`, leaving exactly those trailing bytes as the unconsumed tail.
-/
theorem decode_encode (n : UInt64) (xs : List UInt8) : decode (encode n ++ xs) = some (n, xs) := by
  unfold encode
  split_ifs with h1 h2 h3
  · have hb : n.toUInt8 < (0xFD : UInt8) := by bv_decide
    have hv : n.toUInt8.toUInt64 = n := by
      narrow_widen (show n < 2 ^ 8 from UInt64.lt_trans h1 (by decide))
    simp [decode, hb, hv]
  · have hge : ¬ n.toUInt16 < (0xFD : UInt16) :=
      UInt16.not_lt.mpr (not_to_uint16_lt_253 (UInt64.not_lt.mp h1) h2)
    have hv : n.toUInt16.toUInt64 = n := by narrow_widen h2
    simp [decode, Codec.decode_encode, hge, hv]
  · have hge : ¬ n.toUInt32 < (2 ^ 16 : UInt32) := not_to_uint32_lt_two_pow_16 h2 h3
    have hv : n.toUInt32.toUInt64 = n := by narrow_widen h3
    simp [decode, Codec.decode_encode, hge, hv]
  · have hge : ¬ n < (2 ^ 32 : UInt64) := h3
    simp [decode, Codec.decode_encode, hge]

/-- CompactSize encodings are bounded by the one marker byte plus eight data bytes. -/
theorem encode_length_le (n : UInt64) : (encode n).length ≤ 9 := by
  have e16 : (Codec.encode n.toUInt16).length = 2 := encodeBitVecLE_length 2 n.toUInt16.toBitVec
  have e32 : (Codec.encode n.toUInt32).length = 4 := encodeBitVecLE_length 4 n.toUInt32.toBitVec
  have e64 : (Codec.encode n).length = 8 := encodeBitVecLE_length 8 n.toBitVec
  unfold encode
  split_ifs <;>
    simp only [List.length_cons, List.length_nil, e16, e32, e64] <;>
    omega

/--
  Canonicality of accepted parses.

  If `decode` accepts `bs` as value `n` with tail `rest`, then `bs` is exactly
  the canonical encoding of `n` followed by `rest`. Equivalently, every
  accepted consumed prefix is the shortest CompactSize representation.
-/
theorem decode_canonical (bs : List UInt8) (n : UInt64) (rest : List UInt8) :
    decode bs = some (n, rest) → bs = encode n ++ rest := by
  intro parses
  match bs with
  | [] => simp [decode] at parses
  | h :: t =>
    simp only [decode] at parses
    split_ifs at parses with c1 c2 c3 c4
    · -- h < 0xFD
      simp only [Option.some.injEq, Prod.mk.injEq] at parses
      obtain ⟨rfl, rfl⟩ := parses
      have h253 : h.toUInt64 < 253 := by simpa [UInt8.lt_iff_toNat_lt] using c1
      simp [encode, h253]
    · -- h = 0xFD
      cases hdec : Codec.decode (α := UInt16) t with
      | none => simp [hdec] at parses
      | some wr =>
        obtain ⟨w, rest'⟩ := wr
        simp only [hdec] at parses
        by_cases cw : w < 0xFD
        · simp [cw] at parses
        · rw [if_neg cw] at parses
          simp only [Option.some.injEq, Prod.mk.injEq] at parses
          obtain ⟨rfl, rfl⟩ := parses
          have ht := Codec.decode_canonical t w rest' hdec
          have h16 : w.toUInt64 < 2 ^ 16 := uint16_to_uint64_lt_two_pow_16 w
          have h253 : ¬ w.toUInt64 < 253 := by
            have hle : (253 : UInt64) ≤ w.toUInt64 := by
              simpa using UInt16.toUInt64_le.mpr (UInt16.not_lt.mp cw)
            exact UInt64.not_lt.mpr hle
          have hn16 : w.toUInt64.toUInt16 = w := by simp [UInt16.toUInt16_toUInt64]
          subst c2
          simp [encode, h253, h16, hn16, ht]
    · -- h = 0xFE
      cases hdec : Codec.decode (α := UInt32) t with
      | none => simp [hdec] at parses
      | some wr =>
        obtain ⟨w, rest'⟩ := wr
        simp only [hdec] at parses
        by_cases cw : w < 2 ^ 16
        · simp [cw] at parses
        · rw [if_neg cw] at parses
          simp only [Option.some.injEq, Prod.mk.injEq] at parses
          obtain ⟨rfl, rfl⟩ := parses
          have ht := Codec.decode_canonical t w rest' hdec
          have h32 : w.toUInt64 < 2 ^ 32 := uint32_to_uint64_lt_two_pow_32 w
          have h16 : ¬ w.toUInt64 < 2 ^ 16 := by
            have hle : (2 ^ 16 : UInt64) ≤ w.toUInt64 := by
              simpa using UInt32.toUInt64_le.mpr (UInt32.not_lt.mp cw)
            exact UInt64.not_lt.mpr hle
          have h253 : ¬ w.toUInt64 < 253 :=
            UInt64.not_lt.mpr (UInt64.le_trans (by decide) (UInt64.not_lt.mp h16))
          have hn32 : w.toUInt64.toUInt32 = w := by simp [UInt32.toUInt32_toUInt64]
          subst c3
          simp [encode, h253, h16, h32, hn32, ht]
    · -- h = 0xFF
      cases hdec : Codec.decode (α := UInt64) t with
      | none => simp [hdec] at parses
      | some wr =>
        obtain ⟨w, rest'⟩ := wr
        simp only [hdec] at parses
        by_cases cw : w < 2 ^ 32
        · simp [cw] at parses
        · rw [if_neg cw] at parses
          simp only [Option.some.injEq, Prod.mk.injEq] at parses
          obtain ⟨rfl, rfl⟩ := parses
          have ht := Codec.decode_canonical t w rest' hdec
          have h16 : ¬ w < 2 ^ 16 :=
            UInt64.not_lt.mpr (UInt64.le_trans (by decide) (UInt64.not_lt.mp cw))
          have h253 : ¬ w < 253 :=
            UInt64.not_lt.mpr (UInt64.le_trans (by decide) (UInt64.not_lt.mp cw))
          subst c4
          simp [encode, h253, h16, cw, ht]

/--
  The CompactSize encoding packaged as a `Codec UInt64`.

  This is a worked codec, not the registered `Codec UInt64` instance: the
  canonical full-width `Codec UInt64` is the fixed 8-byte little-endian form,
  whereas CompactSize is the distinguished variable-length encoding used for
  counts.
-/
abbrev compactSizeCodec : Codec UInt64 where
  encode := encode
  decode := decode
  decode_encode := decode_encode
  decode_canonical := decode_canonical

end BtcVerified.CompactSize
