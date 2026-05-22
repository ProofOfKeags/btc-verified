import Std.Tactic.BVDecide
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ApplyAt
import Batteries.Tactic.Init
/-!
  # Bitcoin CompactSize encoding

  This module formalizes Bitcoin's CompactSize variable-length integer
  encoding over `UInt64`. CompactSize appears throughout Bitcoin
  serialization, so this is a small but useful first leaf in a larger verified
  Bitcoin protocol library.

  The encoder chooses one of four canonical forms:

  * `n < 253`: one byte, `[n]`
  * `n < 2^16`: marker `0xFD` followed by a little-endian `UInt16`
  * `n < 2^32`: marker `0xFE` followed by a little-endian `UInt32`
  * otherwise: marker `0xFF` followed by a little-endian `UInt64`

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

/-- Encodes a `UInt16` in the two little-endian bytes used by CompactSize. -/
def encode_u16_le (n : UInt16) : List UInt8 := [n.toUInt8, (n >>> 8).toUInt8]

/-- Decodes two little-endian bytes into a `UInt16`. -/
def decode_u16_le (b0 b1 : UInt8) : UInt16 := (b1.toUInt16 <<< 8) + b0.toUInt16

/-- Decoding two bytes and encoding the result returns the original bytes. -/
theorem encode_decode_u16_le (b0 b1 : UInt8) : encode_u16_le (decode_u16_le b0 b1) = [b0, b1] := by
  simp [encode_u16_le, decode_u16_le]
  bv_decide

/-- Encoding and decoding a `UInt16` little-endian word returns the word. -/
theorem decode_encode_u16_le (w : UInt16) :
    decode_u16_le w.toUInt8 (w >>> 8).toUInt8 = w := by
  simp [decode_u16_le]
  bv_decide

/-- Encodes a `UInt32` as two little-endian `UInt16` chunks. -/
def encode_u32_le (n : UInt32) : List UInt8 :=
  encode_u16_le n.toUInt16 ++ encode_u16_le (n >>> 16).toUInt16

/-- Decodes two little-endian `UInt16` chunks into a `UInt32`. -/
def decode_u32_le (w0 w1 : UInt16) : UInt32 := (w1.toUInt32 <<< 16) + w0.toUInt32

/-- Decoding two chunks and encoding the result returns the original chunks. -/
theorem encode_decode_u32_le (w0 w1 : UInt16) :
    encode_u32_le (decode_u32_le w0 w1) = encode_u16_le w0 ++ encode_u16_le w1 := by
  simp [encode_u32_le, decode_u32_le, encode_u16_le]
  bv_decide

/-- Encoding and decoding a `UInt32` little-endian word returns the word. -/
theorem decode_encode_u32_le (d : UInt32) :
    decode_u32_le d.toUInt16 (d >>> 16).toUInt16 = d := by
  simp [decode_u32_le]
  bv_decide

/-- Encodes a `UInt64` as two little-endian `UInt32` chunks. -/
def encode_u64_le (n : UInt64) : List UInt8 :=
  encode_u32_le n.toUInt32 ++ encode_u32_le (n >>> 32).toUInt32

/-- Decodes two little-endian `UInt32` chunks into a `UInt64`. -/
def decode_u64_le (d0 d1 : UInt32) : UInt64 := (d1.toUInt64 <<< 32) + d0.toUInt64

/-- Decoding two chunks and encoding the result returns the original chunks. -/
theorem encode_decode_u64_le (d0 d1 : UInt32) :
    encode_u64_le (decode_u64_le d0 d1) = encode_u32_le d0 ++ encode_u32_le d1 := by
  simp [decode_u64_le, encode_u64_le, encode_u32_le, encode_u16_le]
  bv_decide

/-- Encoding and decoding a `UInt64` little-endian word returns the word. -/
theorem decode_encode_u64_le (q : UInt64) :
    decode_u64_le q.toUInt32 (q >>> 32).toUInt32 = q := by
  simp [decode_u64_le]
  bv_decide

/--
  Canonically encodes a `UInt64` as Bitcoin CompactSize bytes.

  The branch conditions implement the shortest-form rule: marker bytes are used
  only when the value cannot fit in a shorter CompactSize form.
-/
def encode (n : UInt64) : List UInt8 :=
  if n < 253 then
    [n.toUInt8]
  else if n < 2^16 then
    0xFD :: encode_u16_le n.toUInt16
  else if n < 2^32 then
    0xFE :: encode_u32_le n.toUInt32
  else
    0xFF :: encode_u64_le n

/--
  Decodes a CompactSize value from the front of a byte list.

  On success, the result contains the decoded value and the unconsumed tail.
  Non-canonical forms and incomplete inputs return `none`.
-/
def decode (bs : List UInt8) : Option (UInt64 × List UInt8) :=
  match bs with
  | [] => none
  | h :: t =>
    if h < 0xFD then
      some (h.toUInt64, t)
    else if h == 0xFD then
      match t with
      | b0 :: b1 :: rest =>
        let n := decode_u16_le b0 b1
        if n < 0xFD then none
        else some (n.toUInt64, rest)
      | _ => none
    else if h == 0xFE then
      match t with
      | b0 :: b1 :: b2 :: b3 :: rest =>
        let w0 := decode_u16_le b0 b1
        let w1 := decode_u16_le b2 b3
        let dw := decode_u32_le w0 w1
        if dw < 2^16 then none
        else some (dw.toUInt64, rest)
      | _ => none
    else if h == 0xFF then
      match t with
      | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
        let w0 := decode_u16_le b0 b1
        let w1 := decode_u16_le b2 b3
        let w2 := decode_u16_le b4 b5
        let w3 := decode_u16_le b6 b7
        let d0 := decode_u32_le w0 w1
        let d1 := decode_u32_le w2 w3
        let qw := decode_u64_le d0 d1
        if qw < 2^32 then none
        else some (qw, rest)
      | _ => none
    else
      none

private theorem toUInt8_toUInt64_eq_of_lt {n : UInt64} (h : n < 2^8) :
    n.toUInt8.toUInt64 = n := by
  simpa using UInt64.mod_eq_of_lt h

private theorem toUInt16_toUInt64_eq_of_lt {n : UInt64} (h : n < 2^16) :
    n.toUInt16.toUInt64 = n := by
  simpa using UInt64.mod_eq_of_lt h

private theorem toUInt32_toUInt64_eq_of_lt {n : UInt64} (h : n < 2^32) :
    n.toUInt32.toUInt64 = n := by
  simpa using UInt64.mod_eq_of_lt h

private theorem uint16_toUInt64_lt_two_pow_16 (n : UInt16) : n.toUInt64 < 2^16 := by
  simpa [UInt64.lt_iff_toNat_lt] using UInt16.toNat_lt n

private theorem uint32_toUInt64_lt_two_pow_32 (n : UInt32) : n.toUInt64 < 2^32 := by
  simpa [UInt64.lt_iff_toNat_lt] using UInt32.toNat_lt n

private theorem not_toUInt16_lt_253 {n : UInt64}
    (h253 : 253 ≤ n) (h16 : n < 2^16) : 0xFD ≤ n.toUInt16 := by
  apply UInt16.toUInt64_le.mp
  simpa [toUInt16_toUInt64_eq_of_lt h16] using h253

private theorem not_toUInt32_lt_two_pow_16 {n : UInt64}
    (h16 : ¬ n < 2^16) (h32 : n < 2^32) :
    ¬ n.toUInt32 < 2^16 := by
  intro h
  exact h16 (by
    have h64 := UInt32.toUInt64_lt.mpr h
    simpa [toUInt32_toUInt64_eq_of_lt h32] using h64)

/--
  Round-trip correctness for canonical encodings.

  Encoding `n` and appending arbitrary trailing bytes always decodes back to
  `n`, leaving exactly those trailing bytes as the unconsumed tail.
-/
theorem decode_encode (n : UInt64) (xs : List UInt8) : decode (encode n ++ xs) = some (n, xs) := by
  have u8_u32_trans_expand : ∀ (x : UInt32), x.toUInt8 = x.toUInt16.toUInt8 := by bv_decide
  have u8_u64_trans_expand : ∀ (x : UInt64), x.toUInt8 = x.toUInt32.toUInt16.toUInt8 := by bv_decide
  have u16_u64_trans_expand : ∀ (x : UInt64), x.toUInt16 = x.toUInt32.toUInt16 := by bv_decide
  unfold encode decode
  split_ifs with h1 h2 h3
  · simp [List.cons_append, List.nil_append,
      show n.toUInt8 < (0xFD : UInt8) by bv_decide,
      toUInt8_toUInt64_eq_of_lt (UInt64.lt_trans h1 (by decide))]
  · rw [List.cons_append]
    simp
    unfold encode_u16_le
    simp only [List.cons_append, List.nil_append]
    rw [decode_encode_u16_le]
    simp
    constructor
    · apply not_toUInt16_lt_253
      · exact (UInt64.not_lt.mp h1)
      · exact h2
    · exact toUInt16_toUInt64_eq_of_lt h2
  · rw [List.cons_append]
    simp [encode_u32_le, encode_u16_le]
    repeat rw [u8_u32_trans_expand, u8_u64_trans_expand, u16_u64_trans_expand]
    repeat rw [decode_encode_u16_le]
    repeat rw [decode_encode_u32_le]
    simp
    exact ⟨UInt32.not_lt.mp (not_toUInt32_lt_two_pow_16 h2 h3),
      toUInt32_toUInt64_eq_of_lt h3⟩
  · rw [List.cons_append]
    simp [encode_u64_le, encode_u32_le, encode_u16_le]
    repeat rw [u8_u32_trans_expand, u8_u64_trans_expand, u16_u64_trans_expand]
    repeat rw [decode_encode_u16_le]
    repeat rw [decode_encode_u32_le]
    repeat rw [decode_encode_u64_le]
    exact ⟨UInt64.not_lt.mp h3, rfl⟩

/-- CompactSize encodings are bounded by the one marker byte plus eight data bytes. -/
theorem encode_length_le (n : UInt64) :
    (encode n).length ≤ 9 := by
  unfold encode
  split_ifs <;> simp [encode_u16_le, encode_u32_le, encode_u64_le]

/--
  Canonicality of accepted parses.

  If `decode` accepts `bs` as value `n` with tail `rest`, then `bs` is exactly
  the canonical encoding of `n` followed by `rest`. Equivalently, every
  accepted consumed prefix is the shortest CompactSize representation.
-/
theorem decode_canonical (bs : List UInt8) (n : UInt64) (rest : List UInt8) :
    decode bs = some (n, rest) →
    bs = encode n ++ rest := by
  intro parses
  unfold decode at parses
  match bs with
  | [] => simp at parses
  | hd :: tl =>
    simp at parses
    split_ifs at parses with one three five nine
    · obtain ⟨rfl, rfl⟩ := parses
      simp [encode, show hd.toUInt64 < 0xFD by simpa [UInt8.lt_iff_toNat_lt] using one]
    · split at parses
      · next b0 b1 rest' =>
          simp at parses
          obtain ⟨ge_253, pre, rfl⟩ := parses
          subst three
          have h253 : ¬ n < 253 := UInt64.not_lt.mpr (by
            simpa [pre] using (UInt16.toUInt64_le.mpr ge_253))
          have h16 : n < 2^16 := by
            simpa [pre] using uint16_toUInt64_lt_two_pow_16 (decode_u16_le b0 b1)
          have hn16 : n.toUInt16 = decode_u16_le b0 b1 := by
            symm
            simpa [UInt16.toUInt16_toUInt64] using congrArg UInt64.toUInt16 pre
          simp [encode, h253, h16, hn16, encode_decode_u16_le]
      · next => contradiction
    · split at parses
      · next b0 b1 b2 b3 rest' =>
          simp at parses
          obtain ⟨ge16, pre, rfl⟩ := parses
          subst five
          let x := decode_u32_le (decode_u16_le b0 b1) (decode_u16_le b2 b3)
          change (2^16 : UInt32) ≤ x at ge16
          change x.toUInt64 = n at pre
          have le16 : 2^16 ≤ n := by
            simpa [pre] using (UInt32.toUInt64_le.mpr ge16)
          have h253 : ¬ n < 253 := UInt64.not_lt.mpr (UInt64.le_trans (by decide) le16)
          have h16 : ¬ n < 2^16 := UInt64.not_lt.mpr le16
          have h32 : n < 2^32 := by
            simpa [pre] using uint32_toUInt64_lt_two_pow_32 x
          have hn32 : n.toUInt32 = x := by
            symm
            simpa [UInt32.toUInt32_toUInt64] using congrArg UInt64.toUInt32 pre
          simp [encode, h253, h16, h32, hn32, x, encode_decode_u32_le, encode_decode_u16_le]
      · next => contradiction
    · split at parses
      · next b0 b1 b2 b3 b4 b5 b6 b7 rest' =>
          simp at parses
          obtain ⟨ge32, pre, rfl⟩ := parses
          subst nine
          let x := decode_u64_le
            (decode_u32_le (decode_u16_le b0 b1) (decode_u16_le b2 b3))
            (decode_u32_le (decode_u16_le b4 b5) (decode_u16_le b6 b7))
          change 2^32 ≤ x at ge32
          change x = n at pre
          have hx253 : ¬ x < 253 := UInt64.not_lt.mpr (UInt64.le_trans (by decide) ge32)
          have hx16 : ¬ x < 2^16 := UInt64.not_lt.mpr (UInt64.le_trans (by decide) ge32)
          have hx32 : ¬ x < 2^32 := UInt64.not_lt.mpr ge32
          simp [encode, ←pre, hx253, hx16, hx32, x, encode_decode_u64_le,
            encode_decode_u32_le, encode_decode_u16_le]
      · next => contradiction

end BtcVerified.CompactSize
