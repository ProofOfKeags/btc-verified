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

  The three marker forms are *one* idea — a marker byte followed by a
  fixed-width little-endian payload, accepted only when the value is large
  enough that no shorter form would do. That idea is factored into
  `encodeFixedWidth`/`decodeFixedWidth` (working uniformly in `BitVec`/`UInt64`,
  parameterized by the byte width), whose round-trip and canonicality are
  proved once and applied to each marker. So the top-level proofs are a
  dispatch over the markers, not three copies of the same argument.

  The main checked claims are:

  * `decode_encode`: encoding and then decoding returns the original value,
    preserving any following bytes as the unconsumed tail.
  * `encode_length_le`: every canonical CompactSize encoding is at most
    nine bytes.
  * `decode_canonical`: every accepted byte string has a consumed prefix equal
    to `encode n`, which rules out accepted non-canonical encodings.
-/

namespace BtcVerified.CompactSize

open BtcVerified.Serialize

/-- The `byteWidth` little-endian bytes carrying `n`'s low `8 * byteWidth` bits:
the payload that follows a CompactSize marker. -/
def encodeFixedWidth (byteWidth : Nat) (n : UInt64) : List UInt8 :=
  encodeBitVecLE byteWidth (n.toBitVec.setWidth (8 * byteWidth))

/-- A fixed-width payload is exactly `byteWidth` bytes long. -/
theorem encodeFixedWidth_length (byteWidth : Nat) (n : UInt64) :
    (encodeFixedWidth byteWidth n).length = byteWidth :=
  encodeBitVecLE_length byteWidth (n.toBitVec.setWidth (8 * byteWidth))

/-- Decode `byteWidth` little-endian payload bytes, rejecting as non-canonical
any value below `minValue` (the shortest-form minimum for this marker). -/
def decodeFixedWidth (byteWidth minValue : Nat) (bs : List UInt8) :
    Option (UInt64 × List UInt8) := do
  let (w, rest) ← decodeBitVecLE byteWidth bs
  guard (minValue ≤ w.toNat)
  return (⟨w.setWidth 64⟩, rest)

/-- Encoding a value that lies in this form's range
(`minValue ≤ n < 2 ^ (8 * byteWidth)`) as its fixed-width payload and then
decoding returns the value, leaving the trailing bytes as the unconsumed
tail. -/
theorem decodeFixedWidth_encodeFixedWidth (byteWidth minValue : Nat) (n : UInt64)
    (hlo : minValue ≤ n.toNat) (hhi : n.toNat < 2 ^ (8 * byteWidth)) (xs : List UInt8) :
    decodeFixedWidth byteWidth minValue (encodeFixedWidth byteWidth n ++ xs) = some (n, xs) := by
  have hw : (n.toBitVec.setWidth (8 * byteWidth)).toNat = n.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hhi
  simp only [encodeFixedWidth, decodeFixedWidth, decodeBitVecLE_encodeBitVecLE,
    Option.bind_eq_bind, Option.bind_some, hw]
  unfold guard
  rw [if_pos hlo]
  simp [setWidth_setWidth_eq_self hhi, UInt64.ofBitVec_toBitVec]

/-- If the fixed-width decoder accepts `bs` as `n` with tail `rest`, then `n`
lies in this form's range and `bs` is exactly its payload encoding followed by
`rest` — an accepted payload is never a longer form's value in disguise. -/
theorem decodeFixedWidth_canonical (byteWidth minValue : Nat) (hbw : 8 * byteWidth ≤ 64)
    (bs : List UInt8) (n : UInt64) (rest : List UInt8) :
    decodeFixedWidth byteWidth minValue bs = some (n, rest) →
      minValue ≤ n.toNat ∧ n.toNat < 2 ^ (8 * byteWidth) ∧
        bs = encodeFixedWidth byteWidth n ++ rest := by
  intro parses
  unfold decodeFixedWidth at parses
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at parses
  obtain ⟨⟨w, rest'⟩, hd, _, hg, parses⟩ := parses
  dsimp only at hg parses
  unfold guard at hg
  by_cases hw : minValue ≤ w.toNat
  · rw [if_pos hw] at hg
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at parses
    obtain ⟨rfl, rfl⟩ := parses
    have hwlt : w.toNat < 2 ^ (8 * byteWidth) := w.isLt
    have hw64 : w.toNat < 2 ^ 64 := lt_of_lt_of_le hwlt (Nat.pow_le_pow_right (by omega) hbw)
    have hval : (⟨w.setWidth 64⟩ : UInt64).toNat = w.toNat := by
      rw [UInt64.toNat_ofBitVec, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hw64
    refine ⟨?_, ?_, ?_⟩
    · rw [hval]; exact hw
    · rw [hval]; exact hwlt
    · have hbs := decodeBitVecLE_canonical byteWidth bs w rest' hd
      have hb : encodeFixedWidth byteWidth (⟨w.setWidth 64⟩ : UInt64)
          = encodeBitVecLE byteWidth w := by
        unfold encodeFixedWidth
        rw [UInt64.toBitVec_ofBitVec, setWidth_setWidth_eq_self hw64]
      rw [hbs, hb]
  · rw [if_neg hw] at hg
    simp at hg

/-- Canonically encodes a `UInt64` as Bitcoin CompactSize bytes.

The branch conditions implement the shortest-form rule: marker bytes are used
only when the value cannot fit in a shorter CompactSize form. -/
def encode (n : UInt64) : List UInt8 :=
  if n < 253 then [n.toUInt8]
  else if n < 2 ^ 16 then 0xFD :: encodeFixedWidth 2 n
  else if n < 2 ^ 32 then 0xFE :: encodeFixedWidth 4 n
  else 0xFF :: encodeFixedWidth 8 n

/-- Decodes a CompactSize value from the front of a byte list.

On success, the result contains the decoded value and the unconsumed tail.
Non-canonical forms (a value encoded in a longer-than-necessary marker) and
incomplete inputs return `none`. -/
def decode (bs : List UInt8) : Option (UInt64 × List UInt8) :=
  match bs with
  | [] => none
  | h :: t =>
    if h < 0xFD then some (h.toUInt64, t)
    else if h = 0xFD then decodeFixedWidth 2 253 t
    else if h = 0xFE then decodeFixedWidth 4 (2 ^ 16) t
    else if h = 0xFF then decodeFixedWidth 8 (2 ^ 32) t
    else none

private theorem decode_FD (t : List UInt8) :
    decode (0xFD :: t) = decodeFixedWidth 2 253 t := rfl

private theorem decode_FE (t : List UInt8) :
    decode (0xFE :: t) = decodeFixedWidth 4 (2 ^ 16) t := rfl

private theorem decode_FF (t : List UInt8) :
    decode (0xFF :: t) = decodeFixedWidth 8 (2 ^ 32) t := rfl

/-- Round-trip correctness for canonical encodings.

Encoding `n` and appending arbitrary trailing bytes always decodes back to
`n`, leaving exactly those trailing bytes as the unconsumed tail. -/
theorem decode_encode (n : UInt64) (xs : List UInt8) : decode (encode n ++ xs) = some (n, xs) := by
  unfold encode
  split_ifs with h1 h2 h3
  · have hb : n.toUInt8 < (0xFD : UInt8) := by bv_decide
    have hv : n.toUInt8.toUInt64 = n := by
      narrow_widen (show n < 2 ^ 8 from UInt64.lt_trans h1 (by decide))
    simp [decode, hb, hv]
  · rw [List.cons_append, decode_FD]
    exact decodeFixedWidth_encodeFixedWidth 2 253 n
      (by simpa using UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h1))
      (by simpa using UInt64.lt_iff_toNat_lt.mp h2) xs
  · rw [List.cons_append, decode_FE]
    exact decodeFixedWidth_encodeFixedWidth 4 (2 ^ 16) n
      (by simpa using UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h2))
      (by simpa using UInt64.lt_iff_toNat_lt.mp h3) xs
  · rw [List.cons_append, decode_FF]
    exact decodeFixedWidth_encodeFixedWidth 8 (2 ^ 32) n
      (by simpa using UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h3))
      n.toBitVec.isLt xs

/-- CompactSize encodings are bounded by the one marker byte plus eight data bytes. -/
theorem encode_length_le (n : UInt64) : (encode n).length ≤ 9 := by
  unfold encode
  split_ifs <;> simp only [List.length_cons, List.length_nil, encodeFixedWidth_length] <;> omega

/-- The first byte of a CompactSize encoding is `0x00` only when the value is
zero. Equivalently, a non-zero count never begins with `0x00` — which is exactly
what lets the SegWit marker (a reserved zero input count) be told apart from a
real legacy input count. -/
theorem encode_head (n : UInt64) :
    ∃ b t, encode n = b :: t ∧ (n ≠ 0 → b ≠ 0) := by
  unfold encode
  split_ifs with h1 h2 h3
  · exact ⟨n.toUInt8, [], rfl, fun hn => by bv_decide⟩
  · exact ⟨0xFD, encodeFixedWidth 2 n, rfl, fun _ => by decide⟩
  · exact ⟨0xFE, encodeFixedWidth 4 n, rfl, fun _ => by decide⟩
  · exact ⟨0xFF, encodeFixedWidth 8 n, rfl, fun _ => by decide⟩

/-- Canonicality of accepted parses.

If `decode` accepts `bs` as value `n` with tail `rest`, then `bs` is exactly
the canonical encoding of `n` followed by `rest`. Equivalently, every
accepted consumed prefix is the shortest CompactSize representation. -/
theorem decode_canonical (bs : List UInt8) (n : UInt64) (rest : List UInt8) :
    decode bs = some (n, rest) → bs = encode n ++ rest := by
  intro parses
  match bs with
  | [] => simp [decode] at parses
  | h :: t =>
    simp only [decode] at parses
    split_ifs at parses with c1 c2 c3 c4
    · simp only [Option.some.injEq, Prod.mk.injEq] at parses
      obtain ⟨rfl, rfl⟩ := parses
      have h253 : h.toUInt64 < 253 := by simpa [UInt8.lt_iff_toNat_lt] using c1
      simp [encode, h253]
    · subst c2
      obtain ⟨hlo, hhi, rfl⟩ := decodeFixedWidth_canonical 2 253 (by decide) t n rest parses
      have hn1 : ¬ n < 253 := UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr (by simpa using hlo))
      have hn2 : n < 2 ^ 16 := UInt64.lt_iff_toNat_lt.mpr (by simpa using hhi)
      simp [encode, hn1, hn2]
    · subst c3
      obtain ⟨hlo, hhi, rfl⟩ := decodeFixedWidth_canonical 4 (2 ^ 16) (by decide) t n rest parses
      have hn1 : ¬ n < 2 ^ 16 := UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr (by simpa using hlo))
      have hn2 : n < 2 ^ 32 := UInt64.lt_iff_toNat_lt.mpr (by simpa using hhi)
      have hn0 : ¬ n < 253 := fun hc => hn1 (UInt64.lt_trans hc (by decide))
      simp [encode, hn0, hn1, hn2]
    · subst c4
      obtain ⟨hlo, hhi, rfl⟩ := decodeFixedWidth_canonical 8 (2 ^ 32) (by decide) t n rest parses
      have hn1 : ¬ n < 2 ^ 32 := UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr (by simpa using hlo))
      have hn2 : ¬ n < 2 ^ 16 := fun hc => hn1 (UInt64.lt_trans hc (by decide))
      have hn0 : ¬ n < 253 := fun hc => hn1 (UInt64.lt_trans hc (by decide))
      simp [encode, hn0, hn2, hn1]

/-- The CompactSize encoding packaged as a `Codec UInt64`.

This is a worked codec, not the registered `Codec UInt64` instance: the
canonical full-width `Codec UInt64` is the fixed 8-byte little-endian form,
whereas CompactSize is the distinguished variable-length encoding used for
counts. -/
abbrev compactSizeCodec : Codec UInt64 where
  encode := encode
  decode := decode
  decode_encode := decode_encode
  decode_canonical := decode_canonical

end BtcVerified.CompactSize
