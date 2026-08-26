import BtcVerified.Serialize.CompactSize
import BtcVerified.Impl.Packed.Codec
/-!
  # Packed CompactSize

  The packed counterpart of the CompactSize variable-length integer (issue
  #52), mirroring the spec's factoring: one fixed-width marker-payload form
  (`readFixedWidth`/`pushFixedWidth`, shared by the three marker branches)
  and a top-level dispatch over the marker byte. Each mirror carries its
  agreement with the spec form, so the spec's round-trip, canonicality, and
  shortest-form rule apply to every packed run.

  Checked claims:

  * `mapToList_readFixedWidth` / `toList_pushFixedWidth`: the packed
    marker-payload forms agree with `decodeFixedWidth`/`encodeFixedWidth`.
  * `mapToList_readCompactSize` / `toList_pushCompactSize`: the packed
    dispatch agrees with `CompactSize.decode`/`CompactSize.encode`.
-/

namespace BtcVerified.Impl.Packed

open BtcVerified.Serialize BtcVerified.CompactSize

/-- Append the `byteWidth` little-endian payload bytes carrying `n`'s low
bits: the packed mirror of `encodeFixedWidth`. -/
def pushFixedWidth (byteWidth : Nat) (n : UInt64) (acc : ByteArray) : ByteArray :=
  pushBitVecLE byteWidth (n.toBitVec.setWidth (8 * byteWidth)) acc

/-- The packed payload append appends exactly the spec payload. -/
theorem toList_pushFixedWidth (byteWidth : Nat) (n : UInt64) (acc : ByteArray) :
    (pushFixedWidth byteWidth n acc).toList
      = acc.toList ++ encodeFixedWidth byteWidth n :=
  toList_pushBitVecLE byteWidth _ acc

/-- Read a `byteWidth` little-endian payload, rejecting values below
`minValue`: the packed mirror of `decodeFixedWidth`. -/
def readFixedWidth (byteWidth minValue : Nat) (s : ByteSlice) :
    Option (UInt64 × ByteSlice) := do
  let (w, rest) ← readBitVecLE byteWidth s
  guard (minValue ≤ w.toNat)
  return (⟨w.setWidth 64⟩, rest)

/-- The packed payload read, through the abstraction, is the spec's. -/
theorem mapToList_readFixedWidth (byteWidth minValue : Nat) (s : ByteSlice) :
    mapToList (readFixedWidth byteWidth minValue s)
      = decodeFixedWidth byteWidth minValue s.toList := by
  cases hr : readBitVecLE byteWidth s with
  | none =>
    have ht := mapToList_readBitVecLE byteWidth s
    rw [hr, mapToList_none] at ht
    simp [readFixedWidth, decodeFixedWidth, hr, ← ht]
  | some p =>
    obtain ⟨w, rest⟩ := p
    have ht := mapToList_readBitVecLE byteWidth s
    rw [hr, mapToList_some] at ht
    by_cases hg : minValue ≤ w.toNat
    · simp [readFixedWidth, decodeFixedWidth, hr, ← ht, hg, guard]
    · simp [readFixedWidth, decodeFixedWidth, hr, ← ht, hg, guard]

/-- Append a canonical CompactSize encoding: the packed mirror of
`CompactSize.encode`, choosing the same shortest form. -/
def pushCompactSize (n : UInt64) (acc : ByteArray) : ByteArray :=
  if n < 253 then acc.push n.toUInt8
  else if n < 2 ^ 16 then pushFixedWidth 2 n (acc.push 0xFD)
  else if n < 2 ^ 32 then pushFixedWidth 4 n (acc.push 0xFE)
  else pushFixedWidth 8 n (acc.push 0xFF)

/-- The packed CompactSize append appends exactly the spec encoding. -/
theorem toList_pushCompactSize (n : UInt64) (acc : ByteArray) :
    (pushCompactSize n acc).toList = acc.toList ++ CompactSize.encode n := by
  rw [pushCompactSize, CompactSize.encode]
  split_ifs <;>
    simp [toList_pushFixedWidth]

/-- Read a CompactSize value off the front of a slice: the packed mirror of
`CompactSize.decode`, dispatching on the marker byte. -/
def readCompactSize (s : ByteSlice) : Option (UInt64 × ByteSlice) :=
  match s.uncons with
  | none => none
  | some (h, t) =>
    if h < 0xFD then some (h.toUInt64, t)
    else if h = 0xFD then readFixedWidth 2 253 t
    else if h = 0xFE then readFixedWidth 4 (2 ^ 16) t
    else if h = 0xFF then readFixedWidth 8 (2 ^ 32) t
    else none

/-- The packed CompactSize read, through the abstraction, is the spec's. -/
theorem mapToList_readCompactSize (s : ByteSlice) :
    mapToList (readCompactSize s) = CompactSize.decode s.toList := by
  cases hu : s.uncons with
  | none =>
    rw [ByteSlice.toList_of_uncons_none hu]
    simp [readCompactSize, CompactSize.decode, hu]
  | some p =>
    obtain ⟨b, t⟩ := p
    rw [ByteSlice.toList_of_uncons_some hu, readCompactSize, hu]
    simp only [CompactSize.decode]
    split_ifs with h1 h2 h3 h4
    · simp
    · exact mapToList_readFixedWidth 2 253 t
    · exact mapToList_readFixedWidth 4 (2 ^ 16) t
    · exact mapToList_readFixedWidth 8 (2 ^ 32) t
    · simp

end BtcVerified.Impl.Packed
