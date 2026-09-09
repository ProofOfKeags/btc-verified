import BtcVerified.Serialize.CompactSize
import BtcVerified.Packed.Codec
/-!
  # Packed CompactSize

  The packed counterpart of the CompactSize variable-length integer (issue
  #52), mirroring the spec's factoring: one fixed-width marker-payload form
  (`readFixedWidth`/`pushFixedWidth`, shared by the three marker branches)
  and a top-level dispatch over the marker byte. Each mirror carries its
  agreement with the spec form, so the spec's round-trip, canonicality, and
  shortest-form rule apply to every packed run.

  Checked claims:

  * `abstractParse_readFixedWidth` / `toList_pushFixedWidth`: the packed
    marker-payload forms agree with `decodeFixedWidth`/`encodeFixedWidth`.
  * `abstractParse_readCompactSize` / `toList_pushCompactSize`: the packed
    dispatch agrees with `CompactSize.decode`/`CompactSize.encode`.
-/

namespace BtcVerified.Packed

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
theorem abstractParse_readFixedWidth (byteWidth minValue : Nat) (s : ByteSlice) :
    abstractParse (readFixedWidth byteWidth minValue s)
      = decodeFixedWidth byteWidth minValue s.toList := by
  unfold readFixedWidth decodeFixedWidth
  rw [← abstractParse_readBitVecLE byteWidth s]
  refine abstractParse_bind _ fun w rest => ?_
  dsimp only
  exact abstractParse_bindValue _ fun _ => rfl

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
def readCompactSize (s : ByteSlice) : Option (UInt64 × ByteSlice) := do
  let (h, t) ← s.uncons
  if h < 0xFD then some (h.toUInt64, t)
  else if h = 0xFD then readFixedWidth 2 253 t
  else if h = 0xFE then readFixedWidth 4 (2 ^ 16) t
  else if h = 0xFF then readFixedWidth 8 (2 ^ 32) t
  else none

/-- `CompactSize.decode` restated as a single-byte read followed by the
marker dispatch, so the agreement proof can chain through `decodeByte`. -/
private theorem decode_eq_decodeByte_bind (bs : List UInt8) :
    CompactSize.decode bs = (decodeByte bs).bind fun p =>
      if p.1 < 0xFD then some (p.1.toUInt64, p.2)
      else if p.1 = 0xFD then decodeFixedWidth 2 253 p.2
      else if p.1 = 0xFE then decodeFixedWidth 4 (2 ^ 16) p.2
      else if p.1 = 0xFF then decodeFixedWidth 8 (2 ^ 32) p.2
      else none := by
  cases bs <;> rfl

/-- The packed CompactSize read, through the abstraction, is the spec's. -/
theorem abstractParse_readCompactSize (s : ByteSlice) :
    abstractParse (readCompactSize s) = CompactSize.decode s.toList := by
  unfold readCompactSize
  rw [decode_eq_decodeByte_bind, ← abstractParse_uncons s]
  refine abstractParse_bind _ fun b t => ?_
  dsimp only
  split_ifs <;> first | rfl | apply abstractParse_readFixedWidth

end BtcVerified.Packed
