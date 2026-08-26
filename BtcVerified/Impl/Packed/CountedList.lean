import BtcVerified.Serialize.CountedList
import BtcVerified.Impl.Packed.CompactSize
import BtcVerified.Impl.Packed.Bytes
/-!
  # Packed CompactSize-prefixed lists

  The packed counterpart of the counted-list codec (issue #52): a packed
  CompactSize count, then the elements encoded back to back through their
  own packed codec. The element sequence mirrors the spec's
  `encodeElems`/`decodeElems` pair, and the value-level smart constructor
  (`CountedList.ofList?`) is shared with the spec decoder, so agreement only
  tracks the byte threading.

  Byte contents — scripts, witness items — are `CountedList UInt8`, and for
  them the generic element walk pays a full codec dispatch per byte. The
  spec's byte-element sequence is the identity on the list
  (`encodeElems_uint8` / `decodeElems_uint8`), so a dedicated
  `CountedList UInt8` instance moves whole byte regions at once; it carries
  the same agreement laws and outranks the generic instance by priority.

  Checked claims:

  * `mapToList_readElems` / `toList_pushElems`: the packed element sequence
    agrees with `decodeElems`/`encodeElems` whenever the element codec
    agrees.
  * `instPackedCodecCountedList`: the packed counted-list codec agrees with
    `instCodecCountedList`, so any packed element codec lifts.
  * `encodeElems_uint8` / `decodeElems_uint8`: the spec's byte-element
    sequence is take/drop on the raw bytes, which grounds the bulk
    `instPackedCodecCountedListBytes` fast path and its agreement.
-/

namespace BtcVerified.Impl.Packed

open BtcVerified.Serialize

/-- Append the encodings of a list of values, in order: the packed mirror of
`encodeElems`. -/
def pushElems {α : Type} [Codec α] [PackedCodec α] : List α → ByteArray → ByteArray
  | [], acc => acc
  | x :: xs, acc => pushElems xs (PackedCodec.encodeInto x acc)

/-- The packed element append appends exactly the spec element encoding. -/
theorem toList_pushElems {α : Type} [Codec α] [PackedCodec α]
    (xs : List α) (acc : ByteArray) :
    (pushElems xs acc).toList = acc.toList ++ encodeElems xs := by
  induction xs generalizing acc with
  | nil => simp [pushElems, encodeElems]
  | cons x xs ih =>
    change (pushElems xs (PackedCodec.encodeInto x acc)).toList = _
    rw [ih, PackedCodec.toList_encodeInto, encodeElems, ← List.append_assoc]

/-- Read exactly `n` consecutive values, threading the slice: the packed
mirror of `decodeElems`. -/
def readElems {α : Type} [Codec α] [PackedCodec α] :
    Nat → ByteSlice → Option (List α × ByteSlice)
  | 0, s => some ([], s)
  | n + 1, s => do
    let (x, s1) ← PackedCodec.decodeSlice s
    let (xs, s2) ← readElems n s1
    return (x :: xs, s2)

/-- The packed element read, through the abstraction, is the spec's. -/
theorem mapToList_readElems {α : Type} [Codec α] [PackedCodec α] :
    ∀ (n : Nat) (s : ByteSlice),
      mapToList (readElems (α := α) n s) = decodeElems (α := α) n s.toList := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    cases hx : PackedCodec.decodeSlice (α := α) s with
    | none =>
      have hs := PackedCodec.mapToList_decodeSlice (α := α) s
      rw [hx, mapToList_none] at hs
      simp [readElems, decodeElems, hx, ← hs]
    | some p =>
      obtain ⟨x, s1⟩ := p
      have hs := PackedCodec.mapToList_decodeSlice (α := α) s
      rw [hx, mapToList_some] at hs
      cases hr : readElems (α := α) n s1 with
      | none =>
        have ht := ih s1
        rw [hr, mapToList_none] at ht
        simp [readElems, decodeElems, hx, hr, ← hs, ← ht]
      | some q =>
        obtain ⟨xs, s2⟩ := q
        have ht := ih s1
        rw [hr, mapToList_some] at ht
        simp [readElems, decodeElems, hx, hr, ← hs, ← ht]

/-- Append a counted list: the packed CompactSize count of its length, then
its elements — the packed mirror of `encodeCountedList`. -/
def pushCountedList {α : Type} [Codec α] [PackedCodec α]
    (cl : CountedList α) (acc : ByteArray) : ByteArray :=
  pushElems cl.val (pushCompactSize (UInt64.ofNat cl.val.length) acc)

/-- Read a counted list: the packed count, that many elements, then the
shared length-bound attachment — the packed mirror of `decodeCountedList`. -/
def readCountedList {α : Type} [Codec α] [PackedCodec α] (s : ByteSlice) :
    Option (CountedList α × ByteSlice) := do
  let (count, s1) ← readCompactSize s
  let (xs, s2) ← readElems count.toNat s1
  let cl ← CountedList.ofList? xs
  return (cl, s2)

/-- The packed counted-list codec: count prefix then elements, agreeing with
`instCodecCountedList`, so any packed element codec lifts to a packed codec
of its counted lists. -/
instance instPackedCodecCountedList {α : Type} [Codec α] [PackedCodec α] :
    PackedCodec (CountedList α) where
  encodeInto := pushCountedList
  decodeSlice := readCountedList
  toList_encodeInto cl acc := by
    change (pushCountedList cl acc).toList = acc.toList ++ encodeCountedList cl
    rw [pushCountedList, encodeCountedList, toList_pushElems, toList_pushCompactSize,
      List.append_assoc]
  mapToList_decodeSlice s := by
    change _ = decodeCountedList s.toList
    cases hc : readCompactSize s with
    | none =>
      have hcs := mapToList_readCompactSize s
      rw [hc, mapToList_none] at hcs
      simp [readCountedList, decodeCountedList, hc, ← hcs]
    | some p =>
      obtain ⟨count, s1⟩ := p
      have hcs := mapToList_readCompactSize s
      rw [hc, mapToList_some] at hcs
      cases hr : readElems (α := α) count.toNat s1 with
      | none =>
        have ht := mapToList_readElems (α := α) count.toNat s1
        rw [hr, mapToList_none] at ht
        simp [readCountedList, decodeCountedList, hc, hr, ← hcs, ← ht]
      | some q =>
        obtain ⟨xs, s2⟩ := q
        have ht := mapToList_readElems (α := α) count.toNat s1
        rw [hr, mapToList_some] at ht
        cases ho : CountedList.ofList? xs with
        | none =>
          simp [readCountedList, decodeCountedList, hc, hr, ho, ← hcs, ← ht]
        | some cl =>
          simp [readCountedList, decodeCountedList, hc, hr, ho, ← hcs, ← ht]

/-! ## The byte-content fast path -/

/-- A byte encodes as itself: the spec's `UInt8` codec emits the one-byte
list. -/
theorem encode_uint8 (b : UInt8) : Codec.encode b = [b] := by
  change encodeBitVecLE 1 b.toBitVec = [b]
  simp [encodeBitVecLE, BitVec.setWidth_eq, UInt8.ofBitVec_toBitVec]

/-- The spec's byte-element sequence encodes a byte list as itself. -/
theorem encodeElems_uint8 (bs : List UInt8) : encodeElems (α := UInt8) bs = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [encodeElems, encode_uint8, ih, List.singleton_append]

/-- The spec's byte-element sequence decodes `n` bytes as take/drop on the
raw input: it succeeds exactly when `n` bytes are present, consuming them
unchanged. -/
theorem decodeElems_uint8 (n : Nat) (bs : List UInt8) :
    decodeElems (α := UInt8) n bs
      = if n ≤ bs.length then some (bs.take n, bs.drop n) else none := by
  induction n generalizing bs with
  | zero => simp [decodeElems]
  | succ n ih =>
    cases bs with
    | nil =>
      have hd : Codec.decode (α := UInt8) [] = none := rfl
      simp [decodeElems, hd]
    | cons b t =>
      have hd : Codec.decode (α := UInt8) (b :: t) = some (b, t) := by
        rw [show b :: t = Codec.encode b ++ t by rw [encode_uint8]; rfl]
        exact Codec.decode_encode b t
      by_cases h : n ≤ t.length
      · simp [decodeElems, hd, ih, h]
      · simp [decodeElems, hd, ih, h]

/-- Read `n` raw bytes off a slice as a list: the bulk mirror of `n`
byte-element decodes. The remainder is zero-copy; only the content bytes
are materialized. -/
def readByteList (n : Nat) (s : ByteSlice) : Option (List UInt8 × ByteSlice) :=
  if n ≤ s.length then some ((s.take n).toList, s.drop n) else none

/-- The bulk byte read, through the abstraction, is the spec's byte-element
sequence. -/
theorem mapToList_readByteList (n : Nat) (s : ByteSlice) :
    mapToList (readByteList n s) = decodeElems (α := UInt8) n s.toList := by
  rw [readByteList, decodeElems_uint8]
  by_cases h : n ≤ s.length
  · rw [if_pos h, if_pos (by simpa using h), mapToList_some]
    simp
  · rw [if_neg h, if_neg (by simpa using h), mapToList_none]

/-- The packed codec for byte contents: a `CountedList UInt8` moves as one
region — count, then a bulk read or append — instead of a codec dispatch
per byte. Agrees with the same spec codec as the generic instance, and
outranks it by priority wherever the elements are bytes. -/
instance (priority := high) instPackedCodecCountedListBytes :
    PackedCodec (CountedList UInt8) where
  encodeInto cl acc :=
    pushBytes cl.val (pushCompactSize (UInt64.ofNat cl.val.length) acc)
  decodeSlice s := do
    let (count, s1) ← readCompactSize s
    let (bytes, s2) ← readByteList count.toNat s1
    let cl ← CountedList.ofList? bytes
    return (cl, s2)
  toList_encodeInto cl acc := by
    change _ = acc.toList ++ encodeCountedList cl
    rw [encodeCountedList, toList_pushBytes, toList_pushCompactSize,
      encodeElems_uint8, List.append_assoc]
  mapToList_decodeSlice s := by
    change _ = decodeCountedList s.toList
    cases hc : readCompactSize s with
    | none =>
      have hcs := mapToList_readCompactSize s
      rw [hc, mapToList_none] at hcs
      simp [decodeCountedList, ← hcs]
    | some p =>
      obtain ⟨count, s1⟩ := p
      have hcs := mapToList_readCompactSize s
      rw [hc, mapToList_some] at hcs
      cases hr : readByteList count.toNat s1 with
      | none =>
        have ht := mapToList_readByteList count.toNat s1
        rw [hr, mapToList_none] at ht
        simp [decodeCountedList, hr, ← hcs, ← ht]
      | some q =>
        obtain ⟨bytes, s2⟩ := q
        have ht := mapToList_readByteList count.toNat s1
        rw [hr, mapToList_some] at ht
        cases ho : CountedList.ofList? bytes with
        | none =>
          simp [decodeCountedList, hr, ho, ← hcs, ← ht]
        | some cl =>
          simp [decodeCountedList, hr, ho, ← hcs, ← ht]

end BtcVerified.Impl.Packed
