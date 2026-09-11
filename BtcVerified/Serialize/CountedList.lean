import Mathlib.Data.UInt
import BtcVerified.Serialize.Codec
import BtcVerified.Serialize.CompactSize
import BtcVerified.Serialize.Bytes
/-!
  # CompactSize-prefixed lists

  Every variable-length Bitcoin field — scripts, the input/output lists, a
  witness stack — is serialized the same way: a CompactSize count prefix,
  followed by the contents back to back. This module captures that one shape
  once, as a `Codec` for a length-bounded list.

  The bound lives in the type. A `CountedList α` is a `List α` whose length fits
  in a `UInt64` — exactly what a CompactSize count can address. This is a pure
  serialization-layer property: nothing behind a CompactSize prefix can be
  longer than the prefix is able to count. (It is *not* a consensus limit; real
  scripts and vectors are far smaller still, but those caps are downstream of
  the block-size limit and have no place here.) Putting the bound in the type
  keeps the round-trip law unconditional: there is no out-of-range list to break
  it on.

  Checked claims:

  * `decodeCountedList_encodeCountedList`: a counted list round-trips, tail
    preserved.
  * `decodeCountedList_canonical`: an accepted parse consumed exactly the
    canonical encoding — the canonical count prefix followed by the canonical
    element encodings.

  Both laws are packaged as `instCodecCountedList : Codec (CountedList α)`, so a
  script (`CountedList UInt8`) or a vector of structures (`CountedList TxIn`)
  serializes by composition like any other field.

  ## Packed codec

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

  * `abstractParse_readElems` / `toList_pushElems`: the packed element sequence
    agrees with `decodeElems`/`encodeElems` whenever the element codec
    agrees.
  * `instPackedCodecCountedList`: the packed counted-list codec agrees with
    `instCodecCountedList`, so any packed element codec lifts.
  * `encodeElems_uint8` / `decodeElems_uint8`: the spec's byte-element
    sequence is take/drop on the raw bytes, which grounds the bulk
    `instPackedCodecCountedListBytes` fast path and its agreement.
-/

namespace BtcVerified.Serialize

/-- A list short enough for a CompactSize count to address: its length fits in a
`UInt64`. The bound is a serialization-layer fact — a sequence carried behind a
CompactSize prefix cannot be longer than that prefix can count. -/
abbrev CountedList (α : Type) := { l : List α // l.length < 2 ^ 64 }

/-- Wrap a list as a `CountedList` when its length is in CompactSize range. The
decoder uses this to attach the length bound to a freshly parsed list; on real
input the check always succeeds, since the count it parsed is itself a
`UInt64`. -/
def CountedList.ofList? {α : Type} (l : List α) : Option (CountedList α) :=
  if h : l.length < 2 ^ 64 then some ⟨l, h⟩ else none

/-- `ofList?` accepts any list already known to be in range. -/
theorem CountedList.ofList?_eq_some {α : Type} {l : List α} (h : l.length < 2 ^ 64) :
    CountedList.ofList? l = some ⟨l, h⟩ := by
  simp only [CountedList.ofList?, dif_pos h]

/-- An accepted `ofList?` returns exactly the list it was given. -/
theorem CountedList.val_of_ofList? {α : Type} {l : List α} {cl : CountedList α}
    (h : CountedList.ofList? l = some cl) : cl.val = l := by
  unfold CountedList.ofList? at h
  split at h
  · simp only [Option.some.injEq] at h; rw [← h]
  · exact absurd h (by simp)

/-! ## Element sequences

  A counted list is a count prefix followed by its elements encoded back to
  back. The element sequence — encode-all / decode-exactly-`n` — is its own
  small concern, proved here independently of the count.
-/

/-- Concatenate the encodings of a list of values, in order. -/
def encodeElems {α : Type} [Codec α] : List α → List UInt8
  | [] => []
  | x :: xs => Codec.encode x ++ encodeElems xs

/-- Decode exactly `n` consecutive values, threading the unconsumed tail. -/
def decodeElems {α : Type} [Codec α] : Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (x, rest) ← Codec.decode (α := α) bs
    let (xs, rest') ← decodeElems n rest
    return (x :: xs, rest')

/-- Decoding exactly `n` elements yields exactly `n` of them. -/
theorem decodeElems_length {α : Type} [Codec α] (n : Nat) (bs : List UInt8)
    (xs : List α) (rest : List UInt8) (h : decodeElems n bs = some (xs, rest)) :
    xs.length = n := by
  induction n generalizing bs xs rest with
  | zero =>
    simp only [decodeElems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; rfl
  | succ n ih =>
    simp only [decodeElems, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨x, r1⟩, hd, ⟨xs', r2⟩, hd2, rfl, rfl⟩ := h
    simp only [List.length_cons]
    rw [ih r1 xs' r2 hd2]

/-- Round-trip for the element sequence: encoding a list and decoding exactly its
length returns it, tail preserved. -/
theorem decodeElems_encodeElems {α : Type} [Codec α] (xs : List α) (rest : List UInt8) :
    decodeElems xs.length (encodeElems xs ++ rest) = some (xs, rest) := by
  induction xs generalizing rest with
  | nil => rfl
  | cons x xs ih =>
    simp only [encodeElems, List.append_assoc, decodeElems, Option.bind_eq_bind,
      Codec.decode_encode, Option.bind_some, ih, Option.pure_def]

/-- Canonicality for the element sequence: an accepted parse of `n` elements
consumed exactly their canonical encodings. -/
theorem decodeElems_canonical {α : Type} [Codec α] (n : Nat) (bs : List UInt8)
    (xs : List α) (rest : List UInt8) (h : decodeElems n bs = some (xs, rest)) :
    bs = encodeElems xs ++ rest := by
  induction n generalizing bs xs rest with
  | zero =>
    simp only [decodeElems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | succ n ih =>
    simp only [decodeElems, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨x, r1⟩, hd, ⟨xs', r2⟩, hd2, rfl, rfl⟩ := h
    have e1 := Codec.decode_canonical bs x r1 hd
    have e2 := ih r1 xs' r2 hd2
    rw [e1, e2, encodeElems, List.append_assoc]

/-! ## The counted-list codec -/

/-- Encode a counted list: the CompactSize count of its length, then its elements
encoded back to back. -/
def encodeCountedList {α : Type} [Codec α] (cl : CountedList α) : List UInt8 :=
  CompactSize.encode (UInt64.ofNat cl.val.length) ++ encodeElems cl.val

/-- Decode a counted list: read the CompactSize count, decode that many elements,
then attach the length bound. -/
def decodeCountedList {α : Type} [Codec α] (bs : List UInt8) :
    Option (CountedList α × List UInt8) := do
  let (count, rest) ← CompactSize.decode bs
  let (xs, rest') ← decodeElems count.toNat rest
  let cl ← CountedList.ofList? xs
  return (cl, rest')

/-- Round-trip: a counted list encodes and decodes back to itself, tail
preserved. -/
theorem decodeCountedList_encodeCountedList {α : Type} [Codec α]
    (cl : CountedList α) (rest : List UInt8) :
    decodeCountedList (encodeCountedList cl ++ rest) = some (cl, rest) := by
  obtain ⟨l, hl⟩ := cl
  unfold encodeCountedList decodeCountedList
  rw [List.append_assoc]
  have hc : (UInt64.ofNat l.length).toNat = l.length := UInt64.toNat_ofNat_of_lt' hl
  simp only [Option.bind_eq_bind, CompactSize.decode_encode, Option.bind_some, hc,
    decodeElems_encodeElems, CountedList.ofList?_eq_some hl, Option.pure_def]

/-- Canonicality: an accepted parse consumed exactly the canonical count prefix
followed by the canonical element encodings. -/
theorem decodeCountedList_canonical {α : Type} [Codec α]
    (bs : List UInt8) (cl : CountedList α) (rest : List UInt8)
    (h : decodeCountedList bs = some (cl, rest)) :
    bs = encodeCountedList cl ++ rest := by
  unfold decodeCountedList at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨count, rest0⟩, hcs, ⟨xs, rest'⟩, hln, cl', hof, rfl, rfl⟩ := h
  have hcv : cl'.val = xs := CountedList.val_of_ofList? hof
  have ecs := CompactSize.decode_canonical bs count rest0 hcs
  have eel := decodeElems_canonical count.toNat rest0 xs rest' hln
  have hlen : xs.length = count.toNat := decodeElems_length count.toNat rest0 xs rest' hln
  have hcnt : count = UInt64.ofNat xs.length := by
    rw [hlen, UInt64.ofNat_toNat]
  unfold encodeCountedList
  rw [hcv, ecs, eel, hcnt, List.append_assoc]

/-- The codec for a CompactSize-prefixed list: a count prefix followed by the
elements. Both laws come from the count codec (`CompactSize`) and the element
sequence, so any `Codec α` lifts to a `Codec (CountedList α)`. -/
instance instCodecCountedList {α : Type} [Codec α] : Codec (CountedList α) where
  encode := encodeCountedList
  decode := decodeCountedList
  decode_encode := decodeCountedList_encodeCountedList
  decode_canonical := decodeCountedList_canonical

end BtcVerified.Serialize

/-! ## Packed codec -/

namespace BtcVerified.Packed

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
theorem abstractParse_readElems {α : Type} [Codec α] [PackedCodec α] :
    ∀ (n : Nat) (s : ByteSlice),
      abstractParse (readElems (α := α) n s) = decodeElems (α := α) n s.toList := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp only [readElems, decodeElems]
    rw [← PackedCodec.abstractParse_decodeSlice (α := α) s]
    refine abstractParse_bind _ fun x s1 => ?_
    dsimp only
    rw [← ih s1]
    exact abstractParse_bind _ fun xs s2 => rfl

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
  abstractParse_decodeSlice s := by
    change _ = decodeCountedList s.toList
    unfold readCountedList decodeCountedList
    rw [← abstractParse_readCompactSize s]
    refine abstractParse_bind _ fun count s1 => ?_
    dsimp only
    rw [← abstractParse_readElems (α := α) count.toNat s1]
    refine abstractParse_bind _ fun xs s2 => ?_
    dsimp only
    exact abstractParse_bindValue _ fun cl => rfl

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
  if n ≤ s.size then some ((s.take n).toList, s.drop n) else none

/-- The bulk byte read, through the abstraction, is the spec's byte-element
sequence. -/
theorem abstractParse_readByteList (n : Nat) (s : ByteSlice) :
    abstractParse (readByteList n s) = decodeElems (α := UInt8) n s.toList := by
  rw [readByteList, decodeElems_uint8]
  by_cases h : n ≤ s.size
  · rw [if_pos h, if_pos (by simpa using h), abstractParse_some]
    simp
  · rw [if_neg h, if_neg (by simpa using h), abstractParse_none]

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
  abstractParse_decodeSlice s := by
    change _ = decodeCountedList s.toList
    unfold decodeCountedList
    rw [← abstractParse_readCompactSize s]
    refine abstractParse_bind _ fun count s1 => ?_
    dsimp only
    rw [← abstractParse_readByteList count.toNat s1]
    refine abstractParse_bind _ fun bytes s2 => ?_
    dsimp only
    exact abstractParse_bindValue _ fun cl => rfl

end BtcVerified.Packed
