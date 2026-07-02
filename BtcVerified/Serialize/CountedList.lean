import Mathlib.Data.UInt
import BtcVerified.Serialize.Codec
import BtcVerified.Serialize.CompactSize
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
    Option (CountedList α × List UInt8) :=
  match CompactSize.decode bs with
  | none => none
  | some (count, rest) =>
    match decodeElems count.toNat rest with
    | none => none
    | some (xs, rest') =>
      match CountedList.ofList? xs with
      | none => none
      | some cl => some (cl, rest')

/-- Round-trip: a counted list encodes and decodes back to itself, tail
preserved. -/
theorem decodeCountedList_encodeCountedList {α : Type} [Codec α]
    (cl : CountedList α) (rest : List UInt8) :
    decodeCountedList (encodeCountedList cl ++ rest) = some (cl, rest) := by
  obtain ⟨l, hl⟩ := cl
  unfold encodeCountedList decodeCountedList
  rw [List.append_assoc]
  have hc : (UInt64.ofNat l.length).toNat = l.length := UInt64.toNat_ofNat_of_lt' hl
  simp only [CompactSize.decode_encode, hc, decodeElems_encodeElems,
    CountedList.ofList?_eq_some hl]

/-- Canonicality: an accepted parse consumed exactly the canonical count prefix
followed by the canonical element encodings. -/
theorem decodeCountedList_canonical {α : Type} [Codec α]
    (bs : List UInt8) (cl : CountedList α) (rest : List UInt8)
    (h : decodeCountedList bs = some (cl, rest)) :
    bs = encodeCountedList cl ++ rest := by
  unfold decodeCountedList at h
  cases hcs : CompactSize.decode bs with
  | none => simp [hcs] at h
  | some p =>
    obtain ⟨count, rest0⟩ := p
    simp only [hcs] at h
    cases hln : decodeElems (α := α) count.toNat rest0 with
    | none => simp [hln] at h
    | some q =>
      obtain ⟨xs, rest'⟩ := q
      simp only [hln] at h
      cases hof : CountedList.ofList? xs with
      | none => simp [hof] at h
      | some cl' =>
        simp only [hof, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
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
