import BtcVerified.Ext.ByteArray
/-!
  # Byte slices

  The packed decoders (issue #52) consume a `ByteArray` without copying it: a
  parser's remainder is the same underlying array viewed from a further start
  offset, not a fresh structural tail. `ByteSlice` is that view — a base
  array with start/stop offsets, carrying the bounds that make every in-range
  read total.

  `toList` is the abstraction function into the specification's byte type:
  the slice's bytes as a `List UInt8`. Every agreement theorem between a
  packed codec and its spec codec is stated through it. It doubles as the
  runtime materializer for decoded byte contents (hashes, script bytes),
  costing only the slice's own length.

  Checked claims:

  * `toList_eq`: the abstraction is the drop/take window of the base array's
    bytes — the bridge from slice reads to `List` reasoning.
  * `toList_of_uncons_some` / `toList_of_uncons_none`: reading one byte off a
    slice is exactly uncons on its abstraction.
  * `toList_take` / `toList_drop`: sub-slicing commutes with the abstraction.
-/

namespace BtcVerified.Impl.Packed

/-- A zero-copy view of a contiguous region of a `ByteArray`: the base array
with start/stop offsets. Decoders advance `start`; the base array is shared,
never copied. The bounds make every in-range read total. -/
structure ByteSlice where
  /-- The underlying bytes, shared by every slice into them. -/
  base : ByteArray
  /-- The offset of the first byte in view. -/
  start : Nat
  /-- The offset one past the last byte in view. -/
  stop : Nat
  /-- The view is not inverted. -/
  start_le_stop : start ≤ stop
  /-- The view lies inside the base array. -/
  stop_le_size : stop ≤ base.size

namespace ByteSlice

/-- The whole of a byte array, in view — the slice a decode starts from. -/
def ofByteArray (bytes : ByteArray) : ByteSlice :=
  ⟨bytes, 0, bytes.size, Nat.zero_le _, Nat.le_refl _⟩

/-- How many bytes are in view. -/
def length (s : ByteSlice) : Nat := s.stop - s.start

/-- The slice's bytes as the specification's byte type. This is the
abstraction function every packed/spec agreement is stated through, and the
runtime materializer for decoded byte contents; it costs the slice's length,
not the base array's size. -/
def toList (s : ByteSlice) : List UInt8 :=
  (s.base.extract s.start s.stop).toList

/-- The abstraction is the drop/take window of the base array's bytes. -/
theorem toList_eq (s : ByteSlice) :
    s.toList = (s.base.data.toList.drop s.start).take s.length := by
  rw [toList, ByteArray.toList_eq_data_toList, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, length]

/-- Viewing a whole byte array abstracts to all of its bytes. -/
@[simp] theorem toList_ofByteArray (bytes : ByteArray) :
    (ofByteArray bytes).toList = bytes.toList := by
  rw [toList, ofByteArray, ByteArray.extract_zero_size]

/-- A slice abstracts to as many bytes as its length. -/
@[simp] theorem length_toList (s : ByteSlice) : s.toList.length = s.length := by
  have hsize : s.stop ≤ s.base.data.size := s.stop_le_size
  have hstart := s.start_le_stop
  rw [toList_eq]
  simp only [List.length_take, List.length_drop, Array.length_toList, length]
  omega

/-- Read one byte off the front of the slice, advancing the view past it. The
base array is untouched — the tail is the same array, one offset further in. -/
def uncons (s : ByteSlice) : Option (UInt8 × ByteSlice) :=
  if h : s.start < s.stop then
    some (s.base[s.start]'(Nat.lt_of_lt_of_le h s.stop_le_size),
      ⟨s.base, s.start + 1, s.stop, h, s.stop_le_size⟩)
  else none

/-- A slice with nothing to read abstracts to the empty byte string. -/
theorem toList_of_uncons_none {s : ByteSlice} (h : s.uncons = none) :
    s.toList = [] := by
  rw [uncons] at h
  split at h
  · exact absurd h (by simp)
  · next hns =>
    rw [toList_eq, length, Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hns), List.take_zero]

/-- Reading one byte is uncons on the abstraction: the byte read is the head,
and the advanced slice abstracts to the tail. -/
theorem toList_of_uncons_some {s : ByteSlice} {b : UInt8} {t : ByteSlice}
    (h : s.uncons = some (b, t)) : s.toList = b :: t.toList := by
  rw [uncons] at h
  split at h
  · next hlt =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hsize : s.stop ≤ s.base.data.size := s.stop_le_size
    have hstart : s.start < s.base.data.toList.length := by
      simp only [Array.length_toList]
      omega
    rw [toList_eq, toList_eq, List.drop_eq_getElem_cons hstart]
    simp only [length]
    rw [show s.stop - s.start = (s.stop - (s.start + 1)) + 1 by omega,
      List.take_succ_cons]
    congr 1
  · exact absurd h (by simp)

/-- The sub-slice of the first `n` bytes in view (all of them, if fewer). -/
def take (s : ByteSlice) (n : Nat) : ByteSlice :=
  ⟨s.base, s.start, min (s.start + n) s.stop,
    Nat.le_min.mpr ⟨Nat.le_add_right .., s.start_le_stop⟩,
    Nat.le_trans (Nat.min_le_right ..) s.stop_le_size⟩

/-- The view past the first `n` bytes (empty, if there are fewer). -/
def drop (s : ByteSlice) (n : Nat) : ByteSlice :=
  ⟨s.base, min (s.start + n) s.stop, s.stop, Nat.min_le_right .., s.stop_le_size⟩

/-- Taking `n` bytes leaves `min n s.length` in view. -/
@[simp] theorem length_take (s : ByteSlice) (n : Nat) :
    (s.take n).length = min n s.length := by
  have := s.start_le_stop
  simp only [take, length]
  omega

/-- Taking bytes off a slice takes them off its abstraction. -/
@[simp] theorem toList_take (s : ByteSlice) (n : Nat) :
    (s.take n).toList = s.toList.take n := by
  rw [toList_eq, toList_eq, List.take_take]
  simp only [take, length]
  congr 1
  omega

/-- Dropping bytes off a slice drops them off its abstraction. -/
@[simp] theorem toList_drop (s : ByteSlice) (n : Nat) :
    (s.drop n).toList = s.toList.drop n := by
  have hstart := s.start_le_stop
  rcases Nat.le_total (s.start + n) s.stop with h | h
  · rw [toList_eq, toList_eq]
    simp only [drop, length, Nat.min_eq_left h, List.drop_take, List.drop_drop]
    congr 1
    omega
  · have hnil : s.toList.length ≤ n := by
      rw [length_toList, length]
      omega
    rw [List.drop_eq_nil_of_le hnil]
    refine List.length_eq_zero_iff.mp ?_
    rw [length_toList]
    simp only [drop, length]
    omega

end ByteSlice

/-- The spec-level reading of a packed parse result: keep the value, abstract
the remainder slice to its bytes. The agreement laws state that this reading
of a packed decoder's output is exactly the spec decoder's output. -/
def mapToList {α : Type} (parse : Option (α × ByteSlice)) : Option (α × List UInt8) :=
  parse.map fun p => (p.1, p.2.toList)

/-- A failed packed parse reads as a failed spec parse. -/
@[simp] theorem mapToList_none {α : Type} : mapToList (α := α) none = none := rfl

/-- A successful packed parse reads as its value with the abstracted tail. -/
@[simp] theorem mapToList_some {α : Type} (a : α) (s : ByteSlice) :
    mapToList (some (a, s)) = some (a, s.toList) := rfl

end BtcVerified.Impl.Packed
