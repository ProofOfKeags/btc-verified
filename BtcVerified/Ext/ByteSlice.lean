import Std.Data.ByteSlice
import BtcVerified.Ext.ByteArray
/-!
  # `ByteSlice` extensions: the byte-list abstraction

  `Std.Data.ByteSlice` is the zero-copy view of a `ByteArray` region — base
  array, start/stop offsets, and the bounds that make reads total — but it
  ships with no connection to `List UInt8`. These extensions add the
  abstraction the packed codecs (issue #52) state agreement through:
  `toList`, the slice's bytes as the specification's byte type, together
  with the reader operations (`uncons`, `take`, `drop`, all thin wrappers
  over `ByteSlice.slice`) and the lemmas showing each commutes with the
  abstraction. Everything rests on a one-time characterization of `slice`'s
  clamping. Upstreaming candidates.

  Checked claims:

  * `byteArray_slice` / `start_slice` / `stop_slice`: a sub-slice shares
    the base array, and its offsets are the clamped bounds — the complete
    characterization of `ByteSlice.slice`.
  * `toList_eq`: the abstraction is the drop/take window of the base
    array's bytes — the bridge from slice reads to `List` reasoning.
  * `toList_of_uncons_some` / `toList_of_uncons_none`: reading one byte off
    a slice is exactly uncons on its abstraction.
  * `toList_take` / `toList_drop`: sub-slicing commutes with the
    abstraction.
-/

namespace ByteSlice

/-! ## Characterizing `slice` -/

/-- A sub-slice views the same base array. -/
@[simp] theorem byteArray_slice (s : ByteSlice) (a b : Nat) :
    (s.slice a b).byteArray = s.byteArray := by
  unfold ByteSlice.slice
  dsimp only
  split
  · split <;> rfl
  · rfl

/-- A sub-slice starts at the clamped start bound: relative starts past the
requested stop, or past the slice, are pulled back. -/
theorem start_slice (s : ByteSlice) (a b : Nat) :
    (s.slice a b).start = s.start + min (min a s.size) (min b s.size) := by
  have h1 : s.stop ≤ s.byteArray.size := s.stop_le_size_byteArray
  have h2 := s.start_le_stop
  have h3 : s.size = s.stop - s.start := rfl
  unfold ByteSlice.slice
  dsimp only
  split
  · split
    · next h =>
      show s.start + min a s.size = _
      omega
    · next h =>
      show s.start + min b s.size = _
      omega
  · next h => exact absurd (by omega) h

/-- A sub-slice stops at the clamped stop bound. -/
theorem stop_slice (s : ByteSlice) (a b : Nat) :
    (s.slice a b).stop = s.start + min b s.size := by
  have h1 : s.stop ≤ s.byteArray.size := s.stop_le_size_byteArray
  have h2 := s.start_le_stop
  have h3 : s.size = s.stop - s.start := rfl
  unfold ByteSlice.slice
  dsimp only
  split
  · split
    · next h => rfl
    · next h => rfl
  · next h => exact absurd (by omega) h

/-! ## The abstraction into `List UInt8` -/

/-- The slice's bytes as the specification's byte type. This is the
abstraction function the packed codecs state agreement through, and the
runtime materializer for decoded byte contents; it costs the slice's size,
not the base array's. -/
def toList (s : ByteSlice) : List UInt8 :=
  (s.byteArray.extract s.start s.stop).toList

/-- The abstraction is the drop/take window of the base array's bytes. -/
theorem toList_eq (s : ByteSlice) :
    s.toList = (s.byteArray.data.toList.drop s.start).take s.size := by
  rw [toList, ByteArray.toList_eq_data_toList, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop]
  rfl

/-- Viewing a whole byte array abstracts to all of its bytes. -/
@[simp] theorem toList_ofByteArray (bytes : ByteArray) :
    (ByteSlice.ofByteArray bytes).toList = bytes.toList := by
  rw [toList]
  show (bytes.extract 0 bytes.size).toList = _
  rw [ByteArray.extract_zero_size]

/-- A slice abstracts to as many bytes as its size. -/
@[simp] theorem length_toList (s : ByteSlice) : s.toList.length = s.size := by
  have h1 : s.stop ≤ s.byteArray.data.size := s.stop_le_size_byteArray
  have h2 := s.start_le_stop
  have h3 : s.size = s.stop - s.start := rfl
  rw [toList_eq]
  simp only [List.length_take, List.length_drop, Array.length_toList]
  omega

/-! ## Reader operations -/

/-- The sub-slice of the first `n` bytes in view (all of them, if fewer). -/
def take (s : ByteSlice) (n : Nat) : ByteSlice := s.slice 0 n

/-- The view past the first `n` bytes (empty, if there are fewer). -/
def drop (s : ByteSlice) (n : Nat) : ByteSlice := s.slice n s.size

/-- Taking `n` bytes leaves `min n s.size` in view. -/
@[simp] theorem size_take (s : ByteSlice) (n : Nat) :
    (s.take n).size = min n s.size := by
  have hst : (s.slice 0 n).start = s.start := by
    rw [start_slice]
    omega
  show (s.slice 0 n).stop - (s.slice 0 n).start = _
  rw [hst, stop_slice]
  omega

/-- Taking bytes off a slice takes them off its abstraction. -/
@[simp] theorem toList_take (s : ByteSlice) (n : Nat) :
    (s.take n).toList = s.toList.take n := by
  have hst : (s.slice 0 n).start = s.start := by
    rw [start_slice]
    omega
  have hsz : (s.slice 0 n).size = min n s.size := size_take s n
  simp only [take] at hsz ⊢
  rw [toList_eq, toList_eq, byteArray_slice, hst, hsz, List.take_take]

/-- Dropping bytes off a slice drops them off its abstraction. -/
@[simp] theorem toList_drop (s : ByteSlice) (n : Nat) :
    (s.drop n).toList = s.toList.drop n := by
  have h2 := s.start_le_stop
  have h3 : s.size = s.stop - s.start := rfl
  have hst : (s.slice n s.size).start = s.start + min n s.size := by
    rw [start_slice]
    omega
  have hsz : (s.slice n s.size).size = s.size - n := by
    show (s.slice n s.size).stop - (s.slice n s.size).start = _
    rw [hst, stop_slice]
    omega
  simp only [drop]
  rw [toList_eq, toList_eq, byteArray_slice, hst, hsz]
  rcases Nat.le_total n s.size with h | h
  · rw [Nat.min_eq_left h, List.drop_take, List.drop_drop]
  · have hnil : s.toList.length ≤ n := by
      rw [length_toList]
      omega
    rw [← toList_eq, List.drop_eq_nil_of_le hnil]
    refine List.length_eq_zero_iff.mp ?_
    simp only [List.length_take, List.length_drop, Array.length_toList]
    have h1 : s.stop ≤ s.byteArray.data.size := s.stop_le_size_byteArray
    omega

/-- Read one byte off the front of the slice, advancing the view past it.
The base array is untouched — the tail is the same array, one offset
further in. -/
def uncons (s : ByteSlice) : Option (UInt8 × ByteSlice) :=
  if h : 0 < s.size then some (s[0]'h, s.drop 1) else none

/-- A slice with nothing to read abstracts to the empty byte string. -/
theorem toList_of_uncons_none {s : ByteSlice} (h : s.uncons = none) :
    s.toList = [] := by
  rw [uncons] at h
  split at h
  · exact absurd h (by simp)
  · next hns =>
    refine List.length_eq_zero_iff.mp ?_
    rw [length_toList]
    omega

/-- Reading one byte is uncons on the abstraction: the byte read is the
head, and the advanced slice abstracts to the tail. -/
theorem toList_of_uncons_some {s : ByteSlice} {b : UInt8} {t : ByteSlice}
    (h : s.uncons = some (b, t)) : s.toList = b :: t.toList := by
  rw [uncons] at h
  by_cases hpos : 0 < s.size
  · rw [dif_pos hpos] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h1 : s.stop ≤ s.byteArray.data.size := s.stop_le_size_byteArray
    have h2 := s.start_le_stop
    have h3 : s.size = s.stop - s.start := rfl
    have hidx : s.start < s.byteArray.data.toList.length := by
      simp only [Array.length_toList]
      omega
    have hb : s[0]'hpos
        = s.byteArray[s.start]'(by have h4 := s.stop_le_size_byteArray; omega) := rfl
    have htail : (s.drop 1).toList
        = (s.byteArray.data.toList.drop (s.start + 1)).take (s.size - 1) := by
      rw [toList_drop, toList_eq, List.drop_take, List.drop_drop]
    rw [toList_eq, List.drop_eq_getElem_cons hidx,
      show s.size = (s.size - 1) + 1 from by omega, List.take_succ_cons, htail, hb]
    congr 1
  · rw [dif_neg hpos] at h
    exact absurd h (by simp)

end ByteSlice
