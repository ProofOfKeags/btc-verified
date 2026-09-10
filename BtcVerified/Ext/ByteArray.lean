/-!
  # `ByteArray` extensions: `toList` through `data`

  Core defines `ByteArray.toList` by its own accumulator loop and proves
  almost nothing about it, while `ByteArray.data` carries the full `Array`
  lemma ecosystem. The bridge `toList_eq_data_toList` lets a statement about
  a byte array's bytes be phrased through the readable `toList` and
  discharged through `data`; the corollaries cover the constructors the
  packed codecs use (`push`, `List.toByteArray`). Upstreaming candidates.
-/

namespace ByteArray

private theorem toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  generalize hfuel : bs.size - i = fuel
  induction fuel generalizing i r with
  | zero =>
    rw [ByteArray.toList.loop, if_neg (by omega),
      List.drop_eq_nil_of_le (by simpa using Nat.le_of_sub_eq_zero hfuel),
      List.append_nil]
  | succ fuel ih =>
    have hi : i < bs.size := by omega
    have hi' : i < bs.data.toList.length := by simpa using hi
    rw [ByteArray.toList.loop, if_pos hi, ih (i + 1) _ (by omega),
      List.drop_eq_getElem_cons hi']
    simp [ByteArray.get!, hi]
    rfl

/-- The bytes of a `ByteArray`, as produced by `toList`, are the bytes of its
underlying array. -/
theorem toList_eq_data_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop]
  simp

/-- Pushing a byte appends it to the bytes. -/
@[simp] theorem toList_push (bs : ByteArray) (b : UInt8) :
    (bs.push b).toList = bs.toList ++ [b] := by
  simp [toList_eq_data_toList, ByteArray.data_push]

/-- A byte list packed into a `ByteArray` reads back as itself. -/
@[simp] theorem _root_.List.toList_toByteArray (l : List UInt8) :
    l.toByteArray.toList = l := by
  rw [toList_eq_data_toList, List.data_toByteArray]

end ByteArray
