import BtcVerified.Serialize.Codec
/-!
  # Width-indexed byte strings

  Some Bitcoin fields are uninterpreted byte strings whose width is part of
  their wire format. `Bytes n` records that width in the type while retaining
  the repository's specification-level `List UInt8` representation. The
  checked constructors are the boundary from untrusted variable-length bytes;
  after one succeeds, downstream definitions cannot forget the width.

  The codec consumes exactly `n` bytes. Its round-trip and canonicality laws
  make width-indexed byte strings available as a primitive for larger codecs.

  Checked claims:

  * each checked constructor is characterized by its exact acceptance condition
    and returned byte list;
  * reversal preserves width, is involutive, and exchanges left-oriented
    padding and truncation with right-oriented operations on the reversed input;
  * padding and truncation success depend only on input width, not direction;
  * successful padding has the stated padding region and boundary byte, and
    same-side truncation back to the original width recovers the input;
  * for either direction, exactly one list constructor succeeds: padding when
    the input is short, exact conversion when widths agree, or truncation when
    the input is long;
  * `instCodecBytes`: width-indexed bytes round-trip and every accepted parse
    consumes exactly their canonical `n`-byte encoding.
-/

namespace BtcVerified

/-- A byte string whose width is fixed at `n`. -/
abbrev Bytes (n : Nat) := { bytes : List UInt8 // bytes.length = n }

/-- The underlying bytes, in their original order. -/
@[reducible] def Bytes.bytes {n : Nat} (bs : Bytes n) : List UInt8 := bs.1

/-- Reverse byte order while preserving width. -/
def Bytes.reverse {n : Nat} (bs : Bytes n) : Bytes n :=
  ⟨bs.1.reverse, by simpa only [List.length_reverse] using bs.2⟩

/-- Reversal acts on the underlying byte list. -/
@[simp] theorem Bytes.val_reverse {n : Nat} (bs : Bytes n) :
    bs.reverse.val = bs.val.reverse := rfl

/-- Reversing a width-indexed byte string twice returns the original value. -/
@[simp] theorem Bytes.reverse_reverse {n : Nat} (bs : Bytes n) :
    bs.reverse.reverse = bs := by
  apply Subtype.ext
  simp [Bytes.reverse]

/-- Refine a list when it has exactly the required width. -/
def Bytes.ofListExact? {n : Nat} (bs : List UInt8) : Option (Bytes n) :=
  if h : bs.length = n then some ⟨bs, h⟩ else none

/-- Exact conversion succeeds with `out` precisely when the width agrees and
`out` contains the original bytes. -/
theorem Bytes.ofListExact?_eq_some_iff {n : Nat} (bs : List UInt8) (out : Bytes n) :
    Bytes.ofListExact? bs = some out ↔ bs.length = n ∧ out.val = bs := by
  by_cases h : bs.length = n
  · constructor
    · intro hout
      simp only [Bytes.ofListExact?, dif_pos h, Option.some.injEq] at hout
      exact ⟨h, (congrArg Subtype.val hout).symm⟩
    · rintro ⟨_, hout⟩
      simp only [Bytes.ofListExact?, dif_pos h, Option.some.injEq]
      apply Subtype.ext
      exact hout.symm
  · simp [Bytes.ofListExact?, h]

/-- Exact conversion succeeds exactly at the required width. -/
@[simp] theorem Bytes.ofListExact?_isSome_iff {n : Nat} (bs : List UInt8) :
    (Bytes.ofListExact? (n := n) bs).isSome ↔ bs.length = n := by
  by_cases h : bs.length = n <;> simp [Bytes.ofListExact?, h]

/-- Exact conversion rejects exactly the lists of the wrong width. -/
@[simp] theorem Bytes.ofListExact?_eq_none_iff {n : Nat} (bs : List UInt8) :
    Bytes.ofListExact? (n := n) bs = none ↔ bs.length ≠ n := by
  by_cases h : bs.length = n <;> simp [Bytes.ofListExact?, h]

/-- Refining the underlying list of width-indexed bytes recovers the original value. -/
@[simp] theorem Bytes.ofListExact?_val {n : Nat} (bs : Bytes n) :
    Bytes.ofListExact? bs.val = some bs := by
  simp [Bytes.ofListExact?, bs.property]

/-- Exact conversion commutes with reversal. -/
theorem Bytes.ofListExact?_map_reverse {n : Nat} (bs : List UInt8) :
    (Bytes.ofListExact? (n := n) bs).map Bytes.reverse =
      Bytes.ofListExact? (n := n) bs.reverse := by
  by_cases h : bs.length = n <;> simp [Bytes.ofListExact?, Bytes.reverse, h]

/-- Pad a list on the left to the required width. Succeeds only when the input
is strictly shorter; the padding byte is explicit. -/
def Bytes.ofListPadLeft? {n : Nat} (padding : UInt8) (bs : List UInt8) :
    Option (Bytes n) :=
  if h : bs.length < n then
    some ⟨List.replicate (n - bs.length) padding ++ bs, by simp; omega⟩
  else none

/-- Pad a list on the right to the required width. Succeeds only when the input
is strictly shorter; the padding byte is explicit. -/
def Bytes.ofListPadRight? {n : Nat} (padding : UInt8) (bs : List UInt8) :
    Option (Bytes n) :=
  if h : bs.length < n then
    some ⟨bs ++ List.replicate (n - bs.length) padding, by simp; omega⟩
  else none

/-- Left padding succeeds with `out` precisely when the input is short and
`out` is the required padding prefix followed by the original bytes. -/
theorem Bytes.ofListPadLeft?_eq_some_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) (out : Bytes n) :
    Bytes.ofListPadLeft? padding bs = some out ↔
      bs.length < n ∧
        out.val = List.replicate (n - bs.length) padding ++ bs := by
  by_cases h : bs.length < n
  · constructor
    · intro hout
      simp only [Bytes.ofListPadLeft?, dif_pos h, Option.some.injEq] at hout
      exact ⟨h, (congrArg Subtype.val hout).symm⟩
    · rintro ⟨_, hout⟩
      simp only [Bytes.ofListPadLeft?, dif_pos h, Option.some.injEq]
      apply Subtype.ext
      exact hout.symm
  · simp [Bytes.ofListPadLeft?, h]

/-- Right padding succeeds with `out` precisely when the input is short and
`out` is the original bytes followed by the required padding suffix. -/
theorem Bytes.ofListPadRight?_eq_some_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) (out : Bytes n) :
    Bytes.ofListPadRight? padding bs = some out ↔
      bs.length < n ∧
        out.val = bs ++ List.replicate (n - bs.length) padding := by
  by_cases h : bs.length < n
  · constructor
    · intro hout
      simp only [Bytes.ofListPadRight?, dif_pos h, Option.some.injEq] at hout
      exact ⟨h, (congrArg Subtype.val hout).symm⟩
    · rintro ⟨_, hout⟩
      simp only [Bytes.ofListPadRight?, dif_pos h, Option.some.injEq]
      apply Subtype.ext
      exact hout.symm
  · simp [Bytes.ofListPadRight?, h]

/-- Left padding succeeds exactly for inputs shorter than the target width. -/
@[simp] theorem Bytes.ofListPadLeft?_isSome_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) :
    (Bytes.ofListPadLeft? (n := n) padding bs).isSome ↔ bs.length < n := by
  simp [Bytes.ofListPadLeft?]

/-- Right padding succeeds exactly for inputs shorter than the target width. -/
@[simp] theorem Bytes.ofListPadRight?_isSome_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) :
    (Bytes.ofListPadRight? (n := n) padding bs).isSome ↔ bs.length < n := by
  simp [Bytes.ofListPadRight?]

/-- Left padding rejects exactly the inputs at least as wide as the target. -/
@[simp] theorem Bytes.ofListPadLeft?_eq_none_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) :
    Bytes.ofListPadLeft? (n := n) padding bs = none ↔ n ≤ bs.length := by
  simp [Bytes.ofListPadLeft?, Nat.not_lt]

/-- Right padding rejects exactly the inputs at least as wide as the target. -/
@[simp] theorem Bytes.ofListPadRight?_eq_none_iff {n : Nat} (padding : UInt8)
    (bs : List UInt8) :
    Bytes.ofListPadRight? (n := n) padding bs = none ↔ n ≤ bs.length := by
  simp [Bytes.ofListPadRight?, Nat.not_lt]

/-- A successful left padding consists of exactly the inserted padding prefix
followed by the original input. -/
theorem Bytes.parts_of_ofListPadLeft? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadLeft? padding bs = some out) :
    out.val.take (n - bs.length) = List.replicate (n - bs.length) padding ∧
      out.val.drop (n - bs.length) = bs := by
  obtain ⟨_, hout⟩ := (Bytes.ofListPadLeft?_eq_some_iff padding bs out).mp h
  simp [hout]

/-- A successful right padding consists of the original input followed by
exactly the inserted padding suffix. -/
theorem Bytes.parts_of_ofListPadRight? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadRight? padding bs = some out) :
    out.val.take bs.length = bs ∧
      out.val.drop bs.length = List.replicate (n - bs.length) padding := by
  obtain ⟨_, hout⟩ := (Bytes.ofListPadRight?_eq_some_iff padding bs out).mp h
  simp [hout]

/-- Successful left padding places the padding byte first. -/
theorem Bytes.head?_of_ofListPadLeft? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadLeft? padding bs = some out) :
    out.val.head? = some padding := by
  obtain ⟨hlen, hout⟩ := (Bytes.ofListPadLeft?_eq_some_iff padding bs out).mp h
  have hne : n - bs.length ≠ 0 := by omega
  simp [hout, List.head?_replicate, hne]

/-- Successful right padding places the padding byte last. -/
theorem Bytes.getLast?_of_ofListPadRight? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadRight? padding bs = some out) :
    out.val.getLast? = some padding := by
  obtain ⟨hlen, hout⟩ := (Bytes.ofListPadRight?_eq_some_iff padding bs out).mp h
  have hne : n - bs.length ≠ 0 := by omega
  simp [hout, List.getLast?_replicate, hne]

/-- Reversing a left-padded result is right padding of the reversed input. -/
theorem Bytes.ofListPadLeft?_map_reverse {n : Nat} (padding : UInt8) (bs : List UInt8) :
    (Bytes.ofListPadLeft? (n := n) padding bs).map Bytes.reverse =
      Bytes.ofListPadRight? (n := n) padding bs.reverse := by
  by_cases h : bs.length < n
  · simp [Bytes.ofListPadLeft?, Bytes.ofListPadRight?, Bytes.reverse, h]
  · simp [Bytes.ofListPadLeft?, Bytes.ofListPadRight?, h]

/-- Truncate a list on the left to the required width: drop its prefix and keep
the rightmost `n` bytes. Succeeds only when the input is strictly longer. -/
def Bytes.ofListTruncateLeft? {n : Nat} (bs : List UInt8) : Option (Bytes n) :=
  if h : n < bs.length then
    some ⟨bs.drop (bs.length - n), by rw [List.length_drop]; omega⟩
  else none

/-- Truncate a list on the right to the required width: drop its suffix and
keep the leftmost `n` bytes. Succeeds only when the input is strictly longer. -/
def Bytes.ofListTruncateRight? {n : Nat} (bs : List UInt8) : Option (Bytes n) :=
  if h : n < bs.length then
    some ⟨bs.take n, by rw [List.length_take]; omega⟩
  else none

/-- Left truncation succeeds with `out` precisely when the input is long and
`out` contains its rightmost `n` bytes. -/
theorem Bytes.ofListTruncateLeft?_eq_some_iff {n : Nat} (bs : List UInt8)
    (out : Bytes n) :
    Bytes.ofListTruncateLeft? bs = some out ↔
      n < bs.length ∧ out.val = bs.drop (bs.length - n) := by
  by_cases h : n < bs.length
  · constructor
    · intro hout
      simp only [Bytes.ofListTruncateLeft?, dif_pos h, Option.some.injEq] at hout
      exact ⟨h, (congrArg Subtype.val hout).symm⟩
    · rintro ⟨_, hout⟩
      simp only [Bytes.ofListTruncateLeft?, dif_pos h, Option.some.injEq]
      apply Subtype.ext
      exact hout.symm
  · simp [Bytes.ofListTruncateLeft?, h]

/-- Right truncation succeeds with `out` precisely when the input is long and
`out` contains its leftmost `n` bytes. -/
theorem Bytes.ofListTruncateRight?_eq_some_iff {n : Nat} (bs : List UInt8)
    (out : Bytes n) :
    Bytes.ofListTruncateRight? bs = some out ↔
      n < bs.length ∧ out.val = bs.take n := by
  by_cases h : n < bs.length
  · constructor
    · intro hout
      simp only [Bytes.ofListTruncateRight?, dif_pos h, Option.some.injEq] at hout
      exact ⟨h, (congrArg Subtype.val hout).symm⟩
    · rintro ⟨_, hout⟩
      simp only [Bytes.ofListTruncateRight?, dif_pos h, Option.some.injEq]
      apply Subtype.ext
      exact hout.symm
  · simp [Bytes.ofListTruncateRight?, h]

/-- Left truncation succeeds exactly for inputs longer than the target width. -/
@[simp] theorem Bytes.ofListTruncateLeft?_isSome_iff {n : Nat} (bs : List UInt8) :
    (Bytes.ofListTruncateLeft? (n := n) bs).isSome ↔ n < bs.length := by
  simp [Bytes.ofListTruncateLeft?]

/-- Right truncation succeeds exactly for inputs longer than the target width. -/
@[simp] theorem Bytes.ofListTruncateRight?_isSome_iff {n : Nat} (bs : List UInt8) :
    (Bytes.ofListTruncateRight? (n := n) bs).isSome ↔ n < bs.length := by
  simp [Bytes.ofListTruncateRight?]

/-- Left truncation rejects exactly the inputs no longer than the target. -/
@[simp] theorem Bytes.ofListTruncateLeft?_eq_none_iff {n : Nat} (bs : List UInt8) :
    Bytes.ofListTruncateLeft? (n := n) bs = none ↔ bs.length ≤ n := by
  simp [Bytes.ofListTruncateLeft?, Nat.not_lt]

/-- Right truncation rejects exactly the inputs no longer than the target. -/
@[simp] theorem Bytes.ofListTruncateRight?_eq_none_iff {n : Nat} (bs : List UInt8) :
    Bytes.ofListTruncateRight? (n := n) bs = none ↔ bs.length ≤ n := by
  simp [Bytes.ofListTruncateRight?, Nat.not_lt]

/-- Reversing a left-truncated result is right truncation of the reversed input. -/
theorem Bytes.ofListTruncateLeft?_map_reverse {n : Nat} (bs : List UInt8) :
    (Bytes.ofListTruncateLeft? (n := n) bs).map Bytes.reverse =
      Bytes.ofListTruncateRight? (n := n) bs.reverse := by
  by_cases h : n < bs.length
  · simp [Bytes.ofListTruncateLeft?, Bytes.ofListTruncateRight?, Bytes.reverse, h,
      List.reverse_drop]
    omega
  · simp [Bytes.ofListTruncateLeft?, Bytes.ofListTruncateRight?, h]

/-- Truncating a successful left padding back to the input width recovers the
exact conversion of the original input. -/
theorem Bytes.ofListTruncateLeft?_of_ofListPadLeft? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadLeft? padding bs = some out) :
    Bytes.ofListTruncateLeft? (n := bs.length) out.val =
      Bytes.ofListExact? (n := bs.length) bs := by
  obtain ⟨hlen, hout⟩ := (Bytes.ofListPadLeft?_eq_some_iff padding bs out).mp h
  rw [hout]
  have hpad : 0 < n - bs.length := by omega
  simp [Bytes.ofListTruncateLeft?, Bytes.ofListExact?, hpad]

/-- Truncating a successful right padding back to the input width recovers the
exact conversion of the original input. -/
theorem Bytes.ofListTruncateRight?_of_ofListPadRight? {n : Nat} {padding : UInt8}
    {bs : List UInt8} {out : Bytes n}
    (h : Bytes.ofListPadRight? padding bs = some out) :
    Bytes.ofListTruncateRight? (n := bs.length) out.val =
      Bytes.ofListExact? (n := bs.length) bs := by
  obtain ⟨hlen, hout⟩ := (Bytes.ofListPadRight?_eq_some_iff padding bs out).mp h
  rw [hout]
  have hpad : 0 < n - bs.length := by omega
  simp [Bytes.ofListTruncateRight?, Bytes.ofListExact?, hpad]

/-- Left and right padding succeed on exactly the same inputs. -/
theorem Bytes.ofListPad_isSome_eq {n : Nat} (padding : UInt8) (bs : List UInt8) :
    (Bytes.ofListPadLeft? (n := n) padding bs).isSome =
      (Bytes.ofListPadRight? (n := n) padding bs).isSome := by
  by_cases h : bs.length < n <;>
    simp [Bytes.ofListPadLeft?, Bytes.ofListPadRight?, h]

/-- Left and right truncation succeed on exactly the same inputs. -/
theorem Bytes.ofListTruncate_isSome_eq {n : Nat} (bs : List UInt8) :
    (Bytes.ofListTruncateLeft? (n := n) bs).isSome =
      (Bytes.ofListTruncateRight? (n := n) bs).isSome := by
  by_cases h : n < bs.length <;>
    simp [Bytes.ofListTruncateLeft?, Bytes.ofListTruncateRight?, h]

/-- For left-oriented conversion, exactly one of padding, exact conversion,
and truncation succeeds. -/
theorem Bytes.ofList_left_exactly_one {n : Nat} (padding : UInt8) (bs : List UInt8) :
    [(Bytes.ofListPadLeft? (n := n) padding bs).isSome,
      (Bytes.ofListExact? (n := n) bs).isSome,
      (Bytes.ofListTruncateLeft? (n := n) bs).isSome].count true = 1 := by
  rcases Nat.lt_trichotomy bs.length n with h | h | h
  · have hne : bs.length ≠ n := by omega
    have hnlt : ¬ n < bs.length := by omega
    simp [Bytes.ofListPadLeft?, Bytes.ofListExact?, Bytes.ofListTruncateLeft?, h, hne, hnlt]
  · subst n
    simp [Bytes.ofListPadLeft?, Bytes.ofListExact?, Bytes.ofListTruncateLeft?]
  · have hnlt : ¬ bs.length < n := by omega
    have hne : bs.length ≠ n := by omega
    simp [Bytes.ofListPadLeft?, Bytes.ofListExact?, Bytes.ofListTruncateLeft?, h, hnlt, hne]

/-- For right-oriented conversion, exactly one of padding, exact conversion,
and truncation succeeds. -/
theorem Bytes.ofList_right_exactly_one {n : Nat} (padding : UInt8) (bs : List UInt8) :
    [(Bytes.ofListPadRight? (n := n) padding bs).isSome,
      (Bytes.ofListExact? (n := n) bs).isSome,
      (Bytes.ofListTruncateRight? (n := n) bs).isSome].count true = 1 := by
  rcases Nat.lt_trichotomy bs.length n with h | h | h
  · have hne : bs.length ≠ n := by omega
    have hnlt : ¬ n < bs.length := by omega
    simp [Bytes.ofListPadRight?, Bytes.ofListExact?, Bytes.ofListTruncateRight?, h, hne, hnlt]
  · subst n
    simp [Bytes.ofListPadRight?, Bytes.ofListExact?, Bytes.ofListTruncateRight?]
  · have hnlt : ¬ bs.length < n := by omega
    have hne : bs.length ≠ n := by omega
    simp [Bytes.ofListPadRight?, Bytes.ofListExact?, Bytes.ofListTruncateRight?, h, hnlt, hne]

/-- A width-indexed byte string has the width recorded in its type. -/
@[simp] theorem Bytes.length_val {n : Nat} (bs : Bytes n) : bs.1.length = n := bs.2

namespace Serialize

/-- Decode exactly `n` bytes from the front of the input. -/
def decodeBytes (n : Nat) (bs : List UInt8) : Option (Bytes n × List UInt8) :=
  if h : n ≤ bs.length then
    some (⟨bs.take n, by rw [List.length_take]; omega⟩, bs.drop n)
  else none

/-- Width-indexed bytes serialize as themselves and decode by consuming exactly
the width recorded in their type. -/
instance instCodecBytes (n : Nat) : Codec (Bytes n) where
  encode bs := bs.1
  decode := decodeBytes n
  decode_encode bs rest := by
    have hlen : n ≤ (bs.1 ++ rest).length := by
      rw [List.length_append, bs.2]
      omega
    simp only [decodeBytes, dif_pos hlen, List.take_left' bs.2,
      List.drop_left' bs.2]
  decode_canonical bs value rest hdec := by
    simp only [decodeBytes] at hdec
    split at hdec
    · rw [Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨hvalue, hrest⟩ := hdec
      have hval : bs.take n = value.1 := congrArg Subtype.val hvalue
      rw [← hrest, ← hval, List.take_append_drop]
    · exact absurd hdec (by simp)

/-- Width-indexed bytes encode to exactly the width recorded in their type. -/
theorem Bytes.encode_length {n : Nat} (bs : Bytes n) :
    (Codec.encode bs).length = n := bs.2

end Serialize

end BtcVerified
