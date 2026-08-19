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

/-- Refine a list when it has exactly the required width. -/
def Bytes.ofListExact? {n : Nat} (bs : List UInt8) : Option (Bytes n) :=
  if h : bs.length = n then some ⟨bs, h⟩ else none

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
