import Mathlib.Data.UInt
/-!
  # Width-cast truncation inverses

  A recurring fact when serializing narrowed values: truncating a value to a
  smaller width and widening it back is the identity, *provided the value
  already fits in the smaller width*. This is the general shape behind the
  conversions in `CompactSize` (e.g. a `UInt64` count known to be below `2^16`
  round-trips through `UInt16`).

  The content is a single `BitVec`-level theorem (`setWidth_setWidth_eq_self`),
  proved once by `toNat`. Rather than restate it as one lemma per
  `(source, target)` integer-width pair — a quadratic pile — the `narrow_widen`
  tactic discharges any fixed-width roundtrip `x.toNarrow.toWide = x` by pushing
  the goal down to `BitVec` through Lean core's `int_toBitVec` simp set (which
  already supplies the per-pair `toBitVec`/order bridges) and closing with the
  one theorem. The only width-specific data left is the source type, which the
  tactic resolves by trying each in turn.
-/

namespace BtcVerified.Serialize

/--
  Truncating `a : BitVec n` to `m` bits and widening back to `n` bits is the
  identity whenever `a` already fits in `m` bits (`a.toNat < 2 ^ m`).
-/
theorem setWidth_setWidth_eq_self {n m : Nat} {a : BitVec n} (h : a.toNat < 2 ^ m) :
    (a.setWidth m).setWidth n = a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt a.isLt]

/--
  Close a fixed-width truncate-then-widen roundtrip goal `x.toNarrow.toWide = x`
  from a proof `h` that `x` fits in the narrow width (`x < 2 ^ k`).

  The goal is reduced to `BitVec` via core's `int_toBitVec` simp set — which
  carries every per-pair `toBitVec` bridge — and closed by
  `setWidth_setWidth_eq_self`. This avoids defining a separate widen/truncate
  lemma for each pair of integer widths.
-/
macro "narrow_widen " h:term : tactic =>
  `(tactic|
    (simp only [int_toBitVec]
     apply BtcVerified.Serialize.setWidth_setWidth_eq_self
     first
       | exact by simpa using UInt64.lt_iff_toNat_lt.mp $h
       | exact by simpa using UInt32.lt_iff_toNat_lt.mp $h
       | exact by simpa using UInt16.lt_iff_toNat_lt.mp $h
       | exact by simpa using UInt8.lt_iff_toNat_lt.mp $h))

end BtcVerified.Serialize
