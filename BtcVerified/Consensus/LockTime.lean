import BtcVerified.Consensus.Limits
/-!
  # Absolute transaction lock time

  The consensus reading of the raw `TxBody.lockTime` wire field. The field is
  zero when disabled; otherwise values below `lockTimeThreshold` name an
  absolute block height and values at or above it name an absolute UNIX time
  ([Bitcoin Core v28.0, `IsFinalTx`, `tx_verify.cpp` lines
  17–37](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L17-L37)).

  Keeping this interpretation as an algebraic data type makes the selected
  axis structural in the reasoning model instead of repeating Core's nested
  numeric conditional in every rule. The wire object remains `UInt32`, and
  `LockTime.ofUInt32` is the explicit boundary between syntax and semantics.

  This type describes the transaction's absolute `nLockTime`. BIP68 relative
  lock times are a separate interpretation of each input's sequence field and
  remain the sequence-locks leaf tracked by #46 ([Bitcoin Core v28.0,
  `CalculateSequenceLocks`, `tx_verify.cpp` lines
  39–109](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L39-L109)).
-/

namespace BtcVerified.Consensus

/-- The semantic reading of a transaction's absolute lock-time wire field. -/
inductive LockTime where
  /-- Lock-time enforcement is disabled by the zero wire value. -/
  | disabled
  /-- The transaction is locked until strictly after this block height. -/
  | blockHeight (height : Nat)
  /-- The transaction is locked until strictly after this UNIX time. -/
  | blockTime (time : Nat)
  deriving DecidableEq

/-- Interpret the raw transaction lock-time field, making its selected axis
explicit. Relative lock times do not come from this field; #46 will interpret
input sequence fields separately. -/
def LockTime.ofUInt32 (value : UInt32) : LockTime :=
  if value = 0 then
    .disabled
  else if value.toNat < lockTimeThreshold then
    .blockHeight value.toNat
  else
    .blockTime value.toNat

/-- The semantic proposition that an absolute lock time has passed at the
given admitting height and selected measuring time. -/
def LockTime.Past : LockTime → Nat → Nat → Prop
  | .disabled, _, _ => True
  | .blockHeight lockHeight, height, _ => lockHeight < height
  | .blockTime lockTime, _, time => lockTime < time

/-- Decide whether an absolute lock time has passed at the given admitting
height and selected measuring time. -/
def LockTime.isPast : LockTime → Nat → Nat → Bool
  | .disabled, _, _ => true
  | .blockHeight lockHeight, height, _ => decide (lockHeight < height)
  | .blockTime lockTime, _, time => decide (lockTime < time)

/-- The executable absolute-lock-time comparison enforces exactly its
semantic proposition. -/
theorem LockTime.isPast_iff {lockTime : LockTime} {height time : Nat} :
    lockTime.isPast height time = true ↔ lockTime.Past height time := by
  cases lockTime <;> simp [isPast, Past]

/-- Interpreting the wire field and comparing its semantic value is exactly
Core's raw zero-or-threshold conditional. This is the compatibility bridge
from the reasoning type back to the wire-shaped statement. -/
theorem LockTime.ofUInt32_past_iff {value : UInt32} {height time : Nat} :
    (LockTime.ofUInt32 value).Past height time ↔
      value = 0 ∨ value.toNat <
        (if value.toNat < lockTimeThreshold then height else time) := by
  unfold ofUInt32
  by_cases hzero : value = 0
  · simp [hzero, Past]
  · simp only [hzero, ↓reduceIte]
    by_cases hheight : value.toNat < lockTimeThreshold
    · simp [hheight, Past]
    · simp [hheight, Past]

end BtcVerified.Consensus
