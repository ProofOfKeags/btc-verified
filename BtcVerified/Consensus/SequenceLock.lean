import BtcVerified.Consensus.Limits
/-!
  # Relative input lock times

  An input sequence encodes a disabled lock, a block delay, or a delay in
  seconds. The transaction version and active rules decide whether this
  interpretation is enforced. Keeping the selected unit in the type avoids
  mixing height and time when the contextual rules compare coin ages.

  The wire interpretation follows the pinned
  [Core sequence constants](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/primitives/transaction.h#L84-L114).

  Checked claims:

  * `SequenceLock.isHeightSatisfied_iff`: the height checker decides its
    semantic age condition.
  * `SequenceLock.isTimeSatisfied_iff`: the time checker decides its
    semantic age condition.
  * `SequenceLock.blocks_heightSatisfied_iff`: the inclusive age condition
    equals the signed last-invalid-height comparison, including at zero.
  * `SequenceLock.blocks_same_height_iff`: spending at the creation height
    satisfies a block lock exactly when its delay is zero.
-/

namespace BtcVerified.Consensus

/-- The relative delay encoded by one input's sequence field. -/
inductive SequenceLock where
  /-- The input imposes no relative lock. -/
  | disabled
  /-- The input requires this many blocks since its coin's creation. -/
  | blocks (delay : Nat)
  /-- The input requires this many seconds since its coin's time anchor. -/
  | seconds (delay : Nat)
  deriving DecidableEq

/-- Interpret an input sequence: bit 31 disables the lock, bit 22 selects
seconds, and the low 16 bits count blocks or units of 512 seconds. -/
def SequenceLock.ofUInt32 (sequence : UInt32) : SequenceLock :=
  if sequence &&& 0x80000000 != 0 then .disabled
  else if sequence &&& 0x00400000 != 0 then
    .seconds ((sequence &&& 0x0000ffff).toNat * 512)
  else .blocks (sequence &&& 0x0000ffff).toNat

/-- The height component is satisfied once the coin has aged by the block
delay. Disabled and time-based locks impose no height requirement. -/
def SequenceLock.HeightSatisfied : SequenceLock → Nat → Nat → Prop
  | .blocks delay, birthHeight, height => birthHeight + delay ≤ height
  | _, _, _ => True

/-- Decide the height component using the first valid height, including zero.
Time-based locks impose no height requirement. -/
def SequenceLock.isHeightSatisfied : SequenceLock → Nat → Nat → Bool
  | .blocks delay, birthHeight, height => decide (birthHeight + delay ≤ height)
  | _, _, _ => true

/-- The time component is satisfied once parent median-time-past reaches the
coin's historical median-time-past plus delay. Other lock units impose no
time requirement. -/
def SequenceLock.TimeSatisfied : SequenceLock → Nat → Nat → Prop
  | .seconds delay, birthTime, time => birthTime + delay ≤ time
  | _, _, _ => True

/-- Decide the relative time component using the first valid time, including
zero. Block-based and disabled locks impose no time requirement. -/
def SequenceLock.isTimeSatisfied : SequenceLock → Nat → Nat → Bool
  | .seconds delay, birthTime, time => decide (birthTime + delay ≤ time)
  | _, _, _ => true

/-- The height checker accepts exactly when the relative height condition
holds, including the unconstrained disabled and time-based cases. -/
theorem SequenceLock.isHeightSatisfied_iff {lock : SequenceLock}
    {birthHeight height : Nat} :
    lock.isHeightSatisfied birthHeight height = true ↔
      lock.HeightSatisfied birthHeight height := by
  cases lock <;> simp [isHeightSatisfied, HeightSatisfied]

/-- The time checker accepts exactly when the relative time condition holds,
including the unconstrained disabled and block-based cases. -/
theorem SequenceLock.isTimeSatisfied_iff {lock : SequenceLock}
    {birthTime time : Nat} :
    lock.isTimeSatisfied birthTime time = true ↔
      lock.TimeSatisfied birthTime time := by
  cases lock <;> simp [isTimeSatisfied, TimeSatisfied]

/-- The first-valid height condition equals a strict comparison against the
signed last-invalid height used by Core, even when the first valid height is
zero ([calculation and evaluation](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/consensus/tx_verify.cpp#L95-L110)). -/
theorem SequenceLock.blocks_heightSatisfied_iff {delay birthHeight height : Nat} :
    (SequenceLock.blocks delay).HeightSatisfied birthHeight height ↔
      (birthHeight : Int) + (delay : Int) - 1 < (height : Int) := by
  simp only [HeightSatisfied]
  omega

/-- A coin spent at its creation height satisfies a block delay exactly when
the delay is zero. -/
theorem SequenceLock.blocks_same_height_iff {delay height : Nat} :
    (SequenceLock.blocks delay).HeightSatisfied height height ↔ delay = 0 := by
  simp only [HeightSatisfied]
  omega

end BtcVerified.Consensus
