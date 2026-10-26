import BtcVerified.Chainstate.UtxoSet
import BtcVerified.Transaction.TxBody
import BtcVerified.Consensus.SequenceLock
import BtcVerified.Consensus.TxContext
/-!
  # Transaction sequence-lock premises

  Each input's sequence is compared with the provenance of its own spent coin.
  Input existence is a separate contextual premise; absent coins impose no
  age condition here. The caller selects activation explicitly, and the raw
  unsigned transaction version must be at least two
  ([pinned Core](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/consensus/tx_verify.cpp#L45-L98)).

  The height and time components are separate premises, both enforced by
  contextual admission. Time locks use MTP at the ancestor before coin creation
  (height zero for genesis) and the candidate parent's MTP. The caller supplies
  that history; constructing it from validated headers remains #122.

  Checked claims:

  * `TxBody.isHeightLocksSatisfied_iff`: the executable height-lock check
    decides the per-input specification under its activation and version gates.
  * `TxBody.isTimeLocksSatisfied_iff`: the executable time-lock check decides
    the per-input specification using the supplied historical MTP values.
  * `TxBody.TimeLocksSatisfied.same_block_delay_eq_zero`: a same-block time
    lock has zero delay when activation/version enable it and history agrees
    with the candidate parent's MTP.
-/

namespace BtcVerified

/-- When sequence locks are active and the version is at least two, every
present input coin satisfies the height component of its decoded lock. -/
def TxBody.HeightLocksSatisfied (body : TxBody) (utxos : UtxoSet)
    (ctx : TxContext) : Prop :=
  ctx.sequenceLocksActive = true → 2 ≤ body.version.toNat →
    ∀ input ∈ body.inputs.val, ∀ coin,
      utxos.lookup input.prevout = some coin →
        (Consensus.SequenceLock.ofUInt32 input.sequence).HeightSatisfied
          coin.provenance.height ctx.height

/-- Check every present input's height lock when both activation and version
enable it. Missing coins are rejected by the separate existence premise. -/
def TxBody.isHeightLocksSatisfied (body : TxBody) (utxos : UtxoSet)
    (ctx : TxContext) : Bool :=
  if ctx.sequenceLocksActive && decide (2 ≤ body.version.toNat) then
    body.inputs.val.all fun input =>
      ((utxos.lookup input.prevout).map fun coin =>
        (Consensus.SequenceLock.ofUInt32 input.sequence).isHeightSatisfied
          coin.provenance.height ctx.height).getD true
  else true

/-- When activation and version enable sequence locks, every present input
coin satisfies its time component using MTP before its creation block and
the candidate parent's MTP. Genesis creation uses ancestor height zero. -/
def TxBody.TimeLocksSatisfied (body : TxBody) (utxos : UtxoSet)
    (ctx : TxContext) : Prop :=
  ctx.sequenceLocksActive = true → 2 ≤ body.version.toNat →
    ∀ input ∈ body.inputs.val, ∀ coin,
      utxos.lookup input.prevout = some coin →
        (Consensus.SequenceLock.ofUInt32 input.sequence).TimeSatisfied
          (ctx.medianTimePastAt (coin.provenance.height - 1)) ctx.medianTimePast

/-- Check every present input's relative time lock against the supplied
history. Candidate header time and the absolute-lock clock are not consulted. -/
def TxBody.isTimeLocksSatisfied (body : TxBody) (utxos : UtxoSet)
    (ctx : TxContext) : Bool :=
  if ctx.sequenceLocksActive && decide (2 ≤ body.version.toNat) then
    body.inputs.val.all fun input =>
      ((utxos.lookup input.prevout).map fun coin =>
        (Consensus.SequenceLock.ofUInt32 input.sequence).isTimeSatisfied
          (ctx.medianTimePastAt (coin.provenance.height - 1)) ctx.medianTimePast).getD true
  else true

/-- The transaction height-lock checker accepts exactly when every present
input coin meets its height condition under the activation and version gates. -/
theorem TxBody.isHeightLocksSatisfied_iff {body : TxBody} {utxos : UtxoSet}
    {ctx : TxContext} :
    body.isHeightLocksSatisfied utxos ctx = true ↔
      body.HeightLocksSatisfied utxos ctx := by
  by_cases hactive : ctx.sequenceLocksActive = true
  · by_cases hversion : 2 ≤ body.version.toNat
    · simp only [isHeightLocksSatisfied, HeightLocksSatisfied, hactive, hversion,
        decide_true, Bool.and_self, ↓reduceIte, true_implies, List.all_eq_true]
      apply forall_congr'
      intro input
      apply forall_congr'
      intro _
      cases hcoin : utxos.lookup input.prevout <;>
        simp [Consensus.SequenceLock.isHeightSatisfied_iff]
    · simp [isHeightLocksSatisfied, HeightLocksSatisfied, hactive, hversion]
  · simp [isHeightLocksSatisfied, HeightLocksSatisfied, hactive]

/-- The transaction time-lock checker accepts exactly when every present
input coin meets its time condition under the activation and version gates. -/
theorem TxBody.isTimeLocksSatisfied_iff {body : TxBody} {utxos : UtxoSet}
    {ctx : TxContext} :
    body.isTimeLocksSatisfied utxos ctx = true ↔
      body.TimeLocksSatisfied utxos ctx := by
  by_cases hactive : ctx.sequenceLocksActive = true
  · by_cases hversion : 2 ≤ body.version.toNat
    · simp only [isTimeLocksSatisfied, TimeLocksSatisfied, hactive, hversion,
        decide_true, Bool.and_self, ↓reduceIte, true_implies, List.all_eq_true]
      apply forall_congr'
      intro input
      apply forall_congr'
      intro _
      cases hcoin : utxos.lookup input.prevout <;>
        simp [Consensus.SequenceLock.isTimeSatisfied_iff]
    · simp [isTimeLocksSatisfied, TimeLocksSatisfied, hactive, hversion]
  · simp [isTimeLocksSatisfied, TimeLocksSatisfied, hactive]

/-- An enforced time lock on a coin created in the admitting block has zero
delay, provided the supplied history agrees with the candidate parent's MTP. -/
theorem TxBody.TimeLocksSatisfied.same_block_delay_eq_zero
    {body : TxBody} {utxos : UtxoSet} {ctx : TxContext}
    {input : TxIn} {coin : Coin} {delay : Nat}
    (hlocks : body.TimeLocksSatisfied utxos ctx)
    (hactive : ctx.sequenceLocksActive = true) (hversion : 2 ≤ body.version.toNat)
    (hinput : input ∈ body.inputs.val) (hcoin : utxos.lookup input.prevout = some coin)
    (hheight : coin.provenance.height = ctx.height)
    (hhistory : ctx.medianTimePastAt (ctx.height - 1) = ctx.medianTimePast)
    (hsequence : Consensus.SequenceLock.ofUInt32 input.sequence = .seconds delay) :
    delay = 0 := by
  have htime := hlocks hactive hversion input hinput coin hcoin
  rw [hsequence, hheight, hhistory] at htime
  exact Consensus.SequenceLock.seconds_same_time_iff.mp htime

end BtcVerified
