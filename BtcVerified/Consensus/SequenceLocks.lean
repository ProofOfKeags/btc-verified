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

  This leaf supplies the height component. Time locks require historical MTP
  context and are the next increment in #145; this component alone is not a
  complete BIP68 verdict.
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

end BtcVerified
