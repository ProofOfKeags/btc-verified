import BtcVerified.Consensus.TxStateless
import BtcVerified.Consensus.TxContextual
/-!
  # Guarded application

  Where transaction premises meet the machine. The discharge lemma turns
  `creates_do_not_overwrite` into the exact absence-after-spend hypothesis
  the action theorems carry, and the gated conservation theorems specialize
  `UtxoSet.totalValue_apply` with every machine hypothesis supplied by a
  premise. In particular, the transaction-local stripped-size premise implies
  the output-count bound that keeps `UInt32` output indices injective.

  Fees are not spec objects (#37): the conservation statement is the
  accounting identity itself, and "the total drops by exactly the fee" is
  its English reading, not a definition in the model.

  `applyChecked` is the internal regular-transaction step that the block fold
  in #37 will iterate: check its local and contextual premises, then act on
  success. It is not a root consensus interface; only the complete block fold,
  coinbase epilogue, and block-wide premises establish a valid extension. A
  convenience in `Consensus/`, never structure in `Chainstate/`, it stamps the
  provenance a regular transaction earns — created at the admitting height,
  not in coinbase position.

  Checked claims:

  * `Tx.creates_do_not_overwrite_after_spend`: a premise-passing
    transaction's created outpoints remain fresh after its spends are erased.
  * `UtxoSet.totalValue_apply_of_admissible`: for a premise-passing
    transaction the accounting identity holds, every machine hypothesis
    discharged by a rule.
  * `UtxoSet.totalValue_apply_le_of_admissible`: a premise-passing transaction
    never increases the total value the set holds.
  * `UtxoSet.applyChecked_eq_some_iff`: the internal step succeeds exactly
    when its transaction premises hold, and then agrees with the guard-free
    action.
-/

namespace BtcVerified

/-- If a transaction's creations do not overwrite the current set, they remain
fresh after its spends are erased because spending only shrinks the set. This
is the exact absence hypothesis the action theorems carry. -/
theorem Tx.creates_do_not_overwrite_after_spend
    {scriptOk : ScriptCheck} {utxos : UtxoSet}
    {ctx : TxContext} {tx : Tx} (h : Tx.Admissible scriptOk utxos ctx tx) :
    ∀ o ∈ tx.body.creates.map Prod.fst, o ∉ utxos.spend tx.body.spends :=
  fun o ho hmem =>
    h.creates_do_not_overwrite o ho (UtxoSet.mem_spend.mp hmem).1

/-- For a premise-passing transaction the accounting identity holds: total
value after application plus the value spent equals total value before plus
the value created. Every machine hypothesis is discharged by a transaction
premise, including output-index injectivity via the stripped-size premise. -/
theorem UtxoSet.totalValue_apply_of_admissible {scriptOk : ScriptCheck}
    {utxos : UtxoSet} {ctx : TxContext} {provenance : Provenance} {tx : Tx}
    (hwf : tx.WellFormed) (hadm : Tx.Admissible scriptOk utxos ctx tx) :
    totalValue (utxos.apply provenance tx.body)
        + (tx.body.spends.map utxos.valueAt).sum
      = utxos.totalValue
        + (tx.body.outputs.val.map fun output => output.value.toNat).sum :=
  totalValue_apply (Tx.WellFormed.outputs_length_le hwf)
    hwf.spends_nodup hadm.spends_mem
    (Tx.creates_do_not_overwrite_after_spend hadm)

/-- A premise-passing transaction never increases the total value the set
holds: the total drops by exactly the value the inputs carry beyond the
outputs — the fee, in English; fees are not spec objects (#37). -/
theorem UtxoSet.totalValue_apply_le_of_admissible {scriptOk : ScriptCheck}
    {utxos : UtxoSet} {ctx : TxContext} {provenance : Provenance} {tx : Tx}
    (hwf : tx.WellFormed) (hadm : Tx.Admissible scriptOk utxos ctx tx) :
    totalValue (utxos.apply provenance tx.body) ≤ utxos.totalValue := by
  have hidentity := totalValue_apply_of_admissible hwf hadm
    (provenance := provenance)
  have hcover := hadm.values_cover
  omega

/-- Run the premises for one regular-transaction step, then act: `some` of the
guard-free application on success, `none` on any premise failure. This is the
internal step of #37's block fold, not a standalone consensus verdict. It
stamps the provenance a regular transaction earns — created at the admitting
height, not in coinbase position. -/
def UtxoSet.applyChecked (scriptOk : ScriptCheck) (utxos : UtxoSet)
    (ctx : TxContext) (tx : Tx) : Option UtxoSet :=
  if tx.isWellFormed && tx.isAdmissible scriptOk utxos ctx
  then some (utxos.apply ⟨ctx.height, false⟩ tx.body)
  else none

/-- The internal regular-transaction step succeeds exactly when its local and
contextual premises hold, then agrees with the guard-free action under the
regular-transaction provenance stamp. -/
theorem UtxoSet.applyChecked_eq_some_iff {scriptOk : ScriptCheck}
    {utxos next : UtxoSet} {ctx : TxContext} {tx : Tx} :
    utxos.applyChecked scriptOk ctx tx = some next
      ↔ tx.WellFormed ∧ Tx.Admissible scriptOk utxos ctx tx
          ∧ next = utxos.apply ⟨ctx.height, false⟩ tx.body := by
  unfold applyChecked
  split
  · next hcond =>
      rw [Bool.and_eq_true, Tx.isWellFormed_iff, Tx.isAdmissible_iff] at hcond
      simp only [Option.some.injEq]
      exact ⟨fun hnext => ⟨hcond.1, hcond.2, hnext.symm⟩,
        fun ⟨_, _, hnext⟩ => hnext.symm⟩
  · next hcond =>
      refine iff_of_false (fun h => by cases h) ?_
      rintro ⟨hwf, hadm, -⟩
      refine hcond ?_
      rw [Bool.and_eq_true]
      exact ⟨Tx.isWellFormed_iff.mpr hwf, Tx.isAdmissible_iff.mpr hadm⟩

end BtcVerified
