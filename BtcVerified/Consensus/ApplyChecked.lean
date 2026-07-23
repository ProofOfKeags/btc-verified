import BtcVerified.Consensus.TxStateless
import BtcVerified.Consensus.TxContextual
/-!
  # Guarded application

  Where the rules meet the machine. The discharge lemma turns a
  rule-passing transaction's `creates_absent` into the exact absence-after-
  spend hypothesis the action theorems carry, and the gated conservation
  theorems specialize `UtxoSet.totalValue_apply` with every machine
  hypothesis supplied by a rule — except the output-count bound, which the
  block-size rule provides (#37), so it stays a hypothesis here.

  Fees are not spec objects (#37): the conservation statement is the
  accounting identity itself, and "the total drops by exactly the fee" is
  its English reading, not a definition in the model.

  `applyChecked` is the strict interface — rules first, act on success —
  provably agreeing with the guard-free action whenever it returns `some`.
  A convenience in `Consensus/`, never structure in `Chainstate/`: every
  transaction acts identically; only the rules differ. It stamps the
  provenance a regular transaction earns — created at the admitting height,
  not in coinbase position (the coinbase epilogue is a block rule, #37).

  Checked claims:

  * `Tx.creates_absent_spend`: a rule-passing transaction's created
    outpoints are absent even after its spends are erased.
  * `UtxoSet.totalValue_apply_of_admissible`: for a rule-passing
    transaction the accounting identity holds, every machine hypothesis
    discharged by a rule (the output-count bound by #37).
  * `UtxoSet.totalValue_apply_le_of_admissible`: a rule-passing transaction
    never increases the total value the set holds.
  * `UtxoSet.applyChecked_eq_some_iff`: the strict interface succeeds on
    exactly the rule-passing transactions, and then agrees with the
    guard-free action.
-/

namespace BtcVerified

/-- A rule-passing transaction's created outpoints are absent even after its
spends are erased — `creates_absent` survives the spend because spending
only shrinks the set. This is the exact absence hypothesis the action
theorems carry. -/
theorem Tx.creates_absent_spend {scriptOk : ScriptCheck} {utxos : UtxoSet}
    {ctx : TxContext} {tx : Tx} (h : Tx.Admissible scriptOk utxos ctx tx) :
    ∀ o ∈ tx.body.creates.map Prod.fst, o ∉ utxos.spend tx.body.spends :=
  fun o ho hmem => h.creates_absent o ho (UtxoSet.mem_spend.mp hmem).1

/-- For a rule-passing transaction the accounting identity holds: total
value after application plus the value spent equals total value before plus
the value created. Every machine hypothesis is discharged by a rule, except
the output-count bound the block-size rule supplies (#37). -/
theorem UtxoSet.totalValue_apply_of_admissible {scriptOk : ScriptCheck}
    {utxos : UtxoSet} {ctx : TxContext} {provenance : Provenance} {tx : Tx}
    (houtputs : tx.body.outputs.val.length ≤ 2 ^ 32)
    (hwf : tx.WellFormed) (hadm : Tx.Admissible scriptOk utxos ctx tx) :
    totalValue (utxos.apply provenance tx.body)
        + (tx.body.spends.map utxos.valueAt).sum
      = utxos.totalValue
        + (tx.body.outputs.val.map fun output => output.value.toNat).sum :=
  totalValue_apply houtputs hwf.spends_nodup hadm.spends_mem
    (Tx.creates_absent_spend hadm)

/-- A rule-passing transaction never increases the total value the set
holds: the total drops by exactly the value the inputs carry beyond the
outputs — the fee, in English; fees are not spec objects (#37). -/
theorem UtxoSet.totalValue_apply_le_of_admissible {scriptOk : ScriptCheck}
    {utxos : UtxoSet} {ctx : TxContext} {provenance : Provenance} {tx : Tx}
    (houtputs : tx.body.outputs.val.length ≤ 2 ^ 32)
    (hwf : tx.WellFormed) (hadm : Tx.Admissible scriptOk utxos ctx tx) :
    totalValue (utxos.apply provenance tx.body) ≤ utxos.totalValue := by
  have hidentity := totalValue_apply_of_admissible houtputs hwf hadm
    (provenance := provenance)
  have hcover := hadm.values_cover
  omega

/-- Run the regular-transaction rules, then act: `some` of the guard-free
application on success, `none` on any rule failure. Stamps the provenance a
regular transaction earns — created at the admitting height, not in
coinbase position (the coinbase epilogue is a block rule, #37). -/
def UtxoSet.applyChecked (scriptOk : ScriptCheck) (utxos : UtxoSet)
    (ctx : TxContext) (tx : Tx) : Option UtxoSet :=
  if tx.isWellFormed && tx.isAdmissible scriptOk utxos ctx
  then some (utxos.apply ⟨ctx.height, false⟩ tx.body)
  else none

/-- The strict interface succeeds on exactly the rule-passing transactions,
and then agrees with the guard-free action under the regular-transaction
provenance stamp. -/
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
