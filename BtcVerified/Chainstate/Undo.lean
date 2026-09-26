import BtcVerified.Chainstate.TxUndo
/-!
  # Undoing a transaction's UTXO action

  Remove the transaction's created outputs, then restore the captured spent
  coins. Undo is a total action, not a check of the record's authenticity:
  the round-trip theorem uses the record captured from the original state.

  The no-overwrite premise is explicit. This leaf does not cover the
  historical duplicate-coinbase exceptions tracked in #39, Core's undo
  implementation, or complete block validity. Output-index injectivity is
  unnecessary for this inverse: every created key is removed, even if the
  guard-free action created that key more than once.

  Checked claims:

  * `UtxoSet.undo_apply`: spending distinct, present coins and creating only
    fresh keys can be reversed exactly with the captured spent coins.
-/

namespace BtcVerified

/-- Remove a transaction's created keys and restore the supplied spent
coins. The caller must supply the undo record for this transaction and state. -/
def UtxoSet.undo (utxos : UtxoSet) (body : TxBody) (record : TxUndo) : UtxoSet :=
  (utxos.spend (body.creates.map Prod.fst)).create record.spentCoins

/-- Applying a transaction with distinct, present spends and fresh created
keys, then undoing it with its captured coins, restores the entire original
UTXO set, including every coin's script, value, and provenance. -/
theorem UtxoSet.undo_apply {utxos : UtxoSet} {body : TxBody}
    {provenance : Provenance}
    (hnodup : body.spends.Nodup)
    (hmem : ∀ o ∈ body.spends, o ∈ utxos)
    (hfresh : ∀ o ∈ body.creates.map Prod.fst, o ∉ utxos) :
    (utxos.apply provenance body).undo body (TxUndo.capture utxos body) = utxos := by
  apply Finmap.ext_lookup
  intro o
  unfold undo
  have hkeys := TxUndo.capture_keys hmem
  by_cases hspent : o ∈ body.spends
  · obtain ⟨c, hc⟩ := Finmap.mem_iff.mp (hmem o hspent)
    rw [lookup_create_of_mem (by simpa only [hkeys] using hnodup)
      (TxUndo.mem_capture.mpr ⟨hspent, hc⟩), hc]
  · rw [lookup_create_of_notMem (by simpa only [hkeys] using hspent)]
    by_cases hcreated : o ∈ body.creates.map Prod.fst
    · rw [lookup_spend_of_mem hcreated]
      exact (Finmap.lookup_eq_none.mpr (hfresh o hcreated)).symm
    · rw [lookup_spend_of_notMem hcreated,
        lookup_apply_of_notMem hspent hcreated]

end BtcVerified
