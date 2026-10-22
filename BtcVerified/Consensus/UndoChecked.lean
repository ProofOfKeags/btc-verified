import BtcVerified.Consensus.ApplyChecked
import BtcVerified.Chainstate.Undo
/-!
  # Undo after a guarded transaction step

  The regular-transaction premises discharge every hypothesis of the
  machine's inverse theorem. This uses the existing internal `applyChecked`
  step, not a new block-validity interface.

  Checked claims:

  * `UtxoSet.undo_of_applyChecked_eq_some`: a successful guarded step can
    be undone exactly using the coins captured before that step.
-/

namespace BtcVerified

/-- If the guarded regular-transaction step succeeds, undoing the resulting
state with coins captured before the step restores the original UTXO set. -/
theorem UtxoSet.undo_of_applyChecked_eq_some {scriptOk : ScriptCheck}
    {utxos next : UtxoSet} {clock : LockTimeClock} {ctx : TxContext} {tx : Tx}
    (h : utxos.applyChecked scriptOk clock ctx tx = some next) :
    next.undo tx.body (TxUndo.capture utxos tx.body) = utxos := by
  obtain ⟨hwf, hadm, rfl⟩ := applyChecked_eq_some_iff.mp h
  exact undo_apply hwf.allInputOutpointsDistinct hadm.spends_mem hadm.creates_do_not_overwrite

end BtcVerified
