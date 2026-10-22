import BtcVerified.Chainstate.Apply
/-!
  # Transaction undo data

  Capture only the coins a transaction spends, with their original output
  and provenance. This is an abstract in-memory record, not Bitcoin Core's
  undo serialization. Missing inputs are omitted; the round-trip theorem
  requires that every input was present when the record was captured.

  Checked claims:

  * `TxUndo.mem_capture`: captured entries are exactly the spent outpoints
    paired with their original coins.
  * `TxUndo.capture_keys`: when all inputs exist, captured keys are exactly
    the transaction's spend list, in its original order.
-/

namespace BtcVerified

/-- The original coins consumed by a transaction, keyed by spent outpoint.
This stores their outputs and provenance, not a snapshot of the whole set. -/
structure TxUndo where
  /-- Spent outpoints paired with their coins before application. -/
  spentCoins : List (OutPoint × Coin)
deriving DecidableEq

/-- Capture the present coins named by a transaction's inputs, in input
order. An absent input contributes no entry. -/
def TxUndo.capture (utxos : UtxoSet) (body : TxBody) : TxUndo :=
  ⟨body.spends.filterMap fun o => (utxos.lookup o).map fun c => (o, c)⟩

/-- A captured entry names a spent outpoint and contains exactly the coin
found there before the transaction is applied. -/
theorem TxUndo.mem_capture {utxos : UtxoSet} {body : TxBody}
    {o : OutPoint} {c : Coin} :
    (o, c) ∈ (capture utxos body).spentCoins
      ↔ o ∈ body.spends ∧ utxos.lookup o = some c := by
  simp only [capture, List.mem_filterMap, Option.map_eq_some_iff]
  aesop

/-- If every spent outpoint is present, capturing coins preserves exactly
the spend list, including its order and multiplicities. -/
theorem TxUndo.capture_keys {utxos : UtxoSet} {body : TxBody}
    (hmem : ∀ o ∈ body.spends, o ∈ utxos) :
    (capture utxos body).spentCoins.map Prod.fst = body.spends := by
  unfold capture
  generalize body.spends = spends at *
  induction spends with
  | nil => rfl
  | cons o rest ih =>
    obtain ⟨c, hc⟩ := Finmap.mem_iff.mp (hmem o List.mem_cons_self)
    simp only [List.filterMap_cons, hc, Option.map_some, List.map_cons]
    exact congrArg (o :: ·) (ih fun k hk => hmem k (List.mem_cons_of_mem o hk))

end BtcVerified
