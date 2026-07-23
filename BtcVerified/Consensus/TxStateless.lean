import BtcVerified.Transaction.Tx
import BtcVerified.Chainstate.Apply
import BtcVerified.Consensus.Limits
/-!
  # Stateless transaction rules

  The context-free bucket: what consensus demands of a regular transaction
  before looking at any chain state — Core's `CheckTransaction`
  (`src/consensus/tx_check.cpp`), restricted to a transaction with real
  inputs. A transaction in coinbase position is judged by block rules (#37),
  because coinbase-ness is positional; here its null prevout simply fails
  `spends_ne_null`.

  The enforced rule is the checker `Tx.isWellFormed`; `Tx.WellFormed` is the
  specification it is proved to enforce (`Tx.isWellFormed_iff`). Downstream
  theorems consume the specification's named fields.

  Core checks with no rule here, and why:

  * empty `vin` — a type invariant, not a rule: `Tx.body_inputs_ne_nil`.
  * negative amounts — unrepresentable (`UInt64` values, `Nat` sums).
  * per-output and running-total `MoneyRange` — in `Nat` the single sum
    bound `values_bounded` subsumes every per-output bound; no overflow
    exists to re-check.
  * oversize — a block rule (#37); it is also what discharges the
    `outputs.length ≤ 2 ^ 32` hypothesis of the action theorems.
  * coinbase scriptSig length — a block rule (#37), with the rest of the
    coinbase's structural checks.

  Checked claims:

  * `Tx.isWellFormed_iff`: the checker accepts a transaction exactly when it
    satisfies the four stateless rules — some output exists, no outpoint is
    spent twice, no input claims the null outpoint, and the outputs create
    at most `maxMoney` satoshis in total.
-/

namespace BtcVerified

/-- Decide the context-free validity of a regular transaction: some output
exists, no outpoint is spent twice, no input claims the null outpoint, and
the outputs create at most `maxMoney` satoshis in total. -/
def Tx.isWellFormed (tx : Tx) : Bool :=
  decide (tx.body.outputs.val ≠ [])
    && decide tx.body.spends.Nodup
    && tx.body.spends.all (· != OutPoint.null)
    && decide ((tx.body.outputs.val.map fun o => o.value.toNat).sum
        ≤ Consensus.maxMoney)

/-- The specification `Tx.isWellFormed` enforces — Core's `CheckTransaction`
for a transaction with real inputs, one field per rule. -/
structure Tx.WellFormed (tx : Tx) : Prop where
  /-- There is at least one output (`bad-txns-vout-empty`). -/
  outputs_ne_nil : tx.body.outputs.val ≠ []
  /-- No two inputs consume the same outpoint (`bad-txns-inputs-duplicate`). -/
  spends_nodup : tx.body.spends.Nodup
  /-- No input claims the null outpoint (`bad-txns-prevout-null`). -/
  spends_ne_null : ∀ o ∈ tx.body.spends, o ≠ OutPoint.null
  /-- The outputs create at most `maxMoney` satoshis in total — which in
  `Nat` also bounds every individual output (`bad-txns-vout-toolarge`,
  `bad-txns-txouttotal-toolarge`). -/
  values_bounded : (tx.body.outputs.val.map fun o => o.value.toNat).sum
    ≤ Consensus.maxMoney

/-- The checker enforces exactly its specification: `isWellFormed` accepts a
transaction iff it is `WellFormed`. -/
theorem Tx.isWellFormed_iff {tx : Tx} :
    tx.isWellFormed = true ↔ tx.WellFormed := by
  simp only [isWellFormed, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, bne_iff_ne]
  constructor
  · rintro ⟨⟨⟨houtputs, hnodup⟩, hnull⟩, hbound⟩
    exact ⟨houtputs, hnodup, hnull, hbound⟩
  · rintro ⟨houtputs, hnodup, hnull, hbound⟩
    exact ⟨⟨⟨houtputs, hnodup⟩, hnull⟩, hbound⟩

instance instDecidableWellFormed : DecidablePred Tx.WellFormed :=
  fun _ => decidable_of_iff _ Tx.isWellFormed_iff

end BtcVerified
