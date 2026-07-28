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
  * coinbase scriptSig length — a block rule (#37), with the rest of the
    coinbase's structural checks.

  Checked claims:

  * `Tx.isWellFormed_iff`: the checker accepts a transaction exactly when it
    satisfies the five stateless rules — some output exists, no outpoint is
    spent twice, no input claims the null outpoint, the outputs create at
    most `maxMoney` satoshis in total, and the stripped serialization fits
    within the per-transaction weight ceiling.
  * `Tx.WellFormed.outputs_length_le`: a stateless-valid transaction has at
    most `2 ^ 32` outputs, so its `UInt32` output indices cannot wrap.
-/

namespace BtcVerified

/-- The transaction's serialization size without witness data: exactly Core's
`GetSerializeSize(TX_NO_WITNESS(tx))`, because `TxBody` is the stripped
serialization. -/
def Tx.strippedSize (tx : Tx) : Nat :=
  (Serialize.Codec.encode tx.body).length

/-- Decide the context-free validity of a regular transaction: some output
exists, no outpoint is spent twice, no input claims the null outpoint, and
the outputs create at most `maxMoney` satoshis in total, and the stripped
serialization fits within Core's per-transaction weight ceiling
([Bitcoin Core v28.0, `tx_check.cpp` lines 18–21](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L18-L21)). -/
def Tx.isWellFormed (tx : Tx) : Bool :=
  decide (tx.body.outputs.val ≠ [])
    && decide tx.body.spends.Nodup
    && tx.body.spends.all (· != OutPoint.null)
    && decide ((tx.body.outputs.val.map fun o => o.value.toNat).sum
        ≤ Consensus.maxMoney)
    && decide (tx.strippedSize * Consensus.witnessScaleFactor
        ≤ Consensus.maxBlockWeight)

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
  /-- The stripped serialization, scaled to weight units, fits within Core's
  per-transaction ceiling (`bad-txns-oversize`; [Bitcoin Core v28.0,
  `tx_check.cpp` lines 18–21](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L18-L21)). -/
  stripped_size_bounded : tx.strippedSize * Consensus.witnessScaleFactor
    ≤ Consensus.maxBlockWeight

/-- The checker enforces exactly its specification: `isWellFormed` accepts a
transaction iff it is `WellFormed`. -/
theorem Tx.isWellFormed_iff {tx : Tx} :
    tx.isWellFormed = true ↔ tx.WellFormed := by
  simp only [isWellFormed, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, bne_iff_ne]
  constructor
  · rintro ⟨⟨⟨⟨houtputs, hnodup⟩, hnull⟩, hbound⟩, hsize⟩
    exact ⟨houtputs, hnodup, hnull, hbound, hsize⟩
  · rintro ⟨houtputs, hnodup, hnull, hbound, hsize⟩
    exact ⟨⟨⟨⟨houtputs, hnodup⟩, hnull⟩, hbound⟩, hsize⟩

private theorem TxOut.one_le_encode_length (output : TxOut) :
    1 ≤ (Serialize.Codec.encode output).length := by
  change 1 ≤ (Serialize.Codec.encode output.value
    ++ Serialize.Codec.encode output.scriptPubKey).length
  have hvalue : (Serialize.Codec.encode output.value).length = 8 :=
    Serialize.encodeBitVecLE_length 8 output.value.toBitVec
  simp only [List.length_append, hvalue]
  omega

private theorem TxOut.list_length_le_encodeElems_length (outputs : List TxOut) :
    outputs.length ≤ (Serialize.encodeElems outputs).length := by
  induction outputs with
  | nil => rfl
  | cons output outputs ih =>
    simp only [List.length_cons, Serialize.encodeElems, List.length_append]
    have houtput := TxOut.one_le_encode_length output
    omega

/-- A stateless-valid transaction has at most `2 ^ 32` outputs: Core's
stripped-size rule is far tighter than the width of an outpoint's `vout`, so
the `UInt32` indices used by the UTXO action cannot wrap. -/
theorem Tx.WellFormed.outputs_length_le {tx : Tx} (h : tx.WellFormed) :
    tx.body.outputs.val.length ≤ 2 ^ 32 := by
  have helems := TxOut.list_length_le_encodeElems_length tx.body.outputs.val
  have houtputs :
      tx.body.outputs.val.length ≤
        (Serialize.Codec.encode tx.body.outputs).length := by
    change tx.body.outputs.val.length ≤
      (CompactSize.encode
        (UInt64.ofNat tx.body.outputs.val.length)
        ++ Serialize.encodeElems tx.body.outputs.val).length
    simp only [List.length_append]
    omega
  have hbody :
      (Serialize.Codec.encode tx.body.outputs).length ≤ tx.strippedSize := by
    unfold Tx.strippedSize
    change (Serialize.Codec.encode tx.body.outputs).length ≤
      (Serialize.Codec.encode tx.body.version
        ++ (Serialize.Codec.encode tx.body.inputs
          ++ (Serialize.Codec.encode tx.body.outputs
            ++ Serialize.Codec.encode tx.body.lockTime))).length
    simp only [List.length_append]
    omega
  have hsize := h.stripped_size_bounded
  unfold Consensus.witnessScaleFactor Consensus.maxBlockWeight at hsize
  omega

instance instDecidableWellFormed : DecidablePred Tx.WellFormed :=
  fun _ => decidable_of_iff _ Tx.isWellFormed_iff

end BtcVerified
