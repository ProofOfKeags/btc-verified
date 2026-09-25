import BtcVerified.Transaction.Tx
import BtcVerified.Chainstate.Apply
import BtcVerified.Consensus.Limits
/-!
  # Transaction-local premises

  The transaction-local premises used while checking a regular transaction
  inside a candidate block, before looking at any chain state — Core's
  [`CheckTransaction`, Bitcoin Core v28.0, `tx_check.cpp` lines
  11–59](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L11-L59),
  specialized to a transaction in regular position. A transaction in coinbase
  position is judged by block rules (#37), because coinbase-ness is positional;
  here its null prevout simply fails `Tx.AllInputOutpointsNeNull`. Passing these premises is
  not a standalone consensus verdict; block-extension validity composes them
  with contextual and block-wide premises.

  The enforced rule is the checker `Tx.isWellFormed`; `Tx.WellFormed` is the
  specification it is proved to enforce (`Tx.isWellFormed_iff`). Downstream
  theorems consume the specification's named fields. Each field refers to a
  reusable predicate whose name guides intuition and whose definition supplies
  the precise logical meaning.

  Core checks represented differently here, and why:

  * empty `vin` — an explicit premise, because the syntax admits the degenerate
    empty transaction Core's witness-aware decoder accepts ([Bitcoin Core
    v28.0, `transaction.h` lines
    220–252](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L220-L252)).
  * negative amounts — unrepresentable (`UInt64` values, `Nat` sums), unlike
    Core's signed `CAmount` and explicit negative-output rejection
    ([`amount.h` lines 11–12](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/amount.h#L11-L12),
    [`tx_check.cpp` lines 23–30](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L23-L30)).
  * per-output and running-total `MoneyRange` — in `Nat` the single sum
    bound `Tx.TotalOutputValueLeMaxMoney` subsumes every per-output bound; no overflow
    exists to re-check ([Bitcoin Core v28.0, `tx_check.cpp` lines
    23–33](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L23-L33)).
  * coinbase scriptSig length — a block rule (#37), with the rest of the
    coinbase's structural checks ([Bitcoin Core v28.0, `tx_check.cpp` lines
    47–50](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L47-L50)).

  Checked claims:

  * `Tx.stripped_size_bound_iff_core`: the semantic stripped transaction-size
    bound is equivalent to Core v28's weight-unit expression.
  * `Tx.isWellFormed_iff`: the checker accepts a transaction exactly when it
    satisfies the six stateless rules — some input and output exist, no outpoint
    is spent twice, no input claims the null outpoint, the outputs create at most
    `maxMoney` satoshis in total, and the stripped serialization fits within the
    historical one-million-byte ceiling.
  * `Tx.WellFormed.outputs_length_le`: a transaction satisfying the local
    premises has at most `2 ^ 32` outputs, so its `UInt32` output indices
    cannot wrap.
-/

namespace BtcVerified

/-- The transaction's serialization size without witness data: exactly Core's
`GetSerializeSize(TX_NO_WITNESS(tx))`, because `TxBody` is the stripped
serialization ([Bitcoin Core v28.0, `tx_check.cpp` lines
18–20](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L18-L20)). -/
def Tx.strippedSize (tx : Tx) : Nat :=
  (Serialize.Codec.encode tx.body).length

/-- The semantic stripped transaction-size bound is exactly equivalent to the
weight-unit expression Core v28 uses in `CheckTransaction`. This theorem keeps
the historical protocol rule primary while making the implementation
correspondence explicit ([Bitcoin Core v28.0, `tx_check.cpp` lines
18–21](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L18-L21)). -/
theorem Tx.stripped_size_bound_iff_core {tx : Tx} :
    tx.strippedSize ≤ Consensus.maxStrippedTransactionSize ↔
      tx.strippedSize * Consensus.witnessScaleFactor
        ≤ Consensus.maxBlockWeight := by
  unfold Consensus.maxStrippedTransactionSize Consensus.witnessScaleFactor
    Consensus.maxBlockWeight
  omega

/-- At least one input occurs in the transaction. This is list nonemptiness,
not the existence of the referenced outputs in a UTXO set. -/
def Tx.ExistsInput (tx : Tx) : Prop :=
  tx.body.inputs.val ≠ []

/-- At least one output occurs in the transaction. -/
def Tx.ExistsOutput (tx : Tx) : Prop :=
  tx.body.outputs.val ≠ []

/-- All input outpoints are distinct: no two input positions reference the same
outpoint. This excludes duplicate spends within this transaction, not conflicts
with other transactions. -/
def Tx.AllInputOutpointsDistinct (tx : Tx) : Prop :=
  tx.body.spends.Nodup

/-- Every input outpoint differs from the null outpoint. -/
def Tx.AllInputOutpointsNeNull (tx : Tx) : Prop :=
  ∀ outpoint ∈ tx.body.spends, outpoint ≠ OutPoint.null

/-- The sum of all output values is at most `Consensus.maxMoney` satoshis. -/
def Tx.TotalOutputValueLeMaxMoney (tx : Tx) : Prop :=
  (tx.body.outputs.val.map fun output => output.value.toNat).sum ≤ Consensus.maxMoney

/-- Witness-stripped serialization is at most `Consensus.maxStrippedTransactionSize`
bytes. This is not a bound on the full witness-inclusive encoding. -/
def Tx.StrippedSizeLeMaxStrippedTransactionSize (tx : Tx) : Prop :=
  tx.strippedSize ≤ Consensus.maxStrippedTransactionSize

-- Expand decision instances before compilation so `&&` keeps later checks conditional,
-- particularly the serialization-based size check.
/-- Decide whether an input exists. -/
@[macro_inline]
instance instDecidableExistsInput : DecidablePred Tx.ExistsInput :=
  fun _ => by unfold Tx.ExistsInput; infer_instance

/-- Decide whether an output exists. -/
@[macro_inline]
instance instDecidableExistsOutput : DecidablePred Tx.ExistsOutput :=
  fun _ => by unfold Tx.ExistsOutput; infer_instance

/-- Decide whether all input outpoints are distinct. -/
@[macro_inline]
instance instDecidableAllInputOutpointsDistinct :
    DecidablePred Tx.AllInputOutpointsDistinct :=
  fun _ => by unfold Tx.AllInputOutpointsDistinct; infer_instance

/-- Decide whether every input outpoint differs from the null outpoint. -/
@[macro_inline]
instance instDecidableAllInputOutpointsNeNull : DecidablePred Tx.AllInputOutpointsNeNull :=
  fun _ => by unfold Tx.AllInputOutpointsNeNull; infer_instance

/-- Decide whether total output value is at most `Consensus.maxMoney`. -/
@[macro_inline]
instance instDecidableTotalOutputValueLeMaxMoney : DecidablePred Tx.TotalOutputValueLeMaxMoney :=
  fun _ => by unfold Tx.TotalOutputValueLeMaxMoney; infer_instance

/-- Decide whether stripped size is at most `Consensus.maxStrippedTransactionSize`. -/
@[macro_inline]
instance instDecidableStrippedSizeLeMaxStrippedTransactionSize :
    DecidablePred Tx.StrippedSizeLeMaxStrippedTransactionSize :=
  fun _ => by unfold Tx.StrippedSizeLeMaxStrippedTransactionSize; infer_instance

/-- Decide the transaction-local admissibility premises for a regular
transaction: some input and output exist, no outpoint is spent twice, no input claims
the null outpoint, the outputs create at most `maxMoney` satoshis in total,
and the stripped serialization fits within the historical one-million-byte
ceiling. Core v28 expresses the equivalent check in weight units
([Bitcoin Core v28.0, `tx_check.cpp` lines
18–21](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L18-L21)). -/
def Tx.isWellFormed (tx : Tx) : Bool :=
  decide tx.ExistsInput
    && decide tx.ExistsOutput
    && decide tx.AllInputOutpointsDistinct
    && decide tx.AllInputOutpointsNeNull
    && decide tx.TotalOutputValueLeMaxMoney
    && decide tx.StrippedSizeLeMaxStrippedTransactionSize

/-- The specification `Tx.isWellFormed` enforces — the regular-transaction
projection of Core's `CheckTransaction`, one field per rule ([Bitcoin Core
v28.0, `tx_check.cpp` lines
11–59](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L11-L59)).
Each proof field uses its predicate's name with a lowercase initial. -/
structure Tx.WellFormed (tx : Tx) : Prop where
  /-- There is at least one input (`bad-txns-vin-empty`; [Bitcoin Core v28.0,
  `tx_check.cpp` lines 14–15](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L14-L15)). -/
  existsInput : tx.ExistsInput
  /-- There is at least one output (`bad-txns-vout-empty`; [Bitcoin Core v28.0,
  `tx_check.cpp` lines 16–17](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L16-L17)). -/
  existsOutput : tx.ExistsOutput
  /-- No two inputs consume the same outpoint (`bad-txns-inputs-duplicate`;
  [Bitcoin Core v28.0, `tx_check.cpp` lines
  36–44](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L36-L44)). -/
  allInputOutpointsDistinct : tx.AllInputOutpointsDistinct
  /-- No regular input claims the null outpoint (`bad-txns-prevout-null`;
  [Bitcoin Core v28.0, `tx_check.cpp` lines
  47–56](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L47-L56)). -/
  allInputOutpointsNeNull : tx.AllInputOutpointsNeNull
  /-- The outputs create at most `maxMoney` satoshis in total — which in
  `Nat` also bounds every individual output (`bad-txns-vout-toolarge`,
  `bad-txns-txouttotal-toolarge`; [Bitcoin Core v28.0, `tx_check.cpp` lines
  23–33](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L23-L33)). -/
  totalOutputValueLeMaxMoney : tx.TotalOutputValueLeMaxMoney
  /-- The stripped serialization fits within the historical one-million-byte
  ceiling (`bad-txns-oversize`). Core v28's weight-unit expression is proved
  equivalent by `Tx.stripped_size_bound_iff_core` ([Bitcoin Core v28.0,
  `tx_check.cpp` lines
  18–21](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L18-L21)). -/
  strippedSizeLeMaxStrippedTransactionSize : tx.StrippedSizeLeMaxStrippedTransactionSize

/-- The checker enforces exactly its specification: `isWellFormed` accepts a
transaction iff it is `WellFormed`. -/
theorem Tx.isWellFormed_iff {tx : Tx} :
    tx.isWellFormed = true ↔ tx.WellFormed := by
  simp only [isWellFormed, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨hinputs, houtputs⟩, hnodup⟩, hnull⟩, hbound⟩, hsize⟩
    exact ⟨hinputs, houtputs, hnodup, hnull, hbound, hsize⟩
  · rintro ⟨hinputs, houtputs, hnodup, hnull, hbound, hsize⟩
    exact ⟨⟨⟨⟨⟨hinputs, houtputs⟩, hnodup⟩, hnull⟩, hbound⟩, hsize⟩

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

/-- A transaction satisfying the local premises has at most `2 ^ 32` outputs:
the stripped transaction-size rule is far tighter than the width of an outpoint's
`vout`, so the `UInt32` indices used by the UTXO action cannot wrap
([Bitcoin Core v28.0, `tx_check.cpp` lines
18–21](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L18-L21)). -/
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
  have hsize := h.strippedSizeLeMaxStrippedTransactionSize
  unfold Tx.StrippedSizeLeMaxStrippedTransactionSize Consensus.maxStrippedTransactionSize at hsize
  omega

instance instDecidableWellFormed : DecidablePred Tx.WellFormed :=
  fun _ => decidable_of_iff _ Tx.isWellFormed_iff

end BtcVerified
