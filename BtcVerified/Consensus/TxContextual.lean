import BtcVerified.Chainstate.Apply
import BtcVerified.Consensus.Limits
import BtcVerified.Consensus.TxContext
import BtcVerified.Consensus.ScriptCheck
/-!
  # Contextual transaction rules

  The chain-contextual bucket: what consensus demands of a regular
  transaction relative to the UTXO set and the admitting block — Core's
  `Consensus::CheckTxInputs` (`src/consensus/tx_verify.cpp`) and `IsFinalTx`,
  plus the rule that keeps the machine's insert-replaces path unreachable.
  Script validity is the `ScriptCheck` parameter; every rule here is
  script-agnostic.

  The enforced rule is the checker `Tx.isAdmissible`; `Tx.Admissible` is the
  specification it is proved to enforce (`Tx.isAdmissible_iff`), and its
  named fields are exactly the facts the action theorems consume.

  Two Core checks have no rule here, and why:

  * the `MoneyRange` re-checks on value-in and fee are `int64` overflow
    armor; in `Nat` there is no overflow, and the sub-`maxMoney` bound on
    any honest set's values is the supply theorem's business (#37).
  * BIP68 relative lock times need per-coin median-time-past history that
    no leaf provides yet; deferred to its own leaf.

  `creates_absent` is BIP30's content in current-state vocabulary: a
  transaction may not create an outpoint that *currently* holds an unspent
  coin (recreating a fully-spent outpoint is legal — it happened before
  BIP34). The two 2010 duplicate-coinbase blocks and Core's post-BIP34 skip
  of this check are activation history, owned by the ruleset mapping
  (#38/#39); the rule itself is height-free.

  Checked claims:

  * `Coin.isMature_iff`: the maturity checker accepts a coin at a height
    exactly when the coin is non-coinbase or `coinbaseMaturity` blocks deep.
  * `TxBody.isFinal_iff`: the finality checker accepts exactly when the lock
    is zero, already past on the axis the lock time selects, or overridden
    by every input carrying the final sequence.
  * `Tx.spentCoins_length`: under the existence rule, the spent-coin list
    has one coin per input.
  * `Tx.isAdmissible_iff`: the checker accepts a transaction exactly when it
    satisfies the six contextual rules — inputs exist, coinbase spends are
    mature, inputs cover outputs, the transaction is final, no created
    outpoint is currently unspent, and every input passes the script
    judgment.
-/

namespace BtcVerified

/-- Decide that a coin is spendable at `height`: immediately, unless it was
created in coinbase position — then only once `coinbaseMaturity` blocks
deep. -/
def Coin.isMature (coin : Coin) (height : Nat) : Bool :=
  !coin.provenance.coinbase
    || decide (coin.provenance.height + Consensus.coinbaseMaturity ≤ height)

/-- The specification `Coin.isMature` enforces: coinbase provenance implies
the creation height is at least `coinbaseMaturity` blocks above. -/
def Coin.Mature (coin : Coin) (height : Nat) : Prop :=
  coin.provenance.coinbase = true →
    coin.provenance.height + Consensus.coinbaseMaturity ≤ height

/-- The maturity checker enforces exactly its specification: `isMature`
accepts a coin at a height iff the coin is `Mature` there. -/
theorem Coin.isMature_iff {coin : Coin} {height : Nat} :
    coin.isMature height = true ↔ coin.Mature height := by
  simp only [isMature, Mature, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq]
  constructor
  · rintro (hcb | hdeep) htrue
    · rw [htrue] at hcb
      cases hcb
    · exact hdeep
  · intro h
    cases hcb : coin.provenance.coinbase with
    | false => exact Or.inl rfl
    | true => exact Or.inr (h hcb)

/-- Decide lock-time finality for an evaluation context (Core's `IsFinalTx`):
the lock is disabled (zero), already past — the lock time itself selecting
the height or time axis by `lockTimeThreshold` — or overridden by every
input carrying the final sequence. -/
def TxBody.isFinal (body : TxBody) (ctx : TxContext) : Bool :=
  body.lockTime == 0
    || decide (body.lockTime.toNat <
        if body.lockTime.toNat < Consensus.lockTimeThreshold
        then ctx.height else ctx.time)
    || body.inputs.val.all (·.sequence == Consensus.sequenceFinal)

/-- The specification `TxBody.isFinal` enforces: the lock time is zero, or
strictly below the height or time the threshold axis selects, or every
input's sequence is final. -/
def TxBody.Final (body : TxBody) (ctx : TxContext) : Prop :=
  body.lockTime = 0
    ∨ body.lockTime.toNat <
        (if body.lockTime.toNat < Consensus.lockTimeThreshold
         then ctx.height else ctx.time)
    ∨ ∀ input ∈ body.inputs.val, input.sequence = Consensus.sequenceFinal

/-- The finality checker enforces exactly its specification: `isFinal`
accepts a body in a context iff the body is `Final` there. -/
theorem TxBody.isFinal_iff {body : TxBody} {ctx : TxContext} :
    body.isFinal ctx = true ↔ body.Final ctx := by
  simp [isFinal, Final, Bool.or_eq_true, List.all_eq_true, or_assoc]

/-- The coins a transaction's inputs consume, in input order — total via
`filterMap`, aligned with the inputs whenever the existence rule holds
(`Tx.spentCoins_length`). -/
def Tx.spentCoins (tx : Tx) (utxos : UtxoSet) : List Coin :=
  tx.body.spends.filterMap fun o => utxos.lookup o

/-- Under the existence rule the spent-coin list is aligned with the inputs:
one coin per input, in order. -/
theorem Tx.spentCoins_length {tx : Tx} {utxos : UtxoSet}
    (h : ∀ o ∈ tx.body.spends, o ∈ utxos) :
    (tx.spentCoins utxos).length = tx.body.inputs.val.length := by
  have hlen : (tx.body.spends.filterMap fun o => utxos.lookup o).length
      = tx.body.spends.length :=
    List.filterMap_length_eq_length.mpr
      fun o ho => Finmap.lookup_isSome.mpr (h o ho)
  rw [spentCoins, hlen, TxBody.spends, List.length_map]

/-- Decide the chain-contextual validity of a regular transaction over the
UTXO set, script validity supplied as a parameter: inputs exist, coinbase
spends are mature, inputs cover outputs, the transaction is final, no
created outpoint is currently unspent, and every input passes the script
judgment. -/
def Tx.isAdmissible (scriptOk : ScriptCheck) (utxos : UtxoSet)
    (ctx : TxContext) (tx : Tx) : Bool :=
  tx.body.spends.all (fun o => (utxos.lookup o).isSome)
    && tx.body.spends.all
        (fun o => ((utxos.lookup o).map (·.isMature ctx.height)).getD true)
    && decide ((tx.body.outputs.val.map fun o => o.value.toNat).sum
        ≤ (tx.body.spends.map utxos.valueAt).sum)
    && tx.body.isFinal ctx
    && tx.body.creates.all (fun entry => (utxos.lookup entry.1).isNone)
    && (List.range tx.body.inputs.val.length).all
        (fun i => scriptOk (tx.spentCoins utxos) i tx)

/-- The specification `Tx.isAdmissible` enforces — Core's contextual checks
for a regular transaction, one field per rule; the fields are the facts the
action theorems consume. -/
structure Tx.Admissible (scriptOk : ScriptCheck) (utxos : UtxoSet)
    (ctx : TxContext) (tx : Tx) : Prop where
  /-- Every input's outpoint is an unspent coin
  (`bad-txns-inputs-missingorspent`). -/
  spends_mem : ∀ o ∈ tx.body.spends, o ∈ utxos
  /-- Every coinbase coin spent is at least `coinbaseMaturity` blocks deep
  (`bad-txns-premature-spend-of-coinbase`). -/
  spends_mature : ∀ o ∈ tx.body.spends, ∀ coin,
    utxos.lookup o = some coin → coin.Mature ctx.height
  /-- The inputs cover the outputs: value out ≤ value in, in `Nat` — fee
  non-negativity is this same fact (`bad-txns-in-belowout`). -/
  values_cover : (tx.body.outputs.val.map fun o => o.value.toNat).sum
    ≤ (tx.body.spends.map utxos.valueAt).sum
  /-- The transaction is final for the admitting block (`non-final`). -/
  final : tx.body.Final ctx
  /-- No created outpoint currently holds an unspent coin — BIP30's content;
  its historical carve-outs are the activation layer's business (#38/#39). -/
  creates_absent : ∀ o ∈ tx.body.creates.map Prod.fst, o ∉ utxos
  /-- Every input satisfies the script judgment against the coins the
  transaction spends. -/
  scripts_ok : ∀ i < tx.body.inputs.val.length,
    scriptOk (tx.spentCoins utxos) i tx = true

/-- The checker enforces exactly its specification: `isAdmissible` accepts a
transaction iff it is `Admissible`. -/
theorem Tx.isAdmissible_iff {scriptOk : ScriptCheck} {utxos : UtxoSet}
    {ctx : TxContext} {tx : Tx} :
    tx.isAdmissible scriptOk utxos ctx = true
      ↔ Tx.Admissible scriptOk utxos ctx tx := by
  simp only [isAdmissible, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, TxBody.isFinal_iff, List.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨⟨hmem, hmature⟩, hcover⟩, hfinal⟩, habsent⟩, hscripts⟩
    refine ⟨fun o ho => Finmap.lookup_isSome.mp (hmem o ho), ?_, hcover,
      hfinal, ?_, fun i hi => hscripts i hi⟩
    · intro o ho coin hcoin
      have hgetD := hmature o ho
      rw [hcoin] at hgetD
      exact Coin.isMature_iff.mp hgetD
    · intro o ho
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp ho
      have hnone := habsent entry hentry
      rw [Option.isNone_iff_eq_none, Finmap.lookup_eq_none] at hnone
      exact hnone
  · rintro ⟨hmem, hmature, hcover, hfinal, habsent, hscripts⟩
    refine ⟨⟨⟨⟨⟨fun o ho => Finmap.lookup_isSome.mpr (hmem o ho), ?_⟩,
      hcover⟩, hfinal⟩, ?_⟩, fun i hi => hscripts i hi⟩
    · intro o ho
      cases hcoin : utxos.lookup o with
      | none => rfl
      | some coin =>
          exact Coin.isMature_iff.mpr (hmature o ho coin hcoin)
    · intro entry hentry
      rw [Option.isNone_iff_eq_none, Finmap.lookup_eq_none]
      exact habsent _ (List.mem_map_of_mem hentry)

instance instDecidableAdmissible (scriptOk : ScriptCheck) (utxos : UtxoSet)
    (ctx : TxContext) : DecidablePred (Tx.Admissible scriptOk utxos ctx) :=
  fun _ => decidable_of_iff _ Tx.isAdmissible_iff

end BtcVerified
