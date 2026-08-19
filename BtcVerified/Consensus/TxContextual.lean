import BtcVerified.Chainstate.Apply
import BtcVerified.Consensus.Limits
import BtcVerified.Consensus.LockTime
import BtcVerified.Consensus.TxContext
import BtcVerified.Consensus.ScriptCheck
/-!
  # Contextual transaction premises

  The chain-contextual premises a regular transaction must establish while a
  candidate block is being checked against the UTXO set — Core's
  [`Consensus::CheckTxInputs`, Bitcoin Core v28.0, `tx_verify.cpp` lines
  164–204](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L164-L204)
  and [`IsFinalTx`, lines
  17–37](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L17-L37),
  plus the rule that keeps the machine's insert-replaces path unreachable.
  These predicates are reusable steps inside block-extension validity, not a
  standalone consensus verdict for a transaction. Script validity is the
  `ScriptCheck` parameter; every rule here is script-agnostic.

  The enforced rule is the checker `Tx.isAdmissible`; `Tx.Admissible` is the
  specification it is proved to enforce (`Tx.isAdmissible_iff`), and its
  named fields are exactly the facts the action theorems consume.

  Core's `MoneyRange` checks on value-in and fee remain explicit here even
  though `Nat` eliminates arithmetic overflow: this checker ranges over an
  arbitrary `UtxoSet`, not only states reachable from genesis ([Bitcoin Core
  v28.0, `tx_verify.cpp` lines
  184–200](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L184-L200)). Issue #50
  tracks proving these checks redundant under the supply invariant once #37
  provides it.

  One contextual Core rule remains deferred: BIP68 relative lock times need
  per-coin median-time-past history that no leaf provides yet ([Bitcoin Core
  v28.0, `tx_verify.cpp` lines
  39–109](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L39-L109)).

  `creates_do_not_overwrite` is BIP30's content in current-state vocabulary: a
  transaction may not create an outpoint that *currently* holds an unspent
  coin (recreating a fully-spent outpoint is legal — it happened before
  BIP34). The two 2010 duplicate-coinbase blocks and Core's post-BIP34 skip
  of this check are activation history ([Bitcoin Core v28.0, `validation.cpp`
  lines 2495–2575](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L2495-L2575)),
  owned by the ruleset mapping (#38/#39); the rule itself is height-free.

  Checked claims:

  * `Coin.isMature_iff`: the maturity checker accepts a coin at a height
    exactly when the coin is non-coinbase or `coinbaseMaturity` blocks deep.
  * `TxBody.isLockTimeSatisfied_iff`: for an explicitly selected lock-time
    clock, the checker accepts exactly when the interpreted absolute lock is
    disabled or past, or every input carries the `sequenceFinal` sentinel.
  * `Tx.spentCoins_aligned`: under the existence rule, each spent coin is the
    lookup of the outpoint named by the corresponding input.
  * `Tx.spentCoins_length`: the aligned lists have equal length.
  * `Tx.isAdmissible_iff`: the checker accepts a transaction exactly when it
    satisfies the eight contextual rules — inputs exist, coinbase spends are
    mature, input value and fee stay within `maxMoney`, inputs cover outputs,
    the transaction's absolute lock-time condition is satisfied, no created
    outpoint is currently unspent, and every input passes the script judgment.
-/

namespace BtcVerified

/-- Decide that a coin is spendable at `height`: immediately, unless it was
created in coinbase position — then only once `coinbaseMaturity` blocks
deep ([Bitcoin Core v28.0, `tx_verify.cpp` lines
178–181](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L178-L181)). -/
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

/-- The semantic absolute lock time interpreted from the body's raw wire
field. Relative lock times are per-input sequence semantics deferred to #46. -/
def TxBody.interpretedLockTime (body : TxBody) : Consensus.LockTime :=
  Consensus.LockTime.ofUInt32 body.lockTime

/-- Decide whether the transaction's absolute lock-time condition is satisfied
under an explicitly selected clock (Core calls this `IsFinalTx`): the
interpreted absolute lock is disabled or already
past, or every input overrides it with the `sequenceFinal` value ([Bitcoin Core
v28.0, `tx_verify.cpp` lines
17–37](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L17-L37)).
The height-indexed ruleset in #38 selects `.blockTime` before BIP113 and
`.medianTimePast` after it. -/
def TxBody.isLockTimeSatisfied (body : TxBody) (clock : LockTimeClock)
    (ctx : TxContext) : Bool :=
  body.interpretedLockTime.isPast ctx.height (ctx.timeFor clock)
    || body.inputs.val.all (·.sequence == Consensus.sequenceFinal)

/-- The specification `TxBody.isLockTimeSatisfied` enforces: the interpreted
absolute lock has passed under the selected clock, or every input carries the
`sequenceFinal` sentinel. -/
def TxBody.LockTimeSatisfied (body : TxBody) (clock : LockTimeClock)
    (ctx : TxContext) : Prop :=
  body.interpretedLockTime.Past ctx.height (ctx.timeFor clock)
    ∨ ∀ input ∈ body.inputs.val, input.sequence = Consensus.sequenceFinal

/-- The lock-time checker enforces exactly its specification:
`isLockTimeSatisfied` accepts a body in a context iff its `LockTimeSatisfied`
proposition holds there. -/
theorem TxBody.isLockTimeSatisfied_iff {body : TxBody} {clock : LockTimeClock}
    {ctx : TxContext} :
    body.isLockTimeSatisfied clock ctx = true ↔
      body.LockTimeSatisfied clock ctx := by
  simp [isLockTimeSatisfied, LockTimeSatisfied,
    Consensus.LockTime.isPast_iff, List.all_eq_true]

/-- The semantic lock-time specification is equivalent to Core's wire-shaped
`IsFinalTx` statement: zero lock time, raw threshold-selected comparison, or
the all-`sequenceFinal` override ([Bitcoin Core v28.0, `tx_verify.cpp` lines
17–37](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L17-L37)). -/
theorem TxBody.lockTimeSatisfied_iff_core {body : TxBody}
    {clock : LockTimeClock}
    {ctx : TxContext} :
    body.LockTimeSatisfied clock ctx ↔
      body.lockTime = 0
        ∨ body.lockTime.toNat <
          (if body.lockTime.toNat < Consensus.lockTimeThreshold
           then ctx.height else ctx.timeFor clock)
        ∨ ∀ input ∈ body.inputs.val,
          input.sequence = Consensus.sequenceFinal := by
  simp only [LockTimeSatisfied, interpretedLockTime,
    Consensus.LockTime.ofUInt32_past_iff]
  tauto

/-- The coins a transaction's inputs consume, in input order — total via
`filterMap`, aligned with the inputs whenever the existence rule holds
(`Tx.spentCoins_length`). -/
def Tx.spentCoins (tx : Tx) (utxos : UtxoSet) : List Coin :=
  tx.body.spends.filterMap fun o => utxos.lookup o

/-- Under the existence rule, the spent-coin list is pointwise aligned with
the inputs: each coin is exactly the lookup of the outpoint named by the
corresponding input. -/
theorem Tx.spentCoins_aligned {tx : Tx} {utxos : UtxoSet}
    (h : ∀ o ∈ tx.body.spends, o ∈ utxos) :
    List.Forall₂ (fun input coin =>
      utxos.lookup input.prevout = some coin)
      tx.body.inputs.val (tx.spentCoins utxos) := by
  have aligned : ∀ inputs : List TxIn,
      (∀ input ∈ inputs, input.prevout ∈ utxos) →
      List.Forall₂ (fun input coin =>
        utxos.lookup input.prevout = some coin)
        inputs ((inputs.map fun input => input.prevout).filterMap utxos.lookup) := by
    intro inputs
    induction inputs with
    | nil =>
        intro _
        exact .nil
    | cons input inputs ih =>
        intro hinputs
        have hmem : input.prevout ∈ utxos := hinputs input (by simp)
        have hsome := Finmap.lookup_isSome.mpr hmem
        cases hlookup : utxos.lookup input.prevout with
        | none => simp [hlookup] at hsome
        | some coin =>
            simp only [List.map_cons, List.filterMap_cons, hlookup]
            exact .cons hlookup
              (ih fun next hnext => hinputs next (by simp [hnext]))
  unfold spentCoins
  rw [TxBody.spends]
  exact aligned tx.body.inputs.val fun input hinput =>
    h input.prevout (by
      rw [TxBody.spends]
      exact List.mem_map.mpr ⟨input, hinput, rfl⟩)

/-- Under the existence rule there is one spent coin per input. This is the
length consequence of `Tx.spentCoins_aligned`. -/
theorem Tx.spentCoins_length {tx : Tx} {utxos : UtxoSet}
    (h : ∀ o ∈ tx.body.spends, o ∈ utxos) :
    (tx.spentCoins utxos).length = tx.body.inputs.val.length :=
  (Tx.spentCoins_aligned h).length_eq.symm

/-- Decide the contextual admissibility premises for one regular-transaction
step over the UTXO set, script validity supplied as a parameter: inputs exist,
coinbase spends are mature, input value and fee stay within `maxMoney`, inputs
cover outputs, the absolute lock-time condition is satisfied, no created
outpoint is currently overwritten, and every input passes the script judgment. -/
def Tx.isAdmissible (scriptOk : ScriptCheck) (utxos : UtxoSet)
    (clock : LockTimeClock) (ctx : TxContext) (tx : Tx) : Bool :=
  tx.body.spends.all (fun o => (utxos.lookup o).isSome)
    && tx.body.spends.all
        (fun o => ((utxos.lookup o).map (·.isMature ctx.height)).getD true)
    && decide ((tx.body.spends.map utxos.valueAt).sum
        ≤ Consensus.maxMoney)
    && decide ((tx.body.outputs.val.map fun o => o.value.toNat).sum
        ≤ (tx.body.spends.map utxos.valueAt).sum)
    && decide ((tx.body.spends.map utxos.valueAt).sum
        - (tx.body.outputs.val.map fun o => o.value.toNat).sum
        ≤ Consensus.maxMoney)
    && tx.body.isLockTimeSatisfied clock ctx
    && tx.body.creates.all (fun entry => (utxos.lookup entry.1).isNone)
    && (List.range tx.body.inputs.val.length).all
        (fun i => scriptOk (tx.spentCoins utxos) i tx)

/-- The specification `Tx.isAdmissible` enforces — an abstract factoring of
Core's contextual checks for a regular transaction, one field per rule; the
fields are the facts the action theorems consume ([Bitcoin Core v28.0,
`tx_verify.cpp` lines
164–204](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L164-L204)). -/
structure Tx.Admissible (scriptOk : ScriptCheck) (utxos : UtxoSet)
    (clock : LockTimeClock) (ctx : TxContext) (tx : Tx) : Prop where
  /-- Every input's outpoint is an unspent coin
  (`bad-txns-inputs-missingorspent`; [Bitcoin Core v28.0, `tx_verify.cpp` lines
  164–170](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L164-L170)). -/
  spends_mem : ∀ o ∈ tx.body.spends, o ∈ utxos
  /-- Every coinbase coin spent is at least `coinbaseMaturity` blocks deep
  (`bad-txns-premature-spend-of-coinbase`; [Bitcoin Core v28.0,
  `tx_verify.cpp` lines 178–181](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L178-L181)). -/
  spends_mature : ∀ o ∈ tx.body.spends, ∀ coin,
    utxos.lookup o = some coin → coin.Mature ctx.height
  /-- The total input value stays within `maxMoney`; in `Nat` this one total
  bound subsumes Core's per-coin and running-total `MoneyRange` checks
  ([Bitcoin Core v28.0, `tx_verify.cpp` lines
  184–188](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L184-L188)). -/
  input_values_bounded : (tx.body.spends.map utxos.valueAt).sum
    ≤ Consensus.maxMoney
  /-- The inputs cover the outputs: value out ≤ value in, in `Nat` — fee
  non-negativity is this same fact (`bad-txns-in-belowout`; [Bitcoin Core
  v28.0, `tx_verify.cpp` lines
  191–195](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L191-L195)). -/
  values_cover : (tx.body.outputs.val.map fun o => o.value.toNat).sum
    ≤ (tx.body.spends.map utxos.valueAt).sum
  /-- The fee — input value minus output value in `Nat` — stays within
  `maxMoney` ([Bitcoin Core v28.0, `tx_verify.cpp` lines
  197–200](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L197-L200)). -/
  fee_bounded : (tx.body.spends.map utxos.valueAt).sum
      - (tx.body.outputs.val.map fun o => o.value.toNat).sum
    ≤ Consensus.maxMoney
  /-- The transaction's absolute lock-time condition is satisfied for the
  admitting block (`bad-txns-nonfinal`;
  [Bitcoin Core v28.0, `validation.cpp` lines
  4231–4239](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L4231-L4239)). -/
  lock_time_satisfied : tx.body.LockTimeSatisfied clock ctx
  /-- Creating this transaction's outputs does not overwrite any currently
  unspent outpoint — BIP30's content; its historical carve-outs are the
  activation layer's business (#38/#39; [Bitcoin Core v28.0, `validation.cpp`
  lines 2495–2575](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L2495-L2575)). -/
  creates_do_not_overwrite :
    ∀ o ∈ tx.body.creates.map Prod.fst, o ∉ utxos
  /-- Every input satisfies the script judgment against the coins the
  transaction spends; Core invokes `CheckInputScripts` for every regular
  transaction while connecting a block ([Bitcoin Core v28.0, `validation.cpp`
  lines 2659–2671](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L2659-L2671)). -/
  scripts_ok : ∀ i < tx.body.inputs.val.length,
    scriptOk (tx.spentCoins utxos) i tx = true

/-- The checker enforces exactly its specification: `isAdmissible` accepts a
transaction iff it is `Admissible`. -/
theorem Tx.isAdmissible_iff {scriptOk : ScriptCheck} {utxos : UtxoSet}
    {clock : LockTimeClock} {ctx : TxContext} {tx : Tx} :
    tx.isAdmissible scriptOk utxos clock ctx = true
      ↔ Tx.Admissible scriptOk utxos clock ctx tx := by
  simp only [isAdmissible, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, TxBody.isLockTimeSatisfied_iff, List.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨hmem, hmature⟩, hinputBound⟩, hcover⟩, hfee⟩,
      hlock⟩, habsent⟩, hscripts⟩
    refine ⟨fun o ho => Finmap.lookup_isSome.mp (hmem o ho), ?_,
      hinputBound, hcover, hfee, hlock, ?_, fun i hi => hscripts i hi⟩
    · intro o ho coin hcoin
      have hgetD := hmature o ho
      rw [hcoin] at hgetD
      exact Coin.isMature_iff.mp hgetD
    · intro o ho
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp ho
      have hnone := habsent entry hentry
      rw [Option.isNone_iff_eq_none, Finmap.lookup_eq_none] at hnone
      exact hnone
  · rintro ⟨hmem, hmature, hinputBound, hcover, hfee, hlock, habsent,
      hscripts⟩
    refine ⟨⟨⟨⟨⟨⟨⟨fun o ho => Finmap.lookup_isSome.mpr (hmem o ho), ?_⟩,
      hinputBound⟩, hcover⟩, hfee⟩, hlock⟩, ?_⟩,
      fun i hi => hscripts i hi⟩
    · intro o ho
      cases hcoin : utxos.lookup o with
      | none => rfl
      | some coin =>
          exact Coin.isMature_iff.mpr (hmature o ho coin hcoin)
    · intro entry hentry
      rw [Option.isNone_iff_eq_none, Finmap.lookup_eq_none]
      exact habsent _ (List.mem_map_of_mem hentry)

instance instDecidableAdmissible (scriptOk : ScriptCheck) (utxos : UtxoSet)
    (clock : LockTimeClock) (ctx : TxContext) :
    DecidablePred (Tx.Admissible scriptOk utxos clock ctx) :=
  fun _ => decidable_of_iff _ Tx.isAdmissible_iff

end BtcVerified
