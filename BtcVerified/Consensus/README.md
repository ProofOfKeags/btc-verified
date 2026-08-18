# BtcVerified/Consensus

The rules layer: the central, legible statement of what Bitcoin consensus
demands, stated over the `Chainstate/` machine and never inside it (rules
import the machine; the machine never imports rules). The root consensus
judgment is whether a candidate block extends a parent-chain state under the
active ruleset, not whether a transaction is valid in isolation. Rules
therefore separate along two axes — their scope (transaction-local premises
vs block-wide conditions) and what they need (nothing beyond the object vs
chain state and position). This directory currently supplies the reusable
transaction premises and regular-transaction transition step; the block fold
that composes them into extension validity is next (#37).

Three disciplines hold everywhere. First, this is an abstract reasoning model:
its rules are factored to make protocol behavior and Bitcoin-level theorems
legible, not to reproduce Core's C++ control flow definitionally. Core strongly
influences the initial boundaries, and every claim about its behavior carries a
release-pinned source citation. Implementation-shaped transcriptions belong in
`Impl/`, where they can be proved equivalent to this model at the observable
boundary — accepted block extensions and the state transitions they produce —
and other implementations or forks can be compared against the same object.
Second, no premise embeds an activation height: premises take evaluation
context (the admitting block's height, block time, and median-time-past) plus
an explicit finality-clock choice, and "which rules are in force when" is an
external mapping, a later leaf (#38). Third, an enforced premise is a runnable `Bool` checker (the
definition), a `Prop` specification record naming its structural content, and a
proved equivalence between them; derived properties (conservation, the supply
limit) are theorems only, never runtime checks.

## The shape of a rule

`Limits.lean` holds the numeric constants (`maxMoney`, `coinbaseMaturity`,
`maxLegacySerializedSize`, `maxBlockWeight`, `witnessScaleFactor`, `lockTimeThreshold`,
`sequenceFinal`), each citing its Core counterpart. `LockTime.lean` interprets
the raw transaction lock-time field as disabled, an absolute block height, or
an absolute time; BIP68 relative locks remain the separate sequence-field leaf
#46. `TxContext.lean` carries the admitting height plus separately named block
time and median-time-past values. `FinalityClock` selects which one measures
absolute time locks: BIP113 changed that choice without changing `IsFinalTx`
([Bitcoin Core v28.0, `validation.cpp` lines
4224–4238](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L4224-L4238)),
so #38's ruleset mapping owns the explicit clock choice. `ScriptCheck.lean` is the
script-validity parameter: no formal script model exists yet, so these
premises take an abstract judgment over (all spent coins, input index,
spending transaction) — wide in the coin list because taproot signature
hashes commit to every spent output — with widening combinators (`ofCoinFree`,
`ofPerInput`) so narrower judgments are stated at their natural scope. A
zipper or other focus-by-construction API is deliberately deferred until the
script model can determine the interface it actually needs; the current
indexed interface is backed by a pointwise alignment theorem.

## Transaction-local premises

`TxStateless.lean`: what a regular transaction must satisfy before any chain
state is consulted — Core's [`CheckTransaction`, Bitcoin Core v28.0,
`tx_check.cpp` lines
11–59](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_check.cpp#L11-L59).
Empty inputs are an explicit premise: the syntax now admits the degenerate
empty-input/output object Core's witness-aware decoder accepts
([`transaction.h` lines
220–252](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L220-L252)).
Negative amounts remain unrepresentable, and in `Nat` one total-value bound
subsumes Core's per-output and running-total `MoneyRange` checks. The
legacy one-million-byte stripped-size ceiling is also a transaction-local
rule. Current Core expresses the equivalent predicate in block-weight units;
`Tx.stripped_size_bound_iff_core` records that implementation correspondence
without making the semantic rule depend on SegWit constants. The coinbase's
positional structural checks remain block rules (#37).

Checked claims:

- `Tx.stripped_size_bound_iff_core`: the semantic legacy serialized-size
  bound is exactly equivalent to Core v28's weight-unit expression.
- `Tx.isWellFormed_iff`: the stateless checker accepts a transaction exactly
  when some input and output exist, no outpoint is spent twice, no input claims
  the null outpoint, the outputs create at most `maxMoney` satoshis, and the
  stripped serialization fits within the legacy one-million-byte ceiling.
- `Tx.WellFormed.outputs_length_le`: that stripped-size rule implies every
  accepted transaction has at most `2 ^ 32` outputs, so its `UInt32` output
  indices cannot wrap.
Why it matters: these are reusable premises a block validator establishes for
every transaction before it ever reads the UTXO set, and the null-outpoint
rule is what separates the coinbase (judged positionally, by block rules) from
the regular transactions judged here.

## Contextual transaction premises

`TxContextual.lean`: what a regular transaction must satisfy relative to the
UTXO set and the admitting block — Core's [`Consensus::CheckTxInputs`, Bitcoin
Core v28.0, `tx_verify.cpp` lines
164–204](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L164-L204)
and [`IsFinalTx`, lines
17–37](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L17-L37),
script validity as the parameter, plus
`creates_do_not_overwrite`: no created outpoint may currently hold an unspent
coin. Input value and fee retain Core's explicit `MoneyRange` checks over
arbitrary UTXO sets ([Bitcoin Core v28.0, `tx_verify.cpp` lines
184–200](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L184-L200)); #50
tracks proving them redundant on reachable states once #37 supplies the
supply invariant. The no-overwrite rule is BIP30's content in current-state
vocabulary — recreating a fully-spent outpoint stays legal; the two 2010
duplicate-coinbase blocks and Core's post-BIP34 skip of the scan are activation
history ([Bitcoin Core v28.0, `validation.cpp` lines
2495–2575](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L2495-L2575))
(#38/#39), not rule content. BIP68 relative lock times need median-time-past
history no leaf provides yet and are deferred ([Bitcoin Core v28.0,
`tx_verify.cpp` lines
39–109](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L39-L109)).

Checked claims:

- `Coin.isMature_iff`: the maturity checker accepts a coin at a height
  exactly when it is non-coinbase or at least `coinbaseMaturity` blocks
  deep.
- `TxBody.isFinal_iff`: the finality checker accepts exactly when the lock
  time is zero, already past on the axis it selects, or overridden by every
  input carrying the final sequence.
- `Tx.spentCoins_aligned`: under the existence premise, each spent coin is
  exactly the lookup of the outpoint named by the corresponding input.
- `Tx.spentCoins_length`: the aligned input and coin lists have equal length.
- `Tx.isAdmissible_iff`: the contextual checker accepts exactly when inputs
  exist, coinbase spends are mature, cumulative input value and fee remain
  within `maxMoney`, inputs cover outputs, the transaction is final, no
  created outpoint is currently unspent, and every input passes the script
  judgment.

Why it matters: the specification record's fields are, by construction, the
hypotheses of the machine's action theorems. They are the contextual premises
the block fold consumes, stated in exactly the vocabulary the ledger
accounting uses.

## Guarded regular-transaction step

`ApplyChecked.lean`: where transaction premises meet the machine. The
discharge lemma converts an admissible transaction's guarantees into the
action theorems'
hypotheses, the gated conservation theorems specialize the accounting
identity with every local machine obligation discharged, and `applyChecked`
is the internal regular-transaction step that #37's block fold will iterate.
It is not a root consensus interface: only the complete fold, coinbase
epilogue, and block-wide premises establish a valid extension. Fees are not
spec objects: conservation is the accounting identity, and "the total drops
by exactly the fee" is its English reading.

Checked claims:

- `Tx.creates_do_not_overwrite_after_spend`: an admissible transaction's
  created outpoints remain fresh after its spends are erased.
- `UtxoSet.totalValue_apply_of_admissible`: for a premise-passing transaction,
  total value after plus value spent equals total value before plus value
  created.
- `UtxoSet.totalValue_apply_le_of_admissible`: a premise-passing transaction
  never increases the total value the set holds.
- `UtxoSet.applyChecked_eq_some_iff`: the internal step succeeds exactly when
  its transaction premises hold and then agrees with the guard-free action.

Why it matters: this is the per-transaction step the block fold (#37)
iterates. The delta invariant — a block grows the total by at most the
subsidy — and from it the 21-million supply bound are inductions over
exactly these theorems, and the ruleset mapping (#38) attaches exactly these
rules to heights.
