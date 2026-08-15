# BtcVerified/Consensus

The rules layer: the central, legible statement of what Bitcoin consensus
demands, stated over the `Chainstate/` machine and never inside it (rules
import the machine; the machine never imports rules). Rules separate along
two axes — what they judge (transactions vs blocks) and what they need
(nothing beyond the object vs chain state and position). This directory
currently fills the two transaction buckets; block rules are next (#37).

Three disciplines hold everywhere. Every rule corresponds 1:1 to a check in
Bitcoin Core's consensus module and its doc-string says which; the *checkers*
are stated at whatever level of abstraction reads best, with equivalence to
Core's literal control flow left to `Impl/` transcriptions if ever wanted.
No rule embeds an activation height — rules take evaluation context (the
admitting block's height, the time lock times are measured against), and
"which rules are in force when" is an external mapping, a later leaf (#38).
An enforced rule is a runnable `Bool` checker (the definition), a `Prop`
specification record naming its structural content, and a proved equivalence
between them; derived properties (conservation, the supply limit) are
theorems only, never runtime checks.

## The shape of a rule

`Limits.lean` holds the numeric constants (`maxMoney`, `coinbaseMaturity`,
`maxBlockWeight`, `witnessScaleFactor`, `lockTimeThreshold`,
`sequenceFinal`), each citing its Core counterpart.
`TxContext.lean` is the evaluation context — height and measuring time;
BIP113 changed which clock Core passes without changing any rule, so the
clock choice belongs to the activation layer. `ScriptCheck.lean` is the
script-validity parameter: consensus does not execute scripts yet, so the
rules take a judgment over (all spent coins, input index, spending
transaction) — wide in the coin list because taproot signature hashes commit
to every spent output — with widening combinators (`ofCoinFree`,
`ofPerInput`) so narrower judgments are stated at their natural scope.

## Stateless transaction rules

`TxStateless.lean`: what a regular transaction must satisfy before any chain
state is consulted — Core's `CheckTransaction`. Empty inputs need no rule
(the transaction type cannot represent them), negative amounts are
unrepresentable, and in `Nat` one total-value bound subsumes Core's
per-output and running-total `MoneyRange` checks. The stripped-size ceiling is
also a transaction-local rule: although Core expresses it in block-weight
units, it reads only the transaction. The coinbase's positional structural
checks remain block rules (#37).

Checked claims:

- `Tx.isWellFormed_iff`: the stateless checker accepts a transaction exactly
  when some output exists, no outpoint is spent twice, no input claims the
  null outpoint, the outputs create at most `maxMoney` satoshis, and the
  stripped serialization fits within the per-transaction weight ceiling.
- `Tx.WellFormed.outputs_length_le`: that stripped-size rule implies every
  accepted transaction has at most `2 ^ 32` outputs, so its `UInt32` output
  indices cannot wrap.
- `Tx.body_inputs_ne_nil` (with the `Tx` type): every transaction has at
  least one input — Core's empty-`vin` check as a type invariant.

Why it matters: these are the rules a block validator runs on every
transaction before it ever reads the UTXO set, and the null-outpoint rule is
what separates the coinbase (judged positionally, by block rules) from the
regular transactions judged here.

## Contextual transaction rules

`TxContextual.lean`: what a regular transaction must satisfy relative to the
UTXO set and the admitting block — Core's `Consensus::CheckTxInputs` and
`IsFinalTx`, script validity as the parameter, plus `creates_absent`: no
created outpoint may currently hold an unspent coin. Input value and fee
retain Core's explicit `MoneyRange` checks over arbitrary UTXO sets; #50
tracks proving them redundant on reachable states once #37 supplies the
supply invariant. The no-overwrite rule is BIP30's content in current-state
vocabulary — recreating a fully-spent outpoint stays legal; the two 2010
duplicate-coinbase blocks and Core's post-BIP34 skip of the scan are
activation history (#38/#39), not rule content. BIP68 relative lock times
need median-time-past history no leaf provides yet and are deferred.

Checked claims:

- `Coin.isMature_iff`: the maturity checker accepts a coin at a height
  exactly when it is non-coinbase or at least `coinbaseMaturity` blocks
  deep.
- `TxBody.isFinal_iff`: the finality checker accepts exactly when the lock
  time is zero, already past on the axis it selects, or overridden by every
  input carrying the final sequence.
- `Tx.spentCoins_length`: under the existence rule, the spent-coin list
  aligns with the inputs — one coin per input, in order.
- `Tx.isAdmissible_iff`: the contextual checker accepts exactly when inputs
  exist, coinbase spends are mature, cumulative input value and fee remain
  within `maxMoney`, inputs cover outputs, the transaction is final, no
  created outpoint is currently unspent, and every input passes the script
  judgment.

Why it matters: the specification record's fields are, by construction,
the hypotheses of the machine's action theorems — the rules are stated in
exactly the vocabulary the ledger accounting consumes.

## Guarded application

`ApplyChecked.lean`: where rules meet machine. The discharge lemma converts
a rule-passing transaction's guarantees into the action theorems'
hypotheses, the gated conservation theorems specialize the accounting
identity with every root-level transaction property discharged, and
`applyChecked` is the strict rules-then-act interface. Fees are not spec
objects: conservation is the accounting identity, and "the total drops by
exactly the fee" is its English reading.

Checked claims:

- `Tx.creates_absent_spend`: a rule-passing transaction's created outpoints
  are absent even after its spends are erased.
- `UtxoSet.totalValue_apply_of_admissible`: for a rule-passing transaction,
  total value after plus value spent equals total value before plus value
  created.
- `UtxoSet.totalValue_apply_le_of_admissible`: a rule-passing transaction
  never increases the total value the set holds.
- `UtxoSet.applyChecked_eq_some_iff`: the strict interface succeeds on
  exactly the rule-passing transactions and then agrees with the guard-free
  action.

Why it matters: this is the per-transaction step the block fold (#37)
iterates. The delta invariant — a block grows the total by at most the
subsidy — and from it the 21-million supply bound are inductions over
exactly these theorems, and the ruleset mapping (#38) attaches exactly these
rules to heights.
