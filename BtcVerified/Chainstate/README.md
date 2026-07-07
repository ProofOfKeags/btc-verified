# BtcVerified/Chainstate

The UTXO set and the uniform action a transaction performs on it — the
*machine* that consensus rules will be stated over, kept strictly free of the
rules themselves. `UtxoSet` is the finite map from `OutPoint` to `Coin`
(Mathlib `Finmap` as the spec representation; efficiency is a later `Impl/`
transport). A `Coin` is the `TxOut` plus its `Provenance` — creation height
and coinbase-position flag, the metadata spend-time guards need and the
spending transaction cannot carry; coinbase-ness is positional, so the block
layer supplies the flag. `UtxoSet.apply` erases what a transaction spends and
inserts what it creates, keyed by txid and output index — one total,
guard-free function for every transaction, coinbase included (its
null-outpoint erase is vacuous), over `TxBody` because witnesses never touch
the UTXO set. `totalValue` sums in `Nat`: `UInt64` sums wrap, and the bound
that would prevent it is a guard, which this layer does not have.

Checked claims:

- `UtxoSet.lookup_apply_of_mem_creates` / `UtxoSet.lookup_apply_output`:
  after applying a transaction (at most 2³² outputs, the `vout` width),
  lookup at a created outpoint finds exactly that output as a coin — output
  `i` sits at the outpoint keyed by the txid and `i`, stamped with the
  supplied provenance (`TxBody.creates` is a function of the transaction
  alone; provenance is context, stamped on at `apply`).
- `UtxoSet.lookup_apply_of_mem_spends`: lookup at a spent outpoint the
  transaction does not re-create returns `none`.
- `UtxoSet.lookup_apply_of_notMem`: lookup at an outpoint the transaction
  neither spends nor creates is untouched.
- `UtxoSet.totalValue_apply`: the accounting identity, subtraction-free in
  `Nat` — total value after applying, plus the values spent, equals total
  value before, plus the values created. Its hypotheses (distinct, present
  spends; created keys fresh; the 2³² output bound) are exactly what the
  transaction-validity guards will supply.
- Beneath these, the primitive characterizations
  (`UtxoSet.lookup_spend_of_mem` / `of_notMem`, `UtxoSet.lookup_create_of_mem`,
  `UtxoSet.totalValue_spend`, `UtxoSet.totalValue_create`),
  `UtxoSet.spend_perm` (order-freedom within a transaction is a theorem of
  the machine, not a type-level restatement), and `Finmap.insert_erase` in
  `Ext/`.

Why it matters: this is the validity layer's foundation. Consensus validity
is stateful — a chain is valid when folding its blocks through the state
succeeds — and the action/guard split made here is what keeps that layer
honest: every transaction, coinbase included, *acts* identically; only the
*guards* differ, and they land as explicitly stated rules in a dedicated
consensus layer. The accounting identity is the engine of the coming monetary
theorems: under the block-level delta invariant (`totalValue` grows by at
most the subsidy) it folds directly into the supply limit.
