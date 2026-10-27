# BtcVerified/Consensus/Activation

Deployment composition keeps applicability outside individual requirements.
Every assembled `Rule` contains a predicate, an executable checker, and a
proof of their equivalence. These are selected obligations, not a claim of
complete Bitcoin block validity. Historical activation thresholds are supplied
explicitly; accepting a threshold does not apply its rule before that height.

### `BtcVerified.Consensus.Activation.Height`

`Rule.atHeight` gates an existing requirement using a candidate-height
projection. Its threshold is inclusive. The requirement itself has no
deployment flag, and the input type can carry any context it needs.

Checked claims:

- `Rule.atHeight_check_before`: the gate accepts below its threshold.
- `Rule.atHeight_check_of_le`: from the threshold onward it runs the requirement.

Why it matters: a known historical activation can be expressed before adding
signaling or a complete block validator. Future sequence-lock rules can use
the same gate with `TxContext.height` as their height projection.

### `BtcVerified.Consensus.Activation.LockTime`

`TxBody.lockTimeRule` packages the existing absolute-finality specification
and checker over `(TxContext, TxBody)`. It preserves the explicitly selected
clock and the transaction's final-sequence override.

Checked claims:

- `TxBody.isLockTimeSatisfied_iff`: the adapter retains the existing theorem
  deciding exactly the `LockTimeSatisfied` requirement.

Why it matters: the height gate already applies to a real contextual rule.
The adapter does not authenticate the supplied clocks or choose a network's
activation history.

### Exceptions and explicit replacement

`Rule.unless` suspends one requirement for a checked exception. `Rule.choose`
selects one of two requirements. Neither operation implicitly waives other
requirements, and replacement carries no automatic refinement claim.

Checked claims:

- `Rule.check_unless_of_exception` and `check_unless_of_not_exception`: the
  exception affects exactly the requirement to which it is applied.
- `Rule.check_choose_of_condition` and `check_choose_of_not_condition`: only
  the selected requirement supplies the decision.

Why it matters: rare historical exceptions and non-refining replacements
stay explicit at assembly boundaries. The BIP30 identity examples distinguish
exact height/hash matches from height-only matches; their supplied freshness
results test selection, not the UTXO implementation or complete validity.
