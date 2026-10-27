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

### `BtcVerified.Consensus.Activation.Finality`

The finality bundle always enforces block-time finality and adds MTP finality
at a supplied height. It demonstrates cumulative refinement using real rules.

Checked claims:

- `TxBody.lockTimeSatisfied_blockTime_of_medianTimePast`: MTP finality implies
  block-time finality when the supplied clocks are ordered.
- `TxBody.finalityRules_check_before`: before activation the checker is the
  existing block-time checker.
- `TxBody.finalityRules_check_of_le`: after activation it is the MTP checker,
  assuming MTP is no later than block time.

Why it matters: stronger rules can subsume older checks with explicit
hypotheses; arbitrary `TxContext` values do not establish clock order.
