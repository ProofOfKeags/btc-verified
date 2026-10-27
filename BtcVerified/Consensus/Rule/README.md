# BtcVerified/Consensus/Rule

### `BtcVerified.Consensus.Rule.Composition`

Conjunction and finite bundles combine verified requirements on the same
input. `contramap` supplies smaller rules with their own view of that input.
`stronger ≤ weaker` states implication using mathlib's partial order.

Checked claims:

- `Rule.all_le_of_mem`: an accepted bundle establishes every member.
- `Rule.all_append`: appending bundles conjoins their requirements.
- `Rule.map_all`: maps preserving meets and top preserve finite bundles.
- `Rule.and_atHeight_holds_iff_left`: an inactive addition has no effect.

Why it matters: one deployment can gate a whole bundle while later proofs
extract the individual named requirements they consume.
