# BtcVerified/Consensus/Rule

### `BtcVerified.Consensus.Rule.Composition`

Finite bundles require every member on the same input and retain `List.all`
as their checker. They use the standard implication order: `stronger ≤ weaker`
means every input accepted by the stronger rule is accepted by the weaker one.
Conjunction is meet (`⊓`), and the empty bundle is top (`⊤`), accepting every input.

Ordinary mathlib laws apply directly. For `h : stronger ≤ weaker`,
`inf_eq_left.mpr h` proves `stronger ⊓ weaker = stronger`; `inf_assoc`,
`inf_comm`, and `le_trans` handle regrouping, reordering, and implication.

`Rule.contramap project` supplies a rule with the part of an input it reads.
It is an `InfTopHom`, so standard `map_inf`, `map_top`, and monotonicity laws
apply. `Rule.map_all` extends this to finite bundles for any such homomorphism,
including context projection.

Checked claims:

- `Rule.all_nil` and `Rule.all_cons`: empty and extended bundles agree with
  top and meet.
- `Rule.all_le_of_mem`: an accepted bundle establishes every member.
- `Rule.all_append`: appending bundles takes their meet.
- `Rule.map_all`: every homomorphism preserving finite meets and top preserves
  bundles.
- `Rule.inf_atHeight_holds_iff_left`: before activation, an added scheduled
  rule leaves the existing requirement unchanged.

Why it matters: one deployment can gate a whole bundle while later proofs
extract the individual requirements they consume. Standard order and
homomorphism laws supply the composition reasoning.
