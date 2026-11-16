# BtcVerified/Crypto

The hashing layer: the abstract 256-bit digest type, a concrete computable
SHA-256, the collision vocabulary that lets proofs consume collision
resistance soundly, and Bitcoin's merkle tree.

## `Hash256` and the collision vocabulary

`Hash256` is the digest type everything downstream states commitments against.
`Collision h a b` states that the two specified inputs are distinct and have the
same image. `CollisionAt h f g` locates such a collision at a common position in
two indexed hashing runs. Binding theorems retain these inputs or positions, so
an unrelated collision cannot discharge their conclusions. `CollisionResistant h`
states that no pair of distinct inputs has the same image under `h`.

Checked claims:

- `Collision.comp`: a collision in a composite on specified inputs gives an
  inner collision on those inputs or an outer collision on their images.
- `Collision.comp_inner`: a collision in the inner function is a collision in
  the composite on the same inputs.
- `CollisionResistant.injective`: a collision-resistant function is injective.

Why it matters: consumers can rule out collisions at the compared inputs or
positions to derive equality from the binding theorems.

## `BtcVerified.Sha256`

A concrete, computable SHA-256 (FIPS 180-4) and Bitcoin's double-SHA-256
(`sha256d = sha256 ∘ sha256`) over byte strings. These are ordinary reducible
`def`s — not abstract, not `opaque` — so a digest *computes*: txids, merkle
roots, and block hashes can be evaluated and checked by reduction against real
data, which is what consensus consistency checks require.

Checked claims:

- Golden-vector known-answer tests (`Tests`): `sha256`/`sha256d` match the
  published FIPS 180-4 and Bitcoin vectors — including the empty string, `"abc"`,
  double-SHA of empty, and the 55/56/64-byte padding boundaries — evaluated at
  build time.
- Axiom audit: `sha256d` depends on no axiom beyond the standard three — no
  `sorry`, no `native_decide`.

Why it matters: collision-resistance is deliberately *not* asserted here. For a
concrete hash it is provably false (an infinite domain into 256 bits collides by
pigeonhole), so it can never be an axiom over this function — it lives as a
hypothesis over an abstract hash where a soundness proof needs it. What the
concrete function buys instead is computation: a verified decoder plus a
computable hash is what lets a real block's merkle root or a header's
proof-of-work be checked, not just asserted.

## `BtcVerified.Merkle`

Bitcoin's merkle tree, as a tree — the platonic spec, with the root computation
and canonicality factored apart. The root is a structural tree fold: the tree is
built top-down by bisection, procedural duplication an explicit `pad` constructor
rather than an artifact of iteration order. Canonicality is a first-class
decidable property of the leaf list, constraining exactly what threatens the
root's binding: padding only duplicates trailing power-of-two-aligned blocks, so
only a right-spine duplication can materialize a shorter list's padding
(CVE-2012-2459). The bottom-up vector computation of this root, and the clients
that run it, live under `Impl/`.

Checked claims:

- `combine_binding`: equal parent digests imply equal child pairs, or the two
  specified 64-byte node inputs collide under double-SHA-256.
- `root_binding_of_length_eq`: between equal-length lists, the root identifies
  the list — or inputs at a common tree path collide under double-SHA-256.
- `root_binding_of_canonical`: between nonempty canonical lists of equal enclosing
  width, the root identifies the list — or inputs at a common tree path collide.
  This is the binding the canonicality rule exists to restore.
- `Block.merkleCommits` (in `Block/Commitment.lean`): the consensus condition —
  a canonical txid list whose root is the header's. Checked on the genesis
  block and block 170 at build time, and on all 1866 transactions of block
  481824 under `lake test`, which with the header-hash check pins every
  transaction byte of the fixture (txids → merkle root → header →
  proof-of-work hash).

Why it matters: this is the first consensus-validity leaf — the commitment
that ties a block's body to the header that proof of work covers. The known
residual is documented rather than papered over: equal enclosing widths are a
hypothesis because a 64-byte transaction can confuse a leaf with an interior
node across heights (the ambiguity the Great Consensus Cleanup proposes to
close); for block validity the transaction count is in hand, so the hypothesis
is free.
