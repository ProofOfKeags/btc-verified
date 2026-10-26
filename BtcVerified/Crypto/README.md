# BtcVerified/Crypto

The hashing layer: the 256-bit digest type, a concrete computable SHA-256,
collision predicates that retain the compared inputs, and Bitcoin's merkle tree.

## `Hash256` and the collision vocabulary

`Hash256 := Bytes 32` represents a digest as its raw 32 bytes. `Collides h a b`
states that the specified inputs are distinct and have equal hashes.
`CollisionBetween h left right` requires one colliding input from each supplied
list. Concrete binding theorems use these predicates to connect their collision
conclusion to the objects being compared; an unrelated collision does not suffice.

Checked claims:

- `CollisionBetween.mono`: enlarging the two preimage lists preserves a collision
  between them.
- `collisionBetween_singletons`: two singleton lists collide exactly when their
  specified inputs do.
- `not_collisionBetween_nil_left` / `not_collisionBetween_nil_right`: an empty
  list cannot supply a collision preimage.
- `CollisionFree.injective`: absence of any collision implies injectivity.

Why it matters: `Collision h` still names global collision existence, and
`CollisionFree h` names its negation, formerly called `CollisionResistant`.
Collision freedom is mathematical injectivity, not computational collision
resistance. It is false for a hash from all byte strings to a finite digest type.
The concrete binding results neither assume it nor prove computational security.

Terminology policy: use *collision freedom* for the mathematical absence of
collisions and reserve *collision resistance* for computational hardness
claims. Name new no-collision predicates `CollisionFree`. The existing BitVM
`CollisionResistance` identifier is retained for API compatibility.

## `BtcVerified.Sha256`

A concrete, computable SHA-256 (FIPS 180-4) and Bitcoin's double-SHA-256
(`sha256d = sha256 ∘ sha256`) over byte strings. Both are ordinary reducible
`def`s, so txids, merkle roots, and block hashes can be evaluated against real
data. `Sha256.Collides` and `Sha256.CollisionBetween` specialize the collision
predicates to double-SHA-256.

Checked claims:

- Golden-vector known-answer tests (`Tests`): `sha256`/`sha256d` match the
  published FIPS 180-4 and Bitcoin vectors — including the empty string, `"abc"`,
  double-SHA of empty, and the 55/56/64-byte padding boundaries — evaluated at
  build time.
- Axiom audit: `sha256d` depends on no axiom beyond the standard three — no
  `sorry`, no `native_decide`.
- `collisionFree_sha256_iff_sha256d`: global mathematical collision freedom of
  SHA-256 is equivalent to that of its double application. Both properties are
  false for these concrete finite-output hashes; the conditional algebraic
  theorem makes no computational security claim.

Why it matters: a verified decoder and computable hash let the tests check a
real block's merkle root and header hash. Known-answer vectors check finite
examples; they do not establish collision resistance or an implementation-wide
comparison with Bitcoin Core.

## `BtcVerified.Merkle`

Bitcoin's merkle tree has a structural tree fold for its root: the tree is built
by bisection, and a `pad` constructor records procedural duplication.
`Tree.hashPreimages` lists the byte strings hashed at interior and padding nodes;
leaves are already digests and add no preimage. `Merkle.hashPreimages` applies
that definition to the tree constructed from a leaf list.

Canonicality is a decidable scan of the right spine, exempting the root. Within
one enclosing width, it excludes ambiguity from materializing a shorter list's
padding (CVE-2012-2459). The bottom-up computation and Core's stronger mutation
scan live under `Impl/`.

Checked claims:

- `combine_binding`: equal parent digests imply equal child pairs, or the two
  specified 64-byte node preimages collide.
- `root_binding_of_length_eq`: equal-length lists with equal roots are equal, or
  node preimages from the two constructed trees collide.
- `root_binding_of_canonical`: nonempty canonical lists of equal enclosing width
  with equal roots are equal, or node preimages from their trees collide.
- `Block.merkleCommits` (in `Block/Commitment.lean`): the decidable condition that
  a canonical txid list has the header's merkle root. Tests check it on genesis,
  block 170, and all 1866 transactions of block 481824.

Why it matters: the theorems expose both padding ambiguity and the hash inputs
needed to explain a failed commitment. Equal enclosing widths remain an explicit
hypothesis: across widths, a leaf can equal an internal-node digest without a
hash collision. Knowing the two transaction counts does not establish equality
of their widths, and `merkleCommits` alone does not supply it.
