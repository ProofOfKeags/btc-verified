# Illustrative audit: Merkle canonicality versus Core's mutation flag

## Subject and immutable evidence

This is an example packet for the verify-leaf skill and the first proposed
pilot under [issue #54](https://github.com/ProofOfKeags/btc-verified/issues/54).
It is a source-pinned reading of existing fixtures, not a blind independent
audit and not an independent Bitcoin Core executable comparison.

- btc-verified baseline: 2fdeb40ca2b3f289896ed14a3340ad231cd16538
- Spec: BtcVerified/Crypto/Merkle.lean, blob 909d8429b876187b43b9c7e7d702345d88db0f9e
- Core-shaped model: BtcVerified/Impl/BitcoinCore/Merkle.lean, blob a0b1c5c7c274bcd140e551e525705fb553337b99
- Witnesses: Tests/GoldenVectors.lean, blob 022a54a489e383f95514f3508dfc52875fa585d3
- Axiom declarations: Tests/AxiomAudit.lean, blob 2e4cbb23d99730896d8bf14ceecf85bb917164d5
- Core code cited by the model: bitcoin/bitcoin src/consensus/merkle.cpp at d84fc352
- Reference Lean and Mathlib versions: repository-pinned files at baseline;
  no new toolchain migration is part of this pilot

The checked claim is
BtcVerified.Impl.BitcoinCore.canonical_of_not_mutated:

For every list of Hash256 leaves xs, if the second component of
computeMerkleRoot(xs) equals false, then Merkle.Canonical(xs) holds.

The root binding claim needs additional hypotheses about nonempty inputs,
equal enclosing widths and collision evidence; see
eq_of_computeMerkleRoot_eq_of_not_mutated. The converse of
canonical_of_not_mutated is absent and false.

## Adequacy and applicability

The following cases already appear as executable #guard declarations in
Tests/GoldenVectors.lean and are checked by the repository's default Lean
build. Their status is **existing compiled fixture**, not a newly invented
oracle.

| Input | Existing expected mutation | Canonicality | Review role |
| --- | --- | --- | --- |
| [1,2,3] | false | true | Nontrivial satisfying witness |
| [1,2,2] | false | true | Odd-tail, scan-before-padding discriminator |
| [1,2,3,3] | true | false | Materialized-padding ambiguity |
| [7,7] | true | true | Counterexample to the converse |
| [1,1,2,3] | true | true | Pair-aligned duplicate with canonical root |
| [1,2,3,4,5,6,5,6] | true | false | Mutation visible at a higher level |

The [7,7] case tests the important distinction: the spec considers the
list canonical at its width, while the Core-style mutation scan flags an
actual adjacent duplicate. The theorem's implication is the correct
one-way direction.

## Mutation probes

**M1, scan after padding.** Candidate edit in a scratch copy: move the
adjacent-equality scan below the operation that duplicates an odd final
node. Predicted outcome: input [1,2,2] changes from mutation=false to
mutation=true, because the synthetic last 2 would be compared to its
copy. The existing negative #guard would then reject the changed behavior.
Classification: **predicted distinguishing fixture, mutation NOT RUN**.
A future audit should execute the scratch edit, preserve the diff and
record the resulting Lean command and failure. Merely breaking the build
for unrelated reasons would not be detection.

**M2, reverse the proved implication.** Candidate semantic weakening:
assume Canonical(xs) implies mutation=false. Input [7,7] disproves this
because it is canonical and mutated=true in existing fixtures.
Classification: **checked counterexample to a proposed stronger claim**,
not a counterexample to the actual theorem.

**M3, omit the scan in Core.** Predicted outcome: [1,2,3,3] loses its
mutation flag. This also appears as a positive #guard. Classification:
**predicted distinguishing fixture, mutation NOT RUN**.

## Proof and correspondence evidence

The repository registers canonical_of_not_mutated,
computeMerkleRoot_fst, and the strengthened root-equivalence theorem in
Tests/AxiomAudit.lean. The normal CI runs Lean elaboration and golden
vectors. The exact build and additional checker results for this candidate
PR must be attached from its CI run; this packet does not assert that
independent proof checking was performed.

The model documents a functional transcription of Bitcoin Core's Merkle
implementation. Fixture agreement is evidence for selected inputs. A
universal equivalence theorem about the compiled Bitcoin Core binary,
including source/version/build provenance and its C++ runtime, remains
a separate correspondence claim.

## Documentation finding and proposed disposition

The original GoldenVectors header said the mutation flag fires
'exactly' on materialized-padding lists. That verbal reading includes
an unintended converse. The same file checks [7,7] as canonical while
its mutation flag is true. The proposed one-line comment correction
describes adjacent duplicate pair detection and leaves both the Lean
theorems and existing runtime tests untouched.

The maintainer decides whether this one-claim pilot is useful for #54.
Recorded evidence here is an illustrative audit packet; it must not be
treated as completed independent human review.
