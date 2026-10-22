---
name: verify-leaf
description: Independently review an existing btc-verified theorem for statement adequacy, vacuity, mutation resistance and correspondence evidence. Use on a pinned proof leaf, separate from proof authorship.
---

# Verify one proof leaf

Use this skill for a **fresh semantic audit** of an existing checked claim. It
complements the author's proof work, the project's axiom checks and the
executable conformance suite. It implements the first, opt-in review packet
described in [issue #54](https://github.com/ProofOfKeags/btc-verified/issues/54).
A Lean proof establishes its proposition under its axioms; implementation
correspondence requires separate evidence.

## Pinned inputs

Record the exact commit SHA; theorem identifiers and propositions; transitive
definitions that control their meaning; implementation or Bitcoin Core revision;
Lean/Mathlib pin; and the intent of the review. Treat this semantic snapshot as
read-only. If the reviewer wants to modify a predicate, that is a separate
change requiring a new evidence record.

Start from the Lean declaration and its definitions, before seeing the
author's explanation when a fresh review can be arranged. Keep the human
claim and the mechanically checked proposition side by side.

## Audit procedure

1. **Statement adequacy.** Read quantifiers, premises, types, bounds and
   conclusions literally. Identify the accepted behavior the claim promises,
   then construct a negative behavior it must exclude. Check whether the
   hypotheses can be satisfied by at least one nontrivial object.
2. **Counterexamples.** Challenge the proposition with malformed objects,
   boundary values, underconstrained inputs, different execution stages and
   historical Bitcoin exceptions. A candidate witness is a hypothesis until
   it has been checked. An inability to prove something is not a refutation.
3. **Mutation probes.** Pin the intended statement and definitions. Mutate
   only a separate scratch implementation or adapter, predict a distinguishing
   observation *before* testing, and record the observed outcome. Count a
   meaningful behavioral/proof rejection as detection. Compilation errors,
   crashes, setup failures and irrelevant test failures are infrastructure
   failures. Classify surviving mutations as equivalent, out of scope or a
   possible adequacy gap after review.
4. **Applicability.** Exhibit an actual witness satisfying the full premise
   set and name the exercised domain partition. Mark unsupported and
   unobservable partitions explicitly.
5. **Trusted fringe.** Inspect referenced axioms, native evaluation and
   certificates, code generators, FFI adapters, compilation flags, harness
   configuration, fixture provenance and independent Core evidence. Distinguish
   a theorem of the Lean model, a finite check of an executable, and
   correspondence with Bitcoin's deployed consensus behavior.

The reviewer must never change a claim's meaning while repairing the proof.
A successful build verifies elaboration relative to trusted axioms; it does
not independently establish proof-statement intent or C++ equivalence.

## Reproducible packet

Produce one Markdown packet with:

- **Subject:** commit, source file/blob identifiers, exact theorem/definition
  names, original claim reading and intended reviewed interpretation
- **Adequacy:** premises, nontrivial positive/negative instances, and
  identified semantic gaps supported by a witness or explicit uncertainty
- **Mutations:** isolated change, expected observation, actual result,
  command/fixture, and classification; never record an unrun candidate as pass
- **Applicability:** checked hypothesis witness, domain exercised, domains
  unexamined
- **Proof evidence:** exact Lean/Mathlib/independent checker versions, commands
  actually run, axiom roots and linked CI evidence
- **Correspondence:** pinned Core implementation or oracle, observed test
  outputs and uncovered stage/FFI/consensus differences
- **Disposition:** suggested follow-up, author/reviewer decision and which
  claims or prior reviews need reassessment

Keep reviewer observations separate from human disposition. If a prerequisite
tool cannot be run, record an explicit NOT RUN with the reason. Never
substitute a fresh AI paraphrase for the reviewed, versioned wording of the
claim.

## Pilot

See [Merkle canonicality case](examples/merkle-canonicality.md) for an
illustrative, source-pinned case using existing Bitcoin Core Merkle semantics.
It distinguishes a checked theorem from its converse and records which
mutation probes still need executing. The case is an example review packet,
not an independent Core validation.

For a full project-wide application, consult issue #54 and the planned
claim/definition catalog in #73.
