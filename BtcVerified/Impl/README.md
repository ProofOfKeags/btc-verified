# BtcVerified/Impl

Models of code that exists in the world, checked against the abstract
consensus specs it must realize: level-order vector layouts and
transcriptions of Bitcoin Core's own consensus code, with other
implementations (btcd, rust-bitcoin) as future candidates. Everything here
is evidence about an implementation, not infrastructure of our own — the
packed executable forms of the spec codecs live beside their types, with
the class and combinators described in the [`Packed` overview](../Packed/README.md).
These are runtime implementations for this repository, not models of anyone
else's code. `Consensus/` is the reasoning substrate, chosen for clear facts
about protocol behavior and heavily informed by Core without being
definitionally identical to it. `Impl/BitcoinCore` models the code-shaped side;
the intended bridge is a refinement/equivalence theorem over observable
behavior — accepted raw block histories and resulting state transitions. That
separation also lets forks and independent implementations be compared against
the same consensus object instead of making Core's internal structure the
definition of Bitcoin.

## `BtcVerified.Impl.BitcoinCore`

Bitcoin's bottom-up merkle computation over a flat vector, and Bitcoin Core's
`ComputeMerkleRoot` (`src/consensus/merkle.cpp`) — the fused variant that also
computes the `mutated` flag — transcribed and checked against the tree spec.
This lives under `Impl/` because level-folding is a fact about the vector layout,
not the tree: `computeRoot`, the plain bottom-up fold, is proved equal to the
spec's `root` by `computeRoot_eq_root`, and Core's `computeMerkleRoot` adds the
duplicate scan on top. The transcription is up to the imperative-to-functional
rendering, not a literal copy: Core's `while` loop becomes a recursion, its sticky
`bool mutation` the OR of each level's scan folded up through the returns.
The fidelity point is the *ordering*: Core scans each level for an adjacent
duplicate **before** it pads, so a duplicate that padding synthesizes is never
compared to its twin (the CVE-2012-2459 defense). The model is computable and run
on concrete vectors at build time: the attack list `[1, 2, 3, 3]` sets `mutated`,
the distinct `[1, 2, 3]` does not, `[1, 2, 2]` (the scan-before-pad discriminator)
does not, and `[7, 7]` is canonical yet mutates — Core is strictly stronger.

Checked claims:

- `computeRoot_eq_root`: the bottom-up vector fold computes the spec's tree root.
- `canonical_of_not_mutated`: a leaf list Core accepts (`mutated = false`) is the
  spec's `Canonical` — unconditionally, no distinctness, no collision caveat. The
  converse fails (`[a, a]` is canonical yet mutates), so Core's scan is strictly
  stronger and no transaction-distinctness hypothesis is needed or used.
- `eq_of_computeMerkleRoot_eq_of_not_mutated`: two nonempty equal-width lists Core
  accepts with equal roots are equal — or a concrete double-SHA-256 collision.
  Core's single check recovers the binding `root_binding_of_canonical` provides.
- `computeMerkleRoot_fst`: the root Core returns is exactly `computeRoot` (hence
  the spec `root`) on every input — anchored to real chain data through the
  `Block.merkleCommits` checks, and confirmed on block 481824 under `lake test`
  (its `mutated` flag is clear, agreeing with Core, which accepted the block).

Why it matters: this closes the gap between the algorithm Bitcoin Core actually
runs and the repo's separated root/canonicality model. Core fuses the root and a
duplicate scan into one pass; the spec factors them apart, and passing Core's
scan is proved to imply the canonicality that recovers the binding — the one-way
direction that matters, since Core is strictly stronger than canonicality
requires.
