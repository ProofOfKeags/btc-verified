# btc-verified

[![CI](https://github.com/ProofOfKeags/btc-verified/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/ProofOfKeags/btc-verified/actions/workflows/ci.yml?query=branch%3Amaster)

Small verified Bitcoin protocol components in Lean 4.

This repository is an early public artifact for Bitcoin protocol verification:
the goal is to build checked, reviewable cores around the parts of Bitcoin and
Bitcoin-adjacent protocols where testing alone is the wrong tool.

The current work is intentionally small. Each leaf should be understandable on
its own, build cleanly, and make the next proof packet easier to state.

## Current proof leaves

What is proved so far, by directory. Each directory's README carries the
precise checked claims, theorem by theorem; each line here is the plain
statement of what stands.

- [`Serialize/`](BtcVerified/Serialize/README.md) — Every encoder/decoder
  pair carries machine-checked proofs that decoding inverts encoding and that
  each value has exactly one accepted encoding, including Bitcoin's
  CompactSize integers.
- [`Crypto/`](BtcVerified/Crypto/README.md) — A computable SHA-256 checked
  against published test vectors, and Bitcoin's merkle tree with proofs of
  exactly what a merkle root does and does not commit to, including the
  defense against the CVE-2012-2459 duplication attack.
- [`Transaction/`](BtcVerified/Transaction/README.md) — Bitcoin transactions,
  legacy and SegWit, with verified serialization in both directions and
  proofs that transaction ids are binding commitments to the transaction.
- [`Block/`](BtcVerified/Block/README.md) — Every byte of a block parses
  through a verified codec (checked against real mainnet blocks), block
  hashes are proved binding, and a chain's tip hash provably commits to the
  entire history behind it.
- [`Script/`](BtcVerified/Script/README.md) — Bitcoin Script programs
  modeled as the raw bytes consensus actually validates, with the boundary
  between parsing and execution drawn where the protocol draws it.
- [`Chainstate/`](BtcVerified/Chainstate/README.md) — The set of spendable
  coins and the single action every transaction performs on it, with the
  accounting identity the supply-limit theorem will be built on.
- [`Impl/`](BtcVerified/Impl/README.md) — Functions transcribed from Bitcoin
  Core's own source code and proved to satisfy the specification, starting
  with its merkle-root computation.
- [`BitVM/`](BtcVerified/BitVM/README.md) — An abstract model of BitVM's bit
  commitments, with a proof that equivocating on a committed bit yields a
  hash collision.

## Roadmap

The trail toward the larger artifacts is tracked as
[GitHub milestones](https://github.com/ProofOfKeags/btc-verified/milestones),
in dependency order. Each milestone page states its claims precisely and
tracks the work items; in outline:

1. [Consensus guards: transaction and block validity](https://github.com/ProofOfKeags/btc-verified/milestone/1)
   — Write down the rules that decide whether a transaction or block is
   valid, and prove that every valid block updates the set of spendable
   coins exactly as specified.
2. [The supply limit theorem](https://github.com/ProofOfKeags/btc-verified/milestone/2)
   — Prove that under those validity rules, the total number of bitcoins
   that can ever exist stays below 21 million.
3. [Proof of work and cumulative work](https://github.com/ProofOfKeags/btc-verified/milestone/3)
   — Define what it means for a block to prove work — the hash target its
   header must meet — and prove how that work adds up along a chain.
4. [The block tree and fork choice](https://github.com/ProofOfKeags/btc-verified/milestone/4)
   — Prove that when competing chains exist, Bitcoin's rule for choosing
   between them selects the valid chain backed by the most total work.
5. [The Core transcription track](https://github.com/ProofOfKeags/btc-verified/milestone/5)
   — Translate consensus-critical functions from Bitcoin Core's actual
   source code into Lean and prove they satisfy the specification, as is
   already done for its merkle-root computation.
6. [Script: tokenization and the execution core](https://github.com/ProofOfKeags/btc-verified/milestone/6)
   — Build a verified interpreter for the core of Bitcoin's Script
   language, and prove the standard payment types accept exactly the
   spends that present a correct signature.
7. [ByteArray transport and the full-chain demo](https://github.com/ProofOfKeags/btc-verified/milestone/7)
   — Make the verified components efficient enough for real use, and
   demonstrate it by checking actual Bitcoin mainnet history with them.

## Build

With Nix, enter the development shell first:

```
nix develop
```

```
lake exe cache get   # fetch the mathlib cache (first build only)
lake build           # the library, plus the golden vectors and axiom audit
lake test            # block 481824 through the block codec (fetched on first run)
lake lint
```

`lake build` also elaborates `Tests/`: golden vectors that run the verified
decoder over real mainnet bytes (the first Bitcoin payment, the SegWit
activation coinbase, the first SegWit spend, the genesis block, block 170,
and the genesis → block 1 chain link) and an axiom audit that fails the
build if any headline theorem depends on `sorry` or an unexpected axiom.
`lake test` decodes the full SegWit activation block,
fetching it from a block explorer on first run and caching it locally (it is
public chain data, so it is not committed). See `CONTRIBUTING.md` for the
contribution workflow.

## License

Licensed under the Apache License, Version 2.0 — matching the Lean and Mathlib
ecosystem this builds on, and carrying an explicit patent grant. See
[`LICENSE`](LICENSE).

## About

`btc-verified` is built by Keagan McClelland ([@ProofOfKeags](https://x.com/ProofOfKeags),
[proofofkeags.com](https://proofofkeags.com)) — an independent Bitcoin/Lightning
engineer working toward verified cores for the protocol's correctness-critical
surfaces.

The thesis behind the work — why AI-assisted authorship is making formal
verification the defensible posture for protocol engineering, rather than a
luxury — is laid out in
[Formal Vibefication](https://proofofkeags.com/research/2026-05-12-formal-vibefication.html).
