---
name: proof-leaf
description: Land a new proof leaf in btc-verified — module layout, codec discipline, axiom audit registration, golden vectors, and the README section format. Use when adding a new module, a new Codec instance, or new headline theorems, or when asked to "add a leaf", "wire up a new module", or "finish landing" verification work.
---

# Landing a proof leaf

A "proof leaf" is this repo's unit of progress: one module that builds
cleanly, states its checked claims, and is wired into the build, the audit,
and the README. Follow this checklist end to end — a leaf is not landed until
every step is done.

## 1. The module

- One concern per file, under the matching directory (`Serialize/`,
  `Transaction/`, `Block/`, `Crypto/`, `BitVM/`).
- `/-!` module header: two-space indented content, `# Title`, the design
  rationale in prose, and — for proof-bearing modules — a `Checked claims:`
  bullet list naming the theorems. Match the voice of
  `BtcVerified/Serialize/Codec.lean`.
- `/--` doc-string on every public declaration, text starting one space after
  `/--`, continuation lines flush-left, closing `-/` on the last text line.

## 2. If the leaf is a serializable structure

- Fields in wire order, doc-string each, `deriving DecidableEq`.
- Codec by composition: write `Foo.equivProd : Foo ≃ (A × B × ...)` and
  `instance instCodecFoo : Codec Foo := Codec.ofEquiv Foo.equivProd
  inferInstance`. Hand-write `encode`/`decode` (plus both law proofs) ONLY
  when wire order and model order genuinely differ — `TxCodec.lean` is the
  reference for that case.
- CompactSize-prefixed fields are `CountedList`s. Structural wire facts
  become type-level invariants, not side conditions.
- Spec stays `List UInt8`; never introduce `ByteArray` here.

## 3. Wiring

- Import the module in `BtcVerified.lean` (dependency order).
- Register every headline theorem in `Tests/AxiomAudit.lean` with
  `#assert_axioms`.
- If the leaf decodes real wire bytes, add a golden vector: real mainnet
  bytes (fetch from `https://blockstream.info/api/...`, cite txid/height in a
  comment), then decode-succeeds-consuming-everything, structural
  spot-checks, and re-encode-equals-original. Inline as `#guard`s in
  `Tests/GoldenVectors.lean` while the bytes stay readable; for
  kilobyte-scale vectors, add a fetched fixture in `Tests/BlockFixtures.lean`
  (runs via `lake test` — the driver downloads the block by hash on first
  run and caches it under the gitignored `Tests/fixtures/`; never commit the
  bytes, they are public chain data). ALWAYS verify an inline literal
  byte-for-byte against the freshly fetched bytes before trusting it, and
  pin enough spot-checks on a fetched fixture (header fields, embedded-tx
  equality with inline vectors) that a wrong download cannot pass.

## 4. Verification

```sh
lake build && lake test && lake lint
```

All three must pass clean. `lake build BtcVerified.<Module>` is the fast loop
while iterating.

## 5. The README section

Add to "Current proof leaves" in `README.md`, matching the existing sections
exactly:

```markdown
### `BtcVerified.<Module>`

One-paragraph description of what is modeled and the key design move.

Checked claims:

- `theorem_name`: one-line statement of what it proves.

Why it matters: how this leaf serves the stack above it (serialization →
consensus validity → proof of work → fork choice).
```

Keep claims honest: list only what is actually proved, and put modeling
assumptions (abstract hashing, opaque scripts) in the description, not the
claims.
