# CLAUDE.md

Verified Bitcoin protocol components in Lean 4 (mathlib-based). The repo grows
as small "proof leaves": each module builds cleanly, states its checked claims
in its header, and makes the next proof packet easier to state.

## Build and feedback loop

```sh
lake build                                  # everything (default targets: BtcVerified, Tests)
lake build BtcVerified.Transaction.TxCodec  # one module — the fast iteration loop
lake build Tests                            # golden vectors + axiom audit only
lake test                                   # fixture checks (block 481824; fetched on first run, cached gitignored)
lake lint                                   # batteries runLinter, mathlib standard linter set
```

- After changing `lean-toolchain` or the mathlib pin, run `lake exe cache get`
  before building, or you will rebuild mathlib from source.
- `lake build` succeeds even with `sorry` (it's a warning). The axiom audit in
  `Tests/AxiomAudit.lean` is what fails the build on `sorryAx` — keep headline
  theorems registered there.

## Architecture

Dependency order, bottom-up:

- `BtcVerified/Serialize/` — the codec discipline. `Codec.lean` defines the
  `Codec` typeclass: encoder, prefix-consuming decoder over `List UInt8`, and
  the two laws (`decode_encode` round-trip, `decode_canonical` canonicality).
  It also proves the product-codec composition, the little-endian
  `BitVec (8 * n)` primitive, and `Codec.ofEquiv` transport. `WidthCast.lean`
  has the width-cast lemmas; `CompactSize.lean` the variable-length integer
  (namespace `BtcVerified.CompactSize`); `CountedList.lean` the
  CompactSize-count-prefixed vector (`CountedList α` = list whose length fits
  `UInt64`).
- `BtcVerified/Crypto/Hash256.lean` — `Hash256 := BitVec 256`. Hashing is
  abstract everywhere; nothing computes SHA-256.
- `BtcVerified/Script/Script.lean` — `Script`: a program as raw,
  CompactSize-prefixed bytes. Tokenization is part of execution, not
  deserialization (consensus never requires script fields to tokenize), so
  the wire layer keeps the bytes uninterpreted; the script-language layer
  grows here later.
- `BtcVerified/Transaction/` — the data model (`OutPoint`, `TxIn`, `TxOut`,
  `TxBody`, `SegwitInput`, `Tx`) and `TxCodec.lean`, the whole-transaction
  codec with the legacy/SegWit marker dispatch.
- `BtcVerified/Block/` — `BlockHeader`, `Block`.
- `BtcVerified/BitVM/` — abstract bit-commitment model, independent of the
  serialization stack.

`BtcVerified.lean` is the root: every module must be imported there or CI
doesn't build it.

## The codec discipline (how to add a serializable structure)

1. Define the structure with one field per wire field, in wire order, with a
   doc-string per field. Derive `DecidableEq`.
2. Write `Foo.equivProd : Foo ≃ (A × B × C)` (fields in wire order) and get
   the codec for free: `instance instCodecFoo : Codec Foo :=
   Codec.ofEquiv Foo.equivProd inferInstance`. No hand-written proofs.
3. Only write `encode`/`decode` by hand when the wire format and the model
   genuinely disagree (e.g. `TxCodec.lean`, where BIP144 groups witnesses
   after inputs but the model bundles them per-input). Then prove both laws
   and package them as a `Codec` instance.
4. Every CompactSize-prefixed wire field (scripts, vectors, witness stacks) is
   a `CountedList`; never hand-roll a count prefix.
5. Structural wire facts go into the types, not side conditions (e.g.
   `Tx.legacy` carries the non-empty-inputs proof because `0x00` is the SegWit
   marker).

Spec/transport split: the spec byte type is `List UInt8`. Do not switch to
`ByteArray` for efficiency — that happens later by transporting proofs across
`List UInt8 ≃ ByteArray`.

## Conventions

- **Naming**: rigid Lean/mathlib casing. `UpperCamelCase` for types, props,
  and predicates; `lowerCamelCase` for defs; theorem names describe the
  conclusion mathlib-style (`decode_encode`, `encodeBitVecLE_length`). Full
  words over abbreviations, except honored Bitcoin nomenclature (`scriptSig`,
  `scriptPubKey`, `nBits`, `vout`, txid).
- **Doc-strings**: every public declaration gets `/--`. Text starts on the
  same line one space after `/--` (the `linter.style.docString` rule);
  continuation lines are flush-left; closing `-/` sits at the end of the last
  text line.
- **Theorem doc-strings state the claim**: every theorem's doc-string is a
  concise English rendering of the formal statement itself — pre-digesting it
  so a reader can then make out the Lean statement. Not an annotation or a
  label ("Round-trip for X"); the English version of the claim ("Encoding a
  value and then decoding returns it, leaving the trailing bytes as the
  tail").
- **Module headers**: every file gets a `/-!` header — content indented two
  spaces, a `# Title`, the design rationale, and a `Checked claims:` list for
  proof-bearing modules.
- **Lints**: `weak.linter.mathlibStandardSet` is on; code must be linter-clean
  (`lake lint`).
- **No `sorry` on master.** New axioms require explicit discussion; the audit
  allowlist is `propext`, `Classical.choice`, `Quot.sound`.

## When a leaf lands

1. Import the module in `BtcVerified.lean`.
2. Register its headline theorems in `Tests/AxiomAudit.lean`.
3. If it's a codec touching real wire bytes, add a golden vector: inline in
   `Tests/GoldenVectors.lean` for anything readable (real mainnet bytes,
   decode + spot-check + re-encode), or a fetched fixture in
   `Tests/BlockFixtures.lean` via `lake test` when the bytes run to
   kilobytes (downloaded by block hash on first run, cached under the
   gitignored `Tests/fixtures/` — never committed).
4. Add a section to `README.md` under "Current proof leaves" in the house
   format: short intro, `Checked claims:` bullets naming the theorems, and a
   "Why it matters:" paragraph tying it to the fork-choice stack.

The `/proof-leaf` skill walks through this checklist.
