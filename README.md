# btc-verified

[![CI](https://github.com/ProofOfKeags/btc-verified/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/ProofOfKeags/btc-verified/actions/workflows/ci.yml?query=branch%3Amaster)

Small verified Bitcoin protocol components in Lean 4.

This repository is an early public artifact for Bitcoin protocol verification:
the goal is to build checked, reviewable cores around the parts of Bitcoin and
Bitcoin-adjacent protocols where testing alone is the wrong tool.

The current work is intentionally small. Each leaf should be understandable on
its own, build cleanly, and make the next proof packet easier to state.

## Current proof leaves

### `BtcVerified.CompactSize`

Bitcoin's CompactSize variable-length integer encoding over `UInt64`.

Checked claims:

- `decode_encode`: encoding and then decoding returns the original value,
  preserving any trailing bytes.
- `encode_length_le`: every canonical encoding is at most nine bytes.
- `decode_canonical`: every accepted parse consumed exactly the canonical
  encoding of the returned value.

Why it matters: CompactSize appears throughout Bitcoin serialization. A
verified encoder/decoder is a small foundation for later byte-level protocol
models.

### `BtcVerified.BitVM.BitCommitment`

An abstract bit-commitment model for the BitVM verification track.

Checked claims:

- Different opened bits imply different openings.
- An equivocation gives a collision witness.
- Collision resistance implies binding.

Why it matters: this fixes the first vocabulary for later BitVM proof packets:
openings, equivocation, collision resistance, and binding.

### `BtcVerified.Serialize`

A serialization codec discipline: the `Codec` typeclass bundles an encoder, a
prefix-consuming decoder, and the two laws relating them — round-trip and
canonicality. Read as an adjunction, `encode` is a section into the byte
strings and `decode` a partial retraction.

Checked claims:

- `encode_injective`: distinct values never share an encoding.
- `Codec (α × β)`: running two codecs in sequence again satisfies both laws, so
  composite structures inherit serialization correctness from their fields.
- fixed-width little-endian `Codec` instances for `UInt16`/`UInt32`/`UInt64`.
- `compactSizeCodec`: the existing CompactSize encoder/decoder satisfies the
  `Codec` laws verbatim — a worked instance validating the abstraction.

Why it matters: a block and its substructures are serialized by composing many
small encoders. Capturing round-trip and canonicality once, as composable laws,
lets each substructure reuse its fields' correctness instead of re-deriving it.

### `BtcVerified` block data model

The data model for Bitcoin blocks and their substructures — `OutPoint`, `TxIn`,
`TxOut`, `Tx`, `BlockHeader`, `Block`, and the `Hash256`/`WitnessStack`
aliases — the foundation that serialization, consensus validity, proof of work,
and fork choice are all stated against.

The model is era- and witness-aware from the start: a transaction's `witness`
field is `none` for the legacy (pre-SegWit) form and `some` for the SegWit
form, since SegWit is a soft fork whose validity is the legacy ruleset plus
added constraints. Scripts and witness items are opaque byte lists; hashing
stays abstract.

Checked claims:

- `witnessWellFormed_of_legacy`: a legacy transaction is always
  witness-well-formed.

Why it matters: fork choice and proof-of-work semantics presuppose an actual
representation of blocks and the substructures that carry consensus-validity
invariants. This fixes that vocabulary as the base of the stack.

## What this is not yet

- Not a full Bitcoin Script semantics.
- Not a concrete SHA-256 or hash-function verification.
- Not a full BitVM fraud-proof model.
- Not a claim that the current leaves are important by themselves.

The point is to make a public, checked trail toward those larger artifacts.

## Build

```
lake build
```
