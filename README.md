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
