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

The fixed-width payloads reuse the little-endian `Codec` primitives from
`BtcVerified.Serialize`, so CompactSize only adds its own concern — marker
dispatch and shortest-form minimality. `compactSizeCodec` packages the whole
encoding as a `Codec UInt64`.

Why it matters: CompactSize is the count prefix throughout Bitcoin
serialization. A verified encoder/decoder is a small foundation for later
byte-level protocol models.

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
- `decodeBitVecLE_encodeBitVecLE` / `decodeBitVecLE_canonical`: one little-endian
  construction serializes any `BitVec (8 * n)` as `n` bytes (low byte first),
  proved by bit-level extensionality. `Codec.ofEquiv` transports it along a
  bijection, giving the fixed-width integer instances (`UInt8`/`UInt16`/`UInt32`/
  `UInt64`) and the 256-bit hash from a single place where endianness is defined.
- `decodeCountedList_canonical` (and round-trip): every variable-length Bitcoin
  field — a script, an input/output vector, a witness stack — is a CompactSize
  count prefix followed by its elements. `CountedList` captures that once as a
  list whose length fits a `UInt64` (the bound a count prefix can address), and
  `Codec (CountedList α)` lifts any `Codec α` to the prefixed-vector codec.

Why it matters: a block and its substructures are serialized by composing many
small encoders. Capturing round-trip and canonicality once, as composable laws,
lets each substructure reuse its fields' correctness instead of re-deriving it.

### `BtcVerified` block data model

The data model for Bitcoin blocks and their substructures — `OutPoint`, `TxIn`,
`TxOut`, `TxBody`, `Tx`, `BlockHeader`, `Block`, and the `Hash256`/`WitnessStack`
aliases — the foundation that serialization, consensus validity, proof of work,
and fork choice are all stated against.

The model is era- and witness-aware from the start, and pushes the structural
facts of the wire format into the types:

- A transaction is an inductive with two constructors over a shared,
  witness-free `TxBody` (version, inputs, outputs, lock time). `legacy` is the
  pre-SegWit form; `segwit` is the BIP144 form. The `TxBody` is at once what a
  txid commits to, the legacy serialization, and the witness-stripped form a
  SegWit transaction shows the pre-SegWit world; `Tx.body` recovers it from
  either constructor.
- A SegWit transaction bundles each input with the witness that unlocks it
  (`SegwitInput`), so the one-witness-per-input arity is structural rather than a
  side condition. The wire groups witnesses after inputs; that regrouping is the
  codec's job, not the model's.
- The `legacy` constructor carries a non-empty-inputs proof, because the SegWit
  serialization reserves a zero input count (the `0x00` marker), so a legacy
  transaction can never encode zero inputs.
- Every CompactSize-prefixed field — scripts, the input/output vectors, witness
  stacks, the block's transactions — is a `CountedList`.

Scripts are `Script` — a program type whose text stays raw because tokenization
belongs to execution, not deserialization; witness items are opaque byte
strings; hashing stays abstract.

Why it matters: fork choice and proof-of-work semantics presuppose an actual
representation of blocks and the substructures that carry consensus-validity
invariants. This fixes that vocabulary as the base of the stack.

### `BtcVerified` transaction codecs

`Codec` instances for every transaction substructure, bottom-up: `OutPoint`,
`TxIn`, `TxOut`, and `TxBody` are each the product of their fields in wire
order, so their codecs come by composition (`Codec.ofEquiv` over the product
codec) with no hand-written proofs. The whole-transaction codec sits on top.

Checked claims:

- `decodeTx_encodeTx`: every transaction round-trips, trailing bytes preserved.
- `decodeTx_canonical`: an accepted parse consumed exactly the canonical
  encoding — including dispatching to the legacy or SegWit branch the value's own
  form dictates.

The transaction codec is the one place the wire format and the data model
disagree on order: `decode` reads the inputs and witnesses from their separate
BIP144 regions and rebundles them (`zipInputs`); `encode` unzips. The
legacy/SegWit dispatch turns on the marker byte, and a CompactSize first byte is
`0x00` only for a zero count — which is what makes a non-empty legacy input count
unambiguous against the marker. Packaged as `instCodecTx : Codec Tx`.

Why it matters: a transaction is the unit a block commits to and the unit fork
choice ultimately weighs. Verified round-trip and canonicality for both eras is
the serialization backbone the block codec and the txid/merkle commitments build
on.

### `BtcVerified` block codecs

`Codec` instances for `BlockHeader` and `Block`, completing the syntactic
hierarchy: every byte of a block is now parsed by a verified codec, from
CompactSize counts up through transactions to the block itself. Both structures
agree with the wire on field order, so both codecs come by composition
(`Codec.ofEquiv` over the product codec) with no hand-written proofs — a header
is its six fields in wire order, and a block is its header followed by its
CompactSize-counted transactions.

Checked claims:

- `instCodecBlockHeader`: the header codec satisfies round-trip and
  canonicality, inherited field by field.
- `BlockHeader.encode_length`: every header encodes to exactly 80 bytes — the
  fixed proof-of-work preimage size.
- `instCodecBlock`: the block codec satisfies round-trip and canonicality.

The golden vectors decode the genesis block and block 170 (the first block with
a non-coinbase transaction) from real mainnet bytes, spot-check the headers and
coinbases, and re-encode byte-for-byte; block 170's embedded payment must
re-encode to exactly the standalone first-payment vector. A fixture check
(`lake test`) does the same for all 989,323 bytes of block 481824 — the SegWit
activation block, whose 1866 transactions mix both serialization eras in one
block — and requires its coinbase and the first SegWit spend to match the
standalone transaction vectors byte-for-byte. The block is public chain data,
so it is fetched by hash on first run and cached locally rather than
committed.

Why it matters: the block is the unit proof of work covers and fork choice
weighs. With its syntax verified end to end, the next layers — txid/merkle
commitments, header-hash targets, cumulative work — can be stated about a
structure whose byte-level meaning is already pinned down.

### `BtcVerified.Sha256`

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

### `BtcVerified.Script`

The `Script` type: a Bitcoin Script program as it exists on the wire — raw,
CompactSize-length-prefixed bytes, type-distinct from anonymous byte strings
like witness items. `TxIn.scriptSig` and `TxOut.scriptPubKey` are `Script`s.

Checked claims:

- `instCodecScript`: the script codec satisfies round-trip and canonicality,
  inherited from the counted byte list.

Keeping the program text raw is a protocol fact, not a simplification: Bitcoin
tokenizes a script only at execution time, and consensus never requires the
bytes to tokenize. Mainnet relies on this — most current coinbase scriptSigs
do not tokenize (pool tags whose bytes read as truncated pushes), and an
output script that fails to tokenize is merely unspendable, not invalid. So
the wire layer accepts every byte string, and tokenization will enter as the
first, fallible stage of the execution layer.

Why it matters: scripts are where transaction validity ultimately gets decided.
Giving programs their own type now — with the protocol's real
syntax/execution boundary built in — is the anchor the script-language layer
attaches to without touching the serialization stack.

## What this is not yet

- Not a full Bitcoin Script semantics.
- Not a *proof* that the SHA-256 implementation equals FIPS 180-4 — it is
  concrete and computable, checked against published test vectors, not verified
  bit-for-bit against the spec.
- Not a full BitVM fraud-proof model.
- Not a claim that the current leaves are important by themselves.

The point is to make a public, checked trail toward those larger artifacts.

## Build

```
lake exe cache get   # fetch the mathlib cache (first build only)
lake build           # the library, plus the golden vectors and axiom audit
lake test            # block 481824 through the block codec (fetched on first run)
lake lint
```

`lake build` also elaborates `Tests/`: golden vectors that run the verified
decoder over real mainnet bytes (the first Bitcoin payment, the SegWit
activation coinbase, the first SegWit spend, the genesis block, block 170) and
an axiom audit that fails the build if any headline theorem depends on `sorry`
or an unexpected axiom. `lake test` decodes the full SegWit activation block,
fetching it from a block explorer on first run and caching it locally (it is
public chain data, so it is not committed). See `CONTRIBUTING.md` for the
contribution workflow.
