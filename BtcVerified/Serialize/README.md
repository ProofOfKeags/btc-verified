# BtcVerified/Serialize

The serialization layer: the codec discipline every wire structure in the
repo is built on, and the primitives Bitcoin composes everywhere — fixed-width
byte strings, fixed-width little-endian integers, and CompactSize-prefixed
vectors.

`Bytes`, `CompactSize`, and `CountedList` also carry their packed encoders,
decoders, and agreement proofs in these same modules, under
`BtcVerified.Packed`. The shared `PackedCodec` class and its instances for
dependency types live in `../Packed/Codec.lean`; see the
[packed-codec overview](../Packed/README.md) for the checked claims.

## The `Codec` discipline

The `Codec` typeclass bundles an encoder, a prefix-consuming decoder, and the
two laws relating them — round-trip and canonicality. Read as an adjunction,
`encode` is a section into the byte strings and `decode` a partial
retraction.

Checked claims:

- `encode_injective`: distinct values never share an encoding.
- `Codec (α × β)`: running two codecs in sequence again satisfies both laws, so
  composite structures inherit serialization correctness from their fields.
- `decodeBitVecLE_encodeBitVecLE` / `decodeBitVecLE_canonical`: one little-endian
  construction serializes any `BitVec (8 * n)` as `n` bytes (low byte first),
  proved by bit-level extensionality. `Codec.ofEquiv` transports it along a
  bijection, giving the fixed-width integer instances (`UInt8`/`UInt16`/`UInt32`/
  `UInt64`) from a single place where endianness is defined.
- `Codec (Bytes n)`: an uninterpreted byte string whose exact width lives
  in its type serializes as itself and decodes by consuming exactly `n` bytes.
  `Hash256` is `Bytes 32`; other 32-byte protocol fields can share the
  width invariant without pretending to be hashes. Conversions from raw lists
  state their policy explicitly: exact width, left padding, right padding, or
  left/right truncation (dropping the prefix/suffix, respectively). For either
  direction these operations partition inputs by length: padding accepts only
  short inputs, exact conversion only equal widths, and truncation only long
  inputs.
- `decodeCountedList_canonical` (and round-trip): every variable-length Bitcoin
  field — a script, an input/output vector, a witness stack — is a CompactSize
  count prefix followed by its elements. `CountedList` captures that once as a
  list whose length fits a `UInt64` (the bound a count prefix can address), and
  `Codec (CountedList α)` lifts any `Codec α` to the prefixed-vector codec.

Why it matters: a block and its substructures are serialized by composing many
small encoders. Capturing round-trip and canonicality once, as composable laws,
lets each substructure reuse its fields' correctness instead of re-deriving it.

## `BtcVerified.CompactSize`

Bitcoin's CompactSize variable-length integer encoding over `UInt64`.

Checked claims:

- `decode_encode`: encoding and then decoding returns the original value,
  preserving any trailing bytes.
- `encode_length_le`: every canonical encoding is at most nine bytes.
- `decode_canonical`: every accepted parse consumed exactly the canonical
  encoding of the returned value.

The fixed-width payloads reuse the little-endian `Codec` primitives, so
CompactSize only adds its own concern — marker dispatch and shortest-form
minimality. `compactSizeCodec` packages the whole encoding as a
`Codec UInt64`.

Why it matters: CompactSize is the count prefix throughout Bitcoin
serialization. A verified encoder/decoder is a small foundation for later
byte-level protocol models.
