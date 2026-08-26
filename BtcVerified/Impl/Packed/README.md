# BtcVerified/Impl/Packed

The executable form of the serialization layer (issue #52). The specification
keeps `List UInt8` as its byte type; these modules run the same codecs over
`ByteArray` — zero-copy slice reads on the way in, in-place buffer appends on
the way out — and prove, instance by instance, that the packed codec computes
exactly what the spec codec computes on every input. Nothing here carries
serialization laws of its own: agreement is the only obligation, and
round-trip, canonicality, and the branch dispatch all transport from the spec
for free. Any run of a packed codec *is* a run of the verified one.

The construction mirrors the spec layer combinator for combinator, so every
structure that gets its spec codec by composition gets its packed codec, and
its agreement, the same way — and future spec leaves inherit the pattern.

On the block-481824 fixture (989,323 bytes, 1,866 transactions), one
development machine measured the packed path at 227x the spec decoder
(3,387 ms → 15 ms) and 4.2x the spec encoder (119 ms → 28 ms); `lake exe
bench` reproduces the numbers locally, checking agreement while it times.

## `BtcVerified.Impl.Packed.ByteSlice`

A zero-copy view into a `ByteArray` — base array plus start/stop offsets with
the bounds that make every read total — and `toList`, the abstraction function
into the spec's byte type, through which every agreement theorem is stated.

Checked claims:

- `toList_eq`: the abstraction is the drop/take window of the base array's
  bytes.
- `toList_of_uncons_some` / `toList_of_uncons_none`: reading one byte off a
  slice is exactly uncons on its abstraction.
- `toList_take` / `toList_drop`: sub-slicing commutes with the abstraction.

Why it matters: the slice is what makes packed decoding zero-copy — a parser's
remainder is the same array at a further offset — and these three lemmas are
the complete interface the agreement proofs consume; no proof below ever
touches array indices again.

## `BtcVerified.Impl.Packed.Codec`

The `PackedCodec` class — an encoder appending into a `ByteArray`, a decoder
consuming a `ByteSlice`, and the two agreement laws tying them to the spec
`Codec` instance — with the combinators that mirror the spec layer: product
composition, `ofEquiv` transport, and the little-endian fixed-width primitive.

Checked claims:

- `instPackedCodecProd`: packed sequential composition agrees whenever the
  component codecs agree.
- `PackedCodec.ofEquiv`: transport along a bijection preserves agreement, in
  step with `Codec.ofEquiv`.
- `mapToList_readBitVecLE` / `toList_pushBitVecLE`: the packed little-endian
  forms agree with the spec construction, giving the fixed-width integers'
  packed codecs (`UInt8`–`UInt64`, `BitVec 256`) by transport.
- `PackedCodec.toList_encode` / `PackedCodec.mapToList_decode_toByteArray`:
  over whole byte arrays, a packed codec produces, accepts, and leaves exactly
  what the spec codec does.

Why it matters: agreement composes exactly the way correctness composes at the
spec layer, so the executable representation never grows proof obligations of
its own — the discipline scales to every future wire structure at the cost of
one instance declaration.

## `BtcVerified.Impl.Packed.CompactSize`

The packed CompactSize integer, mirroring the spec's factoring: one
fixed-width marker-payload form shared by the three marker branches, and the
shortest-form dispatch over the marker byte.

Checked claims:

- `mapToList_readFixedWidth` / `toList_pushFixedWidth`: the packed
  marker-payload forms agree with `decodeFixedWidth`/`encodeFixedWidth`.
- `mapToList_readCompactSize` / `toList_pushCompactSize`: the packed dispatch
  agrees with `CompactSize.decode`/`CompactSize.encode`.

Why it matters: CompactSize prefixes every count on the wire, so the packed
counted-list codec — and through it every vector field in a block — stands on
this agreement.

## `BtcVerified.Impl.Packed.CountedList`

The packed counted list — packed count, then elements through their own
packed codec — plus the byte-content fast path: for `CountedList UInt8`
(script bytes, witness items) the spec's element walk is proved to be
take/drop on the raw bytes, so a dedicated higher-priority instance moves
whole byte regions at once instead of dispatching a codec per byte.

Checked claims:

- `mapToList_readElems` / `toList_pushElems`: the packed element sequence
  agrees with `decodeElems`/`encodeElems` whenever the element codec agrees.
- `instPackedCodecCountedList`: the packed counted-list codec agrees with
  `instCodecCountedList`, so any packed element codec lifts.
- `encodeElems_uint8` / `decodeElems_uint8`: the spec's byte-element sequence
  is the identity encoding and take/drop decoding on raw bytes, grounding the
  bulk `instPackedCodecCountedListBytes` fast path.

Why it matters: most of a real block's bytes are raw contents behind counts;
the fast path is the difference between paying a typeclass dispatch per byte
and moving the region in one pass, and it is proved against the same spec
instance as the generic walk.

## `BtcVerified.Impl.Packed.Tx`

The packed transaction codec: hand-written mirrors of the spec's hand-written
branches — legacy, Core's degenerate empty object, and the BIP144 marker/flag
form — sharing the spec's value-level smart constructors (`Tx.legacy?`,
`zipInputs`) so only the byte threading differs.

Checked claims:

- `mapToList_readSegwit` / `mapToList_readLegacy` / `mapToList_readEmpty`:
  each branch decoder agrees with its spec branch.
- `mapToList_readTx` / `toList_pushTx`: the packed transaction codec agrees
  with `decodeTx`/`encodeTx` — the marker/flag dispatch on slice bytes takes
  exactly the branch the spec's dispatch on list bytes takes — packaged as
  `instPackedCodecTx`.

Why it matters: the transaction codec is the one place the wire format and
the model genuinely disagree (witnesses regrouped, a reserved marker byte),
so its dispatch is where a fast reimplementation would most plausibly
diverge from the spec; the agreement theorem forecloses exactly that.

## Transported instances

`Bytes n` (hence `Hash256`), `OutPoint`, `Script`, `TxIn`, `TxOut`, `TxBody`,
`BlockHeader`, and `Block` each get their packed codec by applying
`PackedCodec.ofEquiv` to the same bijection their spec codec uses — one
declaration per structure, no hand-written proofs. The block level restates
the end-to-end result:

Checked claims:

- `mapToList_decodeBlock`: parsing any byte string with the packed block
  codec is the spec block parse — same acceptance, same block, same
  unconsumed remainder.
- `toList_encodeBlock`: the packed encoding of a block is byte-for-byte its
  spec encoding.

Why it matters: these two theorems are what let an extracted conformance
oracle answer at native speed while every answer remains an answer of the
verified spec — the throughput prerequisite for running this spec
differentially against Bitcoin Core and the wider implementation ecosystem.
The `lake test` fixture run re-checks both on real mainnet bytes through the
compiled code, covering the one link the theorems do not: the Lean compiler.
