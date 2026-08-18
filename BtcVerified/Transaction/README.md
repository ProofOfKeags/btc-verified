# BtcVerified/Transaction

The transaction: its data model, its wire codecs for both serialization
eras, and its ids.

## The data model

The transaction substructures — `OutPoint`, `TxIn`, `TxOut`, `TxBody`,
`SegwitInput`, `Tx`, and the `WitnessStack` alias — are era- and
witness-aware from the start, and push the structural facts of the wire
format into the types:

- A transaction is an inductive with three constructors over a shared,
  witness-free `TxBody` (version, inputs, outputs, lock time). `legacy` is the
  ordinary pre-SegWit form, `empty` is the degenerate zero-input/zero-output
  object Core's witness-aware decoder accepts, and `segwit` is the BIP144 form.
  The `TxBody` is at once what a txid commits to, the legacy serialization, and
  the witness-stripped form a SegWit transaction shows the pre-SegWit world;
  `Tx.body` recovers it from every constructor.
- A SegWit transaction bundles each input with the witness that unlocks it
  (`SegwitInput`), so the one-witness-per-input arity is structural rather than a
  side condition. The wire groups witnesses after inputs; that regrouping is the
  codec's job, not the model's. Per BIP144, if the transaction's witness is
  empty then the old serialization format must be used, so the `segwit`
  constructor also carries a proof that at least one input witness stack is
  non-empty.
- The ordinary `legacy` constructor carries a non-empty-inputs proof. The
  separate `empty` constructor covers Core's accepted `version ‖ 00 ‖ 00 ‖
  locktime` path without admitting empty-input/nonempty-output bodies that the
  witness-aware decoder cannot round-trip ([Bitcoin Core v28.0,
  `transaction.h` lines
  220–282](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L220-L282)).
- Every CompactSize-prefixed field — scripts, the input/output vectors, witness
  stacks — is a `CountedList`; witness items are opaque byte strings; scripts
  are `Script` (see `../Script/`); hash-valued fields are opaque `Hash256`
  digests — nothing in the data model computes a hash (ids are computed in
  `Txid.lean`, below).

Why it matters: consensus validity, proof of work, and fork choice presuppose
an actual representation of the substructures that carry their invariants.
This fixes that vocabulary as the base of the stack.

## The codecs

`Codec` instances for every transaction substructure, bottom-up: `OutPoint`,
`TxIn`, `TxOut`, and `TxBody` are each the product of their fields in wire
order, so their codecs come by composition (`Codec.ofEquiv` over the product
codec) with no hand-written proofs. The whole-transaction codec sits on top.

Checked claims:

- `decodeTx_encodeTx`: every transaction, including Core's degenerate empty
  object, round-trips with trailing bytes preserved.
- `decodeTx_canonical`: an accepted parse consumed exactly the canonical
  encoding — including dispatching to the legacy, empty, or SegWit branch the
  value's own form dictates.

The transaction codec is the one place the wire format and the data model
disagree on order: `decode` reads the inputs and witnesses from their separate
BIP144 regions and rebundles them (`zipInputs`); `encode` unzips. The
dispatch first reads the input count. A zero count makes the following byte
Core-style optional-data flags: `0x00` yields the empty object, `0x01` selects
SegWit, and other flags are rejected. The SegWit branch also enforces Core's
empty-witness rule: marker/flag serialization is rejected when every witness
stack is empty ([Bitcoin Core v28.0, `transaction.h` lines
224–250](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L224-L250)).
Packaged as `instCodecTx : Codec Tx`.

Why it matters: this is an implementation-independent syntax object, not a Lean
copy of `CTransaction`, but its accepted domain is deliberately compatible with
Core's witness-aware decoder. Verified round-trip and canonicality provide the
serialization backbone; an `Impl/BitcoinCore` transcription can later prove its
decoder and validator equivalent to this model at the accepted-block and state-
transition boundary, while other implementations can target the same model.

## Transaction ids

`Tx.txid` — the double-SHA-256 of the witness-free `TxBody` serialization, as
its raw 32 digest bytes — and `Tx.wtxid` (BIP141), the same over the full
serialization. Witness data never affects a txid; for a legacy transaction the
two coincide by `rfl`, as they do for the empty no-witness case.

Checked claims:

- `Tx.txid_binding`: equal txids imply equal witness-free bodies — or two
  concrete byte strings witnessing a double-SHA-256 collision. With
  `CollisionResistant.injective` (the generalized collision vocabulary in
  `BtcVerified.Collision`), a resistance hypothesis collapses this to outright
  injectivity.
- `Tx.wtxid_binding`: equal wtxids imply equal transactions, witnesses
  included — or a concrete collision.
- Golden vectors: the first Bitcoin payment's txid, the genesis coinbase txid
  (which is the genesis merkle root), and the SegWit coinbase's txid with
  `wtxid ≠ txid`.

Why it matters: a hash of an encoding only identifies anything because the
encoding is injective — `encode_injective`, from the codec round-trip law. The
serialization leaves are exactly what make txids meaningful, and the collision
disjunct is constructed, never assumed away: intractability of producing a
witness is the consumer's hypothesis, the only form in which collision
resistance can soundly appear over a concrete hash.
