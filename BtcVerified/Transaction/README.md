# BtcVerified/Transaction

The transaction: its data model, its wire codecs for both serialization
eras, and its ids.

## The data model

The transaction substructures — `OutPoint`, `TxIn`, `TxOut`, `TxBody`,
`SegwitInput`, `Tx`, and the `WitnessStack` alias — are era- and
witness-aware from the start, and push the structural facts of the wire
format into the types:

- A transaction is an inductive with two constructors over a shared,
  witness-free `TxBody` (version, inputs, outputs, lock time). `legacy` is the
  pre-SegWit form; `segwit` is the BIP144 form. The `TxBody` is at once what a
  txid commits to, the legacy serialization, and the witness-stripped form a
  SegWit transaction shows the pre-SegWit world; `Tx.body` recovers it from
  either constructor.
- A SegWit transaction bundles each input with the witness that unlocks it
  (`SegwitInput`), so the one-witness-per-input arity is structural rather than a
  side condition. The wire groups witnesses after inputs; that regrouping is the
  codec's job, not the model's. Per BIP144, if the transaction's witness is
  empty then the old serialization format must be used, so the `segwit`
  constructor also carries a proof that at least one input witness stack is
  non-empty.
- The `legacy` constructor carries a non-empty-inputs proof, because the SegWit
  serialization reserves a zero input count (the `0x00` marker), so a legacy
  transaction can never encode zero inputs.
- Every CompactSize-prefixed field — scripts, the input/output vectors, witness
  stacks — is a `CountedList`; witness items are opaque byte strings; scripts
  are `Script` (see `../Script/`); hashing stays abstract.

Why it matters: consensus validity, proof of work, and fork choice presuppose
an actual representation of the substructures that carry their invariants.
This fixes that vocabulary as the base of the stack.

## The codecs

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
unambiguous against the marker. The SegWit branch also enforces BIP144's
empty-witness rule: marker/flag serialization is rejected when every witness
stack is empty. Packaged as `instCodecTx : Codec Tx`.

Why it matters: a transaction is the unit a block commits to and the unit fork
choice ultimately weighs. Verified round-trip and canonicality for both eras is
the serialization backbone the block codec and the txid/merkle commitments build
on.

## Transaction ids

`Tx.txid` — the double-SHA-256 of the witness-free `TxBody` serialization, as
its raw 32 digest bytes — and `Tx.wtxid` (BIP141), the same over the full
serialization. Witness data never affects a txid; for a legacy transaction the
two coincide by `rfl`.

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
