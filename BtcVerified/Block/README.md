# BtcVerified/Block

The block: its data model and codecs, the block hash, the merkle commitment
condition, and hash-linked chains with binding theorems under explicit length
assumptions.

## The data model and codecs

`BlockHeader` and `Block` complete the syntactic hierarchy: every byte of a
block is parsed by a verified codec, from CompactSize counts up through
transactions to the block itself. Both structures agree with the wire on
field order, so both codecs come by composition (`Codec.ofEquiv` over the
product codec) with no hand-written proofs — a header is its six fields in
wire order, and a block is its header followed by its CompactSize-counted
transactions.

Checked claims:

- `instCodecBlockHeader`: the header codec satisfies round-trip and
  canonicality, inherited field by field.
- `BlockHeader.encode_length`: every header encodes to exactly 80 bytes — the
  fixed proof-of-work preimage size.
- `instCodecBlock`: the block codec satisfies round-trip and canonicality.

`BlockHeader.lean` and `Block.lean` also contain their packed codec instances
and agreement proofs, in separate `BtcVerified.Packed` sections. See the
[packed-codec overview](../Packed/README.md) for the executable transport
and its end-to-end claims.

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

## The merkle commitment

`Block.merkleCommits` (`Commitment.lean`) requires a canonical txid list whose
merkle root is the header's. Applying `Merkle.root_binding_of_canonical` to two
such blocks with the same header additionally requires nonempty lists and equal
enclosing widths. The result is equal txid lists or a collision between node
preimages from their two trees. The condition alone does not establish these
additional premises or equality of transaction counts. See `../Crypto/` for the
tree definition and its binding theorems.

## The witness commitment

SegWit moves witness data outside the txid preimage, so the txid tree no
longer covers it; BIP141 restores the commitment through the coinbase.
`Block.witnessCommits` (`WitnessCommitment.lean`) is the condition: the
wtxids form a second merkle tree — the coinbase's leaf zeroed, since its own
witness sits beneath the commitment it carries — and the coinbase records
the double-SHA-256 of that root and the 32-byte witness reserved value (its
input's single witness item) in the last output opening `6a24aa21a9ed` with
32 bytes behind the header. The extracted values are typed `Bytes 32` — 32
raw bytes, with no hash semantics claimed — while the witness root and the
computed commitment are digests; `Hash256` being definitionally `Bytes 32`
makes the commitment preimage exactly a merkle node's, so the commitment
*is* `Merkle.combine`. The witness binding theorems assume equal transaction
counts explicitly. Under that premise, `Merkle.root_binding_of_length_eq`
excludes padding ambiguity without a canonicality requirement, leaving equality
or a collision between inputs from the compared blocks. A shared txid merkle
commitment does not, by itself, supply equal counts.

Checked claims:

- `witnessCommitment_binding`: equal commitments imply equal witness roots
  and reserved values, or the two specified root-and-reserved-value preimages
  collide under double-SHA-256.
- `Block.witnessRoot_binding`: blocks with equally many transactions and equal
  witness roots agree on transactions beyond the coinbase, witnesses included,
  or collide on preimages from their witness trees or transaction encodings.
- `Block.witnessCommits_binding`: blocks satisfying the condition, recording
  the same commitment, and having equally many transactions agree beyond the
  coinbase, or collide on inputs from their witness commitments, witness trees,
  or transaction encodings.
- Golden vectors: the SegWit activation coinbase's real commitment output
  and reserved value, the recognition rules (minimum length, exact header,
  trailing bytes, last-match-wins), and `witnessCommits` itself over all
  1866 transactions of block 481824 in the `lake test` fixture. These are finite
  checks of the decoded fixture against its expected commitments.

Why it matters: txids hash transaction bodies while wtxids also hash witnesses.
The witness tree zeroes the coinbase leaf, and the outer commitment includes the
coinbase's reserved value. These leaves provide the components for a block-body
binding argument. Combining them requires the stated count or width premises
and shared commitments; header equality alone does not establish equal enclosing
widths ([#14](https://github.com/ProofOfKeags/btc-verified/issues/14)). Collision
conclusions retain inputs from the two compared blocks.

## Block hashes and the chain

`BlockHeader.hash` — the double-SHA-256 of a header's 80-byte encoding, the
same digest `prevBlockHash` links commit to and a proof-of-work target is
checked against (the target check itself is a later leaf). Promoted from the
ad hoc expression the fixture tests computed inline, the same move `Tx.txid`
made for transactions.

On top of it, `Chain`: a structurally linked sequence of block headers,
tip-first (the newest header is the outermost constructor) and hash-anchored
at both ends — `Chain anchor tip` is a segment reaching from the block hash
`anchor` (exclusive) up to the tip hash `tip`, with the linkage carried by
the indices themselves: extending demands the rest's tip hash be the new
header's `prevBlockHash`. Carrying both endpoints in the type is what lets
segments compose (`Chain.append`, with the empty segment as identity) — the
algebra the block tree's branch paths will reuse — while the full Bitcoin
chain stays the plain genesis instantiation `Chain 0 tip` (the zero hash is
the genesis header's own `prevBlockHash`), not a special case. This is the
*linear* chain only: proof of work, cumulative work, and the block tree
(fork detection) are later leaves built on the same linkage relation.

Checked claims:

- `BlockHeader.hash_binding`: equal block hashes imply equal headers, or the
  two specified 80-byte header encodings collide under double-SHA-256.
- `Chain.toList_append`: stacking chain segments concatenates their header
  lists — composition is compatible with the plain-list view.
- `Chain.isChain_toList`: a chain's list-of-headers view satisfies `IsChain`,
  the decidable linkage predicate over an anchor and a plain list, so real
  header lists can be checked directly, without constructing a `Chain` term
  (`Chain.tipHash_toList` recovers the tip index from the list).
- `Chain.tip_commits_prefix`: of two chains sharing a tip hash, the one with
  no more headers carries a prefix (tip-first) of the other's header list —
  or a collision between header encodings from the two chains. Nothing relates
  the anchors: a shorter segment of the same history is this prefix situation.
- `Chain.tip_commits`: two chains of equal length sharing a tip hash carry
  the same header list, or a collision between header encodings from the two
  chains. Equal length is an explicit premise; a shared tip alone does not
  identify arbitrary chain segments.
- Golden vector: block 1's raw 80 header bytes decode, re-encode, and hash
  to the well-known block 1 hash; the decoded header extends the decoded
  genesis header (`BlockHeader.Extends`); and the two headers form an
  `IsChain 0` chain — the genesis instantiation on real mainnet data.

Why it matters: fork choice compares branches, and a branch has to *be*
something before validity or cumulative work can be stated over it. This is
that structural layer: comparisons with a shared tip yield a prefix or equality
under the stated length premises, or collisions involving the compared chains
themselves. Proof of work, the block tree, validity, and fork choice can build on
these results without assuming global collision freedom or treating them as
computational security bounds.
