# BtcVerified/Block

The block: its data model and codecs, the block hash, the merkle commitment
condition, and the chain type where a tip hash commits to the whole history.

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

`Block.merkleCommits` (`Commitment.lean`) is the consensus condition tying a
block's body to its header: a canonical txid list whose merkle root is the
header's. The tree spec it is stated over, and its binding theorems, live in
`../Crypto/` (see that README's `BtcVerified.Merkle` section).

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

- `BlockHeader.hash_binding`: the block hash is a binding commitment to the
  header — equal block hashes mean equal headers, or a concrete
  double-SHA-256 collision, the same shape as `Merkle.root_binding_of_length_eq`.
- `Chain.toList_append`: stacking chain segments concatenates their header
  lists — composition is compatible with the plain-list view.
- `Chain.isChain_toList`: a chain's list-of-headers view satisfies `IsChain`,
  the decidable linkage predicate over an anchor and a plain list, so real
  header lists can be checked directly, without constructing a `Chain` term
  (`Chain.tipHash_toList` recovers the tip index from the list).
- `Chain.tip_commits_prefix`: of two chains sharing a tip hash, the one with
  no more headers carries a prefix (tip-first) of the other's header list —
  or a concrete collision. Nothing relates the anchors: a shorter chain
  anchored higher up the same history is exactly this prefix situation.
- `Chain.tip_commits`: two chains of equal length sharing a tip hash carry
  the same header list — or a concrete collision. The tip hash commits to
  the entire history, proved in the same peel-and-recurse,
  collision-disjunct style as `Merkle.root_binding_of_length_eq`.
- Golden vector: block 1's raw 80 header bytes decode, re-encode, and hash
  to the well-known block 1 hash; the decoded header extends the decoded
  genesis header (`BlockHeader.Extends`); and the two headers form an
  `IsChain 0` chain — the genesis instantiation on real mainnet data.

Why it matters: fork choice compares branches, and a branch has to *be*
something before validity or cumulative work can be stated over it. This is
that structural layer — a tip hash commits to an entire history — and every
later layer (proof of work, the block tree, validity, fork choice) is a
refinement of this type, not a rewrite.
