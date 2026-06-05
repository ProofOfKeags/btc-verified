/-!
  # Bitcoin block data model

  This module fixes the data model for Bitcoin blocks and the substructures they
  contain. It is the foundation the serialization (`Codec`) instances, the
  consensus-validity predicates, proof-of-work, and ultimately fork choice are
  built on top of: none of those can be stated without first having a concrete
  representation of a block.

  The model is deliberately era- and witness-aware from the start. Bitcoin's
  chain history has a real pre-SegWit era, and SegWit is a soft fork — a
  *restriction* of the prior ruleset — so reasoning about consensus validity
  inherently spans the activation boundary. Concretely, a transaction's witness
  data is carried as an `Option`: `none` is the legacy serialization form (no
  BIP144 marker/flag, no witness), and `some` is the SegWit form.

  Hashes (txids, block hashes, merkle nodes) are `BitVec 256`. Scripts and
  witness items are opaque byte lists at this layer — full Bitcoin Script
  semantics is out of scope here; only their byte-level shape matters for
  serialization and the merkle/commitment consistency invariants that come
  later. No concrete hash function is fixed: hashing stays abstract, mirroring
  the `BitVM.BitCommitment` leaf.

  Nothing here is a serialization or validity *claim* yet; this module only
  introduces the vocabulary, plus the smallest structural well-formedness
  predicate (witness arity) that the consistency layer will build on.
-/

namespace BtcVerified

/-- A 256-bit hash: txid, block hash, or merkle node. -/
abbrev Hash256 := BitVec 256

/-- A reference to a specific previous transaction output: the transaction id of
the funding transaction together with the index of the output being spent. -/
structure OutPoint where
  /-- The txid of the transaction whose output is being spent. -/
  txid : Hash256
  /-- The zero-based index of the spent output within that transaction. -/
  vout : UInt32
  deriving DecidableEq

/-- A transaction input: the output it spends, the unlocking script, and the
input sequence number. -/
structure TxIn where
  /-- The previous output this input spends. -/
  prevout : OutPoint
  /-- The unlocking script (`scriptSig`), opaque bytes at this layer. -/
  scriptSig : List UInt8
  /-- The input sequence number (used for relative timelocks / RBF signalling). -/
  sequence : UInt32
  deriving DecidableEq

/-- A transaction output: the amount in satoshis and the locking script that must
be satisfied to spend it. -/
structure TxOut where
  /-- The output amount in satoshis. -/
  value : UInt64
  /-- The locking script (`scriptPubKey`), opaque bytes at this layer. -/
  scriptPubKey : List UInt8
  deriving DecidableEq

/-- The witness stack for a single input: an ordered list of stack items, each an
opaque byte string. SegWit attaches one such stack per transaction input. -/
abbrev WitnessStack := List (List UInt8)

/-- A Bitcoin transaction.

The `witness` field is the era/format discriminator. `none` is the legacy
(pre-SegWit) serialization with no BIP144 marker/flag and no witness data;
`some stacks` is the SegWit serialization carrying one `WitnessStack` per
input. A well-formed SegWit transaction has exactly as many witness stacks as
it has inputs (see `Tx.WitnessWellFormed`). -/
structure Tx where
  /-- Transaction version (serialized as a 4-byte little-endian word). -/
  version : UInt32
  /-- The transaction inputs, in order. -/
  inputs : List TxIn
  /-- The transaction outputs, in order. -/
  outputs : List TxOut
  /-- Witness data: `none` for legacy form, `some` (one stack per input) for SegWit. -/
  witness : Option (List WitnessStack)
  /-- The transaction lock time. -/
  lockTime : UInt32
  deriving DecidableEq

/-- Whether a transaction is in SegWit form (carries witness data). -/
def Tx.isSegWit (tx : Tx) : Bool := tx.witness.isSome

/-- Witness well-formedness: a legacy transaction (no witness) is trivially
well-formed, and a SegWit transaction must carry exactly one witness stack per
input. This is the smallest structural invariant the consistency layer needs
before it can talk about witness commitments. -/
def Tx.WitnessWellFormed (tx : Tx) : Prop :=
  match tx.witness with
  | none => True
  | some stacks => stacks.length = tx.inputs.length

/-- A legacy transaction is always witness-well-formed. -/
theorem witnessWellFormed_of_legacy {tx : Tx} (h : tx.witness = none) :
    tx.WitnessWellFormed := by
  simp [Tx.WitnessWellFormed, h]

/-- An 80-byte Bitcoin block header: the fields covered by proof of work.

`bits` is the compact (`nBits`) encoding of the target; decoding it to a
256-bit target and checking the block hash against it is the proof-of-work
layer's job, not this module's. -/
structure BlockHeader where
  /-- Block version. -/
  version : UInt32
  /-- The hash of the previous block's header. -/
  prevBlockHash : Hash256
  /-- The merkle root committing to the block's transactions. -/
  merkleRoot : Hash256
  /-- The block time (Unix epoch seconds). -/
  time : UInt32
  /-- The compact (`nBits`) encoding of the proof-of-work target. -/
  bits : UInt32
  /-- The proof-of-work nonce. -/
  nonce : UInt32
  deriving DecidableEq

/-- A block: its header together with the ordered list of transactions. -/
structure Block where
  /-- The block header. -/
  header : BlockHeader
  /-- The block's transactions, in order (the first is the coinbase). -/
  txs : List Tx
  deriving DecidableEq

end BtcVerified
