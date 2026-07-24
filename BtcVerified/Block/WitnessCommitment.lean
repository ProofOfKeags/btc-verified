import BtcVerified.Block.Block
import BtcVerified.Transaction.Txid
import BtcVerified.Crypto.Merkle
/-!
  # The block's witness commitment

  SegWit moves witness data outside the txid preimage, so the txid merkle
  root (`Commitment.lean`) no longer covers it; BIP141 restores the
  commitment through the coinbase. The wtxids form a second merkle tree —
  the coinbase's leaf taken as the zero hash, since its own witness sits
  beneath the commitment it carries — and the coinbase records
  `sha256d(witnessRoot ‖ witnessReservedValue)` in an output whose
  scriptPubKey is at least 38 bytes opening `6a24aa21a9ed`; when several
  outputs match, the last one is the commitment (Bitcoin Core's
  `GetWitnessCommitmentIndex`). The reserved value is the single 32-byte
  item of the coinbase input's witness stack.

  Unlike the txid tree, no canonicality condition is demanded of the
  witness tree, and none is needed: the padding ambiguity (CVE-2012-2459)
  needs room to change the leaf count, and in consensus use the
  transaction count is already pinned by the txid tree — between
  equal-length lists the root binds outright
  (`Merkle.root_binding_of_length_eq`). `Block.witnessRoot_binding` is
  that folklore argument made precise.

  Division of labor between the two commitments: the txid tree binds every
  body — including the coinbase's, and through it the recorded commitment
  itself — and misses exactly the witnesses; the witness tree binds every
  transaction beyond the coinbase, witnesses included, and misses exactly
  the coinbase's own witness — which is the reserved value, sitting in the
  commitment preimage. Together they cover every byte of a block. When a
  commitment is *required* (any block carrying witness data must have one)
  is a consensus guard at the validity layer, exactly as `merkleCommits`
  states the condition and not the rule.

  Checked claims:

  * `witnessCommitment_binding`: equal commitments imply equal witness
    roots and equal reserved values — or two concrete byte strings
    witnessing a double-SHA-256 collision.
  * `Block.witnessRoot_binding`: between blocks with equally many
    transactions, equal witness roots imply equal transactions beyond the
    coinbase, witnesses included — or a concrete collision.
  * `Block.witnessCommits_binding`: two blocks satisfying `witnessCommits`
    that record the same commitment and have equally many transactions
    agree on every transaction beyond the coinbase — or a concrete
    collision.
  * `Block.witnessCommits` is decidable, so real blocks are checked
    against it in the golden vectors and the `lake test` fixture.
-/

namespace BtcVerified

/-- The BIP141 witness commitment: the double-SHA-256 of the witness merkle
root followed by the 32-byte witness reserved value. -/
def witnessCommitment (root : Hash256) (reserved : List UInt8) : Hash256 :=
  ⟨Sha256.sha256d (root.1 ++ reserved), Sha256.sha256d_length _⟩

/-- The witness merkle root of a block: the merkle root over wtxids, the
coinbase's leaf taken as the zero hash — its witness sits beneath the
commitment it carries, so BIP141 zeroes its slot and the coinbase stays
bound by the txid tree instead. Degenerate on an empty transaction list (a
real block has at least its coinbase). -/
def Block.witnessRoot (b : Block) : Hash256 :=
  Merkle.root (0 :: (b.txs.val.drop 1).map Tx.wtxid)

/-- Whether an output records a witness commitment: at least 38 script
bytes opening `OP_RETURN`, a 36-byte push, and the BIP141 header
`aa21a9ed`. The 32 bytes after the header are the commitment; bytes past 38
carry no consensus meaning and do not disqualify. -/
def TxOut.isWitnessCommitment (o : TxOut) : Bool :=
  o.scriptPubKey.code.val.take 6 == [0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed]
    && decide (38 ≤ o.scriptPubKey.code.val.length)

/-- The commitment a coinbase records: the 32 bytes after the BIP141 header
in its *last* commitment-shaped output — BIP141 takes the highest output
index when several match, as does Bitcoin Core's
`GetWitnessCommitmentIndex`. `none` when no output matches. -/
def Tx.recordedWitnessCommitment? (coinbase : Tx) : Option (List UInt8) :=
  (coinbase.body.outputs.val.reverse.find? TxOut.isWitnessCommitment).map
    fun o => (o.scriptPubKey.code.val.drop 6).take 32

/-- The witness reserved value a coinbase carries: the single 32-byte item
BIP141 requires as its input's witness stack. Read from the first input —
the coinbase's only one under consensus, though this layer does not enforce
the single-input rule. `none` when the transaction is not
witness-serialized or the stack is not one 32-byte item. -/
def Tx.witnessReservedValue? : Tx → Option (List UInt8)
  | .legacy .. => none
  | .empty .. => none
  | .segwit _ ins _ _ _ =>
    match ins.val with
    | [] => none
    | input :: _ =>
      match input.witness.val with
      | [item] => if item.val.length = 32 then some item.val else none
      | _ => none

/-- The commitment a block records: its coinbase's, when it has one. -/
def Block.recordedWitnessCommitment? (b : Block) : Option (List UInt8) :=
  b.txs.val.head?.bind Tx.recordedWitnessCommitment?

/-- The witness reserved value a block carries: its coinbase's, when it has
one. -/
def Block.witnessReservedValue? (b : Block) : Option (List UInt8) :=
  b.txs.val.head?.bind Tx.witnessReservedValue?

/-- The BIP141 witness commitment condition: the coinbase carries the
32-byte reserved value as its witness, and the commitment it records is
exactly the double-SHA-256 of this block's witness root followed by that
value. Whether a block is *required* to satisfy this (any block carrying
witness data is) is a consensus guard at the validity layer. -/
def Block.witnessCommits (b : Block) : Prop :=
  ∃ reserved, b.witnessReservedValue? = some reserved
    ∧ b.recordedWitnessCommitment?
      = some (witnessCommitment b.witnessRoot reserved).1

instance : DecidablePred Block.witnessCommits := fun b =>
  match hv : b.witnessReservedValue? with
  | some reserved =>
    decidable_of_iff
      (b.recordedWitnessCommitment?
        = some (witnessCommitment b.witnessRoot reserved).1)
      (by simp [Block.witnessCommits, hv])
  | none => isFalse (by rintro ⟨r, hr, -⟩; rw [hv] at hr; cases hr)

/-- Equal witness commitments mean equal witness roots and equal reserved
values — or two concrete byte strings witnessing a double-SHA-256
collision. The commitment preimage splits unambiguously because a root is
exactly 32 bytes, the same shape as `Merkle.combine_binding`. -/
theorem witnessCommitment_binding {r₁ r₂ : Hash256} {v₁ v₂ : List UInt8}
    (h : witnessCommitment r₁ v₁ = witnessCommitment r₂ v₂) :
    (r₁ = r₂ ∧ v₁ = v₂) ∨ Sha256.Collision := by
  have hd : Sha256.sha256d (r₁.1 ++ v₁) = Sha256.sha256d (r₂.1 ++ v₂) :=
    congrArg Subtype.val h
  by_cases hm : r₁.1 ++ v₁ = r₂.1 ++ v₂
  · obtain ⟨h₁, h₂⟩ := List.append_inj hm (by rw [r₁.2, r₂.2])
    exact Or.inl ⟨Subtype.ext h₁, h₂⟩
  · exact Or.inr ⟨_, _, hm, hd⟩

/-- Between blocks with equally many transactions, equal witness roots mean
equal transactions beyond the coinbase, witnesses included — or two
concrete byte strings witnessing a double-SHA-256 collision. No
canonicality condition: with the length pinned (by the txid tree, in
consensus use), the root binds outright — the CVE-2012-2459 ambiguity
needs room to change the leaf count. -/
theorem Block.witnessRoot_binding {b₁ b₂ : Block}
    (hlen : b₁.txs.val.length = b₂.txs.val.length)
    (hroot : b₁.witnessRoot = b₂.witnessRoot) :
    b₁.txs.val.drop 1 = b₂.txs.val.drop 1 ∨ Sha256.Collision := by
  unfold Block.witnessRoot at hroot
  have hlen' : ((0 : Hash256) :: (b₁.txs.val.drop 1).map Tx.wtxid).length
      = ((0 : Hash256) :: (b₂.txs.val.drop 1).map Tx.wtxid).length := by
    simp only [List.length_cons, List.length_map, List.length_drop, hlen]
  rcases Merkle.root_binding_of_length_eq hlen' hroot with heq | c
  · simp only [List.cons.injEq, true_and] at heq
    exact Tx.map_wtxid_binding heq
  · exact Or.inr c

/-- Two blocks satisfying the witness-commitment condition that record the
same commitment and have equally many transactions agree on every
transaction beyond the coinbase, witnesses included — or two concrete byte
strings witnessing a double-SHA-256 collision. In consensus use both
side conditions come from the txid tree: `merkleCommits` binding pins the
transaction count and the coinbase body, and the recorded commitment is
part of that body. -/
theorem Block.witnessCommits_binding {b₁ b₂ : Block}
    (hc₁ : b₁.witnessCommits) (hc₂ : b₂.witnessCommits)
    (hrec : b₁.recordedWitnessCommitment? = b₂.recordedWitnessCommitment?)
    (hlen : b₁.txs.val.length = b₂.txs.val.length) :
    b₁.txs.val.drop 1 = b₂.txs.val.drop 1 ∨ Sha256.Collision := by
  obtain ⟨v₁, -, hr₁⟩ := hc₁
  obtain ⟨v₂, -, hr₂⟩ := hc₂
  rw [hr₁, hr₂, Option.some.injEq] at hrec
  rcases witnessCommitment_binding (Subtype.ext hrec) with ⟨hroot, -⟩ | c
  · exact Block.witnessRoot_binding hlen hroot
  · exact Or.inr c

end BtcVerified
