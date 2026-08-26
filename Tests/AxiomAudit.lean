import BtcVerified
import Lean
/-!
  # Axiom audit

  `lake build` succeeds even when a proof uses `sorry` — it is only a warning.
  This file is what turns "it builds" into "it is proved": `#assert_axioms`
  fails elaboration if a registered constant depends on any axiom outside the
  standard three (`propext`, `Classical.choice`, `Quot.sound`) and the
  natively checked `bv_decide` LRAT certificates — in particular on
  `sorryAx`.

  Every headline theorem and codec instance must be registered here when its
  leaf lands. Auditing a `Codec` instance covers both of its law fields and
  everything they depend on.
-/

namespace Tests.AxiomAudit

open Lean Elab Command

set_option linter.hashCommand false

/-- The axioms a verified result may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `bv_decide` discharges each goal by SAT solving and records the natively
checked LRAT certificate as a per-declaration axiom named
`<decl>._native.bv_decide.ax_*`. Those proofs trust the SAT pipeline (solver +
native LRAT checker), which we accept; this recognizes them so the audit can
allow them while still rejecting `sorryAx` and any other stray axiom. The
match is on the exact last three name components (`._native.bv_decide.ax_*`),
not a substring, so an unrelated declaration whose name merely mentions
`bv_decide` cannot slip through. -/
def isBvDecideCertificate (ax : Name) : Bool :=
  match ax with
  | .str (.str (.str _ "_native") "bv_decide") s => s.startsWith "ax_"
  | _ => false

/-- Fail elaboration if the named constant depends on any axiom outside
`allowedAxioms` (plus `bv_decide` certificates) — in particular on `sorryAx`. -/
elab "#assert_axioms " id:ident : command => do
  let name ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let bad := axioms.filter fun ax =>
    !allowedAxioms.contains ax && !isBvDecideCertificate ax
  unless bad.isEmpty do
    throwError "{name} depends on disallowed axioms: {bad.toList}"

/-! ## Serialization -/

#assert_axioms BtcVerified.Serialize.encode_injective
#assert_axioms BtcVerified.Serialize.instCodecProd
#assert_axioms BtcVerified.Serialize.instCodecUInt8
#assert_axioms BtcVerified.Serialize.instCodecUInt16
#assert_axioms BtcVerified.Serialize.instCodecUInt32
#assert_axioms BtcVerified.Serialize.instCodecUInt64
#assert_axioms BtcVerified.Serialize.instCodecBitVec256
#assert_axioms BtcVerified.Serialize.instCodecBytes
#assert_axioms BtcVerified.Bytes.val_reverse
#assert_axioms BtcVerified.Bytes.reverse_reverse
#assert_axioms BtcVerified.Bytes.ofListExact?_eq_some_iff
#assert_axioms BtcVerified.Bytes.ofListExact?_isSome_iff
#assert_axioms BtcVerified.Bytes.ofListExact?_eq_none_iff
#assert_axioms BtcVerified.Bytes.ofListExact?_val
#assert_axioms BtcVerified.Bytes.ofListExact?_map_reverse
#assert_axioms BtcVerified.Bytes.ofListPadLeft?_eq_some_iff
#assert_axioms BtcVerified.Bytes.ofListPadRight?_eq_some_iff
#assert_axioms BtcVerified.Bytes.ofListPadLeft?_isSome_iff
#assert_axioms BtcVerified.Bytes.ofListPadRight?_isSome_iff
#assert_axioms BtcVerified.Bytes.ofListPadLeft?_eq_none_iff
#assert_axioms BtcVerified.Bytes.ofListPadRight?_eq_none_iff
#assert_axioms BtcVerified.Bytes.parts_of_ofListPadLeft?
#assert_axioms BtcVerified.Bytes.parts_of_ofListPadRight?
#assert_axioms BtcVerified.Bytes.head?_of_ofListPadLeft?
#assert_axioms BtcVerified.Bytes.getLast?_of_ofListPadRight?
#assert_axioms BtcVerified.Bytes.ofListPadLeft?_map_reverse
#assert_axioms BtcVerified.Bytes.ofListTruncateLeft?_eq_some_iff
#assert_axioms BtcVerified.Bytes.ofListTruncateRight?_eq_some_iff
#assert_axioms BtcVerified.Bytes.ofListTruncateLeft?_isSome_iff
#assert_axioms BtcVerified.Bytes.ofListTruncateRight?_isSome_iff
#assert_axioms BtcVerified.Bytes.ofListTruncateLeft?_eq_none_iff
#assert_axioms BtcVerified.Bytes.ofListTruncateRight?_eq_none_iff
#assert_axioms BtcVerified.Bytes.ofListTruncateLeft?_map_reverse
#assert_axioms BtcVerified.Bytes.ofListTruncateLeft?_of_ofListPadLeft?
#assert_axioms BtcVerified.Bytes.ofListTruncateRight?_of_ofListPadRight?
#assert_axioms BtcVerified.Bytes.ofList_left_exactly_one
#assert_axioms BtcVerified.Bytes.ofList_right_exactly_one
#assert_axioms BtcVerified.Bytes.ofListPad_isSome_eq
#assert_axioms BtcVerified.Bytes.ofListTruncate_isSome_eq
#assert_axioms BtcVerified.CompactSize.decode_encode
#assert_axioms BtcVerified.CompactSize.decode_canonical
#assert_axioms BtcVerified.CompactSize.encode_length_le
#assert_axioms BtcVerified.Serialize.instCodecCountedList

/-! ## Scripts -/

#assert_axioms BtcVerified.instCodecScript

/-! ## Transactions -/

#assert_axioms BtcVerified.instCodecOutPoint
#assert_axioms BtcVerified.instCodecTxIn
#assert_axioms BtcVerified.instCodecTxOut
#assert_axioms BtcVerified.instCodecTxBody
#assert_axioms BtcVerified.decodeTx_encodeTx
#assert_axioms BtcVerified.decodeTx_canonical
#assert_axioms BtcVerified.instCodecTx

/-! ## Blocks -/

#assert_axioms BtcVerified.instCodecBlockHeader
#assert_axioms BtcVerified.BlockHeader.encode_length
#assert_axioms BtcVerified.instCodecBlock

/-! ## Cryptography

  SHA-256 is a concrete computable `def`, not a verified theorem, but it is
  load-bearing — so the audit guards it against a stray `sorry` or a sneaked-in
  `native_decide`. Auditing `sha256d` covers `sha256` transitively. -/

#assert_axioms BtcVerified.Collision.comp
#assert_axioms BtcVerified.CollisionResistant.injective
#assert_axioms BtcVerified.CollisionResistant.comp
#assert_axioms BtcVerified.Collision.comp_inner
#assert_axioms BtcVerified.CollisionResistant.of_comp
#assert_axioms BtcVerified.Sha256.sha256d
#assert_axioms BtcVerified.Sha256.sha256d_length
#assert_axioms BtcVerified.Sha256.collisionResistant_sha256d
#assert_axioms BtcVerified.Sha256.collisionResistant_sha256_iff_sha256d
#assert_axioms BtcVerified.instCodecHash256
#assert_axioms BtcVerified.Hash256.encode_length

/-! ## Transaction ids -/

#assert_axioms BtcVerified.Tx.txid_binding
#assert_axioms BtcVerified.Tx.wtxid_binding
#assert_axioms BtcVerified.Tx.wtxid_legacy
#assert_axioms BtcVerified.Tx.wtxid_empty

/-! ## The chainstate -/

#assert_axioms Finmap.insert_erase
#assert_axioms BtcVerified.UtxoSet.lookup_spend_of_mem
#assert_axioms BtcVerified.UtxoSet.lookup_spend_of_notMem
#assert_axioms BtcVerified.UtxoSet.spend_perm
#assert_axioms BtcVerified.UtxoSet.mem_spend
#assert_axioms BtcVerified.UtxoSet.lookup_create_of_notMem
#assert_axioms BtcVerified.UtxoSet.lookup_create_of_mem
#assert_axioms BtcVerified.UtxoSet.mem_create
#assert_axioms BtcVerified.UtxoSet.totalValue_insert
#assert_axioms BtcVerified.UtxoSet.totalValue_erase
#assert_axioms BtcVerified.UtxoSet.totalValue_spend
#assert_axioms BtcVerified.UtxoSet.totalValue_create
#assert_axioms BtcVerified.UtxoSet.lookup_apply_of_mem_creates
#assert_axioms BtcVerified.UtxoSet.lookup_apply_output
#assert_axioms BtcVerified.UtxoSet.lookup_apply_of_mem_spends
#assert_axioms BtcVerified.UtxoSet.lookup_apply_of_notMem
#assert_axioms BtcVerified.UtxoSet.totalValue_apply

/-! ## Block hashes -/

#assert_axioms BtcVerified.BlockHeader.hash_binding

/-! ## The chain -/

#assert_axioms BtcVerified.Chain.toList_append
#assert_axioms BtcVerified.Chain.isChain_toList
#assert_axioms BtcVerified.Chain.tip_commits_prefix
#assert_axioms BtcVerified.Chain.tip_commits

/-! ## Consensus: transaction premises -/

#assert_axioms BtcVerified.Tx.isWellFormed_iff
#assert_axioms BtcVerified.Tx.stripped_size_bound_iff_core
#assert_axioms BtcVerified.Tx.WellFormed.outputs_length_le
#assert_axioms BtcVerified.Coin.isMature_iff
#assert_axioms BtcVerified.Consensus.LockTime.isPast_iff
#assert_axioms BtcVerified.Consensus.LockTime.ofUInt32_past_iff
#assert_axioms BtcVerified.TxBody.isLockTimeSatisfied_iff
#assert_axioms BtcVerified.TxBody.lockTimeSatisfied_iff_core
#assert_axioms BtcVerified.Tx.spentCoins_aligned
#assert_axioms BtcVerified.Tx.spentCoins_length
#assert_axioms BtcVerified.Tx.isAdmissible_iff
#assert_axioms BtcVerified.Tx.creates_do_not_overwrite_after_spend
#assert_axioms BtcVerified.UtxoSet.totalValue_apply_of_admissible
#assert_axioms BtcVerified.UtxoSet.totalValue_apply_le_of_admissible
#assert_axioms BtcVerified.UtxoSet.applyChecked_eq_some_iff

/-! ## The merkle tree -/

#assert_axioms BtcVerified.Merkle.combine_binding
#assert_axioms BtcVerified.Merkle.root_binding_of_length_eq
#assert_axioms BtcVerified.Merkle.root_binding_of_canonical
#assert_axioms BtcVerified.Block.merkleCommits

/-! ## Bitcoin Core's ComputeMerkleRoot -/

#assert_axioms BtcVerified.Impl.BitcoinCore.computeRoot_eq_root
#assert_axioms BtcVerified.Impl.BitcoinCore.computeMerkleRoot_fst
#assert_axioms BtcVerified.Impl.BitcoinCore.canonical_of_not_mutated
#assert_axioms BtcVerified.Impl.BitcoinCore.eq_of_computeMerkleRoot_eq_of_not_mutated

/-! ## Packed codecs

  Auditing a `PackedCodec` instance covers both of its agreement laws —
  packed encode and decode compute exactly what the spec codec computes —
  and everything they depend on.
-/

#assert_axioms BtcVerified.Impl.Packed.ByteSlice.toList_eq
#assert_axioms BtcVerified.Impl.Packed.PackedCodec.toList_encode
#assert_axioms BtcVerified.Impl.Packed.PackedCodec.mapToList_decode_toByteArray
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecProd
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecUInt8
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecUInt16
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecUInt32
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecUInt64
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecBitVec256
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecBytes
#assert_axioms BtcVerified.Impl.Packed.mapToList_readCompactSize
#assert_axioms BtcVerified.Impl.Packed.toList_pushCompactSize
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecCountedList
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecOutPoint
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecScript
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecTxIn
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecTxOut
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecTxBody
#assert_axioms BtcVerified.Impl.Packed.mapToList_readTx
#assert_axioms BtcVerified.Impl.Packed.toList_pushTx
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecTx
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecBlockHeader
#assert_axioms BtcVerified.Impl.Packed.instPackedCodecBlock
#assert_axioms BtcVerified.Impl.Packed.mapToList_decodeBlock
#assert_axioms BtcVerified.Impl.Packed.toList_encodeBlock

/-! ## BitVM -/

#assert_axioms BtcVerified.BitVM.BitCommitment.openings_with_distinct_bits_are_distinct
#assert_axioms BtcVerified.BitVM.BitCommitment.commitment_verifies_against_original_opening
#assert_axioms BtcVerified.BitVM.BitCommitment.equivocation_refutes_collision_resistance
#assert_axioms BtcVerified.BitVM.BitCommitment.CollisionResistance.nonEquivocation
#assert_axioms BtcVerified.BitVM.BitCommitment.NonEquivocation.binding
#assert_axioms BtcVerified.BitVM.BitCommitment.CollisionResistance.binding

end Tests.AxiomAudit
