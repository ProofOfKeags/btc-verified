import BtcVerified
import Lean
/-!
  # Axiom audit

  `lake build` succeeds even when a proof uses `sorry` — it is only a warning.
  This file is what turns "it builds" into "it is proved": `#assert_axioms`
  fails elaboration if a registered constant depends on any axiom outside the
  standard three (`propext`, `Classical.choice`, `Quot.sound`) — in particular
  on `sorryAx`.

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
allow them while still rejecting `sorryAx` and any other stray axiom. -/
def isBvDecideCertificate (ax : Name) : Bool :=
  (ax.toString.splitOn ".bv_decide.ax").length > 1

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

#assert_axioms BtcVerified.Tx.txid_faithful
#assert_axioms BtcVerified.Tx.wtxid_faithful
#assert_axioms BtcVerified.Tx.wtxid_legacy

/-! ## Block hashes -/

#assert_axioms BtcVerified.BlockHeader.hash_faithful

/-! ## The chain -/

#assert_axioms BtcVerified.Chain.toList_append
#assert_axioms BtcVerified.Chain.isChain_toList
#assert_axioms BtcVerified.Chain.tip_commits

/-! ## The merkle tree -/

#assert_axioms BtcVerified.Merkle.combine_inj
#assert_axioms BtcVerified.Merkle.root_inj_of_length_eq
#assert_axioms BtcVerified.Merkle.root_inj_of_canonical
#assert_axioms BtcVerified.Block.merkleCommits

/-! ## Bitcoin Core's ComputeMerkleRoot -/

#assert_axioms BtcVerified.Impl.BitcoinCore.computeRoot_eq_root
#assert_axioms BtcVerified.Impl.BitcoinCore.computeMerkleRoot_fst
#assert_axioms BtcVerified.Impl.BitcoinCore.canonical_of_not_mutated
#assert_axioms BtcVerified.Impl.BitcoinCore.eq_of_computeMerkleRoot_eq_of_not_mutated

/-! ## BitVM -/

#assert_axioms BtcVerified.BitVM.BitCommitment.openings_with_distinct_bits_are_distinct
#assert_axioms BtcVerified.BitVM.BitCommitment.commitment_verifies_against_original_opening
#assert_axioms BtcVerified.BitVM.BitCommitment.equivocation_refutes_collision_resistance
#assert_axioms BtcVerified.BitVM.BitCommitment.CollisionResistance.nonEquivocation
#assert_axioms BtcVerified.BitVM.BitCommitment.NonEquivocation.binding
#assert_axioms BtcVerified.BitVM.BitCommitment.CollisionResistance.binding

end Tests.AxiomAudit
