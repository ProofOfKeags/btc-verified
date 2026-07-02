import BtcVerified.Crypto.Hash256
import BtcVerified.Serialize.Codec
/-!
  # Outpoints

  An outpoint names the output a transaction input spends: the funding
  transaction's txid together with the output's index within it. The codec is
  the product of the field codecs in wire order, so both laws come by
  composition (`Codec.ofEquiv` over the product codec) with no hand-written
  proofs — the pattern every plain-product structure in the data model
  follows.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- A reference to a specific previous transaction output: the transaction id of
the funding transaction together with the index of the output being spent. -/
structure OutPoint where
  /-- The txid of the transaction whose output is being spent. -/
  txid : Hash256
  /-- The zero-based index of the spent output within that transaction. -/
  vout : UInt32
  deriving DecidableEq

/-- An `OutPoint` is exactly its txid followed by its output index. -/
def OutPoint.equivProd : OutPoint ≃ (Hash256 × UInt32) where
  toFun o := (o.txid, o.vout)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Serializes an `OutPoint` as its 32-byte txid followed by its little-endian
4-byte output index. -/
instance instCodecOutPoint : Codec OutPoint :=
  Codec.ofEquiv OutPoint.equivProd inferInstance

/-- An `OutPoint` encodes to 36 bytes: a 32-byte txid and a 4-byte index. -/
theorem encode_outpoint_length (o : OutPoint) : (Codec.encode o).length = 36 := by
  change (Codec.encode o.txid ++ Codec.encode o.vout).length = 36
  rw [List.length_append, Hash256.encode_length, encode_uint32_length]

/-- Every 36-byte string is some `OutPoint`'s encoding. -/
theorem exists_encode_outpoint {L : List UInt8} (h : L.length = 36) :
    ∃ op : OutPoint, Codec.encode op = L := by
  obtain ⟨d, hd⟩ := exists_encode_hash256 (L := L.take 32) (by rw [List.length_take]; omega)
  obtain ⟨vout, hvout⟩ := exists_encode_uint32 (L := L.drop 32) (by rw [List.length_drop]; omega)
  exact ⟨⟨d, vout⟩, by change Codec.encode d ++ Codec.encode vout = L; rw [hd, hvout,
    List.take_append_drop]⟩

end BtcVerified
