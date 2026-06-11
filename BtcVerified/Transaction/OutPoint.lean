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

end BtcVerified
