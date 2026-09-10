import BtcVerified.Crypto.Hash256
import BtcVerified.Serialize.Codec
import BtcVerified.Serialize.Bytes
/-!
  # Outpoints

  An outpoint names the output a transaction input spends: the funding
  transaction's txid together with the output's index within it. The codec is
  the product of the field codecs in wire order, so both laws come by
  composition (`Codec.ofEquiv` over the product codec) with no hand-written
  proofs — the pattern every plain-product structure in the data model
  follows.

  ## Packed codec

  The packed `OutPoint` codec (issue #52). The spec codec is `Codec.ofEquiv`
  over the field product in wire order; the packed codec is the same
  transport applied to the packed field codecs, so agreement with
  `instCodecOutPoint` holds by construction, with no hand-written proof.

  Checked claims:

  * `instPackedCodecOutPoint`: the packed codec agrees with the
    specification encoder and decoder on every input.
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

/-- The outpoint a coinbase input carries: zero txid, all-ones index. It names
no real output — the one outpoint a regular input may never claim (Core's
[`COutPoint::SetNull` / `IsNull`, Bitcoin Core v28.0, `transaction.h` lines
31–42](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L31-L42)). -/
def OutPoint.null : OutPoint := ⟨0, 0xffffffff⟩

end BtcVerified

/-! ## Packed codec -/

namespace BtcVerified.Packed

open BtcVerified.Serialize BtcVerified

/-- The packed `OutPoint` codec, agreeing with `instCodecOutPoint` by
transport over the same field product. -/
instance instPackedCodecOutPoint : PackedCodec OutPoint :=
  PackedCodec.ofEquiv OutPoint.equivProd inferInstance inferInstance

end BtcVerified.Packed
