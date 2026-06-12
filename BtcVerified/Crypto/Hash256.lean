import BtcVerified.Serialize.Codec
/-!
  # The 256-bit hash type

  Txids, block hashes, and merkle nodes are all 256-bit digests; this fixes
  the one type they share, together with the one rule for reading digest
  bytes as a value: little-endian, so the displayed (big-endian) hex is the
  digest bytes reversed — the interpretation Bitcoin's consensus arithmetic
  uses everywhere.

  Checked claims:

  * `Hash256.ofBytesLE_encode` / `Hash256.encode_ofBytesLE`: on full 32-byte
    digests, reading and the little-endian encoding are mutually inverse, so
    `ofBytesLE` loses nothing on the inputs hashing produces.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- A 256-bit hash: txid, block hash, or merkle node. -/
abbrev Hash256 := BitVec 256

/-- Read a 256-bit hash off the front of a byte string, low byte first — the
value Bitcoin's consensus arithmetic assigns to digest bytes (the displayed
hex is these bytes reversed). Returns 0 when fewer than 32 bytes are
supplied; every use site feeds a full digest, where `encode_ofBytesLE` makes
the reading lossless. -/
def Hash256.ofBytesLE (bs : List UInt8) : Hash256 :=
  ((decodeBitVecLE 32 bs).map Prod.fst).getD 0

/-- Reading back the 32-byte little-endian encoding of a hash returns the
hash. -/
theorem Hash256.ofBytesLE_encode (h : Hash256) :
    Hash256.ofBytesLE (encodeBitVecLE 32 h) = h := by
  have hd := decodeBitVecLE_encodeBitVecLE 32 h []
  rw [List.append_nil] at hd
  simp [Hash256.ofBytesLE, hd]

/-- A 32-byte string is exactly the little-endian encoding of the hash read
from it — `ofBytesLE` is injective on full digests. -/
theorem Hash256.encode_ofBytesLE {bs : List UInt8} (hlen : bs.length = 32) :
    encodeBitVecLE 32 (Hash256.ofBytesLE bs) = bs := by
  obtain ⟨v, hv⟩ := decodeBitVecLE_of_le_length 32 bs (by omega)
  rw [List.drop_eq_nil_of_le (by omega)] at hv
  have hcanon := decodeBitVecLE_canonical 32 bs v [] hv
  rw [List.append_nil] at hcanon
  rw [hcanon, Hash256.ofBytesLE_encode]

end BtcVerified
