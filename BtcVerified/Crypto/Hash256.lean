import BtcVerified.Serialize.Codec
/-!
  # The 256-bit hash type

  Txids, block hashes, and merkle nodes are all 256-bit digests; this fixes the
  one type they share — as the 32 raw digest bytes, in the order SHA-256 emits
  them, which is also the order they take on the wire. A digest is an identifier
  you concatenate and compare for equality, never a number you do arithmetic on,
  so the natural representation is bytes, not `BitVec 256`. The numeric reading
  (and the only place endianness matters) is deferred to where a digest meets a
  *target* in the proof-of-work check.

  The familiar big-endian display hex is these bytes reversed; that reversal is
  a display convention only, with no role in hashing or the wire codec — so it
  lives in test helpers, not here. On the wire a hash is exactly its 32 bytes,
  so its codec writes them as-is, with no little-endian step.

  Checked claims:

  * `instCodecHash256`: the hash codec round-trips and is canonical — 32 raw
    bytes off the front.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- A 256-bit hash — txid, block hash, or merkle node — as its 32 raw digest
bytes (SHA-256 emission order, i.e. wire order; the display hex is reversed). -/
abbrev Hash256 := { bytes : List UInt8 // bytes.length = 32 }

/-- The 32 raw digest bytes of a hash. -/
@[reducible] def Hash256.bytes (h : Hash256) : List UInt8 := h.1

/-- Build a hash from 32 raw bytes, when the length is right. -/
def Hash256.ofBytes? (bs : List UInt8) : Option Hash256 :=
  if h : bs.length = 32 then some ⟨bs, h⟩ else none

/-- Decode a hash: take 32 raw bytes off the front. -/
def decodeHash256 (bs : List UInt8) : Option (Hash256 × List UInt8) :=
  if h : 32 ≤ bs.length then
    some (⟨bs.take 32, by rw [List.length_take]; omega⟩, bs.drop 32)
  else none

/-- A hash serializes as its 32 raw bytes, in wire order — no little-endian
reinterpretation, because the stored bytes already are the wire bytes. -/
instance instCodecHash256 : Codec Hash256 where
  encode h := h.1
  decode := decodeHash256
  decode_encode h rest := by
    have hlen : 32 ≤ (h.1 ++ rest).length := by rw [List.length_append, h.2]; omega
    simp only [decodeHash256, dif_pos hlen, List.take_left' h.2, List.drop_left' h.2]
  decode_canonical bs h rest hdec := by
    simp only [decodeHash256] at hdec
    split at hdec
    · next hlen =>
      rw [Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨hh, hr⟩ := hdec
      have hval : bs.take 32 = h.1 := congrArg Subtype.val hh
      rw [← hr, ← hval, List.take_append_drop]
    · exact absurd hdec (by simp)

/-- A hash is exactly 32 bytes. -/
@[simp] theorem Hash256.length_val (h : Hash256) : h.1.length = 32 := h.2

/-- A hash encodes to exactly its 32 bytes. -/
theorem Hash256.encode_length (h : Hash256) : (Codec.encode h).length = 32 := h.2

/-- A natural number as a 256-bit hash, low byte first — distinct numbers give
distinct hashes, which is all the synthetic test vectors need from it. -/
instance (n : Nat) : OfNat Hash256 n :=
  ⟨⟨encodeBitVecLE 32 (BitVec.ofNat (8 * 32) n), encodeBitVecLE_length 32 _⟩⟩

end BtcVerified
