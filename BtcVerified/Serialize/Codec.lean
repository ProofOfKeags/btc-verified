import BtcVerified.CompactSize
/-!
  # The serialization codec discipline

  Bitcoin structures are serialized to byte strings and parsed back. Across the
  many substructures of a block, the same two correctness obligations recur:

  * **round-trip** — encoding a value and then decoding returns it, leaving any
    trailing bytes untouched as the unconsumed tail;
  * **canonicality** — every accepted parse consumed exactly the canonical
    encoding of the value it returned, so no non-canonical byte string is
    accepted.

  This module captures that pair as a single typeclass, `Codec`, whose law
  fields *are* those two obligations. Read as an adjunction, `encode` is a
  section into the byte strings and `decode` a partial retraction: round-trip is
  the retraction triangle, and canonicality makes `encode` an isomorphism onto
  the decoder's accepted sub-language, modulo trailing bytes.

  The payoff is composition. From the two laws we derive, once and for all,
  that `encode` is injective, and — the load-bearing combinator — that two
  codecs run in sequence again satisfy both laws (`Codec (α × β)`). Composite
  structures then inherit their serialization correctness from their fields
  rather than re-deriving it by hand.

  The byte type is `List UInt8`: a structural tail is exactly what the decoder
  recurses over, and it matches the existing `CompactSize` leaf. Efficiency on
  real chain data is a later concern, reached by transporting these proofs
  across the `List UInt8 ≃ ByteArray` isomorphism, not by changing this spec.

  Checked claims:

  * `encode_injective`: distinct values never share an encoding.
  * the `Codec (α × β)` instance: sequential composition preserves both laws.
  * fixed-width little-endian `Codec` instances for `UInt16`/`UInt32`/`UInt64`.
  * `compactSizeCodec`: the existing `CompactSize` encoder/decoder satisfies the
    `Codec` laws verbatim — a worked instance validating the abstraction.
-/

namespace BtcVerified.Serialize

/--
  A serialization codec for `α`: an encoder, a prefix-consuming decoder, and the
  round-trip and canonicality laws relating them.

  `decode` returns the decoded value together with the unconsumed tail, so
  codecs compose by threading the tail from one through the next.
-/
class Codec (α : Type) where
  /-- Serialize a value to bytes. -/
  encode : α → List UInt8
  /-- Parse a value off the front of a byte string, returning it and the tail. -/
  decode : List UInt8 → Option (α × List UInt8)
  /-- Round-trip: encoding then decoding returns the value and the trailing bytes. -/
  decode_encode : ∀ (a : α) (rest : List UInt8), decode (encode a ++ rest) = some (a, rest)
  /-- Canonicality: an accepted parse consumed exactly the canonical encoding. -/
  decode_canonical : ∀ (bs : List UInt8) (a : α) (rest : List UInt8),
    decode bs = some (a, rest) → bs = encode a ++ rest

/--
  Encoders are injective: two values with the same encoding are equal. This
  falls straight out of round-trip with an empty tail.
-/
theorem encode_injective {α : Type} [Codec α] {a b : α}
    (h : Codec.encode a = Codec.encode b) : a = b := by
  have ha := Codec.decode_encode a ([] : List UInt8)
  have hb := Codec.decode_encode b ([] : List UInt8)
  rw [List.append_nil] at ha hb
  rw [h, hb] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  exact ha.1.symm

/-! ## Sequential composition -/

/-- Decode an `α` then a `β` from the remaining bytes, threading the tail. -/
def decodeProd {α β : Type} [Codec α] [Codec β]
    (bs : List UInt8) : Option ((α × β) × List UInt8) :=
  match Codec.decode (α := α) bs with
  | none => none
  | some (a, rest) =>
    match Codec.decode (α := β) rest with
    | none => none
    | some (b, rest') => some ((a, b), rest')

theorem decodeProd_encode {α β : Type} [Codec α] [Codec β]
    (a : α) (b : β) (rest : List UInt8) :
    decodeProd ((Codec.encode a ++ Codec.encode b) ++ rest) = some ((a, b), rest) := by
  unfold decodeProd
  simp only [List.append_assoc, Codec.decode_encode]

theorem decodeProd_canonical {α β : Type} [Codec α] [Codec β]
    (bs : List UInt8) (a : α) (b : β) (rest : List UInt8) :
    decodeProd bs = some ((a, b), rest) →
    bs = (Codec.encode a ++ Codec.encode b) ++ rest := by
  intro h
  unfold decodeProd at h
  cases hd : Codec.decode (α := α) bs with
  | none => simp [hd] at h
  | some ar =>
    obtain ⟨a', r1⟩ := ar
    cases hd2 : Codec.decode (α := β) r1 with
    | none => simp [hd, hd2] at h
    | some br =>
      obtain ⟨b', r2⟩ := br
      simp only [hd, hd2, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨ha, hb⟩, hr⟩ := h
      have e1 := Codec.decode_canonical bs a' r1 hd
      have e2 := Codec.decode_canonical r1 b' r2 hd2
      subst ha; subst hb; subst hr
      rw [e1, e2, List.append_assoc]

/--
  Sequential composition of codecs. Encoding concatenates the field encodings;
  decoding parses the fields left to right, threading the tail. Both laws are
  inherited from the component codecs — this is what lets composite structures
  reuse their fields' serialization correctness.
-/
instance instCodecProd {α β : Type} [Codec α] [Codec β] : Codec (α × β) where
  encode p := Codec.encode p.1 ++ Codec.encode p.2
  decode := decodeProd
  decode_encode := fun (a, b) rest => decodeProd_encode a b rest
  decode_canonical := fun bs (a, b) rest h => decodeProd_canonical bs a b rest h

/-! ## Fixed-width little-endian integer codecs

  These are the natural full-width encodings used by Bitcoin for non-count
  fields (e.g. version, sequence, lock time as `UInt32`; output value as
  `UInt64`). They reuse the little-endian chunk machinery and round-trip lemmas
  from `CompactSize`. (Variable-length counts use CompactSize itself; see
  `compactSizeCodec`.)
-/

/-- Decode a 2-byte little-endian `UInt16`. -/
def decodeU16 (bs : List UInt8) : Option (UInt16 × List UInt8) :=
  match bs with
  | b0 :: b1 :: rest => some (CompactSize.decodeU16LE b0 b1, rest)
  | _ => none

instance instCodecUInt16 : Codec UInt16 where
  encode := CompactSize.encodeU16LE
  decode := decodeU16
  decode_encode w rest := by
    simp only [CompactSize.encodeU16LE, List.cons_append, List.nil_append, decodeU16,
      CompactSize.decode_encode_u16_le]
  decode_canonical bs w rest h := by
    match bs with
    | [] => simp [decodeU16] at h
    | [_] => simp [decodeU16] at h
    | b0 :: b1 :: r =>
      simp only [decodeU16, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hw, hr⟩ := h
      subst hw; subst hr
      simp only [CompactSize.encode_decode_u16_le, List.cons_append, List.nil_append]

/-- Decode a 4-byte little-endian `UInt32`. -/
def decodeU32 (bs : List UInt8) : Option (UInt32 × List UInt8) :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest =>
    some (CompactSize.decodeU32LE (CompactSize.decodeU16LE b0 b1) (CompactSize.decodeU16LE b2 b3),
      rest)
  | _ => none

instance instCodecUInt32 : Codec UInt32 where
  encode := CompactSize.encodeU32LE
  decode := decodeU32
  decode_encode w rest := by
    simp only [CompactSize.encodeU32LE, CompactSize.encodeU16LE, List.cons_append,
      List.nil_append, decodeU32, CompactSize.decode_encode_u16_le,
      CompactSize.decode_encode_u32_le]
  decode_canonical bs w rest h := by
    match bs with
    | [] => simp [decodeU32] at h
    | [_] => simp [decodeU32] at h
    | [_, _] => simp [decodeU32] at h
    | [_, _, _] => simp [decodeU32] at h
    | b0 :: b1 :: b2 :: b3 :: r =>
      simp only [decodeU32, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hw, hr⟩ := h
      subst hw; subst hr
      simp only [CompactSize.encode_decode_u32_le, CompactSize.encode_decode_u16_le,
        List.cons_append, List.nil_append]

/-- Decode an 8-byte little-endian `UInt64`. -/
def decodeU64 (bs : List UInt8) : Option (UInt64 × List UInt8) :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    some (CompactSize.decodeU64LE
      (CompactSize.decodeU32LE (CompactSize.decodeU16LE b0 b1) (CompactSize.decodeU16LE b2 b3))
      (CompactSize.decodeU32LE (CompactSize.decodeU16LE b4 b5) (CompactSize.decodeU16LE b6 b7)),
      rest)
  | _ => none

instance instCodecUInt64 : Codec UInt64 where
  encode := CompactSize.encodeU64LE
  decode := decodeU64
  decode_encode w rest := by
    simp only [CompactSize.encodeU64LE, CompactSize.encodeU32LE, CompactSize.encodeU16LE,
      List.cons_append, List.nil_append, decodeU64, CompactSize.decode_encode_u16_le,
      CompactSize.decode_encode_u32_le, CompactSize.decode_encode_u64_le]
  decode_canonical bs w rest h := by
    match bs with
    | [] => simp [decodeU64] at h
    | [_] => simp [decodeU64] at h
    | [_, _] => simp [decodeU64] at h
    | [_, _, _] => simp [decodeU64] at h
    | [_, _, _, _] => simp [decodeU64] at h
    | [_, _, _, _, _] => simp [decodeU64] at h
    | [_, _, _, _, _, _] => simp [decodeU64] at h
    | [_, _, _, _, _, _, _] => simp [decodeU64] at h
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r =>
      simp only [decodeU64, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hw, hr⟩ := h
      subst hw; subst hr
      simp only [CompactSize.encode_decode_u64_le, CompactSize.encode_decode_u32_le,
        CompactSize.encode_decode_u16_le, List.cons_append, List.nil_append]

/-! ## CompactSize as a codec

  A worked instance validating the abstraction: the existing `CompactSize`
  encoder/decoder discharges the `Codec` laws verbatim. This is a `def` rather
  than a registered `instance` because the canonical full-width `Codec UInt64`
  is the fixed 8-byte little-endian form above; CompactSize is the distinguished
  variable-length encoding used for counts.
-/

/-- The Bitcoin CompactSize variable-length encoding, packaged as a `Codec`. -/
abbrev compactSizeCodec : Codec UInt64 where
  encode := CompactSize.encode
  decode := CompactSize.decode
  decode_encode := CompactSize.decode_encode
  decode_canonical := CompactSize.decode_canonical

end BtcVerified.Serialize
