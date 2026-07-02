import Mathlib.Logic.Equiv.Basic
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
  * `decodeBitVecLE_encodeBitVecLE` / `decodeBitVecLE_canonical`: one little-endian
    construction serializes any `BitVec (8 * n)` as `n` bytes, and `Codec.ofEquiv`
    transports it to the fixed-width integers (`UInt8`/`UInt16`/`UInt32`/`UInt64`)
    and the 256-bit hash, so byte-level endianness is defined and proved once.
-/

namespace BtcVerified.Serialize

/-- A serialization codec for `α`: an encoder, a prefix-consuming decoder, and the
round-trip and canonicality laws relating them.

`decode` returns the decoded value together with the unconsumed tail, so
codecs compose by threading the tail from one through the next. -/
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

/-- Encoders are injective: two values with the same encoding are equal. This
falls straight out of round-trip with an empty tail. -/
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
    (bs : List UInt8) : Option ((α × β) × List UInt8) := do
  let (a, rest) ← Codec.decode (α := α) bs
  let (b, rest') ← Codec.decode (α := β) rest
  return ((a, b), rest')

/-- Decoding a pair from the concatenated encodings of its components returns
both values, leaving the trailing bytes as the unconsumed tail. -/
theorem decodeProd_encode {α β : Type} [Codec α] [Codec β]
    (a : α) (b : β) (rest : List UInt8) :
    decodeProd ((Codec.encode a ++ Codec.encode b) ++ rest) = some ((a, b), rest) := by
  unfold decodeProd
  simp only [List.append_assoc, Option.bind_eq_bind, Codec.decode_encode,
    Option.bind_some, Option.pure_def]

/-- If the pair decoder accepts `bs` as `(a, b)` with tail `rest`, then `bs` is
exactly the two component encodings in sequence followed by `rest`. -/
theorem decodeProd_canonical {α β : Type} [Codec α] [Codec β]
    (bs : List UInt8) (a : α) (b : β) (rest : List UInt8) :
    decodeProd bs = some ((a, b), rest) →
    bs = (Codec.encode a ++ Codec.encode b) ++ rest := by
  intro h
  unfold decodeProd at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨a', r1⟩, hd, ⟨b', r2⟩, hd2, ⟨ha, hb⟩, hr⟩ := h
  subst ha; subst hb; subst hr
  rw [Codec.decode_canonical bs a' r1 hd, Codec.decode_canonical r1 b' r2 hd2,
    List.append_assoc]

/-- Sequential composition of codecs. Encoding concatenates the field encodings;
decoding parses the fields left to right, threading the tail. Both laws are
inherited from the component codecs — this is what lets composite structures
reuse their fields' serialization correctness. -/
instance instCodecProd {α β : Type} [Codec α] [Codec β] : Codec (α × β) where
  encode p := Codec.encode p.1 ++ Codec.encode p.2
  decode := decodeProd
  decode_encode := fun (a, b) rest => decodeProd_encode a b rest
  decode_canonical := fun bs (a, b) rest h => decodeProd_canonical bs a b rest h

/-! ## Byte and fixed-width little-endian codecs

  The primitive serializable unit is a single byte. From it, one generic
  little-endian construction serializes any `BitVec (8 * n)` as `n` bytes, low
  byte first. Every fixed-width Bitcoin integer field — and the 256-bit hash
  type — is then that one construction transported along a bijection, so
  byte-level endianness lives in a single place.
-/

/-- Read a single byte off the front of the input. -/
def decodeByte : List UInt8 → Option (UInt8 × List UInt8)
  | [] => none
  | b :: bs => some (b, bs)

/-- Little-endian serialization of a `BitVec (8 * n)` as `n` bytes, low byte first. -/
def encodeBitVecLE : (n : Nat) → BitVec (8 * n) → List UInt8
  | 0, _ => []
  | n + 1, v => UInt8.ofBitVec (v.setWidth 8) :: encodeBitVecLE n ((v >>> 8).setWidth (8 * n))

/-- Decode `n` little-endian bytes into a `BitVec (8 * n)`. -/
def decodeBitVecLE : (n : Nat) → List UInt8 → Option (BitVec (8 * n) × List UInt8)
  | 0, bs => some (0#0, bs)
  | n + 1, bs => do
    let (b, bs') ← decodeByte bs
    let (hi, rest) ← decodeBitVecLE n bs'
    return (hi ++ b.toBitVec, rest)

/-- The low byte of `high ++ low` is `low`. -/
private theorem setWidth_append_low {n : Nat} (hi : BitVec (8 * n)) (lo : BitVec 8) :
    (hi ++ lo).setWidth 8 = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi8
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp [hi8]

/-- Shifting `high ++ low` past its low byte and truncating recovers `high`. -/
private theorem setWidth_ushiftRight_append {n : Nat} (hi : BitVec (8 * n)) (lo : BitVec 8) :
    ((hi ++ lo) >>> 8).setWidth (8 * n) = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hin
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  have h1 : ¬ (8 + i < 8) := by omega
  have h2 : 8 + i - 8 = i := by omega
  rw [if_neg h1, h2]
  simp [hin]

/-- A word equals its high `8 * n` bits appended to its low byte. -/
private theorem append_split {n : Nat} (v : BitVec (8 * (n + 1))) :
    ((v >>> 8).setWidth (8 * n)) ++ (v.setWidth 8) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hilt
  rw [BitVec.getLsbD_append]
  by_cases h8 : i < 8
  · rw [if_pos h8, BitVec.getLsbD_setWidth]; simp [h8]
  · rw [if_neg h8, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    have h1 : i - 8 < 8 * n := by omega
    have h2 : 8 + (i - 8) = i := by omega
    rw [h2]; simp [h1]

/-- Encoding a `BitVec (8 * n)` as `n` little-endian bytes and then decoding
returns the original value, leaving any trailing bytes as the unconsumed
tail. -/
theorem decodeBitVecLE_encodeBitVecLE :
    ∀ (n : Nat) (v : BitVec (8 * n)) (rest : List UInt8),
      decodeBitVecLE n (encodeBitVecLE n v ++ rest) = some (v, rest) := by
  intro n
  induction n with
  | zero =>
    intro v rest
    have hv : v = 0#0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; exact absurd hi (by omega)
    subst hv
    rfl
  | succ n ih =>
    intro v rest
    simp only [encodeBitVecLE, List.cons_append, decodeBitVecLE, decodeByte,
      Option.bind_eq_bind, Option.bind_some, ih, Option.pure_def]
    rw [append_split v]

/-- If the little-endian decoder accepts `bs` as the value `v` with tail `rest`,
then `bs` is exactly the `n`-byte encoding of `v` followed by `rest`. -/
theorem decodeBitVecLE_canonical :
    ∀ (n : Nat) (bs : List UInt8) (v : BitVec (8 * n)) (rest : List UInt8),
      decodeBitVecLE n bs = some (v, rest) → bs = encodeBitVecLE n v ++ rest := by
  intro n
  induction n with
  | zero =>
    intro bs v rest h
    simp only [decodeBitVecLE, Option.some.injEq, Prod.mk.injEq] at h
    simp only [encodeBitVecLE, List.nil_append, h.2]
  | succ n ih =>
    intro bs v rest h
    cases bs with
    | nil => simp [decodeBitVecLE, decodeByte] at h
    | cons b bs' =>
      simp only [decodeBitVecLE, decodeByte, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨hi, r⟩, hd, hv, hr'⟩ := h
      have ihbs := ih bs' hi r hd
      subst hr'; subst hv
      simp only [encodeBitVecLE, List.cons_append, setWidth_append_low,
        setWidth_ushiftRight_append, UInt8.ofBitVec_toBitVec, ihbs]

/-- The little-endian decoder succeeds on any input of at least `n` bytes,
consuming exactly `n` and leaving the rest as the tail. -/
theorem decodeBitVecLE_of_le_length :
    ∀ (n : Nat) (bs : List UInt8), n ≤ bs.length →
      ∃ v, decodeBitVecLE n bs = some (v, bs.drop n) := by
  intro n
  induction n with
  | zero => exact fun bs _ => ⟨0#0, rfl⟩
  | succ n ih =>
    intro bs h
    cases bs with
    | nil => simp at h
    | cons b bs' =>
      obtain ⟨v, hv⟩ := ih bs' (by simpa using h)
      exact ⟨v ++ b.toBitVec, by simp [decodeBitVecLE, decodeByte, hv]⟩

/-- A little-endian `BitVec (8 * n)` encoding is exactly `n` bytes long. -/
theorem encodeBitVecLE_length :
    ∀ (n : Nat) (v : BitVec (8 * n)), (encodeBitVecLE n v).length = n := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih => intro v; simp [encodeBitVecLE, List.length_cons, ih]

/-- The little-endian byte codec for `BitVec (8 * n)`: the primitive every
fixed-width codec is built from. -/
@[reducible] def bitVecCodecLE (n : Nat) : Codec (BitVec (8 * n)) where
  encode := encodeBitVecLE n
  decode := decodeBitVecLE n
  decode_encode := decodeBitVecLE_encodeBitVecLE n
  decode_canonical := decodeBitVecLE_canonical n

/-- Transport a codec along a bijection: a `Codec β` together with `α ≃ β` gives
a `Codec α`. Round-trip and canonicality transport because the equivalence is a
bijection. -/
@[reducible] def Codec.ofEquiv {α β : Type} (e : α ≃ β) (cb : Codec β) : Codec α where
  encode a := cb.encode (e a)
  decode bs := (cb.decode bs).map (fun p => (e.symm p.1, p.2))
  decode_encode a rest := by
    rw [cb.decode_encode (e a) rest]
    simp [Equiv.symm_apply_apply]
  decode_canonical bs a rest h := by
    cases hdec : cb.decode bs with
    | none => rw [hdec] at h; simp [Option.map] at h
    | some p =>
      obtain ⟨b, rest'⟩ := p
      rw [hdec] at h
      simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hb, hr⟩ := h
      subst hr
      have hb' : b = e a := (Equiv.symm_apply_eq e).mp hb
      subst hb'
      exact cb.decode_canonical bs (e a) rest' hdec

/-- The natural full-width little-endian byte encodings of Bitcoin's integer
fields, each the `BitVec (8 * n)` codec transported along the `UIntN ≃ BitVec`
bijection. (Variable-length counts use CompactSize instead; see
`compactSizeCodec`.) -/
instance instCodecUInt8 : Codec UInt8 :=
  Codec.ofEquiv ⟨UInt8.toBitVec, UInt8.ofBitVec, fun _ => rfl, fun _ => rfl⟩ (bitVecCodecLE 1)

instance instCodecUInt16 : Codec UInt16 :=
  Codec.ofEquiv ⟨UInt16.toBitVec, UInt16.ofBitVec, fun _ => rfl, fun _ => rfl⟩ (bitVecCodecLE 2)

instance instCodecUInt32 : Codec UInt32 :=
  Codec.ofEquiv ⟨UInt32.toBitVec, UInt32.ofBitVec, fun _ => rfl, fun _ => rfl⟩ (bitVecCodecLE 4)

instance instCodecUInt64 : Codec UInt64 :=
  Codec.ofEquiv ⟨UInt64.toBitVec, UInt64.ofBitVec, fun _ => rfl, fun _ => rfl⟩ (bitVecCodecLE 8)

/-- The 256-bit hash type is exactly 32 little-endian bytes. -/
instance instCodecBitVec256 : Codec (BitVec 256) := bitVecCodecLE 32

end BtcVerified.Serialize
