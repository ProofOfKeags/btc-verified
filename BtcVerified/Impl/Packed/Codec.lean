import BtcVerified.Serialize.Codec
import BtcVerified.Ext.ByteSlice
/-!
  # The packed codec discipline

  `Codec` fixes serialization correctness over `List UInt8`, the
  specification byte type. Running the spec decoder over real chain data
  pays for that structure: a cons cell per byte, re-allocated at every
  composition layer. `PackedCodec` is the executable counterpart (issue
  #52): an encoder that appends into a `ByteArray` and a decoder that
  consumes a `ByteSlice`, one instance per spec instance.

  A packed codec proves no serialization laws of its own. Its two fields are
  agreement laws — through the byte abstraction, the packed encoder and
  decoder compute exactly what the spec codec computes, on every input. The
  spec's round-trip and canonicality then transport to the packed forms with
  no further proof, and any run of the packed codec is a run of the verified
  one.

  The construction mirrors the spec layer combinator for combinator —
  product composition, `ofEquiv` transport, and one little-endian
  fixed-width primitive — so every structure that gets its spec codec by
  composition gets its packed codec, and its agreement, the same way.

  Checked claims:

  * `instPackedCodecProd`: packed sequential composition agrees whenever the
    component codecs agree.
  * `PackedCodec.ofEquiv`: transport along a bijection preserves agreement,
    in step with `Codec.ofEquiv`.
  * `abstractParse_readBitVecLE` / `toList_pushBitVecLE`: the packed
    little-endian fixed-width forms agree with the spec construction, giving
    the fixed-width integers' packed codecs by transport.
  * `PackedCodec.toList_encode` / `PackedCodec.abstractParse_decode`: over whole
    byte arrays, a packed codec produces, accepts, and leaves exactly what
    the spec codec does.
-/

namespace BtcVerified.Impl.Packed

open BtcVerified.Serialize

/-- The refinement morphism from packed parse results to spec parse
results: keep the value, abstract the remainder slice to its bytes. It is
nothing but the functor stack — `Option.map` of `Prod.map` of the slice
abstraction — and its lemmas below are instances of the standard
`Option.map`/`bind` laws; the name exists because every agreement law in
the packed layer is stated through it. -/
def abstractParse {α : Type} : Option (α × ByteSlice) → Option (α × List UInt8) :=
  Option.map (Prod.map id ByteSlice.toList)

/-- A failed packed parse reads as a failed spec parse. -/
@[simp] theorem abstractParse_none {α : Type} : abstractParse (α := α) none = none := rfl

/-- A successful packed parse reads as its value with the abstracted tail. -/
@[simp] theorem abstractParse_some {α : Type} (a : α) (s : ByteSlice) :
    abstractParse (some (a, s)) = some (a, s.toList) := rfl

/-- Threading one parse step through the abstraction: whenever the packed
continuation agrees with the spec continuation on the abstracted state, the
whole bind agrees. This is `Option.map_bind` and `Option.bind_map` applied
to the refinement morphism; composite decoder agreement proofs are chains
of it, one link per parsed field. -/
theorem abstractParse_bind {α β : Type} (p : Option (α × ByteSlice))
    {f : α × ByteSlice → Option (β × ByteSlice)}
    {g : α × List UInt8 → Option (β × List UInt8)}
    (h : ∀ a s, abstractParse (f (a, s)) = g (a, s.toList)) :
    abstractParse (p.bind f) = (abstractParse p).bind g := by
  unfold abstractParse
  rw [Option.map_bind, Option.bind_map]
  exact congrArg _ (funext fun q => h q.1 q.2)

/-- Threading a value-level step — a smart constructor, a guard — through
the abstraction: no bytes move, so the bind agrees whenever the
continuations agree pointwise. An instance of `Option.map_bind`. -/
theorem abstractParse_bindValue {α β : Type} (p : Option α)
    {f : α → Option (β × ByteSlice)} {g : α → Option (β × List UInt8)}
    (h : ∀ a, abstractParse (f a) = g a) :
    abstractParse (p.bind f) = p.bind g := by
  unfold abstractParse
  rw [Option.map_bind]
  exact congrArg _ (funext h)

/-- Reading one byte through the abstraction is the spec's single-byte
decoder — the primitive link every fixed-width chain starts from. -/
theorem abstractParse_uncons (s : ByteSlice) :
    abstractParse s.uncons = decodeByte s.toList := by
  cases hu : s.uncons with
  | none =>
    rw [abstractParse_none, ByteSlice.toList_of_uncons_none hu]
    rfl
  | some p =>
    obtain ⟨b, t⟩ := p
    rw [abstractParse_some, ByteSlice.toList_of_uncons_some hu]
    rfl

/-- The executable counterpart of a `Codec`: an encoder appending into a
`ByteArray` and a decoder consuming a `ByteSlice`, each agreeing with the
spec codec through the byte abstraction. The agreement laws make every run
of the packed codec a run of the verified spec codec, so round-trip and
canonicality transport with no further proof. -/
class PackedCodec (α : Type) [Codec α] where
  /-- Append a value's encoding onto an output buffer. -/
  encodeInto : α → ByteArray → ByteArray
  /-- Parse a value off the front of a slice, returning it and the rest. -/
  decodeSlice : ByteSlice → Option (α × ByteSlice)
  /-- Appending the packed encoding appends exactly the spec encoding. -/
  toList_encodeInto : ∀ (a : α) (acc : ByteArray),
    (encodeInto a acc).toList = acc.toList ++ Codec.encode a
  /-- The packed parse, read through the abstraction, is the spec parse. -/
  abstractParse_decodeSlice : ∀ s : ByteSlice,
    abstractParse (decodeSlice s) = Codec.decode (α := α) s.toList

namespace PackedCodec

/-- Serialize a value to a fresh `ByteArray`. -/
def encode {α : Type} [Codec α] [PackedCodec α] (a : α) : ByteArray :=
  encodeInto a ByteArray.empty

/-- Parse a value off the front of a byte array, returning it and the
unconsumed remainder as a slice into the same array. -/
def decode {α : Type} [Codec α] [PackedCodec α] (bytes : ByteArray) :
    Option (α × ByteSlice) :=
  decodeSlice (ByteSlice.ofByteArray bytes)

/-- The packed encoding of a value is byte-for-byte its spec encoding. -/
theorem toList_encode {α : Type} [Codec α] [PackedCodec α] (a : α) :
    (encode (α := α) a).toList = Codec.encode a := by
  rw [encode, toList_encodeInto, ByteArray.toList_empty, List.nil_append]

/-- Parsing a byte array with the packed decoder, read through the
abstraction, is the spec parse of the array's bytes. -/
theorem abstractParse_decode {α : Type} [Codec α] [PackedCodec α] (bytes : ByteArray) :
    abstractParse (decode (α := α) bytes) = Codec.decode (α := α) bytes.toList := by
  rw [decode, abstractParse_decodeSlice, ByteSlice.toList_ofByteArray]

/-- Agreement on every spec input: packing any byte list into an array and
parsing it packed is the spec parse of the list. -/
theorem abstractParse_decode_toByteArray {α : Type} [Codec α] [PackedCodec α]
    (bs : List UInt8) :
    abstractParse (decode (α := α) bs.toByteArray) = Codec.decode (α := α) bs := by
  rw [abstractParse_decode, List.toList_toByteArray]

end PackedCodec

/-! ## Sequential composition -/

/-- Packed sequential composition: encode the two components in order into
the buffer, decode them in order threading the slice. Agreement is inherited
from the component codecs, mirroring `instCodecProd`. -/
instance instPackedCodecProd {α β : Type} [Codec α] [Codec β]
    [PackedCodec α] [PackedCodec β] : PackedCodec (α × β) where
  encodeInto p acc := PackedCodec.encodeInto p.2 (PackedCodec.encodeInto p.1 acc)
  decodeSlice s := do
    let (a, s1) ← PackedCodec.decodeSlice s
    let (b, s2) ← PackedCodec.decodeSlice s1
    return ((a, b), s2)
  toList_encodeInto p acc := by
    rw [PackedCodec.toList_encodeInto, PackedCodec.toList_encodeInto]
    change _ = acc.toList ++ (Codec.encode p.1 ++ Codec.encode p.2)
    rw [List.append_assoc]
  abstractParse_decodeSlice s := by
    change _ = decodeProd s.toList
    unfold decodeProd
    rw [← PackedCodec.abstractParse_decodeSlice (α := α) s]
    refine abstractParse_bind _ fun a s1 => ?_
    dsimp only
    rw [← PackedCodec.abstractParse_decodeSlice (α := β) s1]
    exact abstractParse_bind _ fun b s2 => rfl

/-! ## Transport along a bijection -/

/-- Transport a packed codec along a bijection, in step with
`Codec.ofEquiv`: the packed `α` codec encodes and decodes through `e`, and
agreement with `Codec.ofEquiv e cb` is inherited from the `β` agreement. -/
@[reducible] def PackedCodec.ofEquiv {α β : Type} (e : α ≃ β) (cb : Codec β)
    (pb : @PackedCodec β cb) : @PackedCodec α (Codec.ofEquiv e cb) :=
  letI := cb
  letI := pb
  letI : Codec α := Codec.ofEquiv e cb
  { encodeInto := fun a acc => PackedCodec.encodeInto (e a) acc
    decodeSlice := fun s => (PackedCodec.decodeSlice s).map fun p => (e.symm p.1, p.2)
    toList_encodeInto := fun a acc => PackedCodec.toList_encodeInto (e a) acc
    abstractParse_decodeSlice := fun s => by
      change abstractParse ((PackedCodec.decodeSlice (α := β) s).map fun p => (e.symm p.1, p.2))
        = (cb.decode s.toList).map fun p => (e.symm p.1, p.2)
      rw [show cb.decode s.toList = Codec.decode (α := β) s.toList from rfl,
        ← PackedCodec.abstractParse_decodeSlice (α := β) s]
      cases PackedCodec.decodeSlice (α := β) s with
      | none => rfl
      | some p => rfl }

/-! ## The little-endian fixed-width primitive -/

/-- Read `n` little-endian bytes off a slice into a `BitVec (8 * n)`: the
packed mirror of `decodeBitVecLE`. -/
def readBitVecLE : (n : Nat) → ByteSlice → Option (BitVec (8 * n) × ByteSlice)
  | 0, s => some (0#0, s)
  | n + 1, s => do
    let (b, s1) ← s.uncons
    let (hi, rest) ← readBitVecLE n s1
    return (hi ++ b.toBitVec, rest)

/-- Append the `n` little-endian bytes of a `BitVec (8 * n)` to the buffer:
the packed mirror of `encodeBitVecLE`. -/
def pushBitVecLE : (n : Nat) → BitVec (8 * n) → ByteArray → ByteArray
  | 0, _, acc => acc
  | n + 1, v, acc =>
    pushBitVecLE n ((v >>> 8).setWidth (8 * n)) (acc.push (UInt8.ofBitVec (v.setWidth 8)))

/-- The packed little-endian read, through the abstraction, is the spec's
little-endian decode. -/
theorem abstractParse_readBitVecLE :
    ∀ (n : Nat) (s : ByteSlice),
      abstractParse (readBitVecLE n s) = decodeBitVecLE n s.toList := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp only [readBitVecLE, decodeBitVecLE]
    rw [← abstractParse_uncons s]
    refine abstractParse_bind _ fun b s1 => ?_
    dsimp only
    rw [← ih s1]
    exact abstractParse_bind _ fun hi rest => rfl

/-- The packed little-endian append appends exactly the spec's little-endian
encoding. -/
theorem toList_pushBitVecLE :
    ∀ (n : Nat) (v : BitVec (8 * n)) (acc : ByteArray),
      (pushBitVecLE n v acc).toList = acc.toList ++ encodeBitVecLE n v := by
  intro n
  induction n with
  | zero => intro v acc; simp [pushBitVecLE, encodeBitVecLE]
  | succ n ih =>
    intro v acc
    simp [pushBitVecLE, encodeBitVecLE, ih]

/-- The packed little-endian codec for `BitVec (8 * n)`, agreeing with
`bitVecCodecLE n` — the primitive every packed fixed-width codec is built
from. -/
@[reducible] def packedBitVecLE (n : Nat) :
    @PackedCodec (BitVec (8 * n)) (bitVecCodecLE n) :=
  letI := bitVecCodecLE n
  { encodeInto := pushBitVecLE n
    decodeSlice := readBitVecLE n
    toList_encodeInto := toList_pushBitVecLE n
    abstractParse_decodeSlice := abstractParse_readBitVecLE n }

/-- The packed codecs of the fixed-width integer fields: the packed
little-endian primitive transported along the same bijections as the spec
instances, so each agrees with its spec codec by construction. -/
instance instPackedCodecUInt8 : PackedCodec UInt8 :=
  PackedCodec.ofEquiv ⟨UInt8.toBitVec, UInt8.ofBitVec, fun _ => rfl, fun _ => rfl⟩
    (bitVecCodecLE 1) (packedBitVecLE 1)

instance instPackedCodecUInt16 : PackedCodec UInt16 :=
  PackedCodec.ofEquiv ⟨UInt16.toBitVec, UInt16.ofBitVec, fun _ => rfl, fun _ => rfl⟩
    (bitVecCodecLE 2) (packedBitVecLE 2)

instance instPackedCodecUInt32 : PackedCodec UInt32 :=
  PackedCodec.ofEquiv ⟨UInt32.toBitVec, UInt32.ofBitVec, fun _ => rfl, fun _ => rfl⟩
    (bitVecCodecLE 4) (packedBitVecLE 4)

instance instPackedCodecUInt64 : PackedCodec UInt64 :=
  PackedCodec.ofEquiv ⟨UInt64.toBitVec, UInt64.ofBitVec, fun _ => rfl, fun _ => rfl⟩
    (bitVecCodecLE 8) (packedBitVecLE 8)

/-- The packed codec for numeric 256-bit fields, agreeing with
`instCodecBitVec256`. -/
instance instPackedCodecBitVec256 : PackedCodec (BitVec 256) := packedBitVecLE 32

end BtcVerified.Impl.Packed
