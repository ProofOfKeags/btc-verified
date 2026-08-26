import BtcVerified.Transaction.Tx
import BtcVerified.Impl.Packed.TxBody
/-!
  # The packed transaction codec

  The packed counterpart of the transaction codec (issue #52). The spec
  codec is hand-written — the BIP144 marker/flag dispatch and the witness
  regrouping have no product shape — so the packed forms are hand-written
  mirrors of the same structure: the same three branches, the same shared
  value-level smart constructors (`Tx.legacy?`, `zipInputs`), with only the
  byte threading replaced by slices and buffer appends. Each mirror carries
  its agreement with the spec form, so the spec's round-trip and
  canonicality — including the branch dispatch — apply to every packed run.

  Checked claims:

  * `mapToList_readSegwit` / `mapToList_readLegacy` / `mapToList_readEmpty`:
    each branch decoder agrees with its spec branch.
  * `mapToList_readTx` / `toList_pushTx`: the packed transaction codec
    agrees with `decodeTx`/`encodeTx`, packaged as `instPackedCodecTx`.
-/

namespace BtcVerified.Impl.Packed

open BtcVerified.Serialize BtcVerified

/-! ## Encoding -/

/-- Append the SegWit body (everything after version, marker, and flag):
inputs, outputs, witnesses, lock time — the packed mirror of
`encodeSegwitBody`. -/
def pushSegwitBody (ins : CountedList SegwitInput) (outs : CountedList TxOut)
    (lockTime : UInt32) (acc : ByteArray) : ByteArray :=
  PackedCodec.encodeInto lockTime
    (pushElems (segwitWitnesses ins)
      (PackedCodec.encodeInto outs
        (PackedCodec.encodeInto (segwitInputs ins) acc)))

/-- The packed SegWit-body append appends exactly the spec encoding. -/
theorem toList_pushSegwitBody (ins : CountedList SegwitInput)
    (outs : CountedList TxOut) (lockTime : UInt32) (acc : ByteArray) :
    (pushSegwitBody ins outs lockTime acc).toList
      = acc.toList ++ encodeSegwitBody ins outs lockTime := by
  rw [pushSegwitBody, PackedCodec.toList_encodeInto, toList_pushElems,
    PackedCodec.toList_encodeInto, PackedCodec.toList_encodeInto, encodeSegwitBody]
  simp [List.append_assoc]

/-- Serialize a transaction into the buffer: the packed mirror of
`encodeTx`, with the same three branches. -/
def pushTx : Tx → ByteArray → ByteArray
  | .legacy body _, acc => PackedCodec.encodeInto body acc
  | .empty version lockTime, acc =>
    PackedCodec.encodeInto lockTime
      (((PackedCodec.encodeInto version acc).push 0x00).push 0x00)
  | .segwit version ins outs lockTime _, acc =>
    pushSegwitBody ins outs lockTime
      (((PackedCodec.encodeInto version acc).push 0x00).push 0x01)

/-- The packed transaction append appends exactly the spec encoding, in
whichever branch the value's own form dictates. -/
theorem toList_pushTx (tx : Tx) (acc : ByteArray) :
    (pushTx tx acc).toList = acc.toList ++ encodeTx tx := by
  cases tx with
  | legacy body hne =>
    change (PackedCodec.encodeInto body acc).toList = _
    rw [PackedCodec.toList_encodeInto, encodeTx]
  | empty version lockTime =>
    change (PackedCodec.encodeInto lockTime
      (((PackedCodec.encodeInto version acc).push 0x00).push 0x00)).toList = _
    rw [PackedCodec.toList_encodeInto, ByteArray.toList_push, ByteArray.toList_push,
      PackedCodec.toList_encodeInto, encodeTx]
    simp
  | segwit version ins outs lockTime hWitness =>
    change (pushSegwitBody ins outs lockTime
      (((PackedCodec.encodeInto version acc).push 0x00).push 0x01)).toList = _
    rw [toList_pushSegwitBody, ByteArray.toList_push, ByteArray.toList_push,
      PackedCodec.toList_encodeInto, encodeTx]
    simp

/-! ## Decoding -/

/-- Decode the SegWit body (everything after version, marker, and flag),
rebundling inputs and witnesses through the same `zipInputs` as the spec:
the packed mirror of `decodeSegwit`. -/
def readSegwit (version : UInt32) (s : ByteSlice) : Option (Tx × ByteSlice) := do
  let (txins, s1) ← PackedCodec.decodeSlice (α := CountedList TxIn) s
  let (outs, s2) ← PackedCodec.decodeSlice (α := CountedList TxOut) s1
  let (wits, s3) ← readElems (α := WitnessStack) txins.val.length s2
  let (lockTime, s4) ← PackedCodec.decodeSlice (α := UInt32) s3
  let ins := zipInputs txins wits
  if hWitness : ∃ input, input ∈ ins.val ∧ input.witness.NonEmpty then
    return (.segwit version ins outs lockTime hWitness, s4)
  else
    none

/-- Decode a legacy body after the version, attaching the non-empty-inputs
proof through the same `Tx.legacy?` as the spec: the packed mirror of
`decodeLegacy`. -/
def readLegacy (version : UInt32) (s : ByteSlice) : Option (Tx × ByteSlice) := do
  let (inputs, s1) ← PackedCodec.decodeSlice (α := CountedList TxIn) s
  let (outputs, s2) ← PackedCodec.decodeSlice (α := CountedList TxOut) s1
  let (lockTime, s3) ← PackedCodec.decodeSlice (α := UInt32) s2
  let tx ← Tx.legacy? ⟨version, inputs, outputs, lockTime⟩
  return (tx, s3)

/-- Decode Core's degenerate no-witness path after marker and zero flag:
the packed mirror of `decodeEmpty`. -/
def readEmpty (version : UInt32) (s : ByteSlice) : Option (Tx × ByteSlice) := do
  let (lockTime, rest) ← PackedCodec.decodeSlice (α := UInt32) s
  return (.empty version lockTime, rest)

/-- Decode a transaction: read the version, then dispatch on the marker and
flag bytes — the packed mirror of `decodeTx`'s match on the byte list. -/
def readTx (s : ByteSlice) : Option (Tx × ByteSlice) := do
  let (version, s1) ← PackedCodec.decodeSlice (α := UInt32) s
  match s1.uncons with
  | none => readLegacy version s1
  | some (b1, s2) =>
    if b1 = 0x00 then
      match s2.uncons with
      | none => none
      | some (b2, s3) =>
        if b2 = 0x01 then readSegwit version s3
        else if b2 = 0x00 then readEmpty version s3
        else none
    else
      readLegacy version s1

/-! ## Agreement -/

/-- The packed SegWit-body read, through the abstraction, is the spec's. -/
theorem mapToList_readSegwit (version : UInt32) (s : ByteSlice) :
    mapToList (readSegwit version s) = decodeSegwit version s.toList := by
  cases hi : PackedCodec.decodeSlice (α := CountedList TxIn) s with
  | none =>
    have hi' := PackedCodec.mapToList_decodeSlice (α := CountedList TxIn) s
    rw [hi, mapToList_none] at hi'
    simp [readSegwit, decodeSegwit, hi, ← hi']
  | some p =>
    obtain ⟨txins, s1⟩ := p
    have hi' := PackedCodec.mapToList_decodeSlice (α := CountedList TxIn) s
    rw [hi, mapToList_some] at hi'
    cases ho : PackedCodec.decodeSlice (α := CountedList TxOut) s1 with
    | none =>
      have ho' := PackedCodec.mapToList_decodeSlice (α := CountedList TxOut) s1
      rw [ho, mapToList_none] at ho'
      simp [readSegwit, decodeSegwit, hi, ho, ← hi', ← ho']
    | some q =>
      obtain ⟨outs, s2⟩ := q
      have ho' := PackedCodec.mapToList_decodeSlice (α := CountedList TxOut) s1
      rw [ho, mapToList_some] at ho'
      cases hw : readElems (α := WitnessStack) txins.val.length s2 with
      | none =>
        have hw' := mapToList_readElems (α := WitnessStack) txins.val.length s2
        rw [hw, mapToList_none] at hw'
        simp [readSegwit, decodeSegwit, hi, ho, hw, ← hi', ← ho', ← hw']
      | some r =>
        obtain ⟨wits, s3⟩ := r
        have hw' := mapToList_readElems (α := WitnessStack) txins.val.length s2
        rw [hw, mapToList_some] at hw'
        cases hl : PackedCodec.decodeSlice (α := UInt32) s3 with
        | none =>
          have hl' := PackedCodec.mapToList_decodeSlice (α := UInt32) s3
          rw [hl, mapToList_none] at hl'
          simp [readSegwit, decodeSegwit, hi, ho, hw, hl, ← hi', ← ho', ← hw', ← hl']
        | some t =>
          obtain ⟨lockTime, s4⟩ := t
          have hl' := PackedCodec.mapToList_decodeSlice (α := UInt32) s3
          rw [hl, mapToList_some] at hl'
          by_cases hWitness : ∃ input,
              input ∈ (zipInputs txins wits).val ∧ input.witness.NonEmpty
          · simp [readSegwit, decodeSegwit, hi, ho, hw, hl,
              ← hi', ← ho', ← hw', ← hl', hWitness]
          · simp [readSegwit, decodeSegwit, hi, ho, hw, hl,
              ← hi', ← ho', ← hw', ← hl', hWitness]

/-- The packed legacy read, through the abstraction, is the spec's. -/
theorem mapToList_readLegacy (version : UInt32) (s : ByteSlice) :
    mapToList (readLegacy version s) = decodeLegacy version s.toList := by
  cases hi : PackedCodec.decodeSlice (α := CountedList TxIn) s with
  | none =>
    have hi' := PackedCodec.mapToList_decodeSlice (α := CountedList TxIn) s
    rw [hi, mapToList_none] at hi'
    simp [readLegacy, decodeLegacy, hi, ← hi']
  | some p =>
    obtain ⟨inputs, s1⟩ := p
    have hi' := PackedCodec.mapToList_decodeSlice (α := CountedList TxIn) s
    rw [hi, mapToList_some] at hi'
    cases ho : PackedCodec.decodeSlice (α := CountedList TxOut) s1 with
    | none =>
      have ho' := PackedCodec.mapToList_decodeSlice (α := CountedList TxOut) s1
      rw [ho, mapToList_none] at ho'
      simp [readLegacy, decodeLegacy, hi, ho, ← hi', ← ho']
    | some q =>
      obtain ⟨outputs, s2⟩ := q
      have ho' := PackedCodec.mapToList_decodeSlice (α := CountedList TxOut) s1
      rw [ho, mapToList_some] at ho'
      cases hl : PackedCodec.decodeSlice (α := UInt32) s2 with
      | none =>
        have hl' := PackedCodec.mapToList_decodeSlice (α := UInt32) s2
        rw [hl, mapToList_none] at hl'
        simp [readLegacy, decodeLegacy, hi, ho, hl, ← hi', ← ho', ← hl']
      | some t =>
        obtain ⟨lockTime, s3⟩ := t
        have hl' := PackedCodec.mapToList_decodeSlice (α := UInt32) s2
        rw [hl, mapToList_some] at hl'
        cases hleg : Tx.legacy? ⟨version, inputs, outputs, lockTime⟩ with
        | none =>
          simp [readLegacy, decodeLegacy, hi, ho, hl, hleg, ← hi', ← ho', ← hl']
        | some tx =>
          simp [readLegacy, decodeLegacy, hi, ho, hl, hleg, ← hi', ← ho', ← hl']

/-- The packed empty-path read, through the abstraction, is the spec's. -/
theorem mapToList_readEmpty (version : UInt32) (s : ByteSlice) :
    mapToList (readEmpty version s) = decodeEmpty version s.toList := by
  cases hl : PackedCodec.decodeSlice (α := UInt32) s with
  | none =>
    have hl' := PackedCodec.mapToList_decodeSlice (α := UInt32) s
    rw [hl, mapToList_none] at hl'
    simp [readEmpty, decodeEmpty, hl, ← hl']
  | some t =>
    obtain ⟨lockTime, rest⟩ := t
    have hl' := PackedCodec.mapToList_decodeSlice (α := UInt32) s
    rw [hl, mapToList_some] at hl'
    simp [readEmpty, decodeEmpty, hl, ← hl']

/-- The spec transaction dispatch restated as nested conditionals over the
head bytes, so it can be compared with the packed dispatch branch for
branch without literal-pattern matching. -/
private def specDispatch (version : UInt32) : List UInt8 → Option (Tx × List UInt8)
  | [] => decodeLegacy version []
  | b1 :: t1 =>
    if b1 = 0x00 then
      match t1 with
      | [] => none
      | b2 :: t2 =>
        if b2 = 0x01 then decodeSegwit version t2
        else if b2 = 0x00 then decodeEmpty version t2
        else none
    else decodeLegacy version (b1 :: t1)

/-- `decodeTx` is the version read followed by the head-byte dispatch. -/
private theorem decodeTx_eq_specDispatch (bs : List UInt8) :
    decodeTx bs
      = (Codec.decode (α := UInt32) bs).bind fun p => specDispatch p.1 p.2 := by
  rw [decodeTx]
  cases Codec.decode (α := UInt32) bs with
  | none => rfl
  | some p =>
    obtain ⟨version, rest1⟩ := p
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · rfl
    · rfl
    · rename_i tail h1 h2
      cases tail with
      | nil => simp [specDispatch]
      | cons b2 t2 =>
        have hb2a : ¬b2 = 0x01 := fun hb => h1 t2 (by rw [hb])
        have hb2b : ¬b2 = 0x00 := fun hb => h2 t2 (by rw [hb])
        simp [specDispatch, hb2a, hb2b]
    · rename_i h1 h2 h3
      cases rest1 with
      | nil => simp [specDispatch]
      | cons b1 t1 =>
        have hb1 : ¬b1 = 0x00 := fun hb => h3 t1 (by rw [hb])
        simp [specDispatch, hb1]

/-- The packed transaction read, through the abstraction, is the spec's:
the marker/flag dispatch on slice bytes takes exactly the branch the spec's
dispatch on list bytes takes. -/
theorem mapToList_readTx (s : ByteSlice) :
    mapToList (readTx s) = decodeTx s.toList := by
  rw [decodeTx_eq_specDispatch]
  cases hv : PackedCodec.decodeSlice (α := UInt32) s with
  | none =>
    have hv' := PackedCodec.mapToList_decodeSlice (α := UInt32) s
    rw [hv, mapToList_none] at hv'
    simp [readTx, hv, ← hv']
  | some p =>
    obtain ⟨version, s1⟩ := p
    have hv' := PackedCodec.mapToList_decodeSlice (α := UInt32) s
    rw [hv, mapToList_some] at hv'
    rw [readTx]
    simp only [Option.bind_eq_bind, hv, Option.bind_some, ← hv']
    cases hu1 : s1.uncons with
    | none =>
      have hs1 := ByteSlice.toList_of_uncons_none hu1
      simp [specDispatch, mapToList_readLegacy, hs1]
    | some p1 =>
      obtain ⟨b1, s2⟩ := p1
      have hs1 := ByteSlice.toList_of_uncons_some hu1
      by_cases hb1 : b1 = 0x00
      · subst hb1
        cases hu2 : s2.uncons with
        | none =>
          have hs2 := ByteSlice.toList_of_uncons_none hu2
          simp [specDispatch, hu2, hs1, hs2]
        | some p2 =>
          obtain ⟨b2, s3⟩ := p2
          have hs2 := ByteSlice.toList_of_uncons_some hu2
          by_cases hb2 : b2 = 0x01
          · subst hb2
            simp [specDispatch, hu2, hs1, hs2, mapToList_readSegwit]
          · by_cases hb2' : b2 = 0x00
            · subst hb2'
              simp [specDispatch, hu2, hs1, hs2, hb2, mapToList_readEmpty]
            · simp [specDispatch, hu2, hs1, hs2, hb2, hb2']
      · simp [specDispatch, hb1, hs1, mapToList_readLegacy]

/-- The packed transaction codec: the same three serialization forms,
dispatched the same way, agreeing with `instCodecTx`. -/
instance instPackedCodecTx : PackedCodec Tx where
  encodeInto := pushTx
  decodeSlice := readTx
  toList_encodeInto := toList_pushTx
  mapToList_decodeSlice := mapToList_readTx

end BtcVerified.Impl.Packed
