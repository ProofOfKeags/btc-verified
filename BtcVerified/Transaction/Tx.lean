import BtcVerified.Transaction.TxBody
import BtcVerified.Transaction.SegwitInput
import BtcVerified.Serialize.CompactSize
import BtcVerified.Ext.List
/-!
  # The transaction type and its codec

  A transaction is era-aware from the start: an inductive with a `legacy` and a
  `segwit` constructor over a shared, witness-free `TxBody`. SegWit is a soft
  fork — a restriction of the legacy ruleset — so the body is exactly what a txid
  commits to, exactly the legacy serialization, and exactly the witness-stripped
  form a SegWit transaction shows the pre-SegWit world; `Tx.body` recovers it
  from either form. A SegWit transaction bundles each input with the witness that
  unlocks it (`SegwitInput`), so the one-witness-per-input arity is structural
  rather than a side condition.

  ## Serialization

  A transaction serializes in one of two forms, and the decoder tells them apart
  from the bytes alone. After the 4-byte version:

  * the **legacy** form is its `TxBody` — input vector, output vector, lock time;
  * the **SegWit** (BIP144) form interposes the marker `0x00` and flag `0x01`,
    then serializes the inputs (scriptSigs only), the outputs, one witness stack
    per input (no separate count — the count *is* the number of inputs), and the
    lock time.

  Bitcoin transactions also require at least one input and at least one output.
  The marker `0x00` is the reserved "zero inputs" encoding, never a valid legacy
  transaction — which is what lets the decoder dispatch on it. Both transaction
  constructors carry the non-empty-output proof, and the legacy constructor also
  carries the non-empty-input proof.

  The witness region is the one place the wire format and the data model disagree
  on order: the model bundles each input with its witness, while the wire groups
  all inputs first and all witnesses last. The codec is where that regrouping
  happens — `decode` reads the inputs and witnesses separately and `zipInputs`
  rebundles them; `encode` unzips.

  Checked claims:

  * `decodeTx_encodeTx`: every transaction round-trips, tail preserved.
  * `decodeTx_canonical`: an accepted parse consumed exactly the canonical
    encoding — including taking the legacy/SegWit branch the value's own form
    dictates.

  Both are packaged as `instCodecTx : Codec Tx`.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- A Bitcoin transaction in one of its two serialization forms.

`legacy` is the pre-SegWit form: a witness-free `TxBody`. Its inputs are
non-empty because the SegWit serialization reserves a zero input count (the
`0x00` marker byte), so a legacy transaction can never encode zero inputs on the
wire.

`segwit` is the BIP144 form, where each input carries its own witness. The
arity rule — one witness stack per input — is structural here (it *is* a list of
`SegwitInput`). Both forms also carry Bitcoin's one-or-more-output invariant. -/
inductive Tx where
  /-- A legacy (pre-SegWit) transaction: a witness-free body with non-empty
  inputs and outputs. -/
  | legacy (body : TxBody) (inputsNonempty : body.inputs.val ≠ [])
      (outputsNonempty : body.outputs.val ≠ [])
  /-- A BIP144 SegWit transaction: each input bundled with its witness, and the
  output vector is non-empty as required for transactions. -/
  | segwit (version : UInt32) (inputs : CountedList SegwitInput)
      (outputs : CountedList TxOut) (lockTime : UInt32)
      (outputsNonempty : outputs.val ≠ [])
  deriving DecidableEq

/-- Whether a transaction is in SegWit (witnessed) serialization form. -/
def Tx.isSegWit : Tx → Bool
  | .legacy .. => false
  | .segwit .. => true

/-- The witness-free body of a transaction: its txid preimage and its legacy
interpretation. A legacy transaction *is* its body; a SegWit transaction's body
drops each input's witness. -/
def Tx.body : Tx → TxBody
  | .legacy body _ _ => body
  | .segwit version inputs outputs lockTime _ =>
    { version := version
      inputs := ⟨inputs.val.map SegwitInput.input, by
        rw [List.length_map]; exact inputs.property⟩
      outputs := outputs
      lockTime := lockTime }

/-! ## Bundling and unbundling SegWit inputs -/

/-- The underlying inputs of a SegWit transaction, witnesses dropped — the input
vector as it appears in the inputs region of the wire format. -/
def segwitInputs (ins : CountedList SegwitInput) : CountedList TxIn :=
  ⟨ins.val.map SegwitInput.input, by rw [List.length_map]; exact ins.property⟩

/-- The witnesses of a SegWit transaction in input order — the witness region of
the wire format. -/
def segwitWitnesses (ins : CountedList SegwitInput) : List WitnessStack :=
  ins.val.map SegwitInput.witness

/-- Rebundle a decoded input vector and witness list (read from their separate
wire regions) into SegWit inputs. -/
def zipInputs (txins : CountedList TxIn) (wits : List WitnessStack) :
    CountedList SegwitInput :=
  ⟨List.zipWith SegwitInput.mk txins.val wits, by
    rw [List.length_zipWith]
    exact lt_of_le_of_lt (Nat.min_le_left _ _) txins.property⟩

/-- Rebundling the unbundled inputs and witnesses recovers the SegWit inputs. -/
theorem zipInputs_segwit (ins : CountedList SegwitInput) :
    zipInputs (segwitInputs ins) (segwitWitnesses ins) = ins := by
  apply Subtype.ext
  simp only [zipInputs, segwitInputs, segwitWitnesses]
  exact List.zipWith_map_map_left_right (fun _ => rfl) ins.val

/-- The unbundled inputs of a rebundling are the inputs we started from. -/
theorem segwitInputs_zipInputs (txins : CountedList TxIn) (wits : List WitnessStack)
    (h : wits.length = txins.val.length) :
    segwitInputs (zipInputs txins wits) = txins := by
  apply Subtype.ext
  simp only [segwitInputs, zipInputs]
  exact List.map_zipWith_left (fun _ _ => rfl) txins.val wits h.symm

/-- The unbundled witnesses of a rebundling are the witnesses we started from. -/
theorem segwitWitnesses_zipInputs (txins : CountedList TxIn) (wits : List WitnessStack)
    (h : wits.length = txins.val.length) :
    segwitWitnesses (zipInputs txins wits) = wits := by
  simp only [segwitWitnesses, zipInputs]
  exact List.map_zipWith_right (fun _ _ => rfl) txins.val wits h.symm

/-- Unbundling a SegWit input list yields exactly as many inputs as witnesses. -/
theorem segwitInputs_length (ins : CountedList SegwitInput) :
    (segwitInputs ins).val.length = (segwitWitnesses ins).length := by
  simp only [segwitInputs, segwitWitnesses, List.length_map]

/-- The `UInt64` count of a non-empty input list in CompactSize range is
non-zero. -/
theorem ofNat_length_ne_zero {l : List TxIn} (hne : l ≠ []) (hlt : l.length < 2 ^ 64) :
    UInt64.ofNat l.length ≠ 0 := by
  intro h
  have : l.length = 0 := by
    have := congrArg UInt64.toNat h
    rwa [UInt64.toNat_ofNat_of_lt' hlt] at this
  exact hne (List.length_eq_zero_iff.mp this)

/-! ## Encoding and decoding -/

/-- The SegWit body after the marker and flag: inputs, outputs, witnesses, lock
time. The inputs region carries only the scriptSigs; the witnesses follow the
outputs, one per input. -/
def encodeSegwitBody (ins : CountedList SegwitInput) (outs : CountedList TxOut)
    (lockTime : UInt32) : List UInt8 :=
  Codec.encode (segwitInputs ins) ++ Codec.encode outs
    ++ encodeElems (segwitWitnesses ins) ++ Codec.encode lockTime

/-- Serialize a transaction. Legacy is its `TxBody`; SegWit is the version, the
marker `0x00` and flag `0x01`, then the SegWit body. -/
def encodeTx : Tx → List UInt8
  | .legacy body _ _ => Codec.encode body
  | .segwit version ins outs lockTime _ =>
    Codec.encode version ++ 0x00 :: 0x01 :: encodeSegwitBody ins outs lockTime

/-- Decode the SegWit body (everything after version, marker, and flag),
rebundling the separately-read inputs and witnesses. The output vector must be
non-empty. -/
def decodeSegwit (version : UInt32) (bs : List UInt8) : Option (Tx × List UInt8) := do
  let (txins, r1) ← Codec.decode (α := CountedList TxIn) bs
  let (outs, r2) ← Codec.decode (α := CountedList TxOut) r1
  let (wits, r3) ← decodeElems (α := WitnessStack) txins.val.length r2
  let (lockTime, r4) ← Codec.decode (α := UInt32) r3
  if hOutputs : outs.val ≠ [] then
    return (.segwit version (zipInputs txins wits) outs lockTime hOutputs, r4)
  else
    none

/-- Decode a legacy transaction body (everything after version), then attach the
non-empty input and output proofs required for a transaction. -/
def decodeLegacy (version : UInt32) (bs : List UInt8) : Option (Tx × List UInt8) := do
  let (inputs, r1) ← Codec.decode (α := CountedList TxIn) bs
  let (outputs, r2) ← Codec.decode (α := CountedList TxOut) r1
  let (lockTime, r3) ← Codec.decode (α := UInt32) r2
  if hInputs : inputs.val ≠ [] then
    if hOutputs : outputs.val ≠ [] then
      return (.legacy ⟨version, inputs, outputs, lockTime⟩ hInputs hOutputs, r3)
    else
      none
  else
    none

/-- Decode a transaction: read the version, then dispatch on the marker byte. -/
def decodeTx (bs : List UInt8) : Option (Tx × List UInt8) := do
  let (version, rest1) ← Codec.decode (α := UInt32) bs
  match rest1 with
  | 0x00 :: 0x01 :: rest3 => decodeSegwit version rest3
  | 0x00 :: _ => none
  | _ => decodeLegacy version rest1

/-! ## Round-trip -/

/-- Decoding an encoded SegWit body returns the SegWit transaction it came from,
leaving the trailing bytes as the unconsumed tail. -/
theorem decodeSegwit_encode (version : UInt32) (ins : CountedList SegwitInput)
    (outs : CountedList TxOut) (lockTime : UInt32)
    (hOutputs : outs.val ≠ []) (rest : List UInt8) :
    decodeSegwit version (encodeSegwitBody ins outs lockTime ++ rest)
      = some (.segwit version ins outs lockTime hOutputs, rest) := by
  unfold decodeSegwit encodeSegwitBody
  simp only [List.append_assoc, Option.bind_eq_bind, Codec.decode_encode, Option.bind_some]
  rw [segwitInputs_length, decodeElems_encodeElems]
  simp [hOutputs, Option.pure_def, Codec.decode_encode, zipInputs_segwit]

/-- Decoding the encoded post-version fields of a body with non-empty inputs and
outputs returns the legacy transaction on that body, tail preserved. -/
theorem decodeLegacy_encode (body : TxBody) (hne : body.inputs.val ≠ [])
    (hout : body.outputs.val ≠ [])
    (rest : List UInt8) :
    decodeLegacy body.version
        (Codec.encode body.inputs ++ Codec.encode body.outputs
          ++ Codec.encode body.lockTime ++ rest)
      = some (Tx.legacy body hne hout, rest) := by
  unfold decodeLegacy
  simp only [List.append_assoc, Option.bind_eq_bind, Codec.decode_encode, Option.bind_some]
  simp [hne, hout, Option.pure_def]

/-- When the byte after the version is not the marker `0x00`, `decodeTx`
dispatches to the legacy decoder. -/
theorem decodeTx_legacy_eq (version : UInt32) (inputs : CountedList TxIn)
    (rest1 : List UInt8) (b : UInt8) (t : List UInt8)
    (hbt : (Codec.encode inputs : List UInt8) = b :: t) (hb : b ≠ 0x00) :
    decodeTx (Codec.encode version ++ (Codec.encode inputs ++ rest1))
      = decodeLegacy version (Codec.encode inputs ++ rest1) := by
  unfold decodeTx
  rw [hbt]
  simp only [List.cons_append, Option.bind_eq_bind, Codec.decode_encode, Option.bind_some]
  split <;> simp_all

/-- Round-trip: every transaction encodes and decodes back to itself, tail
preserved. -/
theorem decodeTx_encodeTx (tx : Tx) (rest : List UInt8) :
    decodeTx (encodeTx tx ++ rest) = some (tx, rest) := by
  cases tx with
  | segwit version ins outs lockTime hOutputs =>
    unfold encodeTx decodeTx
    simp only [List.append_assoc, List.cons_append, Option.bind_eq_bind,
      Codec.decode_encode, Option.bind_some]
    exact decodeSegwit_encode version ins outs lockTime hOutputs rest
  | legacy body hne hout =>
    obtain ⟨b, t, hbt, hb0⟩ := CompactSize.encode_head (UInt64.ofNat body.inputs.val.length)
    have hb : b ≠ 0x00 := hb0 (ofNat_length_ne_zero hne body.inputs.property)
    have hins : (Codec.encode body.inputs : List UInt8)
        = b :: (t ++ encodeElems body.inputs.val) := by
      change encodeCountedList body.inputs = _
      unfold encodeCountedList
      rw [hbt, List.cons_append]
    change decodeTx (Codec.encode body ++ rest) = _
    rw [show (Codec.encode body : List UInt8)
        = Codec.encode body.version ++ (Codec.encode body.inputs
          ++ (Codec.encode body.outputs ++ Codec.encode body.lockTime)) from rfl]
    simp only [List.append_assoc]
    rw [decodeTx_legacy_eq body.version body.inputs _ b _ hins hb]
    rw [← List.append_assoc, ← List.append_assoc]
    exact decodeLegacy_encode body hne hout rest

/-! ## Canonicality -/

/-- If the SegWit-body decoder accepts `bs`, the result is a SegWit transaction
carrying the given version and `bs` is exactly the canonical encoding of its
body followed by the tail. -/
theorem decodeSegwit_canonical (version : UInt32) (bs : List UInt8) (tx : Tx)
    (rest : List UInt8) (h : decodeSegwit version bs = some (tx, rest)) :
    ∃ ins outs lockTime hOutputs, tx = .segwit version ins outs lockTime hOutputs ∧
      bs = encodeSegwitBody ins outs lockTime ++ rest := by
  unfold decodeSegwit at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨⟨txins, r1⟩, hti, ⟨outs, r2⟩, hto, ⟨wits, r3⟩, hwit, ⟨lockTime, r4⟩, hlt,
    h⟩ := h
  dsimp only at hto hwit hlt h ⊢
  by_cases hOutputs : outs.val ≠ []
  · simp only [dif_pos hOutputs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨zipInputs txins wits, outs, lockTime, hOutputs, rfl, ?_⟩
    have hwlen : wits.length = txins.val.length := decodeElems_length _ _ _ _ hwit
    have eti := Codec.decode_canonical bs txins r1 hti
    have eto := Codec.decode_canonical r1 outs r2 hto
    have ewit := decodeElems_canonical _ _ _ _ hwit
    have elt := Codec.decode_canonical r3 lockTime r4 hlt
    unfold encodeSegwitBody
    rw [segwitInputs_zipInputs txins wits hwlen,
      segwitWitnesses_zipInputs txins wits hwlen, eti, eto, ewit, elt]
    simp only [List.append_assoc]
  · simp [hOutputs] at h

/-- If the legacy decoder accepts `bs`, the result is a legacy transaction whose
body carries the given version, its inputs are non-empty, and `bs` is exactly
the canonical encodings of the remaining fields followed by the tail. -/
theorem decodeLegacy_canonical (version : UInt32) (bs : List UInt8) (tx : Tx)
    (rest : List UInt8) (h : decodeLegacy version bs = some (tx, rest)) :
    ∃ (inputs : CountedList TxIn) (outputs : CountedList TxOut) (lockTime : UInt32)
      (hne : inputs.val ≠ []) (hout : outputs.val ≠ []),
      tx = Tx.legacy ⟨version, inputs, outputs, lockTime⟩ hne hout ∧
        bs = Codec.encode inputs ++ Codec.encode outputs ++ Codec.encode lockTime ++ rest := by
  unfold decodeLegacy at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨⟨inputs, r1⟩, hti, ⟨outputs, r2⟩, hto, ⟨lockTime, r3⟩, hlt, h⟩ := h
  dsimp only at hto hlt h ⊢
  by_cases hne : inputs.val ≠ []
  · by_cases hout : outputs.val ≠ []
    · simp only [dif_pos hne, dif_pos hout, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨inputs, outputs, lockTime, hne, hout, rfl, ?_⟩
      have eti := Codec.decode_canonical bs inputs r1 hti
      have eto := Codec.decode_canonical r1 outputs r2 hto
      have elt := Codec.decode_canonical r2 lockTime r3 hlt
      rw [eti, eto, elt]
      simp only [List.append_assoc]
    · simp [hne, hout] at h
  · simp [hne] at h

/-- Canonicality: an accepted parse consumed exactly the canonical encoding,
including the legacy/SegWit branch the value's own form dictates. -/
theorem decodeTx_canonical (bs : List UInt8) (tx : Tx) (rest : List UInt8)
    (h : decodeTx bs = some (tx, rest)) : bs = encodeTx tx ++ rest := by
  unfold decodeTx at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨version, rest1⟩, hv, h⟩ := h
  dsimp only at h
  have ev := Codec.decode_canonical bs version rest1 hv
  split at h
  · rename_i rest3
    obtain ⟨ins, outs, lockTime, hOutputs, rfl, hbody⟩ :=
      decodeSegwit_canonical version rest3 tx rest h
    rw [ev, hbody]
    simp only [encodeTx, List.append_assoc, List.cons_append]
  · simp at h
  · obtain ⟨inputs, outputs, lockTime, hne, hout, rfl, hbody⟩ :=
      decodeLegacy_canonical version rest1 tx rest h
    rw [ev, hbody]
    simp only [encodeTx]
    rw [show (Codec.encode (⟨version, inputs, outputs, lockTime⟩ : TxBody) : List UInt8)
        = Codec.encode version ++ (Codec.encode inputs
          ++ (Codec.encode outputs ++ Codec.encode lockTime)) from rfl]
    simp only [List.append_assoc]

/-- The transaction codec: legacy and SegWit forms, dispatched on the BIP144
marker byte. -/
instance instCodecTx : Codec Tx where
  encode := encodeTx
  decode := decodeTx
  decode_encode := decodeTx_encodeTx
  decode_canonical := decodeTx_canonical

end BtcVerified
