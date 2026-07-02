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

  The marker `0x00` is the reserved "zero inputs" encoding, never a valid legacy
  transaction — which is what lets the decoder dispatch on it, and why the
  `legacy` constructor carries a non-empty-inputs proof.

  BIP144 also says that if the witness is empty, the old serialization format
  must be used. Therefore the SegWit constructor carries the corresponding
  invariant: at least one input has a non-empty witness stack. Per-input empty
  witnesses remain valid; what is forbidden is using the marker/flag form when
  every witness stack is empty.

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

/-! ## SegWit input lists -/

/-- Whether a per-input witness stack contains at least one stack item. BIP144
allows individual empty witness stacks, but the SegWit marker/flag transaction
form is only canonical when the transaction's witness as a whole is non-empty. -/
def witnessStackHasItems (wit : WitnessStack) : Bool :=
  !wit.val.isEmpty

/-- Whether a list of per-input witness stacks contains any actual witness data.
BIP144's serialization rule is: if this is false, the transaction must use the
old non-witness serialization format. -/
def witnessListHasWitness (wits : List WitnessStack) : Bool :=
  wits.any witnessStackHasItems

/-- The underlying inputs of a SegWit transaction, witnesses dropped — the input
vector as it appears in the inputs region of the wire format. -/
def segwitInputs (ins : CountedList SegwitInput) : CountedList TxIn :=
  ⟨ins.val.map SegwitInput.input, by rw [List.length_map]; exact ins.property⟩

/-- The witnesses of a SegWit transaction in input order — the witness region of
the wire format. -/
def segwitWitnesses (ins : CountedList SegwitInput) : List WitnessStack :=
  ins.val.map SegwitInput.witness

/-- Whether a SegWit input list has the non-empty witness required by BIP144 for
marker/flag serialization. Empty stacks for non-witness-program inputs are fine;
at least one stack in the transaction must be non-empty. -/
def segwitHasWitness (ins : CountedList SegwitInput) : Bool :=
  witnessListHasWitness (segwitWitnesses ins)

/-- A Bitcoin transaction in one of its two serialization forms.

`legacy` is the pre-SegWit form: a witness-free `TxBody`. Its inputs are
non-empty because the SegWit serialization reserves a zero input count (the
`0x00` marker byte), so a legacy transaction can never encode zero inputs on the
wire.

`segwit` is the BIP144 form, where each input carries its own witness. The
arity rule — one witness stack per input — is structural here (it *is* a list of
`SegwitInput`). BIP144 additionally requires the old serialization when the
transaction's witness is empty, so this constructor carries a proof that at
least one input witness stack is non-empty. -/
inductive Tx where
  /-- A legacy (pre-SegWit) transaction: a witness-free body with non-empty
  inputs. -/
  | legacy (body : TxBody) (inputsNonempty : body.inputs.val ≠ [])
  /-- A BIP144 SegWit transaction: each input bundled with its witness, and at
  least one witness stack non-empty so the marker/flag serialization is
  canonical. -/
  | segwit (version : UInt32) (inputs : CountedList SegwitInput)
      (outputs : CountedList TxOut) (lockTime : UInt32)
      (hasWitness : segwitHasWitness inputs = true)
  deriving DecidableEq

/-- Whether a transaction is in SegWit (witnessed) serialization form. -/
def Tx.isSegWit : Tx → Bool
  | .legacy .. => false
  | .segwit .. => true

/-- The witness-free body of a transaction: its txid preimage and its legacy
interpretation. A legacy transaction *is* its body; a SegWit transaction's body
drops each input's witness. -/
def Tx.body : Tx → TxBody
  | .legacy body _ => body
  | .segwit version inputs outputs lockTime _ =>
    { version := version
      inputs := ⟨inputs.val.map SegwitInput.input, by
        rw [List.length_map]; exact inputs.property⟩
      outputs := outputs
      lockTime := lockTime }

/-! ## Bundling and unbundling SegWit inputs -/

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

/-! ## The legacy smart constructor -/

/-- Build a legacy transaction, checking the non-empty-inputs requirement. The
decoder uses this to attach the proof; on legacy input the check always
succeeds, because the marker byte rules out a zero input count. -/
def Tx.legacy? (body : TxBody) : Option Tx :=
  if h : body.inputs.val ≠ [] then some (Tx.legacy body h) else none

/-- `Tx.legacy?` accepts any body already known to have non-empty inputs. -/
theorem Tx.legacy?_eq_some {body : TxBody} (h : body.inputs.val ≠ []) :
    Tx.legacy? body = some (Tx.legacy body h) := by
  simp only [Tx.legacy?, dif_pos h]

/-- An accepted `Tx.legacy?` returns a legacy transaction on exactly the body it
was given — so the body's inputs were non-empty. -/
theorem Tx.legacy_of_legacy? {body : TxBody} {tx : Tx}
    (h : Tx.legacy? body = some tx) :
    ∃ hne : body.inputs.val ≠ [], tx = Tx.legacy body hne := by
  unfold Tx.legacy? at h
  split at h
  · next hne => exact ⟨hne, by simp only [Option.some.injEq] at h; rw [← h]⟩
  · exact absurd h (by simp)

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
  | .legacy body _ => Codec.encode body
  | .segwit version ins outs lockTime _ =>
    Codec.encode version ++ 0x00 :: 0x01 :: encodeSegwitBody ins outs lockTime

/-- Build a SegWit transaction from separately decoded inputs and witness
stacks, enforcing the two BIP144 shape rules that are not visible in the raw
lists themselves: there must be one witness stack per input, and the
transaction's witness as a whole must be non-empty.

The decoder calls this after `decodeElems` has read exactly one witness stack per
input, so the length check is guaranteed there. Keeping the check here makes the
smart constructor correct for arbitrary separately supplied lists too. -/
def Tx.segwit? (version : UInt32) (txins : CountedList TxIn)
    (outs : CountedList TxOut) (lockTime : UInt32)
    (wits : List WitnessStack) : Option Tx :=
  if hw : witnessListHasWitness wits = true then
    if hwlen : wits.length = txins.val.length then
      have hzip : segwitHasWitness (zipInputs txins wits) = true := by
        unfold segwitHasWitness
        rw [segwitWitnesses_zipInputs txins wits hwlen]
        exact hw
      some (.segwit version (zipInputs txins wits) outs lockTime hzip)
    else
      none
  else
    none

/-- Any transaction produced by `Tx.segwit?` is exactly the zipped SegWit
transaction, and the witness list has the same length as the input list. -/
theorem Tx.segwit_of_segwit? {version : UInt32} {txins : CountedList TxIn}
    {outs : CountedList TxOut} {lockTime : UInt32}
    {wits : List WitnessStack} {tx : Tx}
    (h : Tx.segwit? version txins outs lockTime wits = some tx) :
    ∃ (_ : wits.length = txins.val.length)
      (hasWitness : segwitHasWitness (zipInputs txins wits) = true),
      tx = .segwit version (zipInputs txins wits) outs lockTime hasWitness := by
  unfold Tx.segwit? at h
  split at h
  · rename_i hw
    split at h
    · rename_i hwlen
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hwlen, ?_, ?_⟩
      · unfold segwitHasWitness
        rw [segwitWitnesses_zipInputs txins wits hwlen]
        exact hw
      · rfl
    · simp at h
  · simp at h

/-- Decode the SegWit body (everything after version, marker, and flag),
rebundling the separately-read inputs and witnesses. BIP144 requires old
serialization when the transaction's witness is empty, so all-empty witness
stacks are rejected instead of producing a SegWit transaction. -/
def decodeSegwit (version : UInt32) (bs : List UInt8) : Option (Tx × List UInt8) :=
  match Codec.decode (α := CountedList TxIn) bs with
  | none => none
  | some (txins, r1) =>
    match Codec.decode (α := CountedList TxOut) r1 with
    | none => none
    | some (outs, r2) =>
      match decodeElems (α := WitnessStack) txins.val.length r2 with
      | none => none
      | some (wits, r3) =>
        match Codec.decode (α := UInt32) r3 with
        | none => none
        | some (lockTime, r4) =>
          match Tx.segwit? version txins outs lockTime wits with
          | none => none
          | some tx => some (tx, r4)

/-- Decode a legacy transaction body (everything after version), then attach the
non-empty-inputs proof via the smart constructor. -/
def decodeLegacy (version : UInt32) (bs : List UInt8) : Option (Tx × List UInt8) :=
  match Codec.decode (α := CountedList TxIn) bs with
  | none => none
  | some (inputs, r1) =>
    match Codec.decode (α := CountedList TxOut) r1 with
    | none => none
    | some (outputs, r2) =>
      match Codec.decode (α := UInt32) r2 with
      | none => none
      | some (lockTime, r3) =>
        match Tx.legacy? ⟨version, inputs, outputs, lockTime⟩ with
        | none => none
        | some tx => some (tx, r3)

/-- Decode a transaction: read the version, then dispatch on the marker byte. -/
def decodeTx (bs : List UInt8) : Option (Tx × List UInt8) :=
  match Codec.decode (α := UInt32) bs with
  | none => none
  | some (version, rest1) =>
    match rest1 with
    | 0x00 :: rest2 =>
      match rest2 with
      | 0x01 :: rest3 => decodeSegwit version rest3
      | _ => none
    | _ => decodeLegacy version rest1

/-! ## Round-trip -/

/-- Decoding an encoded SegWit body returns the SegWit transaction it came from,
leaving the trailing bytes as the unconsumed tail. -/
theorem decodeSegwit_encode (version : UInt32) (ins : CountedList SegwitInput)
    (outs : CountedList TxOut) (lockTime : UInt32)
    (hasWitness : segwitHasWitness ins = true) (rest : List UInt8) :
    decodeSegwit version (encodeSegwitBody ins outs lockTime ++ rest)
      = some (.segwit version ins outs lockTime hasWitness, rest) := by
  unfold decodeSegwit encodeSegwitBody
  simp only [List.append_assoc, Codec.decode_encode]
  rw [segwitInputs_length, decodeElems_encodeElems]
  have hw : witnessListHasWitness (segwitWitnesses ins) = true := by
    simpa [segwitHasWitness] using hasWitness
  have hwlen : (segwitWitnesses ins).length = (segwitInputs ins).val.length :=
    (segwitInputs_length ins).symm
  have hm :
      Tx.segwit? version (segwitInputs ins) outs lockTime (segwitWitnesses ins)
        = some (.segwit version ins outs lockTime hasWitness) := by
    unfold Tx.segwit?
    simp [hw, hwlen, zipInputs_segwit]
  simp [hm, Codec.decode_encode]

/-- Decoding the encoded post-version fields of a body with non-empty inputs
returns the legacy transaction on that body, tail preserved. -/
theorem decodeLegacy_encode (body : TxBody) (hne : body.inputs.val ≠ [])
    (rest : List UInt8) :
    decodeLegacy body.version
        (Codec.encode body.inputs ++ Codec.encode body.outputs
          ++ Codec.encode body.lockTime ++ rest)
      = some (Tx.legacy body hne, rest) := by
  unfold decodeLegacy
  simp only [List.append_assoc, Codec.decode_encode]
  rw [Tx.legacy?_eq_some hne]

/-- When the byte after the version is not the marker `0x00`, `decodeTx`
dispatches to the legacy decoder. -/
theorem decodeTx_legacy_eq (version : UInt32) (inputs : CountedList TxIn)
    (rest1 : List UInt8) (b : UInt8) (t : List UInt8)
    (hbt : (Codec.encode inputs : List UInt8) = b :: t) (hb : b ≠ 0x00) :
    decodeTx (Codec.encode version ++ (Codec.encode inputs ++ rest1))
      = decodeLegacy version (Codec.encode inputs ++ rest1) := by
  unfold decodeTx
  rw [hbt]
  simp only [List.cons_append, Codec.decode_encode]
  split
  · next rest2 heq => rw [List.cons.injEq] at heq; exact absurd heq.1 hb
  · rfl

/-- Round-trip: every transaction encodes and decodes back to itself, tail
preserved. -/
theorem decodeTx_encodeTx (tx : Tx) (rest : List UInt8) :
    decodeTx (encodeTx tx ++ rest) = some (tx, rest) := by
  cases tx with
  | segwit version ins outs lockTime hasWitness =>
    unfold encodeTx decodeTx
    simp only [List.append_assoc, List.cons_append, Codec.decode_encode]
    exact decodeSegwit_encode version ins outs lockTime hasWitness rest
  | legacy body hne =>
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
    exact decodeLegacy_encode body hne rest

/-! ## Canonicality -/

/-- If the SegWit-body decoder accepts `bs`, the result is a SegWit transaction
carrying the given version and `bs` is exactly the canonical encoding of its
body followed by the tail. -/
theorem decodeSegwit_canonical (version : UInt32) (bs : List UInt8) (tx : Tx)
    (rest : List UInt8) (h : decodeSegwit version bs = some (tx, rest)) :
    ∃ ins outs lockTime hasWitness, tx = .segwit version ins outs lockTime hasWitness ∧
      bs = encodeSegwitBody ins outs lockTime ++ rest := by
  unfold decodeSegwit at h
  cases hti : Codec.decode (α := CountedList TxIn) bs with
  | none => simp [hti] at h
  | some tir =>
    obtain ⟨txins, r1⟩ := tir
    simp only [hti] at h
    cases hto : Codec.decode (α := CountedList TxOut) r1 with
    | none => simp [hto] at h
    | some tor =>
      obtain ⟨outs, r2⟩ := tor
      simp only [hto] at h
      cases hwit : decodeElems (α := WitnessStack) txins.val.length r2 with
      | none => simp [hwit] at h
      | some wr =>
        obtain ⟨wits, r3⟩ := wr
        simp only [hwit] at h
        cases hlt : Codec.decode (α := UInt32) r3 with
        | none => simp [hlt] at h
        | some lr =>
          obtain ⟨lockTime, r4⟩ := lr
          simp only [hlt] at h
          cases hseg : Tx.segwit? version txins outs lockTime wits with
          | none => simp [hseg] at h
          | some builtTx =>
            simp only [hseg, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hwlen, hasWitness, htx⟩ := Tx.segwit_of_segwit? hseg
            refine ⟨zipInputs txins wits, outs, lockTime, hasWitness, htx, ?_⟩
            have eti := Codec.decode_canonical bs txins r1 hti
            have eto := Codec.decode_canonical r1 outs r2 hto
            have ewit := decodeElems_canonical _ _ _ _ hwit
            have elt := Codec.decode_canonical r3 lockTime r4 hlt
            unfold encodeSegwitBody
            rw [segwitInputs_zipInputs txins wits hwlen,
              segwitWitnesses_zipInputs txins wits hwlen, eti, eto, ewit, elt]
            simp only [List.append_assoc]

/-- If the legacy decoder accepts `bs`, the result is a legacy transaction whose
body carries the given version, its inputs are non-empty, and `bs` is exactly
the canonical encodings of the remaining fields followed by the tail. -/
theorem decodeLegacy_canonical (version : UInt32) (bs : List UInt8) (tx : Tx)
    (rest : List UInt8) (h : decodeLegacy version bs = some (tx, rest)) :
    ∃ (inputs : CountedList TxIn) (outputs : CountedList TxOut) (lockTime : UInt32)
      (hne : inputs.val ≠ []),
      tx = Tx.legacy ⟨version, inputs, outputs, lockTime⟩ hne ∧
        bs = Codec.encode inputs ++ Codec.encode outputs ++ Codec.encode lockTime ++ rest := by
  unfold decodeLegacy at h
  cases hti : Codec.decode (α := CountedList TxIn) bs with
  | none => simp [hti] at h
  | some tir =>
    obtain ⟨inputs, r1⟩ := tir
    simp only [hti] at h
    cases hto : Codec.decode (α := CountedList TxOut) r1 with
    | none => simp [hto] at h
    | some tor =>
      obtain ⟨outputs, r2⟩ := tor
      simp only [hto] at h
      cases hlt : Codec.decode (α := UInt32) r2 with
      | none => simp [hlt] at h
      | some lr =>
        obtain ⟨lockTime, r3⟩ := lr
        simp only [hlt] at h
        cases hleg : Tx.legacy? ⟨version, inputs, outputs, lockTime⟩ with
        | none => simp [hleg] at h
        | some tx' =>
          simp only [hleg, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hne, htxeq⟩ := Tx.legacy_of_legacy? hleg
          refine ⟨inputs, outputs, lockTime, hne, htxeq, ?_⟩
          have eti := Codec.decode_canonical bs inputs r1 hti
          have eto := Codec.decode_canonical r1 outputs r2 hto
          have elt := Codec.decode_canonical r2 lockTime r3 hlt
          rw [eti, eto, elt]
          simp only [List.append_assoc]

/-- Canonicality: an accepted parse consumed exactly the canonical encoding,
including the legacy/SegWit branch the value's own form dictates. -/
theorem decodeTx_canonical (bs : List UInt8) (tx : Tx) (rest : List UInt8)
    (h : decodeTx bs = some (tx, rest)) : bs = encodeTx tx ++ rest := by
  unfold decodeTx at h
  cases hv : Codec.decode (α := UInt32) bs with
  | none => simp [hv] at h
  | some vr =>
    obtain ⟨version, rest1⟩ := vr
    simp only [hv] at h
    have ev := Codec.decode_canonical bs version rest1 hv
    split at h
    · rename_i rest2
      split at h
      · rename_i rest3
        obtain ⟨ins, outs, lockTime, hasWitness, rfl, hbody⟩ :=
          decodeSegwit_canonical version rest3 tx rest h
        rw [ev, hbody]
        simp only [encodeTx, List.append_assoc, List.cons_append]
      · simp at h
    · obtain ⟨inputs, outputs, lockTime, hne, rfl, hbody⟩ :=
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
