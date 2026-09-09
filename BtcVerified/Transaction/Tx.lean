import BtcVerified.Transaction.TxBody
import BtcVerified.Transaction.SegwitInput
import BtcVerified.Serialize.CompactSize
import BtcVerified.Ext.List
/-!
  # The transaction type and its codec

  A transaction is era-aware from the start: an inductive with ordinary
  `legacy`, degenerate `empty`, and `segwit` constructors over a shared,
  witness-free `TxBody`. The `empty` case is the zero-input, zero-output object
  Bitcoin Core's witness-aware decoder accepts when it reads a zero input count
  followed by a zero optional-data flag ([Bitcoin Core v28.0,
  `transaction.h` lines 220–252](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L220-L252)).

  This remains an abstract syntax object rather than Core's `CTransaction`, but
  its admitted wire domain is chosen to be compatible with that decoder instead
  of silently moving Core's empty-input rejection into parsing. SegWit is a soft
  fork — a restriction of the legacy ruleset — so the body is exactly what a txid
  commits to, exactly the legacy serialization, and exactly the witness-stripped
  form a SegWit transaction shows the pre-SegWit world; `Tx.body` recovers it
  from every form. A SegWit transaction bundles each input with the witness that
  unlocks it (`SegwitInput`), so the one-witness-per-input arity is structural
  rather than a side condition.

  ## Serialization

  A transaction serializes in one of three accepted forms, and the decoder tells
  them apart from the bytes alone. After the 4-byte version:

  * the ordinary **legacy** form is its `TxBody` — a non-empty input vector,
    output vector, lock time;
  * the degenerate **empty** form is zero inputs, zero outputs, and lock time;
  * the **SegWit** (BIP144) form interposes the marker `0x00` and flag `0x01`,
    then serializes the inputs (scriptSigs only), the outputs, one witness stack
    per input (no separate count — the count *is* the number of inputs), and the
    lock time.

  Core first reads `0x00` as an empty input vector, then reads the next byte as
  optional-data flags. Flag `0x00` leaves both vectors empty; flag `0x01` selects
  the SegWit body; other flags are rejected. The ordinary `legacy` constructor
  retains its non-empty-input proof, while `empty` names the one canonical
  empty-input result of this witness-aware dispatch.

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

  * `decodeTx_encodeTx`: every transaction, including Core's empty object,
    round-trips with its tail preserved.
  * `decodeTx_canonical`: an accepted parse consumed exactly the canonical
    encoding — including taking the legacy, empty, or SegWit branch the value's
    own form dictates.

  Both are packaged as `instCodecTx : Codec Tx`. Exact equivalence to a
  transcription of Core's decoder belongs in `Impl/`; this type supplies the
  implementation-independent syntax and reasoning substrate it must refine to.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-! ## SegWit witness predicates -/

namespace WitnessStack

/-- A witness stack contains actual witness data exactly when it has at least
one stack item. The item itself may be empty; Bitcoin Core's null-witness test
is about the stack item count ([Bitcoin Core v28.0, `transaction.h` lines
237–245](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L237-L245)). -/
def NonEmpty (wit : WitnessStack) : Prop :=
  wit.val ≠ []

instance instDecidableNonEmpty (wit : WitnessStack) :
    Decidable wit.NonEmpty := by
  unfold NonEmpty
  cases wit.val with
  | nil =>
      exact isFalse (by
        intro hne
        exact hne rfl)
  | cons _ _ =>
      exact isTrue (by
        intro hnil
        cases hnil)

end WitnessStack

/-- Decidability support for the transaction-level check that the SegWit
serialization is carrying some witness data. -/
instance instDecidableExistsNonEmptyWitness (inputs : List SegwitInput) :
    Decidable (∃ input, input ∈ inputs ∧ input.witness.NonEmpty) := by
  induction inputs with
  | nil =>
      exact isFalse (by
        rintro ⟨_, hmem, _⟩
        cases hmem)
  | cons input inputs ih =>
      by_cases hhead : input.witness.NonEmpty
      · exact isTrue ⟨input, List.mem_cons_self, hhead⟩
      · cases ih with
        | isTrue htail =>
            exact isTrue (by
              rcases htail with ⟨tailInput, hmem, hnonempty⟩
              exact ⟨tailInput, List.mem_cons_of_mem _ hmem, hnonempty⟩)
        | isFalse htail =>
            exact isFalse (by
              rintro ⟨found, hmem, hnonempty⟩
              cases hmem with
              | head =>
                exact hhead hnonempty
              | tail _ hmemTail =>
                exact htail ⟨found, hmemTail, hnonempty⟩)

/-- A Bitcoin transaction in one of the serialization forms accepted by the
witness-aware wire decoder.

`legacy` is the pre-SegWit form: a witness-free `TxBody`. Its inputs are
non-empty because the SegWit serialization reserves a zero input count (the
`0x00` marker byte), so a legacy transaction can never encode zero inputs on the
wire.

`empty` is the degenerate no-witness result Core accepts when both the initially
read input vector and the following optional-data flag are zero. Its derived
body has no inputs and no outputs; the transaction-local premises reject it
([Bitcoin Core v28.0, `transaction.h` lines
220–252](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L220-L252)).

`segwit` is the BIP144 form, where each input carries its own witness. The
arity rule — one witness stack per input — is structural here (it *is* a list of
`SegwitInput`). BIP144 additionally requires the old serialization when the
transaction's witness is empty, so this constructor carries a proof that at
least one input witness stack is non-empty. -/
inductive Tx where
  /-- A legacy (pre-SegWit) transaction: a witness-free body with non-empty
  inputs. -/
  | legacy (body : TxBody) (inputsNonempty : body.inputs.val ≠ [])
  /-- The zero-input, zero-output no-witness transaction accepted by Core's
  witness-aware decoder ([Bitcoin Core v28.0, `transaction.h` lines
  220–252](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L220-L252)). -/
  | empty (version : UInt32) (lockTime : UInt32)
  /-- A BIP144 SegWit transaction: each input bundled with its witness, and at
  least one witness stack non-empty so the marker/flag serialization is
  canonical. -/
  | segwit (version : UInt32) (inputs : CountedList SegwitInput)
      (outputs : CountedList TxOut) (lockTime : UInt32)
      (hWitness : ∃ input, input ∈ inputs.val ∧ input.witness.NonEmpty)
  deriving DecidableEq

/-- Whether a transaction is in SegWit (witnessed) serialization form. -/
def Tx.isSegWit : Tx → Bool
  | .legacy .. => false
  | .empty .. => false
  | .segwit .. => true

/-- The witness-free body of a transaction: its txid preimage and its legacy
interpretation. An ordinary legacy transaction *is* its body; an empty
transaction derives the zero-vector body; a SegWit transaction's body drops
each input's witness. -/
def Tx.body : Tx → TxBody
  | .legacy body _ => body
  | .empty version lockTime =>
    { version := version
      inputs := ⟨[], by simp⟩
      outputs := ⟨[], by simp⟩
      lockTime := lockTime }
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

/-- Serialize a transaction. Ordinary legacy is its `TxBody`; empty is the two
zero vectors; SegWit is the version, marker `0x00`, flag `0x01`, and SegWit
body. -/
def encodeTx : Tx → List UInt8
  | .legacy body _ => Codec.encode body
  | .empty version lockTime =>
    Codec.encode version ++ 0x00 :: 0x00 :: Codec.encode lockTime
  | .segwit version ins outs lockTime _ =>
    Codec.encode version ++ 0x00 :: 0x01 :: encodeSegwitBody ins outs lockTime

/-- Decode the SegWit body (everything after version, marker, and flag),
rebundling the separately-read inputs and witnesses. BIP144 requires old
serialization when the transaction's witness is empty, so all-empty witness
stacks are rejected instead of producing a SegWit transaction ([Bitcoin Core
v28.0, `transaction.h` lines
237–245](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L237-L245)). -/
def decodeSegwit (version : UInt32) (bs : List UInt8) : Option (Tx × List UInt8) := do
  let (txins, r1) ← Codec.decode (α := CountedList TxIn) bs
  let (outs, r2) ← Codec.decode (α := CountedList TxOut) r1
  let (wits, r3) ← decodeElems (α := WitnessStack) txins.val.length r2
  let (lockTime, r4) ← Codec.decode (α := UInt32) r3
  let ins := zipInputs txins wits
  if hWitness : ∃ input, input ∈ ins.val ∧ input.witness.NonEmpty then
    return (.segwit version ins outs lockTime hWitness, r4)
  else
    none

/-- Decode a legacy transaction body (everything after version), then attach the
non-empty-inputs proof via the smart constructor. -/
def decodeLegacy (version : UInt32) (bs : List UInt8) : Option (Tx × List UInt8) := do
  let (inputs, r1) ← Codec.decode (α := CountedList TxIn) bs
  let (outputs, r2) ← Codec.decode (α := CountedList TxOut) r1
  let (lockTime, r3) ← Codec.decode (α := UInt32) r2
  let tx ← Tx.legacy? ⟨version, inputs, outputs, lockTime⟩
  return (tx, r3)

/-- Decode Core's degenerate no-witness path after the zero input count and
zero optional-data flag. The output vector remains empty and only lock time is
read ([Bitcoin Core v28.0, `transaction.h` lines
224–252](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L224-L252)). -/
def decodeEmpty (version : UInt32) (bs : List UInt8) : Option (Tx × List UInt8) := do
  let (lockTime, rest) ← Codec.decode (α := UInt32) bs
  return (.empty version lockTime, rest)

/-- Decode a transaction: read the version, then dispatch on the marker byte. -/
def decodeTx (bs : List UInt8) : Option (Tx × List UInt8) := do
  let (version, rest1) ← Codec.decode (α := UInt32) bs
  match rest1 with
  | 0x00 :: 0x01 :: rest3 => decodeSegwit version rest3
  | 0x00 :: 0x00 :: rest3 => decodeEmpty version rest3
  | 0x00 :: _ => none
  | _ => decodeLegacy version rest1

/-! ## Round-trip -/

/-- Decoding an encoded SegWit body returns the SegWit transaction it came from,
leaving the trailing bytes as the unconsumed tail. -/
theorem decodeSegwit_encode (version : UInt32) (ins : CountedList SegwitInput)
    (outs : CountedList TxOut) (lockTime : UInt32)
    (hWitness : ∃ input, input ∈ ins.val ∧ input.witness.NonEmpty)
    (rest : List UInt8) :
    decodeSegwit version (encodeSegwitBody ins outs lockTime ++ rest)
      = some (.segwit version ins outs lockTime hWitness, rest) := by
  unfold decodeSegwit encodeSegwitBody
  simp only [List.append_assoc, Option.bind_eq_bind, Codec.decode_encode, Option.bind_some]
  rw [segwitInputs_length, decodeElems_encodeElems]
  simp [hWitness, Option.pure_def, Codec.decode_encode, zipInputs_segwit]

/-- Decoding the encoded post-version fields of a body with non-empty inputs
returns the legacy transaction on that body, tail preserved. -/
theorem decodeLegacy_encode (body : TxBody) (hne : body.inputs.val ≠ [])
    (rest : List UInt8) :
    decodeLegacy body.version
        (Codec.encode body.inputs ++ Codec.encode body.outputs
          ++ Codec.encode body.lockTime ++ rest)
      = some (Tx.legacy body hne, rest) := by
  unfold decodeLegacy
  simp only [List.append_assoc, Option.bind_eq_bind, Codec.decode_encode, Option.bind_some]
  rw [Tx.legacy?_eq_some hne]
  rfl

/-- The empty transaction encoding decodes to the corresponding `Tx.empty`,
tail preserved. -/
theorem decodeEmpty_encode (version lockTime : UInt32) (rest : List UInt8) :
    decodeEmpty version (Codec.encode lockTime ++ rest)
      = some (.empty version lockTime, rest) := by
  simp [decodeEmpty, Codec.decode_encode]

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
  | segwit version ins outs lockTime hWitness =>
    unfold encodeTx decodeTx
    simp only [List.append_assoc, List.cons_append, Option.bind_eq_bind,
      Codec.decode_encode, Option.bind_some]
    exact decodeSegwit_encode version ins outs lockTime hWitness rest
  | empty version lockTime =>
    unfold encodeTx decodeTx
    simp only [List.append_assoc, List.cons_append, Option.bind_eq_bind,
      Codec.decode_encode, Option.bind_some]
    exact decodeEmpty_encode version lockTime rest
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
    ∃ ins outs lockTime hWitness, tx = .segwit version ins outs lockTime hWitness ∧
      bs = encodeSegwitBody ins outs lockTime ++ rest := by
  unfold decodeSegwit at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨⟨txins, r1⟩, hti, ⟨outs, r2⟩, hto, ⟨wits, r3⟩, hwit,
    ⟨lockTime, r4⟩, hlt, h⟩ := h
  dsimp only at hto hwit hlt h ⊢
  let ins := zipInputs txins wits
  by_cases hWitness : ∃ input, input ∈ ins.val ∧ input.witness.NonEmpty
  · simp only [ins, dif_pos hWitness, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨ins, outs, lockTime, hWitness, rfl, ?_⟩
    have hwlen : wits.length = txins.val.length := decodeElems_length _ _ _ _ hwit
    have eti := Codec.decode_canonical bs txins r1 hti
    have eto := Codec.decode_canonical r1 outs r2 hto
    have ewit := decodeElems_canonical _ _ _ _ hwit
    have elt := Codec.decode_canonical r3 lockTime r4 hlt
    unfold encodeSegwitBody
    dsimp only [ins]
    rw [segwitInputs_zipInputs txins wits hwlen,
      segwitWitnesses_zipInputs txins wits hwlen, eti, eto, ewit, elt]
    simp only [List.append_assoc]
  · simp [hWitness, ins] at h

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
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨inputs, r1⟩, hti, ⟨outputs, r2⟩, hto, ⟨lockTime, r3⟩, hlt, tx', hleg,
    rfl, rfl⟩ := h
  dsimp only at hto hlt hleg ⊢
  obtain ⟨hne, htxeq⟩ := Tx.legacy_of_legacy? hleg
  refine ⟨inputs, outputs, lockTime, hne, htxeq, ?_⟩
  have eti := Codec.decode_canonical bs inputs r1 hti
  have eto := Codec.decode_canonical r1 outputs r2 hto
  have elt := Codec.decode_canonical r2 lockTime r3 hlt
  rw [eti, eto, elt]
  simp only [List.append_assoc]

/-- If the empty-path decoder accepts `bs`, it returns `Tx.empty` at the given
version and `bs` is exactly the canonical lock-time encoding followed by the
tail. -/
theorem decodeEmpty_canonical (version : UInt32) (bs : List UInt8) (tx : Tx)
    (rest : List UInt8) (h : decodeEmpty version bs = some (tx, rest)) :
    ∃ lockTime, tx = .empty version lockTime ∧
      bs = Codec.encode lockTime ++ rest := by
  unfold decodeEmpty at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨lockTime, tail⟩, hlt, rfl, rfl⟩ := h
  exact ⟨lockTime, rfl, Codec.decode_canonical bs lockTime tail hlt⟩

/-- Canonicality: an accepted parse consumed exactly the canonical encoding,
including the legacy, empty, or SegWit branch the value's own form dictates. -/
theorem decodeTx_canonical (bs : List UInt8) (tx : Tx) (rest : List UInt8)
    (h : decodeTx bs = some (tx, rest)) : bs = encodeTx tx ++ rest := by
  unfold decodeTx at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨version, rest1⟩, hv, h⟩ := h
  dsimp only at h
  have ev := Codec.decode_canonical bs version rest1 hv
  split at h
  · rename_i rest3
    obtain ⟨ins, outs, lockTime, hWitness, rfl, hbody⟩ :=
      decodeSegwit_canonical version rest3 tx rest h
    rw [ev, hbody]
    simp only [encodeTx, List.append_assoc, List.cons_append]
  · rename_i rest3
    obtain ⟨lockTime, rfl, hbody⟩ :=
      decodeEmpty_canonical version rest3 tx rest h
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

/-- The transaction codec: ordinary legacy, degenerate empty, and SegWit forms,
dispatched through the BIP144 marker/flags path. -/
instance instCodecTx : Codec Tx where
  encode := encodeTx
  decode := decodeTx
  decode_encode := decodeTx_encodeTx
  decode_canonical := decodeTx_canonical

end BtcVerified
