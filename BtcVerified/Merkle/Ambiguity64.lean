import BtcVerified.Transaction.Tx
import BtcVerified.Crypto.Merkle
/-!
  # The 64-byte transaction / merkle internal-node ambiguity

  A merkle leaf carries a txid — `sha256d` of a transaction's serialization;
  an internal node carries `sha256d` of its two 32-byte children concatenated.
  Both preimages are 64 bytes, so a transaction whose serialization is exactly
  64 bytes is at once a leaf's preimage and an internal node's preimage. That
  structural overlap is the SPV forgery surface of CVE-2017-12842, and the
  reason `Merkle.root_inj_of_canonical` must assume `equal enclosing width`: with
  differing widths it cannot otherwise rule out a leaf at one height coinciding
  with an interior node at another (see that module's header).

  The Consensus Cleanup (BIP 54) closes this by forbidding 64-byte transactions
  outright. Jeremy Rubin's narrower proposal instead forbids only the
  *coincidence*: a block is invalid if any merkle internal-node preimage has the
  byte structure of a minimal one-input/one-output legacy transaction —
  `scriptSig` length `x` and `scriptPubKey` length `4 - x` for `x ∈ {0,1,2,3,4}`,
  with `nValue` in `MoneyRange`. This module begins the formal account of that
  proposal.

  Established here:

  * `decodesAs64ByteTx` — the deserializer-level predicate: a 64-byte string the
    canonical transaction decoder accepts in full.
  * `decodesAs64ByteTx_iff` — that predicate is exactly "a 64-byte string that is
    the canonical serialization of some transaction." It is the semantic referent
    of Rubin's rule, and the rigorous form of his open question about whether a
    node must run the full deserializer: the predicate is canonical and decidable
    by construction, straight from the transaction codec laws.
  * `combine_preimage_length` — every internal-node preimage is exactly 64 bytes,
    the width that makes the ambiguity possible.
  * `Tree.noForbiddenPreimage` — Rubin's rule as a structural property of the
    tree: no internal node's 64-byte preimage decodes as a transaction.

  Open targets (tracked in the PR, deliberately not yet proved): that Rubin's
  explicit fixed-offset byte check equals `decodesAs64ByteTx` restricted to the
  one-input/one-output / `MoneyRange` shape — the equivalence that justifies not
  running the deserializer, and that makes explicit the transaction-validity
  facts the narrow rule silently leans on (a zero-output 64-byte serialization is
  consensus-invalid; an out-of-`MoneyRange` value cannot be a valid leaf); and
  that `noForbiddenPreimage` discharges the `equal enclosing width` hypothesis of
  `root_inj_of_canonical`.
-/

namespace BtcVerified.Merkle

open BtcVerified BtcVerified.Serialize

/-- A byte string the canonical transaction decoder accepts in full as a
64-byte transaction: it is 64 bytes long and `decodeTx` consumes all of it. This
is the leaf / internal-node collision surface — a merkle node preimage is also
64 bytes, so a value satisfying this is at once a transaction and a node
preimage. -/
def decodesAs64ByteTx (bs : List UInt8) : Bool :=
  bs.length == 64 &&
    match decodeTx bs with
    | some (_, []) => true
    | _ => false

/-- The deserializer-level predicate is exactly "a 64-byte canonical
serialization of some transaction." Both directions are immediate from the
transaction codec laws (`decodeTx_canonical` and `decodeTx_encodeTx`), so the
check is canonical and decidable with no bespoke parser. -/
theorem decodesAs64ByteTx_iff (bs : List UInt8) :
    decodesAs64ByteTx bs = true ↔ bs.length = 64 ∧ ∃ tx : Tx, encodeTx tx = bs := by
  simp only [decodesAs64ByteTx, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hlen, hmatch⟩
    refine ⟨hlen, ?_⟩
    cases hd : decodeTx bs with
    | none => rw [hd] at hmatch; simp at hmatch
    | some p =>
      obtain ⟨tx, tail⟩ := p
      rw [hd] at hmatch
      cases tail with
      | nil => exact ⟨tx, by simpa using (decodeTx_canonical bs tx [] hd).symm⟩
      | cons _ _ => simp at hmatch
  · rintro ⟨hlen, tx, rfl⟩
    have hd : decodeTx (encodeTx tx) = some (tx, []) := by
      simpa using decodeTx_encodeTx tx []
    exact ⟨hlen, by rw [hd]⟩

/-- Every internal-node preimage is exactly 64 bytes — the same width as a
64-byte transaction, which is the entire source of the ambiguity. -/
theorem combine_preimage_length (l r : Hash256) : (l.1 ++ r.1).length = 64 := by
  rw [List.length_append, l.2, r.2]

/-- Rubin's rule as a structural property of the tree: no internal node's
64-byte preimage (`l.root ++ r.root`, the bytes the node hashes) decodes as a
transaction. A `pad` node duplicates its child, so its preimage is
`t.root ++ t.root`; leaves carry no preimage. -/
def Tree.noForbiddenPreimage : Tree → Bool
  | .leaf _ => true
  | .node l r =>
    !decodesAs64ByteTx (l.root.1 ++ r.root.1)
      && l.noForbiddenPreimage && r.noForbiddenPreimage
  | .pad t => !decodesAs64ByteTx (t.root.1 ++ t.root.1) && t.noForbiddenPreimage

/-! ## Length probes (foundational codec-length lemmas) -/

/-- A `UInt8` encodes to one byte. -/
theorem encode_uint8_length (b : UInt8) : (Codec.encode b).length = 1 :=
  encodeBitVecLE_length 1 b.toBitVec

/-- A `UInt32` encodes to four bytes. -/
theorem encode_uint32_length (n : UInt32) : (Codec.encode n).length = 4 :=
  encodeBitVecLE_length 4 n.toBitVec

/-- A `UInt64` encodes to eight bytes. -/
theorem encode_uint64_length (n : UInt64) : (Codec.encode n).length = 8 :=
  encodeBitVecLE_length 8 n.toBitVec

/-- A byte sequence encodes to exactly its own length: each `UInt8` is one byte. -/
theorem encodeElems_uint8_length (xs : List UInt8) :
    (encodeElems xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [encodeElems, List.length_append, List.length_cons, encode_uint8_length, ih]
    omega

/-- A CompactSize count below `253` is a single byte. -/
theorem compactSize_length_lt_253 {n : UInt64} (h : n < 253) :
    (CompactSize.encode n).length = 1 := by
  unfold CompactSize.encode
  rw [if_pos h]
  rfl

/-- A CompactSize count below `253` is a single byte, stated for a `Nat` count
in range (the form the counted-list count takes). -/
theorem compactSize_length_ofNat_lt_253 {n : Nat} (h : n < 253) :
    (CompactSize.encode (UInt64.ofNat n)).length = 1 := by
  apply compactSize_length_lt_253
  have hn : n < 2 ^ 64 := by omega
  have htn : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' hn
  have h253 : (253 : UInt64).toNat = 253 := by decide
  rw [UInt64.lt_iff_toNat_lt, htn, h253]; exact h

/-- An `OutPoint` encodes to 36 bytes: a 32-byte txid and a 4-byte index. -/
theorem encode_outpoint_length (o : OutPoint) : (Codec.encode o).length = 36 := by
  change (Codec.encode o.txid ++ Codec.encode o.vout).length = 36
  rw [List.length_append, Hash256.encode_length, encode_uint32_length]

/-- The length of a CompactSize-prefixed list, split into its count prefix and
its element sequence. -/
theorem encode_countedlist_length {α : Type} [Codec α] (cl : CountedList α) :
    (Codec.encode cl).length =
      (CompactSize.encode (UInt64.ofNat cl.val.length)).length
        + (encodeElems cl.val).length := by
  change (encodeCountedList cl).length = _
  unfold encodeCountedList
  rw [List.length_append]

/-- The encoding of a one-element sequence is just the element's encoding. -/
theorem encodeElems_singleton {α : Type} [Codec α] (x : α) :
    (encodeElems [x]).length = (Codec.encode x).length := by
  simp [encodeElems]

/-- A short script (program length below 253) encodes to a one-byte length
prefix plus its program bytes. -/
theorem encode_script_length_lt_253 {s : Script} (h : s.code.val.length < 253) :
    (Codec.encode s).length = 1 + s.code.val.length := by
  change (encodeCountedList s.code).length = 1 + s.code.val.length
  unfold encodeCountedList
  rw [List.length_append, encodeElems_uint8_length, compactSize_length_ofNat_lt_253 h]

/-- A transaction input with a short scriptSig encodes to 41 bytes plus the
scriptSig length: a 36-byte outpoint, the script (one-byte prefix + bytes), and
a 4-byte sequence. -/
theorem encode_txin_length {i : TxIn} (h : i.scriptSig.code.val.length < 253) :
    (Codec.encode i).length = 41 + i.scriptSig.code.val.length := by
  change (Codec.encode i.prevout
    ++ (Codec.encode i.scriptSig ++ Codec.encode i.sequence)).length = _
  rw [List.length_append, List.length_append, encode_outpoint_length,
    encode_script_length_lt_253 h, encode_uint32_length]
  omega

/-- A transaction output with a short scriptPubKey encodes to 9 bytes plus the
scriptPubKey length: an 8-byte value and the script (one-byte prefix + bytes). -/
theorem encode_txout_length {o : TxOut} (h : o.scriptPubKey.code.val.length < 253) :
    (Codec.encode o).length = 9 + o.scriptPubKey.code.val.length := by
  change (Codec.encode o.value ++ Codec.encode o.scriptPubKey).length = _
  rw [List.length_append, encode_uint64_length, encode_script_length_lt_253 h]
  omega

/-- A transaction body encodes to its 4-byte version, its input vector, its
output vector, and its 4-byte lock time. -/
theorem encode_txbody_length (b : TxBody) :
    (Codec.encode b).length =
      4 + (Codec.encode b.inputs).length + (Codec.encode b.outputs).length + 4 := by
  change (Codec.encode b.version
    ++ (Codec.encode b.inputs
      ++ (Codec.encode b.outputs ++ Codec.encode b.lockTime))).length = _
  rw [List.length_append, List.length_append, List.length_append,
    encode_uint32_length, encode_uint32_length]
  omega

/-- A transaction body in Rubin's forbidden shape: one input, one output, with
scriptSig and scriptPubKey lengths summing to 4. The value/`MoneyRange`
condition is orthogonal — it constrains which bytes appear, not the length. -/
def IsMinimal64Body (b : TxBody) : Prop :=
  ∃ i o, b.inputs.val = [i] ∧ b.outputs.val = [o] ∧
    i.scriptSig.code.val.length + o.scriptPubKey.code.val.length = 4

/-- Soundness of the shape, length side: every body in the forbidden shape
serializes (as a txid preimage) to exactly 64 bytes. This is the "bans only
64-byte preimages" half — a body Rubin's rule forbids is necessarily 64 bytes. -/
theorem encode_length_of_isMinimal64 {b : TxBody} (h : IsMinimal64Body b) :
    (Codec.encode b).length = 64 := by
  obtain ⟨i, o, hi, ho, hsum⟩ := h
  have hss : i.scriptSig.code.val.length < 253 := by omega
  have hspk : o.scriptPubKey.code.val.length < 253 := by omega
  rw [encode_txbody_length, encode_countedlist_length b.inputs,
    encode_countedlist_length b.outputs, hi, ho]
  simp only [List.length_singleton, encodeElems_singleton]
  rw [encode_txin_length hss, encode_txout_length hspk,
    compactSize_length_ofNat_lt_253 (show 1 < 253 by decide)]
  omega

/-! ## Completeness, relative to validity (lower bounds) -/

/-- A CompactSize encoding is always at least one byte. -/
theorem compactSize_length_ge_one (n : UInt64) : 1 ≤ (CompactSize.encode n).length := by
  unfold CompactSize.encode
  split_ifs <;> simp [CompactSize.encodeFixedWidth_length]

/-- The general script length: a CompactSize length prefix plus the program
bytes (no size assumption). -/
theorem encode_script_length_eq (s : Script) :
    (Codec.encode s).length
      = (CompactSize.encode (UInt64.ofNat s.code.val.length)).length + s.code.val.length := by
  change (encodeCountedList s.code).length = _
  unfold encodeCountedList
  rw [List.length_append, encodeElems_uint8_length]

/-- An input's length with the scriptSig factored out (no size assumption). -/
theorem encode_txin_length_eq (i : TxIn) :
    (Codec.encode i).length = 40 + (Codec.encode i.scriptSig).length := by
  change (Codec.encode i.prevout
    ++ (Codec.encode i.scriptSig ++ Codec.encode i.sequence)).length = _
  rw [List.length_append, List.length_append, encode_outpoint_length, encode_uint32_length]
  omega

/-- An output's length with the scriptPubKey factored out (no size assumption). -/
theorem encode_txout_length_eq (o : TxOut) :
    (Codec.encode o).length = 8 + (Codec.encode o.scriptPubKey).length := by
  change (Codec.encode o.value ++ Codec.encode o.scriptPubKey).length = _
  rw [List.length_append, encode_uint64_length]

/-- Every transaction input is at least 41 bytes (a 36-byte outpoint, a
nonempty script prefix, and a 4-byte sequence). -/
theorem encode_txin_length_ge (i : TxIn) : 41 ≤ (Codec.encode i).length := by
  rw [encode_txin_length_eq, encode_script_length_eq]
  have := compactSize_length_ge_one (UInt64.ofNat i.scriptSig.code.val.length)
  omega

/-- Every transaction output is at least 9 bytes (an 8-byte value and a
nonempty script prefix). -/
theorem encode_txout_length_ge (o : TxOut) : 9 ≤ (Codec.encode o).length := by
  rw [encode_txout_length_eq, encode_script_length_eq]
  have := compactSize_length_ge_one (UInt64.ofNat o.scriptPubKey.code.val.length)
  omega

/-- An input sequence is at least 41 bytes per input. -/
theorem encodeElems_txin_length_ge (xs : List TxIn) :
    41 * xs.length ≤ (encodeElems xs).length := by
  induction xs with
  | nil => simp [encodeElems]
  | cons x xs ih =>
    simp only [encodeElems, List.length_append, List.length_cons]
    have := encode_txin_length_ge x
    omega

/-- An output sequence is at least 9 bytes per output. -/
theorem encodeElems_txout_length_ge (xs : List TxOut) :
    9 * xs.length ≤ (encodeElems xs).length := by
  induction xs with
  | nil => simp [encodeElems]
  | cons x xs ih =>
    simp only [encodeElems, List.length_append, List.length_cons]
    have := encode_txout_length_ge x
    omega

/-- Completeness, relative to validity: every body that serializes (as a txid
preimage) to 64 bytes and has at least one input and at least one output is in
Rubin's forbidden shape. So the rule bans *all* 64-byte bodies that could be a
real leaf. The `≠ []` hypotheses are exactly the `vin`/`vout`-nonempty
consensus-validity rules: a 0-input or 0-output body can also be 64 bytes (e.g.
1-input/0-output with a 13-byte scriptSig), but is consensus-invalid, so it can
never appear as a leaf — which is precisely why the narrow rule omitting it is
nonetheless complete over valid transactions. -/
theorem isMinimal64_of_encode_length {b : TxBody}
    (hlen : (Codec.encode b).length = 64)
    (hin : b.inputs.val ≠ []) (hout : b.outputs.val ≠ []) :
    IsMinimal64Body b := by
  have hbody := encode_txbody_length b
  rw [encode_countedlist_length b.inputs, encode_countedlist_length b.outputs] at hbody
  have hcin := compactSize_length_ge_one (UInt64.ofNat b.inputs.val.length)
  have hcout := compactSize_length_ge_one (UInt64.ofNat b.outputs.val.length)
  have hein := encodeElems_txin_length_ge b.inputs.val
  have heout := encodeElems_txout_length_ge b.outputs.val
  have hposin : 0 < b.inputs.val.length := List.length_pos_of_ne_nil hin
  have hposout : 0 < b.outputs.val.length := List.length_pos_of_ne_nil hout
  have hnin : b.inputs.val.length = 1 := by omega
  have hnout : b.outputs.val.length = 1 := by omega
  obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hnin
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.mp hnout
  refine ⟨i, o, hi, ho, ?_⟩
  rw [hi, ho] at hbody
  simp only [List.length_singleton, encodeElems_singleton] at hbody
  rw [compactSize_length_ofNat_lt_253 (show 1 < 253 by decide), encode_txin_length_eq i,
    encode_txout_length_eq o, encode_script_length_eq i.scriptSig,
    encode_script_length_eq o.scriptPubKey] at hbody
  have hcsSS := compactSize_length_ge_one (UInt64.ofNat i.scriptSig.code.val.length)
  have hcsSPK := compactSize_length_ge_one (UInt64.ofNat o.scriptPubKey.code.val.length)
  rw [compactSize_length_ofNat_lt_253 (show i.scriptSig.code.val.length < 253 by omega),
    compactSize_length_ofNat_lt_253 (show o.scriptPubKey.code.val.length < 253 by omega)] at hbody
  omega

/-- The exact length characterization: a transaction body with at least one
input and one output serializes to 64 bytes iff it is in Rubin's forbidden
shape. Soundness and completeness in one statement, modulo the `vin`/`vout`
nonemptiness that the merkle preimage's being a real leaf already guarantees. -/
theorem isMinimal64_iff_encode_length {b : TxBody}
    (hin : b.inputs.val ≠ []) (hout : b.outputs.val ≠ []) :
    IsMinimal64Body b ↔ (Codec.encode b).length = 64 :=
  ⟨encode_length_of_isMinimal64, fun h => isMinimal64_of_encode_length h hin hout⟩

/-! ## The explicit byte layout (bridge to Rubin's fixed-offset check) -/

/-- A single byte encodes to itself. -/
theorem encode_uint8_eq (b : UInt8) : Codec.encode b = [b] := by
  change encodeBitVecLE 1 b.toBitVec = [b]
  simp [encodeBitVecLE]

/-- A byte sequence encodes to itself. -/
theorem encodeElems_uint8_eq (xs : List UInt8) : encodeElems xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [encodeElems, encode_uint8_eq, ih, List.singleton_append]

/-- The byte layout of a script: its CompactSize length prefix then its bytes. -/
theorem encode_script_eq (s : Script) :
    Codec.encode s
      = CompactSize.encode (UInt64.ofNat s.code.val.length) ++ s.code.val := by
  change encodeCountedList s.code = _
  unfold encodeCountedList
  rw [encodeElems_uint8_eq]

/-- The byte layout of a one-element vector: a `0x01` count then the element. -/
theorem encode_singleton_countedlist {α : Type} [Codec α] {cl : CountedList α} {x : α}
    (h : cl.val = [x]) :
    Codec.encode cl = CompactSize.encode (UInt64.ofNat 1) ++ Codec.encode x := by
  change encodeCountedList cl = _
  unfold encodeCountedList
  rw [h]
  simp only [List.length_singleton, encodeElems, List.append_nil]

/-- The byte layout of an input: outpoint, scriptSig, sequence. -/
theorem encode_txin_eq (i : TxIn) :
    Codec.encode i
      = Codec.encode i.prevout ++ Codec.encode i.scriptSig ++ Codec.encode i.sequence := by
  change Codec.encode i.prevout
    ++ (Codec.encode i.scriptSig ++ Codec.encode i.sequence) = _
  simp only [List.append_assoc]

/-- The byte layout of an output: value, scriptPubKey. -/
theorem encode_txout_eq (o : TxOut) :
    Codec.encode o = Codec.encode o.value ++ Codec.encode o.scriptPubKey := by
  rfl

/-- The byte layout of a body: version, inputs, outputs, lock time. -/
theorem encode_txbody_eq (b : TxBody) :
    Codec.encode b = Codec.encode b.version ++ Codec.encode b.inputs
      ++ Codec.encode b.outputs ++ Codec.encode b.lockTime := by
  change Codec.encode b.version
    ++ (Codec.encode b.inputs ++ (Codec.encode b.outputs ++ Codec.encode b.lockTime)) = _
  simp only [List.append_assoc]

/-- A CompactSize count below `253` is the single byte carrying that value. -/
theorem compactSize_encode_ofNat_eq {n : Nat} (h : n < 253) :
    CompactSize.encode (UInt64.ofNat n) = [(UInt64.ofNat n).toUInt8] := by
  have hlt : UInt64.ofNat n < 253 := by
    have hn : n < 2 ^ 64 := by omega
    have htn : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' hn
    have h253 : (253 : UInt64).toNat = 253 := by decide
    rw [UInt64.lt_iff_toNat_lt, htn, h253]; exact h
  unfold CompactSize.encode
  rw [if_pos hlt]

/-- The full explicit byte layout of a minimal 1-in/1-out body, all the way down
to its bytes — the layout Rubin's fixed-offset check reads. -/
theorem encode_oneInOneOut_form {b : TxBody} {i : TxIn} {o : TxOut}
    (hi : b.inputs.val = [i]) (ho : b.outputs.val = [o]) :
    Codec.encode b =
      Codec.encode b.version
        ++ CompactSize.encode (UInt64.ofNat 1)
        ++ Codec.encode i.prevout
        ++ CompactSize.encode (UInt64.ofNat i.scriptSig.code.val.length)
        ++ i.scriptSig.code.val
        ++ Codec.encode i.sequence
        ++ CompactSize.encode (UInt64.ofNat 1)
        ++ Codec.encode o.value
        ++ CompactSize.encode (UInt64.ofNat o.scriptPubKey.code.val.length)
        ++ o.scriptPubKey.code.val
        ++ Codec.encode b.lockTime := by
  rw [encode_txbody_eq, encode_singleton_countedlist hi, encode_singleton_countedlist ho,
    encode_txin_eq, encode_txout_eq, encode_script_eq i.scriptSig, encode_script_eq o.scriptPubKey]
  simp only [List.append_assoc]

/-! ## Rubin's forbidden preimage, and its equivalence to the minimal shape -/

/-- The structural property Rubin's fixed-offset byte check decides: `P` is the
64-byte serialization of a one-input/one-output non-witness transaction whose
scriptSig and scriptPubKey lengths sum to 4. His conjunct (`P[4] = 0x01`,
`P[41] = x`, `P[46+x] = 0x01`, `P[55+x] = 4-x`) reads exactly the marker and
length bytes of this layout; here it is captured as the layout itself, so the
equivalence to the modeled transaction is exact rather than offset-by-offset.
(`MoneyRange` on the value field is a separable conjunct; it constrains which
8-byte value appears, not the shape, and is omitted here.) -/
def IsForbiddenPreimage (P : List UInt8) : Prop :=
  ∃ (v : UInt32) (op : OutPoint) (ss : List UInt8) (seq : UInt32)
    (val : UInt64) (spk : List UInt8) (lt : UInt32),
    ss.length + spk.length = 4 ∧
    P = Codec.encode v ++ CompactSize.encode (UInt64.ofNat 1) ++ Codec.encode op
      ++ CompactSize.encode (UInt64.ofNat ss.length) ++ ss ++ Codec.encode seq
      ++ CompactSize.encode (UInt64.ofNat 1) ++ Codec.encode val
      ++ CompactSize.encode (UInt64.ofNat spk.length) ++ spk ++ Codec.encode lt

/-- **Rubin's conjunct is equivalent to the minimal shape.** A byte string is a
forbidden preimage iff it is the serialization of a body in the forbidden shape.
With `isMinimal64_iff_encode_length`, this pins the forbidden preimages to
exactly the 64-byte serializations of valid transaction bodies. -/
theorem isForbiddenPreimage_iff (P : List UInt8) :
    IsForbiddenPreimage P ↔ ∃ b : TxBody, IsMinimal64Body b ∧ Codec.encode b = P := by
  constructor
  · rintro ⟨v, op, ss, seq, val, spk, lt, hsum, hP⟩
    have hss : ss.length < 2 ^ 64 := by omega
    have hspk : spk.length < 2 ^ 64 := by omega
    have h1 : ([(0 : Nat)]).length < 2 ^ 64 := by simp
    refine ⟨⟨v, ⟨[⟨op, ⟨⟨ss, hss⟩⟩, seq⟩], by simp⟩, ⟨[⟨val, ⟨⟨spk, hspk⟩⟩⟩], by simp⟩, lt⟩,
      ⟨_, _, rfl, rfl, hsum⟩, ?_⟩
    rw [encode_oneInOneOut_form rfl rfl]
    exact hP.symm
  · rintro ⟨b, ⟨i, o, hi, ho, hsum⟩, rfl⟩
    exact ⟨b.version, i.prevout, i.scriptSig.code.val, i.sequence, o.value,
      o.scriptPubKey.code.val, b.lockTime, hsum, encode_oneInOneOut_form hi ho⟩

/-- Capstone: a byte string is a forbidden preimage iff it is the 64-byte
serialization of a transaction body with at least one input and one output —
i.e. exactly the txid preimages a real leaf could collide with. Soundness
("only 64-byte"), completeness ("all valid 64-byte"), and the conjunct ⟺ shape
bridge, in one statement. The `≠ []` conditions are the vin/vout-nonempty
validity rules the narrow rule relies on. -/
theorem isForbiddenPreimage_iff_encode_valid (P : List UInt8) :
    IsForbiddenPreimage P ↔
      ∃ b : TxBody, b.inputs.val ≠ [] ∧ b.outputs.val ≠ [] ∧
        (Codec.encode b).length = 64 ∧ Codec.encode b = P := by
  rw [isForbiddenPreimage_iff]
  constructor
  · rintro ⟨b, hmin, hP⟩
    have hlen := encode_length_of_isMinimal64 hmin
    obtain ⟨i, o, hi, ho, _⟩ := hmin
    exact ⟨b, by rw [hi]; simp, by rw [ho]; simp, hlen, hP⟩
  · rintro ⟨b, hin, hout, hlen, hP⟩
    exact ⟨b, isMinimal64_of_encode_length hlen hin hout, hP⟩

/-! ## Rubin's literal fixed-offset byte check -/

/-- The byte at the boundary of an explicit `prefix ++ marker :: rest` layout. -/
theorem getElem?_append_cons {A C : List UInt8} {k : Nat} {b : UInt8}
    (hk : A.length = k) : (A ++ b :: C)[k]? = some b := by
  subst hk
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

/-- A CompactSize-marker byte for a small value reads back as that value. -/
theorem toNat_compactSizeByte {n : Nat} (h : n < 256) :
    ((UInt64.ofNat n).toUInt8).toNat = n := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_ofNat_of_lt' (show n < 2 ^ 64 by omega)]
  omega

/-- Rubin's conjunct in his literal fixed-offset form: a 64-byte string whose
input-count byte is `0x01`, whose scriptSig-length byte `x` is at most 4, whose
output-count byte (at `46+x`) is `0x01`, and whose scriptPubKey-length byte (at
`55+x`) is `4-x`. Byte values are read as naturals (`.map UInt8.toNat`), matching
the count/length semantics. (`MoneyRange` on the value field is the separable
remaining conjunct.) -/
def ForbiddenPreimageBytes (P : List UInt8) : Prop :=
  P.length = 64 ∧ ∃ x : Nat, x ≤ 4 ∧
    (P[4]?).map UInt8.toNat = some 1 ∧
    (P[41]?).map UInt8.toNat = some x ∧
    (P[46 + x]?).map UInt8.toNat = some 1 ∧
    (P[55 + x]?).map UInt8.toNat = some (4 - x)

/-- Every fixed-width little-endian field is in the image of its encoder. -/
theorem exists_encodeBitVecLE {n : Nat} {L : List UInt8} (h : L.length = n) :
    ∃ bv : BitVec (8 * n), encodeBitVecLE n bv = L := by
  obtain ⟨bv, hbv⟩ := decodeBitVecLE_of_le_length n L (by omega)
  have hdrop : L.drop n = [] := by rw [← h]; exact List.drop_length
  rw [hdrop] at hbv
  exact ⟨bv, by simpa using (decodeBitVecLE_canonical n L bv [] hbv).symm⟩

theorem exists_encode_uint32 {L : List UInt8} (h : L.length = 4) :
    ∃ v : UInt32, Codec.encode v = L := by
  obtain ⟨bv, hbv⟩ := exists_encodeBitVecLE (n := 4) h; exact ⟨UInt32.ofBitVec bv, hbv⟩

theorem exists_encode_uint64 {L : List UInt8} (h : L.length = 8) :
    ∃ v : UInt64, Codec.encode v = L := by
  obtain ⟨bv, hbv⟩ := exists_encodeBitVecLE (n := 8) h; exact ⟨UInt64.ofBitVec bv, hbv⟩

theorem exists_encode_hash256 {L : List UInt8} (h : L.length = 32) :
    ∃ d : Hash256, Codec.encode d = L := ⟨⟨L, h⟩, rfl⟩

theorem exists_encode_outpoint {L : List UInt8} (h : L.length = 36) :
    ∃ op : OutPoint, Codec.encode op = L := by
  obtain ⟨d, hd⟩ := exists_encode_hash256 (L := L.take 32) (by rw [List.length_take]; omega)
  obtain ⟨vout, hvout⟩ := exists_encode_uint32 (L := L.drop 32) (by rw [List.length_drop]; omega)
  exact ⟨⟨d, vout⟩, by change Codec.encode d ++ Codec.encode vout = L; rw [hd, hvout,
    List.take_append_drop]⟩

/-- A marker/length byte read as a natural pins down the byte. -/
theorem markerByte_eq {P : List UInt8} {k val : Nat} (hk : k < P.length)
    (hval : (P[k]?).map UInt8.toNat = some val) (hb : val < 256) :
    P[k] = (UInt64.ofNat val).toUInt8 := by
  rw [List.getElem?_eq_getElem hk, Option.map_some, Option.some.injEq] at hval
  exact UInt8.toNat_inj.mp (by rw [toNat_compactSizeByte hb]; exact hval)

/-- One byte off the front of a drop. -/
theorem drop_take_one {P : List UInt8} {k : Nat} (hk : k < P.length) :
    (P.drop k).take 1 = [P[k]] := by
  rw [List.take_one, List.head?_drop, List.getElem?_eq_getElem hk]; rfl

/-- Merge two adjacent `take` slices of `P`. -/
theorem take_merge {P : List UInt8} {a b c : Nat} (hc : a + b = c) :
    P.take a ++ (P.drop a).take b = P.take c := by
  rw [← List.take_add, hc]

/-- **Rubin's literal fixed-offset check fires on his forbidden preimages.**
Every byte string that is the serialization of a body in the forbidden shape
satisfies the byte-index conjunct (`P[4]=0x01`, `P[41]=x`, `P[46+x]=0x01`,
`P[55+x]=4-x`), read as natural-number values. -/
theorem forbiddenPreimageBytes_of_isForbidden {P : List UInt8}
    (h : IsForbiddenPreimage P) : ForbiddenPreimageBytes P := by
    obtain ⟨v, op, ss, seq, val, spk, lt, hsum, hP⟩ := h
    have lev := encode_uint32_length v
    have lop := encode_outpoint_length op
    have lseq := encode_uint32_length seq
    have lval := encode_uint64_length val
    have llt := encode_uint32_length lt
    rw [compactSize_encode_ofNat_eq (show (1 : Nat) < 253 by decide),
      compactSize_encode_ofNat_eq (show ss.length < 253 by omega),
      compactSize_encode_ofNat_eq (show spk.length < 253 by omega)] at hP
    have hlen : P.length = 64 := by
      rw [hP]; simp only [List.length_append, List.length_cons, List.length_nil,
        lev, lop, lseq, lval, llt]; omega
    refine ⟨hlen, ss.length, by omega, ?_, ?_, ?_, ?_⟩
    · -- input-count byte at position 4
      have hg : P = Codec.encode v ++ (UInt64.ofNat 1).toUInt8 ::
          (Codec.encode op ++ (UInt64.ofNat ss.length).toUInt8 :: (ss ++ Codec.encode seq
            ++ (UInt64.ofNat 1).toUInt8 :: (Codec.encode val
            ++ (UInt64.ofNat spk.length).toUInt8 :: (spk ++ Codec.encode lt)))) := by
        rw [hP]; simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [hg, getElem?_append_cons (k := 4) (by rw [lev])]
      decide
    · -- scriptSig-length byte at position 41
      have hg : P = (Codec.encode v ++ (UInt64.ofNat 1).toUInt8 :: Codec.encode op)
          ++ (UInt64.ofNat ss.length).toUInt8 :: (ss ++ Codec.encode seq
            ++ (UInt64.ofNat 1).toUInt8 :: (Codec.encode val
            ++ (UInt64.ofNat spk.length).toUInt8 :: (spk ++ Codec.encode lt))) := by
        rw [hP]; simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [hg, getElem?_append_cons (k := 41)
        (by simp only [List.length_append, List.length_cons]; omega),
        Option.map_some, toNat_compactSizeByte (by omega)]
    · -- output-count byte at position 46 + x
      have hg : P = (Codec.encode v ++ (UInt64.ofNat 1).toUInt8 ::
          (Codec.encode op ++ (UInt64.ofNat ss.length).toUInt8 :: (ss ++ Codec.encode seq)))
          ++ (UInt64.ofNat 1).toUInt8 :: (Codec.encode val
            ++ (UInt64.ofNat spk.length).toUInt8 :: (spk ++ Codec.encode lt)) := by
        rw [hP]; simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [hg, getElem?_append_cons (k := 46 + ss.length)
        (by simp only [List.length_append, List.length_cons]; omega)]
      decide
    · -- scriptPubKey-length byte at position 55 + x
      have hg : P = (Codec.encode v ++ (UInt64.ofNat 1).toUInt8 ::
          (Codec.encode op ++ (UInt64.ofNat ss.length).toUInt8 :: (ss ++ Codec.encode seq
            ++ (UInt64.ofNat 1).toUInt8 :: Codec.encode val)))
          ++ (UInt64.ofNat spk.length).toUInt8 :: (spk ++ Codec.encode lt) := by
        rw [hP]; simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [hg, getElem?_append_cons (k := 55 + ss.length)
        (by simp only [List.length_append, List.length_cons]; omega),
        Option.map_some, toNat_compactSizeByte (by omega)]
      congr 1
      omega

/-- **The converse: Rubin's offset conjunct forces the structure.** A 64-byte
string satisfying the fixed-offset byte check is the serialization of a body in
the forbidden shape. The fields are reconstructed from byte slices, and the
slices reassemble to `P` by a `take`/`drop` telescope. -/
theorem isForbidden_of_forbiddenPreimageBytes {P : List UInt8}
    (h : ForbiddenPreimageBytes P) : IsForbiddenPreimage P := by
  obtain ⟨hlen, x, hx4, h4, h41, h46, h55⟩ := h
  obtain ⟨v, hv⟩ := exists_encode_uint32 (L := P.take 4) (by rw [List.length_take]; omega)
  obtain ⟨op, hop⟩ := exists_encode_outpoint (L := (P.drop 5).take 36)
    (by rw [List.length_take, List.length_drop]; omega)
  obtain ⟨seq, hseq⟩ := exists_encode_uint32 (L := (P.drop (42 + x)).take 4)
    (by rw [List.length_take, List.length_drop]; omega)
  obtain ⟨val, hval⟩ := exists_encode_uint64 (L := (P.drop (47 + x)).take 8)
    (by rw [List.length_take, List.length_drop]; omega)
  obtain ⟨lt, hlt⟩ := exists_encode_uint32 (L := P.drop 60) (by rw [List.length_drop]; omega)
  have hsslen : ((P.drop 42).take x).length = x := by rw [List.length_take, List.length_drop]; omega
  have hspklen : ((P.drop (56 + x)).take (4 - x)).length = 4 - x := by
    rw [List.length_take, List.length_drop]; omega
  have c4 : CompactSize.encode (UInt64.ofNat 1) = (P.drop 4).take 1 := by
    rw [drop_take_one (show 4 < P.length by omega), compactSize_encode_ofNat_eq (by decide),
      markerByte_eq (show 4 < P.length by omega) h4 (by decide)]
  have c41 : CompactSize.encode (UInt64.ofNat x) = (P.drop 41).take 1 := by
    rw [drop_take_one (show 41 < P.length by omega), compactSize_encode_ofNat_eq (by omega),
      markerByte_eq (show 41 < P.length by omega) h41 (by omega)]
  have c46 : CompactSize.encode (UInt64.ofNat 1) = (P.drop (46 + x)).take 1 := by
    rw [drop_take_one (show 46 + x < P.length by omega), compactSize_encode_ofNat_eq (by decide),
      markerByte_eq (show 46 + x < P.length by omega) h46 (by decide)]
  have c55 : CompactSize.encode (UInt64.ofNat (4 - x)) = (P.drop (55 + x)).take 1 := by
    rw [drop_take_one (show 55 + x < P.length by omega), compactSize_encode_ofNat_eq (by omega),
      markerByte_eq (show 55 + x < P.length by omega) h55 (by omega)]
  refine ⟨v, op, (P.drop 42).take x, seq, val, (P.drop (56 + x)).take (4 - x), lt,
    by rw [hsslen, hspklen]; omega, ?_⟩
  rw [hv, hop, hseq, hval, hlt, hsslen, hspklen]
  nth_rewrite 1 [c4]
  rw [take_merge (show 4 + 1 = 5 from rfl), take_merge (show 5 + 36 = 41 from rfl), c41,
    take_merge (show 41 + 1 = 42 from rfl), take_merge (show 42 + x = 42 + x from rfl),
    take_merge (show (42 + x) + 4 = 46 + x by omega)]
  nth_rewrite 1 [c46]
  rw [take_merge (show (46 + x) + 1 = 47 + x by omega),
    take_merge (show (47 + x) + 8 = 55 + x by omega), c55,
    take_merge (show (55 + x) + 1 = 56 + x by omega),
    take_merge (show (56 + x) + (4 - x) = 60 by omega), List.take_append_drop]

/-- **Rubin's literal fixed-offset conjunct is equivalent to his forbidden
preimage** — the byte-index check and the structural property decide the same
set of 64-byte strings. -/
theorem forbiddenPreimageBytes_iff (P : List UInt8) :
    ForbiddenPreimageBytes P ↔ IsForbiddenPreimage P :=
  ⟨isForbidden_of_forbiddenPreimageBytes, forbiddenPreimageBytes_of_isForbidden⟩

end BtcVerified.Merkle
