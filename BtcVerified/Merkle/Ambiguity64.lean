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

end BtcVerified.Merkle
