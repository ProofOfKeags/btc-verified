import BtcVerified.Transaction.Txid
import BtcVerified.Chainstate.UtxoSet
/-!
  # The uniform UTXO action of a transaction

  What a transaction *does* to the UTXO set: erase the outpoints its inputs
  consume (`TxBody.spends`), insert one coin per output, keyed by txid and
  output index (`TxBody.creates`). Every transaction — coinbase included —
  acts through this one function. The coinbase's sole input names the null
  outpoint, which no set contains, so its erase is vacuous: the action
  needs no coinbase case. Validity is *not* checked here; guards are
  consensus rules, stated over this action in a later layer, and the
  theorems below carry as hypotheses exactly the facts those guards will
  supply.

  The split of responsibilities is deliberate on both axes. `spends` and
  `creates` are functions of the transaction *alone* — what it consumes and
  what it brings into existence — while `Provenance` is context the
  transaction cannot know (coinbase-ness is positional, a property of
  sitting first in a block), so the caller supplies it to `apply`, the one
  place transaction meets context, where it is stamped onto every created
  coin. And the action is over `TxBody`, not `Tx`: witnesses never touch
  the UTXO set — they exist only for script verification, which enters
  later as a guard parameter.

  One width wrinkle, inherited from the wire: `OutPoint.vout` is a
  `UInt32`, while a `CountedList` structurally admits up to `2⁶⁴ − 1`
  outputs, so output indexing wraps for a (physically impossible)
  transaction with more than `2³²` outputs. The action stays total; the
  characterization theorems take `body.outputs.val.length ≤ 2 ^ 32` where
  created-key distinctness is needed, and a block-size guard later
  discharges that bound for any transaction a valid block can contain.

  Checked claims:

  * `UtxoSet.lookup_apply_of_mem_creates`: after applying a transaction
    (≤ 2³² outputs), lookup at a created outpoint finds that output as a
    coin stamped with the supplied provenance.
  * `UtxoSet.lookup_apply_output`: the index form — output `i` sits at the
    outpoint keyed by the txid and `i`.
  * `UtxoSet.lookup_apply_of_mem_spends`: lookup at a spent outpoint the
    transaction does not re-create returns `none`.
  * `UtxoSet.lookup_apply_of_notMem`: lookup at an outpoint the
    transaction neither spends nor creates is untouched.
  * `UtxoSet.totalValue_apply`: the accounting identity — the new total
    plus the values spent equals the old total plus the values created
    (subtraction-free, in `Nat`).
-/

namespace BtcVerified

/-- The outpoints a transaction's inputs consume — the erase half of its
action on the UTXO set. -/
def TxBody.spends (body : TxBody) : List OutPoint :=
  body.inputs.val.map fun input => input.prevout

/-- The keyed outputs a transaction brings into existence — the insert half
of its action on the UTXO set: output `i`, at the outpoint keyed by the
transaction's txid and `i`. A function of the transaction alone: the
provenance the UTXO set stores alongside each output is context, stamped on
by `UtxoSet.apply`. -/
def TxBody.creates (body : TxBody) : List (OutPoint × TxOut) :=
  body.outputs.val.zipIdx.map fun entry =>
    (⟨body.txid, UInt32.ofNat entry.2⟩, entry.1)

/-- The uniform action of a transaction on the UTXO set: erase what it
spends, then insert what it creates, each created output stamped with the
supplied provenance. Total and guard-free — validity lives in the consensus
layer above. -/
def UtxoSet.apply (utxos : UtxoSet) (provenance : Provenance) (body : TxBody) : UtxoSet :=
  (utxos.spend body.spends).create
    (body.creates.map fun entry => (entry.1, ⟨entry.2, provenance⟩))

/-! ## The created outpoints -/

/-- Every outpoint a transaction creates carries the transaction's txid. -/
theorem TxBody.txid_of_mem_creates {body : TxBody} {o : OutPoint}
    (h : o ∈ body.creates.map Prod.fst) : o.txid = body.txid := by
  simp only [creates, List.map_map, List.mem_map] at h
  obtain ⟨entry, -, rfl⟩ := h
  rfl

/-- With at most `2 ^ 32` outputs, the created outpoints are pairwise
distinct: the shared txid pins the first component, and indices below the
`vout` width embed injectively into `UInt32`. -/
theorem TxBody.creates_keys_nodup (body : TxBody)
    (houtputs : body.outputs.val.length ≤ 2 ^ 32) :
    (body.creates.map Prod.fst).Nodup := by
  rw [creates, List.map_map]
  refine List.Nodup.map_on ?_ (List.Nodup.of_map _ (List.nodup_zipIdx_map_snd _))
  intro x hx y hy hxy
  obtain ⟨hxlt, hxget⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hx)
  obtain ⟨hylt, hyget⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hy)
  have hv : (UInt32.ofNat x.2).toNat = (UInt32.ofNat y.2).toNat :=
    congrArg (fun o : OutPoint => o.vout.toNat) hxy
  rw [UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hxlt houtputs),
    UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hylt houtputs)] at hv
  have hfst : x.1 = y.1 := by
    rw [← hxget, ← hyget]
    simp [hv]
  exact Prod.ext_iff.mpr ⟨hfst, hv⟩

/-- Output `i` of a transaction appears among its created outputs, at the
outpoint keyed by the txid and `i`. -/
theorem TxBody.mem_creates (body : TxBody) {i : Nat}
    (hi : i < body.outputs.val.length) :
    (⟨body.txid, UInt32.ofNat i⟩, body.outputs.val[i]) ∈ body.creates := by
  rw [creates]
  have hz : ((body.outputs.val[i], i) : TxOut × Nat) ∈ body.outputs.val.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  exact List.mem_map_of_mem hz

/-- The values of the outputs a transaction creates are the values of its
outputs, in order. -/
theorem TxBody.creates_values (body : TxBody) :
    body.creates.map (fun entry => entry.2.value.toNat)
      = body.outputs.val.map fun output => output.value.toNat := by
  conv_rhs => rw [← List.zipIdx_map_fst 0 body.outputs.val]
  rw [creates, List.map_map, List.map_map]
  rfl

/-- Stamping a provenance onto a transaction's created outputs re-keys
nothing: the stamped list's outpoints are exactly `creates`'s outpoints. -/
theorem TxBody.creates_stamped_keys (body : TxBody) (provenance : Provenance) :
    ((body.creates.map fun entry =>
        (entry.1, (⟨entry.2, provenance⟩ : Coin))).map Prod.fst)
      = body.creates.map Prod.fst := by
  rw [List.map_map]
  rfl

/-! ## The lookup characterization -/

/-- After applying a transaction with at most `2 ^ 32` outputs, lookup at
an outpoint it creates finds that output as a coin stamped with the
supplied provenance. -/
theorem UtxoSet.lookup_apply_of_mem_creates {utxos : UtxoSet} {provenance : Provenance}
    {body : TxBody} (houtputs : body.outputs.val.length ≤ 2 ^ 32)
    {o : OutPoint} {out : TxOut} (hmem : (o, out) ∈ body.creates) :
    (utxos.apply provenance body).lookup o = some ⟨out, provenance⟩ := by
  have hkeys : ((body.creates.map fun entry =>
      (entry.1, (⟨entry.2, provenance⟩ : Coin))).map Prod.fst).Nodup := by
    rw [TxBody.creates_stamped_keys]
    exact body.creates_keys_nodup houtputs
  exact lookup_create_of_mem hkeys (List.mem_map_of_mem hmem)

/-- After applying a transaction with at most `2 ^ 32` outputs, its output
`i` sits at the outpoint keyed by the txid and `i`, stamped with the
supplied provenance. -/
theorem UtxoSet.lookup_apply_output {utxos : UtxoSet} {provenance : Provenance}
    {body : TxBody} (houtputs : body.outputs.val.length ≤ 2 ^ 32) {i : Nat}
    (hi : i < body.outputs.val.length) :
    (utxos.apply provenance body).lookup ⟨body.txid, UInt32.ofNat i⟩
      = some ⟨body.outputs.val[i], provenance⟩ :=
  lookup_apply_of_mem_creates houtputs (body.mem_creates hi)

/-- After applying a transaction, lookup at a spent outpoint the
transaction does not re-create returns `none`. (`TxBody.txid_of_mem_creates`
discharges the re-creation hypothesis whenever the outpoint's txid differs
from the transaction's.) -/
theorem UtxoSet.lookup_apply_of_mem_spends {utxos : UtxoSet} {provenance : Provenance}
    {body : TxBody} {o : OutPoint} (hspent : o ∈ body.spends)
    (hnew : o ∉ body.creates.map Prod.fst) :
    (utxos.apply provenance body).lookup o = none := by
  rw [← TxBody.creates_stamped_keys body provenance] at hnew
  have h := lookup_create_of_notMem (utxos := utxos.spend body.spends) hnew
  rw [lookup_spend_of_mem hspent] at h
  exact h

/-- Lookup at an outpoint a transaction neither spends nor creates is
untouched by applying it. -/
theorem UtxoSet.lookup_apply_of_notMem {utxos : UtxoSet} {provenance : Provenance}
    {body : TxBody} {o : OutPoint} (hspends : o ∉ body.spends)
    (hnew : o ∉ body.creates.map Prod.fst) :
    (utxos.apply provenance body).lookup o = utxos.lookup o := by
  rw [← TxBody.creates_stamped_keys body provenance] at hnew
  have h := lookup_create_of_notMem (utxos := utxos.spend body.spends) hnew
  rw [lookup_spend_of_notMem hspends] at h
  exact h

/-! ## The accounting identity -/

/-- The accounting identity of the uniform action, subtraction-free in
`Nat`: after applying a transaction, the total value plus the values spent
equals the old total plus the values created. The hypotheses — distinct,
present spends; created keys fresh once the spends are erased; at most
`2 ^ 32` outputs — are exactly the facts the transaction-validity guards
supply, so the gated conservation theorems specialize this directly. -/
theorem UtxoSet.totalValue_apply {utxos : UtxoSet} {provenance : Provenance}
    {body : TxBody} (houtputs : body.outputs.val.length ≤ 2 ^ 32)
    (hnodup : body.spends.Nodup) (hmem : ∀ o ∈ body.spends, o ∈ utxos)
    (hfresh : ∀ o ∈ body.creates.map Prod.fst, o ∉ utxos.spend body.spends) :
    totalValue (utxos.apply provenance body) + (body.spends.map utxos.valueAt).sum
      = utxos.totalValue
        + (body.outputs.val.map fun output => output.value.toNat).sum := by
  have hkeys : ((body.creates.map fun entry =>
      (entry.1, (⟨entry.2, provenance⟩ : Coin))).map Prod.fst).Nodup := by
    rw [TxBody.creates_stamped_keys]
    exact body.creates_keys_nodup houtputs
  have hfresh' : ∀ e ∈ (body.creates.map fun entry =>
      (entry.1, (⟨entry.2, provenance⟩ : Coin))), e.1 ∉ utxos.spend body.spends := by
    intro e he
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp he
    exact hfresh entry.1 (List.mem_map_of_mem hentry)
  have hcreate := totalValue_create (utxos := utxos.spend body.spends) hkeys hfresh'
  have hspend := totalValue_spend hnodup hmem
  have hvals : ((body.creates.map fun entry =>
      (entry.1, (⟨entry.2, provenance⟩ : Coin))).map
        fun entry => entry.2.output.value.toNat)
      = body.outputs.val.map fun output => output.value.toNat := by
    rw [List.map_map, ← body.creates_values]
    rfl
  have hsum := congrArg List.sum hvals
  change totalValue ((utxos.spend body.spends).create
    (body.creates.map fun entry => (entry.1, ⟨entry.2, provenance⟩))) + _ = _
  omega

end BtcVerified
