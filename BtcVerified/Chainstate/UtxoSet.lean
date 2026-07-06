import BtcVerified.Ext.Finmap
import BtcVerified.Transaction.OutPoint
import BtcVerified.Chainstate.Coin
/-!
  # The UTXO set

  The chainstate's accumulator: the finite map from outpoints to the coins
  they name. This module is the *machine*, not the rules — it defines the
  map, its two primitive bulk operations (`spend` erases a list of
  outpoints, `create` inserts a list of keyed coins), and the value
  accounting, all guard-free and total. Consensus guards are stated over
  this machine later, in `Consensus/`; nothing here decides validity.

  The spec representation is Mathlib's `Finmap` — extensional equality and
  a ready `lookup`/`insert`/`erase` API. Efficiency is a transport concern
  for `Impl/`, exactly as `List UInt8` versus `ByteArray` on the
  serialization side.

  `totalValue` sums in `Nat`, not `UInt64`: `UInt64` addition wraps, and
  the argument that Bitcoin totals stay below 2⁶⁴ is a consequence of
  *guards* — which do not exist at this layer. The `Nat` sum makes the
  accounting identities unconditional.

  Checked claims:

  * `UtxoSet.lookup_spend_of_mem` / `UtxoSet.lookup_spend_of_notMem`: after
    spending a list of outpoints, lookup returns `none` on the list's
    members and is untouched elsewhere.
  * `UtxoSet.spend_perm`: spending is order-insensitive — permuted spend
    lists produce the same set. Order-freedom within a transaction is a
    theorem of the machine, not a type-level restatement.
  * `UtxoSet.mem_spend`: membership after a spend is membership before it,
    minus the spent list.
  * `UtxoSet.lookup_create_of_notMem` / `UtxoSet.lookup_create_of_mem`:
    after creating a list of keyed coins (keys distinct), lookup finds
    exactly the listed coin at each listed key and is untouched elsewhere.
  * `UtxoSet.mem_create`: membership after a create is membership before
    it, plus the created keys.
  * `UtxoSet.totalValue_insert` / `UtxoSet.totalValue_erase`: inserting a
    fresh coin adds its value to the total; erasing a present outpoint
    removes the value held there.
  * `UtxoSet.totalValue_spend`: spending distinct, present outpoints
    removes exactly the sum of the values held at them.
  * `UtxoSet.totalValue_create`: creating coins at distinct, fresh keys
    adds exactly the sum of their values.
-/

namespace BtcVerified

/-- The UTXO set: the finite map from outpoints to the coins they name.
The chainstate accumulator every transaction acts on and every stateful
consensus guard reads. -/
abbrev UtxoSet := Finmap fun _ : OutPoint => Coin

/-- The satoshi value the set holds at an outpoint — zero when the outpoint
is absent. The accounting identities sum this over a transaction's spends. -/
def UtxoSet.valueAt (utxos : UtxoSet) (outpoint : OutPoint) : Nat :=
  ((utxos.lookup outpoint).map fun coin => coin.output.value.toNat).getD 0

/-- The total satoshi value held across the whole set, as a `Nat` sum —
`UInt64` sums wrap, and no guard bounds the total at this layer. -/
def UtxoSet.totalValue (utxos : UtxoSet) : Nat :=
  (utxos.entries.map fun entry => entry.2.output.value.toNat).sum

/-- Erase every outpoint in a list — the spend half of a transaction's
action on the set. -/
def UtxoSet.spend (utxos : UtxoSet) (outpoints : List OutPoint) : UtxoSet :=
  outpoints.foldl (fun m outpoint => m.erase outpoint) utxos

/-- Insert a coin at every key in a list — the create half of a
transaction's action on the set. `Finmap.insert` replaces, so a later entry
overwrites an earlier one at a duplicated key; the characterization lemmas
therefore assume distinct keys. -/
def UtxoSet.create (utxos : UtxoSet) (coins : List (OutPoint × Coin)) : UtxoSet :=
  coins.foldl (fun m coin => m.insert coin.1 coin.2) utxos

/-! ## Lookup characterizations -/

/-- Spending leaves lookup untouched away from the spent outpoints. -/
theorem UtxoSet.lookup_spend_of_notMem {utxos : UtxoSet} {outpoints : List OutPoint}
    {o : OutPoint} (h : o ∉ outpoints) :
    (utxos.spend outpoints).lookup o = utxos.lookup o := by
  induction outpoints generalizing utxos with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.mem_cons, not_or] at h
    change (spend (utxos.erase hd) tl).lookup o = _
    rw [ih h.2, Finmap.lookup_erase_ne h.1]

/-- Spent outpoints are gone: after spending a list of outpoints, lookup on
any of its members returns `none`. -/
theorem UtxoSet.lookup_spend_of_mem {utxos : UtxoSet} {outpoints : List OutPoint}
    {o : OutPoint} (h : o ∈ outpoints) :
    (utxos.spend outpoints).lookup o = none := by
  induction outpoints generalizing utxos with
  | nil => cases h
  | cons hd tl ih =>
    change (spend (utxos.erase hd) tl).lookup o = none
    by_cases htl : o ∈ tl
    · exact ih htl
    · rcases List.mem_cons.mp h with rfl | habs
      · rw [lookup_spend_of_notMem htl, Finmap.lookup_erase]
      · exact absurd habs htl

/-- Spending is order-insensitive: permuted spend lists produce the same
set, because lookup after a spend depends only on membership in the list.
Order-freedom within a transaction is a theorem of the machine, not a
type-level restatement. -/
theorem UtxoSet.spend_perm {utxos : UtxoSet} {l₁ l₂ : List OutPoint} (h : l₁.Perm l₂) :
    utxos.spend l₁ = utxos.spend l₂ :=
  Finmap.ext_lookup fun o => by
    by_cases hmem : o ∈ l₁
    · rw [lookup_spend_of_mem hmem, lookup_spend_of_mem (h.mem_iff.mp hmem)]
    · rw [lookup_spend_of_notMem hmem,
        lookup_spend_of_notMem fun hc => hmem (h.mem_iff.mpr hc)]

/-- Membership after a spend is membership before it, minus the spent
list. -/
theorem UtxoSet.mem_spend {utxos : UtxoSet} {outpoints : List OutPoint} {o : OutPoint} :
    o ∈ utxos.spend outpoints ↔ o ∈ utxos ∧ o ∉ outpoints := by
  rw [← Finmap.lookup_isSome, ← Finmap.lookup_isSome]
  by_cases h : o ∈ outpoints
  · rw [lookup_spend_of_mem h]
    simp [h]
  · rw [lookup_spend_of_notMem h]
    simp [h]

/-- Creating coins leaves lookup untouched away from the created keys. -/
theorem UtxoSet.lookup_create_of_notMem {utxos : UtxoSet} {coins : List (OutPoint × Coin)}
    {o : OutPoint} (h : o ∉ coins.map Prod.fst) :
    (utxos.create coins).lookup o = utxos.lookup o := by
  induction coins generalizing utxos with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.mem_cons, not_or] at h
    change (create (utxos.insert hd.1 hd.2) tl).lookup o = _
    rw [ih h.2, Finmap.lookup_insert_of_ne _ h.1]

/-- After creating a list of keyed coins with distinct keys, lookup at a
listed key finds exactly the listed coin. -/
theorem UtxoSet.lookup_create_of_mem {utxos : UtxoSet} {coins : List (OutPoint × Coin)}
    (hkeys : (coins.map Prod.fst).Nodup) {o : OutPoint} {c : Coin} (hmem : (o, c) ∈ coins) :
    (utxos.create coins).lookup o = some c := by
  induction coins generalizing utxos with
  | nil => cases hmem
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hkeys
    rcases List.mem_cons.mp hmem with heq | htl
    · subst heq
      change (create (utxos.insert o c) tl).lookup o = some c
      rw [lookup_create_of_notMem hkeys.1, Finmap.lookup_insert]
    · exact ih hkeys.2 htl

/-- Membership after a create is membership before it, plus the created
keys. -/
theorem UtxoSet.mem_create {utxos : UtxoSet} {coins : List (OutPoint × Coin)} {o : OutPoint} :
    o ∈ utxos.create coins ↔ o ∈ utxos ∨ o ∈ coins.map Prod.fst := by
  induction coins generalizing utxos with
  | nil => simp [create]
  | cons hd tl ih =>
    change o ∈ create (utxos.insert hd.1 hd.2) tl ↔ _
    rw [ih]
    simp only [Finmap.mem_insert, List.map_cons, List.mem_cons]
    tauto

/-! ## Value accounting -/

/-- Inserting a coin at a fresh key adds its value to the total. -/
theorem UtxoSet.totalValue_insert {utxos : UtxoSet} {o : OutPoint} {c : Coin}
    (h : o ∉ utxos) :
    totalValue (utxos.insert o c) = c.output.value.toNat + utxos.totalValue := by
  rw [totalValue, totalValue, Finmap.entries_insert_of_notMem h, Multiset.map_cons,
    Multiset.sum_cons]

/-- Erasing a present outpoint removes exactly the value held there from
the total. -/
theorem UtxoSet.totalValue_erase {utxos : UtxoSet} {o : OutPoint} (h : o ∈ utxos) :
    totalValue (utxos.erase o) + utxos.valueAt o = utxos.totalValue := by
  obtain ⟨c, hc⟩ := Finmap.mem_iff.mp h
  have hins : totalValue ((utxos.erase o).insert o c)
      = c.output.value.toNat + totalValue (utxos.erase o) :=
    totalValue_insert Finmap.notMem_erase_self
  rw [Finmap.insert_erase hc] at hins
  have hval : utxos.valueAt o = c.output.value.toNat := by simp [valueAt, hc]
  omega

/-- The value held at an outpoint is untouched by erasing a different
one. -/
theorem UtxoSet.valueAt_erase_ne {utxos : UtxoSet} {o o' : OutPoint} (h : o ≠ o') :
    valueAt (utxos.erase o') o = utxos.valueAt o := by
  rw [valueAt, valueAt, Finmap.lookup_erase_ne h]

/-- Spending distinct, present outpoints removes exactly the sum of the
values held at them from the total. -/
theorem UtxoSet.totalValue_spend {utxos : UtxoSet} {outpoints : List OutPoint}
    (hnodup : outpoints.Nodup) (hmem : ∀ o ∈ outpoints, o ∈ utxos) :
    totalValue (utxos.spend outpoints) + (outpoints.map utxos.valueAt).sum
      = utxos.totalValue := by
  induction outpoints generalizing utxos with
  | nil => simp [spend]
  | cons hd tl ih =>
    rw [List.nodup_cons] at hnodup
    have hmap : tl.map utxos.valueAt = tl.map (valueAt (utxos.erase hd)) :=
      List.map_congr_left fun o ho =>
        (valueAt_erase_ne fun (heq : o = hd) => hnodup.1 (heq ▸ ho)).symm
    have hrest := ih (utxos := utxos.erase hd) hnodup.2 fun o ho =>
      Finmap.mem_erase.mpr
        ⟨fun (heq : o = hd) => hnodup.1 (heq ▸ ho), hmem o (List.mem_cons_of_mem _ ho)⟩
    have herase := totalValue_erase (hmem hd List.mem_cons_self)
    change totalValue (spend (utxos.erase hd) tl) + _ = _
    rw [List.map_cons, List.sum_cons, hmap]
    omega

/-- Creating coins at distinct keys, all fresh for the set, adds exactly
the sum of their values to the total. -/
theorem UtxoSet.totalValue_create {utxos : UtxoSet} {coins : List (OutPoint × Coin)}
    (hkeys : (coins.map Prod.fst).Nodup) (hfresh : ∀ e ∈ coins, e.1 ∉ utxos) :
    totalValue (utxos.create coins)
      = utxos.totalValue + (coins.map fun e => e.2.output.value.toNat).sum := by
  induction coins generalizing utxos with
  | nil => simp [create]
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hkeys
    have hfresh' : ∀ e ∈ tl, e.1 ∉ utxos.insert hd.1 hd.2 := fun e he => by
      rw [Finmap.mem_insert, not_or]
      exact ⟨fun heq => hkeys.1 (heq ▸ List.mem_map_of_mem he),
        hfresh e (List.mem_cons_of_mem _ he)⟩
    change totalValue (create (utxos.insert hd.1 hd.2) tl) = _
    rw [ih (utxos := utxos.insert hd.1 hd.2) hkeys.2 hfresh',
      totalValue_insert (hfresh hd List.mem_cons_self), List.map_cons, List.sum_cons]
    omega

end BtcVerified
