import Mathlib.Data.Finmap
/-!
  # `Finmap` extensions

  Lemmas about Mathlib's `Finmap` that Mathlib does not (yet) provide, in
  the `Finmap` namespace per the `Ext/` convention.

  Checked claims:

  * `Finmap.insert_erase`: re-inserting the value found at a key after
    erasing that key restores the original map.
-/

namespace Finmap

variable {α : Type*} {β : α → Type*} [DecidableEq α]

/-- Re-inserting the value found at a key after erasing that key restores
the original map: erasure only forgets the one entry the insertion puts
back. Lets a map be peeled one entry at a time by facts about `insert`
alone. -/
theorem insert_erase {a : α} {b : β a} {s : Finmap β} (h : s.lookup a = some b) :
    (s.erase a).insert a b = s :=
  ext_lookup fun x => by
    by_cases hx : x = a
    · subst hx
      rw [lookup_insert, h]
    · rw [lookup_insert_of_ne _ hx, lookup_erase_ne hx]

end Finmap
