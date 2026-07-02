import Mathlib.Data.List.Basic
/-!
  # `List` extensions: `zipWith` against a binary constructor and its projections

  Extension lemmas for the dependency-defined `List`, added in `namespace List`.
  They are general facts about recombining a list through a two-argument
  constructor `mk` and its projections `f`, `g`: they hold for *any* such
  triple — pairs, custom two-field structures, anything where `mk` and the
  projections round-trip — not for any particular type. Bitcoin's SegWit codec
  uses them to unzip a list of input/witness pairs into the two separate wire
  regions and zip it back, but nothing here mentions transactions.
-/

namespace List

variable {α β γ : Type*}

/-- Recombine a list's two projections with their constructor to recover the
list, when the constructor and projections round-trip. -/
theorem zipWith_map_map_left_right {f : γ → α} {g : γ → β} {mk : α → β → γ}
    (h : ∀ c, mk (f c) (g c) = c) (l : List γ) :
    zipWith mk (l.map f) (l.map g) = l := by
  rw [zipWith_map, zipWith_self]
  simp [h]

/-- The left projection of a `zipWith mk` is the left list, when the lists agree
in length and the projection inverts the constructor on the left. -/
theorem map_zipWith_left {mk : α → β → γ} {f : γ → α} (hf : ∀ a b, f (mk a b) = a)
    (as : List α) (bs : List β) (hlen : as.length = bs.length) :
    (zipWith mk as bs).map f = as := by
  induction as generalizing bs with
  | nil => rfl
  | cons x as ih =>
    cases bs with
    | nil => simp at hlen
    | cons y bs => simp only [zipWith_cons_cons, map_cons, hf, ih bs (by simpa using hlen)]

/-- The right projection of a `zipWith mk` is the right list, when the lists
agree in length and the projection inverts the constructor on the right. -/
theorem map_zipWith_right {mk : α → β → γ} {g : γ → β} (hg : ∀ a b, g (mk a b) = b)
    (as : List α) (bs : List β) (hlen : as.length = bs.length) :
    (zipWith mk as bs).map g = bs := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons y bs => simp at hlen
  | cons x as ih =>
    cases bs with
    | nil => simp at hlen
    | cons y bs => simp only [zipWith_cons_cons, map_cons, hg, ih bs (by simpa using hlen)]

end List
