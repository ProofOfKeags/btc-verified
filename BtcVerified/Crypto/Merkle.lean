import BtcVerified.Crypto.Hash256
import BtcVerified.Crypto.Sha256
import Mathlib.Data.Nat.Log
/-!
  # Bitcoin's merkle tree

  The merkle root is how a block header commits to its transaction list:
  leaves are txids, and each node is the double-SHA-256 of its two children's
  digests. Bitcoin pads an odd level by hashing its last node with itself —
  and that padding rule makes the construction famously non-injective
  (CVE-2012-2459): a list that materializes part of its own padding as actual
  content produces the same root as the shorter list it extends. Core rejects
  such blocks with a uniform per-level duplicate-pair scan fused into its root
  computation (its `mutated` flag). Here the concern is factored apart: the
  root computation is one deterministic cryptographic operation, and
  *canonicality* is a first-class, decidable property of the leaf list.

  The spec is structural rather than procedural: `Tree` is built top-down by
  bisection at the enclosing power of two, and procedural duplication is an
  explicit constructor (`pad`, semantically a node with two equal children)
  instead of an artifact of iteration order. The bottom-up fold Bitcoin
  actually computes (`computeRoot`) is proved equal to the spec.

  Canonicality constrains exactly what threatens injectivity and nothing
  more. Padding only ever duplicates trailing power-of-two-aligned blocks —
  the right spine — so a cross-length collision requires a trailing block
  duplicating its left sibling, and `Canonical` forbids precisely that
  (`Tree.spineCanonical`, root node exempt: a shorter list with the same
  enclosing width must still split at the root). Core's uniform scan is
  strictly stronger — it also rejects pair-aligned duplicates that no padding
  could produce — but the two agree on transaction-valid blocks, where a
  duplicated leaf means a duplicated txid: a self-double-spend or a collision.

  Collision resistance is never assumed: theorems conclude with
  `Sha256.Collision` — two concrete colliding byte strings — as a
  constructed disjunct, and intractability is the consumer's hypothesis.

  Known residual, documented not solved: equal *widths* are a hypothesis of
  `root_inj_of_canonical`. Across widths, a 64-byte transaction whose
  serialization equals the concatenation of two digests confuses a leaf with
  an internal node (the SPV-grade ambiguity the Great Consensus Cleanup
  proposes to close by forbidding 64-byte transactions). For block validity
  the transaction count is in hand, so the hypothesis is free.

  Checked claims:

  * `computeRoot_eq_root`: the bottom-up fold computes the structural spec's
    root.
  * `root_inj_of_length_eq`: between equal-length lists, the root identifies
    the list — or two concrete byte strings collide under double-SHA-256.
  * `root_inj_of_canonical`: between canonical lists of equal enclosing
    width, the root identifies the list — or a concrete collision. This is
    the property the canonicality rule exists to restore.
-/

namespace BtcVerified.Merkle

open BtcVerified.Serialize

/-- A merkle node: the double-SHA-256 of the two children's digests, each
serialized as its 32 little-endian bytes. -/
def combine (l r : Hash256) : Hash256 :=
  Hash256.ofBytesLE (Sha256.sha256d (encodeBitVecLE 32 l ++ encodeBitVecLE 32 r))

/-- Equal merkle nodes have equal children — or their two 64-byte preimages
collide under double-SHA-256. -/
theorem combine_inj {l r l' r' : Hash256} (h : combine l r = combine l' r') :
    (l = l' ∧ r = r') ∨ Sha256.Collision := by
  by_cases hm : encodeBitVecLE 32 l ++ encodeBitVecLE 32 r
      = encodeBitVecLE 32 l' ++ encodeBitVecLE 32 r'
  · obtain ⟨h₁, h₂⟩ := List.append_inj hm (by rw [encodeBitVecLE_length, encodeBitVecLE_length])
    exact Or.inl ⟨by simpa [Hash256.ofBytesLE_encode] using congrArg Hash256.ofBytesLE h₁,
      by simpa [Hash256.ofBytesLE_encode] using congrArg Hash256.ofBytesLE h₂⟩
  · refine Or.inr ⟨_, _, hm, ?_⟩
    have hl := Hash256.encode_ofBytesLE (Sha256.sha256d_length
      (encodeBitVecLE 32 l ++ encodeBitVecLE 32 r))
    have hr := Hash256.encode_ofBytesLE (Sha256.sha256d_length
      (encodeBitVecLE 32 l' ++ encodeBitVecLE 32 r'))
    rw [← hl, ← hr]
    exact congrArg (encodeBitVecLE 32) h

/-! ## The structural spec -/

/-- A Bitcoin merkle tree, with procedural duplication explicit: `pad t` is
the node Bitcoin forms by hashing `t` with itself when a level runs out of
content — semantically a `node t t`, kept distinguishable so the structure
records which duplications the *construction* introduced. -/
inductive Tree where
  /-- A leaf: one txid. -/
  | leaf (h : Hash256)
  /-- An interior node over two materialized subtrees. -/
  | node (l r : Tree)
  /-- A padding node: the right child is a procedural copy of the left. -/
  | pad (t : Tree)
  deriving DecidableEq

namespace Tree

/-- The root hash: leaves are their own digest, and both node forms hash two
children — a `pad` hashes its child with itself. -/
def root : Tree → Hash256
  | leaf h => h
  | node l r => combine l.root r.root
  | pad t => combine t.root t.root

/-- The leaf sequence with all padding materialized: the `2 ^ k` leaves the
hashing actually consumes at width `k`. -/
def virtualLeaves : Tree → List Hash256
  | leaf h => [h]
  | node l r => l.virtualLeaves ++ r.virtualLeaves
  | pad t => t.virtualLeaves ++ t.virtualLeaves

end Tree

/-- Build the width-`2 ^ k` tree over a slice, top-down: bisect while the
content overflows the left half, pad once it fits. (Empty input degenerates
to a `0` leaf; a Bitcoin block has at least its coinbase.) -/
def ofList (xs : List Hash256) : Nat → Tree
  | 0 => .leaf (xs.headD 0)
  | k + 1 =>
    if xs.length ≤ 2 ^ k then .pad (ofList xs k)
    else .node (ofList (xs.take (2 ^ k)) k) (ofList (xs.drop (2 ^ k)) k)

/-- The merkle tree of a leaf list, built at the enclosing power of two. -/
def tree (xs : List Hash256) : Tree := ofList xs (Nat.clog 2 xs.length)

/-- The merkle root of a leaf list (the structural spec). -/
def root (xs : List Hash256) : Hash256 := (tree xs).root

/-! ## The bottom-up computation -/

/-- One level of Bitcoin's bottom-up fold: hash adjacent pairs, hashing an
unpaired last node with itself. -/
def foldLevel : List Hash256 → List Hash256
  | [] => []
  | [x] => [combine x x]
  | x :: y :: rest => combine x y :: foldLevel rest

/-- Each fold level halves the node count, rounding up. -/
theorem foldLevel_length : ∀ xs : List Hash256, (foldLevel xs).length = (xs.length + 1) / 2
  | [] => by simp [foldLevel]
  | [_] => by simp [foldLevel]
  | _ :: _ :: rest => by simp [foldLevel, foldLevel_length rest]; omega

/-- The merkle root as Bitcoin computes it: fold levels bottom-up until one
node remains. One deterministic cryptographic operation — canonicality of the
input is `Canonical`'s concern, decided separately. (Core fuses a duplicate
scan into this same pass under the name `mutated`; see the module header.) -/
def computeRoot : List Hash256 → Hash256
  | [] => 0
  | [x] => x
  | x :: y :: rest => computeRoot (foldLevel (x :: y :: rest))
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

/-- A fold level distributes over an append at an even boundary. -/
theorem foldLevel_append : ∀ (as bs : List Hash256), as.length % 2 = 0 →
    foldLevel (as ++ bs) = foldLevel as ++ foldLevel bs
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | a :: a' :: rest, bs, h => by
    have hrest : rest.length % 2 = 0 := by simp at h; omega
    cases bs with
    | nil => simp [foldLevel]
    | cons b bs' =>
      simp only [List.cons_append, foldLevel, foldLevel_append rest (b :: bs') hrest]

/-- One spec level absorbs one fold level: the width-`2 ^ (k + 1)` tree over
`xs` and the width-`2 ^ k` tree over `foldLevel xs` share a root. -/
theorem ofList_root_foldLevel :
    ∀ (k : Nat) (xs : List Hash256), 0 < xs.length → xs.length ≤ 2 ^ (k + 1) →
      (ofList xs (k + 1)).root = (ofList (foldLevel xs) k).root := by
  intro k
  induction k with
  | zero =>
    intro xs h0 h2
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at h2
    cases xs with
    | nil => simp at h0
    | cons x xs' =>
      cases xs' with
      | nil => simp [ofList, foldLevel, Tree.root]
      | cons y xs'' =>
        have hnil : xs'' = [] := by
          simp only [List.length_cons] at h2
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst hnil
        simp [ofList, foldLevel, Tree.root]
  | succ k ih =>
    intro xs h0 h2
    have hpow : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := Nat.two_pow_succ (k + 1)
    have hpow' : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := Nat.two_pow_succ k
    by_cases hsplit : xs.length ≤ 2 ^ (k + 1)
    · have hfold : (foldLevel xs).length ≤ 2 ^ k := by
        rw [foldLevel_length]; omega
      have hL : ofList xs (k + 1 + 1) = .pad (ofList xs (k + 1)) := by
        rw [ofList, if_pos hsplit]
      have hR : ofList (foldLevel xs) (k + 1) = .pad (ofList (foldLevel xs) k) := by
        rw [ofList, if_pos hfold]
      rw [hL, hR, Tree.root, Tree.root, ih xs h0 hsplit]
    · have hsplit' : 2 ^ (k + 1) < xs.length := by omega
      have htake : (xs.take (2 ^ (k + 1))).length = 2 ^ (k + 1) := by
        rw [List.length_take]; omega
      have hsplitFold : foldLevel xs = foldLevel (xs.take (2 ^ (k + 1)))
          ++ foldLevel (xs.drop (2 ^ (k + 1))) := by
        rw [← foldLevel_append _ _ (by omega), List.take_append_drop]
      have hfoldTake : (foldLevel (xs.take (2 ^ (k + 1)))).length = 2 ^ k := by
        rw [foldLevel_length, htake]; omega
      have hfoldLen : ¬ (foldLevel xs).length ≤ 2 ^ k := by
        rw [foldLevel_length]; omega
      have hL : ofList xs (k + 1 + 1)
          = .node (ofList (xs.take (2 ^ (k + 1))) (k + 1))
              (ofList (xs.drop (2 ^ (k + 1))) (k + 1)) := by
        rw [ofList, if_neg (by omega)]
      have hR : ofList (foldLevel xs) (k + 1)
          = .node (ofList ((foldLevel xs).take (2 ^ k)) k)
              (ofList ((foldLevel xs).drop (2 ^ k)) k) := by
        rw [ofList, if_neg hfoldLen]
      have htakeF : (foldLevel xs).take (2 ^ k) = foldLevel (xs.take (2 ^ (k + 1))) := by
        rw [hsplitFold, List.take_left' hfoldTake]
      have hdropF : (foldLevel xs).drop (2 ^ k) = foldLevel (xs.drop (2 ^ (k + 1))) := by
        rw [hsplitFold, List.drop_left' hfoldTake]
      rw [hL, hR, Tree.root, Tree.root, htakeF, hdropF,
        ih _ (by rw [List.length_take]; omega) (by omega),
        ih _ (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)]

/-- The bottom-up fold computes the structural spec's root. -/
theorem computeRoot_eq_root : ∀ xs : List Hash256, computeRoot xs = root xs
  | [] => by simp [computeRoot, root, tree, Nat.clog_zero_right, ofList, Tree.root]
  | [x] => by simp [computeRoot, root, tree, Nat.clog_one_right, ofList, Tree.root]
  | x :: y :: rest => by
    have hlen : 2 ≤ (x :: y :: rest).length := by simp
    have hclog : Nat.clog 2 (x :: y :: rest).length
        = Nat.clog 2 (((x :: y :: rest).length + 1) / 2) + 1 := by
      rw [Nat.clog_of_two_le (by decide) hlen,
        show (x :: y :: rest).length + 2 - 1 = (x :: y :: rest).length + 1 by omega]
    have hfl : (foldLevel (x :: y :: rest)).length = ((x :: y :: rest).length + 1) / 2 :=
      foldLevel_length _
    have hrec : computeRoot (x :: y :: rest) = computeRoot (foldLevel (x :: y :: rest)) := by
      conv_lhs => rw [computeRoot]
    rw [hrec, computeRoot_eq_root (foldLevel (x :: y :: rest)), root, root, tree, tree,
      hfl, hclog, ofList_root_foldLevel _ _ (by simp) (by
        calc (x :: y :: rest).length ≤ 2 ^ Nat.clog 2 (x :: y :: rest).length :=
              Nat.le_pow_clog (by decide) _
          _ = 2 ^ (Nat.clog 2 (((x :: y :: rest).length + 1) / 2) + 1) := by rw [← hclog])]
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

/-! ## Canonicality -/

/-- The canonicality scan along the right spine: descending through the
content side of every padding node and the right child of every interior
node, no interior node may join two subtrees with identical materialized
leaf sequences — that is exactly the shape a materialized padding suffix
produces, and (`root_inj_of_canonical`) the only shape that threatens
injectivity. -/
def Tree.spineCanonical : Tree → Bool
  | .leaf _ => true
  | .pad t => t.spineCanonical
  | .node l r => l.virtualLeaves != r.virtualLeaves && r.spineCanonical

/-- The canonicality decision procedure for a leaf list: scan the right spine
of its tree. The root node itself is exempt — a shorter list of the same
enclosing width must still overflow the left half, so a duplication at the
root cannot be a materialized padding (it is honest duplicate content, which
transaction validity, not the merkle layer, rejects). -/
def canonicalCheck (xs : List Hash256) : Bool :=
  match tree xs with
  | .node _ r => r.spineCanonical
  | _ => true

/-- A canonical leaf list: one whose merkle root is not also the root of a
shorter list (its trailing blocks never materialize its own padding). The
proposition the consensus layer demands of a block's txids. -/
abbrev Canonical (xs : List Hash256) : Prop := canonicalCheck xs = true

/-! ## Injectivity -/

/-- A width-`2 ^ k` tree materializes exactly `2 ^ k` leaves. -/
theorem length_virtualLeaves_ofList :
    ∀ (k : Nat) (xs : List Hash256), ((ofList xs k).virtualLeaves).length = 2 ^ k := by
  intro k
  induction k with
  | zero => intro xs; rfl
  | succ k ih =>
    intro xs
    rw [ofList]
    split
    · simp [Tree.virtualLeaves, ih, Nat.two_pow_succ]
    · simp [Tree.virtualLeaves, ih, Nat.two_pow_succ]

/-- A full slice needs no padding: its materialized leaves are itself. -/
theorem virtualLeaves_ofList_of_length_eq :
    ∀ (k : Nat) (xs : List Hash256), xs.length = 2 ^ k →
      (ofList xs k).virtualLeaves = xs := by
  intro k
  induction k with
  | zero =>
    intro xs hlen
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    rfl
  | succ k ih =>
    intro xs hlen
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hpow := Nat.two_pow_succ k
    have hlt : ¬ xs.length ≤ 2 ^ k := by omega
    rw [ofList, if_neg hlt, Tree.virtualLeaves,
      ih _ (by rw [List.length_take]; omega),
      ih _ (by rw [List.length_drop]; omega),
      List.take_append_drop]

/-- The materialized leaves extend the actual list: padding only appends. -/
theorem virtualLeaves_ofList_append :
    ∀ (k : Nat) (xs : List Hash256), xs.length ≤ 2 ^ k →
      ∃ ps, (ofList xs k).virtualLeaves = xs ++ ps := by
  intro k
  induction k with
  | zero =>
    intro xs hlen
    match xs, hlen with
    | [], _ => exact ⟨[0], rfl⟩
    | [x], _ => exact ⟨[], rfl⟩
  | succ k ih =>
    intro xs hlen
    rw [ofList]
    split
    · next hfit =>
      obtain ⟨ps, hps⟩ := ih xs hfit
      exact ⟨ps ++ (xs ++ ps), by rw [Tree.virtualLeaves, hps, List.append_assoc]⟩
    · next hover =>
      have htake : (xs.take (2 ^ k)).length = 2 ^ k := by rw [List.length_take]; omega
      obtain ⟨ps, hps⟩ := ih (xs.drop (2 ^ k)) (by rw [List.length_drop]; omega)
      exact ⟨ps, by
        rw [Tree.virtualLeaves, virtualLeaves_ofList_of_length_eq k _ htake, hps,
          ← List.append_assoc, List.take_append_drop]⟩

/-- Equal roots at one width force equal materialized leaf sequences — or a
concrete double-SHA-256 collision. The hashing direction of injectivity. -/
theorem virtualLeaves_eq_of_root_eq :
    ∀ (k : Nat) (xs ys : List Hash256),
      (ofList xs k).root = (ofList ys k).root →
      (ofList xs k).virtualLeaves = (ofList ys k).virtualLeaves ∨ Sha256.Collision := by
  intro k
  induction k with
  | zero =>
    intro xs ys h
    exact Or.inl (by simpa [ofList, Tree.root, Tree.virtualLeaves] using h)
  | succ k ih =>
    intro xs ys h
    simp only [ofList] at h ⊢
    by_cases hx : xs.length ≤ 2 ^ k <;> by_cases hy : ys.length ≤ 2 ^ k
    · rw [if_pos hx, if_pos hy] at h ⊢
      rw [Tree.root, Tree.root] at h
      rw [Tree.virtualLeaves, Tree.virtualLeaves]
      rcases combine_inj h with ⟨ha, _⟩ | c
      · rcases ih xs ys ha with hvl | c
        · exact Or.inl (by rw [hvl])
        · exact Or.inr c
      · exact Or.inr c
    · rw [if_pos hx, if_neg hy] at h ⊢
      rw [Tree.root, Tree.root] at h
      rw [Tree.virtualLeaves, Tree.virtualLeaves]
      rcases combine_inj h with ⟨hl, hr⟩ | c
      · rcases ih xs (ys.take (2 ^ k)) hl with hvl₁ | c
        · rcases ih xs (ys.drop (2 ^ k)) hr with hvl₂ | c
          · exact Or.inl (by rw [← hvl₁, ← hvl₂])
          · exact Or.inr c
        · exact Or.inr c
      · exact Or.inr c
    · rw [if_neg hx, if_pos hy] at h ⊢
      rw [Tree.root, Tree.root] at h
      rw [Tree.virtualLeaves, Tree.virtualLeaves]
      rcases combine_inj h with ⟨hl, hr⟩ | c
      · rcases ih (xs.take (2 ^ k)) ys hl with hvl₁ | c
        · rcases ih (xs.drop (2 ^ k)) ys hr with hvl₂ | c
          · exact Or.inl (by rw [hvl₁, hvl₂])
          · exact Or.inr c
        · exact Or.inr c
      · exact Or.inr c
    · rw [if_neg hx, if_neg hy] at h ⊢
      rw [Tree.root, Tree.root] at h
      rw [Tree.virtualLeaves, Tree.virtualLeaves]
      rcases combine_inj h with ⟨hl, hr⟩ | c
      · rcases ih (xs.take (2 ^ k)) (ys.take (2 ^ k)) hl with hvl₁ | c
        · rcases ih (xs.drop (2 ^ k)) (ys.drop (2 ^ k)) hr with hvl₂ | c
          · exact Or.inl (by rw [hvl₁, hvl₂])
          · exact Or.inr c
        · exact Or.inr c
      · exact Or.inr c

/-- Equal materialized leaves of canonical-spine trees come from equal actual
lists: the combinatorial direction of injectivity, no hashing involved. The
spine conditions kill exactly the materialized-padding case. -/
theorem eq_of_virtualLeaves_eq :
    ∀ (k : Nat) (xs ys : List Hash256),
      0 < xs.length → xs.length ≤ 2 ^ k → 0 < ys.length → ys.length ≤ 2 ^ k →
      (ofList xs k).spineCanonical = true → (ofList ys k).spineCanonical = true →
      (ofList xs k).virtualLeaves = (ofList ys k).virtualLeaves → xs = ys := by
  intro k
  induction k with
  | zero =>
    intro xs ys h0x hx h0y hy _ _ hvl
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (by omega : xs.length = 1)
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp (by omega : ys.length = 1)
    simpa [ofList, Tree.virtualLeaves] using hvl
  | succ k ih =>
    intro xs ys h0x hx h0y hy hcx hcy hvl
    simp only [ofList] at hcx hcy hvl
    by_cases hxs : xs.length ≤ 2 ^ k <;> by_cases hys : ys.length ≤ 2 ^ k
    · -- pad / pad: equal halves, recurse.
      rw [if_pos hxs] at hcx hvl
      rw [if_pos hys] at hcy hvl
      rw [Tree.spineCanonical] at hcx hcy
      rw [Tree.virtualLeaves, Tree.virtualLeaves] at hvl
      have hhalf := (List.append_inj hvl (by
        rw [length_virtualLeaves_ofList, length_virtualLeaves_ofList])).1
      exact ih xs ys h0x hxs h0y hys hcx hcy hhalf
    · -- pad / node: the node side's halves are forced equal — its spine
      -- condition forbids exactly that.
      rw [if_pos hxs] at hcx hvl
      rw [if_neg hys] at hcy hvl
      rw [Tree.virtualLeaves, Tree.virtualLeaves] at hvl
      simp only [Tree.spineCanonical, Bool.and_eq_true, bne_iff_ne, ne_eq] at hcy
      have hlen : ((ofList xs k).virtualLeaves).length
          = ((ofList (ys.take (2 ^ k)) k).virtualLeaves).length := by
        rw [length_virtualLeaves_ofList, length_virtualLeaves_ofList]
      obtain ⟨h₁, h₂⟩ := List.append_inj hvl hlen
      exact absurd (h₁.symm.trans h₂) hcy.1
    · -- node / pad: symmetric.
      rw [if_neg hxs] at hcx hvl
      rw [if_pos hys] at hcy hvl
      rw [Tree.virtualLeaves, Tree.virtualLeaves] at hvl
      simp only [Tree.spineCanonical, Bool.and_eq_true, bne_iff_ne, ne_eq] at hcx
      have hlen : ((ofList (xs.take (2 ^ k)) k).virtualLeaves).length
          = ((ofList ys k).virtualLeaves).length := by
        rw [length_virtualLeaves_ofList, length_virtualLeaves_ofList]
      obtain ⟨h₁, h₂⟩ := List.append_inj hvl hlen
      exact absurd (h₁.trans h₂.symm) hcx.1
    · -- node / node: left halves are full slices, right halves recurse.
      rw [if_neg hxs] at hcx hvl
      rw [if_neg hys] at hcy hvl
      rw [Tree.virtualLeaves, Tree.virtualLeaves] at hvl
      simp only [Tree.spineCanonical, Bool.and_eq_true, bne_iff_ne, ne_eq] at hcx hcy
      have htx : (xs.take (2 ^ k)).length = 2 ^ k := by rw [List.length_take]; omega
      have hty : (ys.take (2 ^ k)).length = 2 ^ k := by rw [List.length_take]; omega
      have hlen : ((ofList (xs.take (2 ^ k)) k).virtualLeaves).length
          = ((ofList (ys.take (2 ^ k)) k).virtualLeaves).length := by
        rw [length_virtualLeaves_ofList, length_virtualLeaves_ofList]
      obtain ⟨h₁, h₂⟩ := List.append_inj hvl hlen
      have htake : xs.take (2 ^ k) = ys.take (2 ^ k) := by
        rw [← virtualLeaves_ofList_of_length_eq k _ htx,
          ← virtualLeaves_ofList_of_length_eq k _ hty, h₁]
      have hdrop : xs.drop (2 ^ k) = ys.drop (2 ^ k) :=
        ih _ _ (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)
          (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)
          hcx.2 hcy.2 h₂
      rw [← List.take_append_drop (2 ^ k) xs, ← List.take_append_drop (2 ^ k) ys,
        htake, hdrop]

/-! ## The headline theorems -/

/-- Between equal-length lists the merkle root identifies the list — or two
concrete byte strings collide under double-SHA-256. No canonicality needed:
padding only appends, so equal lengths leave no room for ambiguity. -/
theorem root_inj_of_length_eq {xs ys : List Hash256}
    (hlen : xs.length = ys.length) (hroot : root xs = root ys) :
    xs = ys ∨ Sha256.Collision := by
  unfold root tree at hroot
  rw [← hlen] at hroot
  rcases virtualLeaves_eq_of_root_eq (Nat.clog 2 xs.length) xs ys hroot with hvl | c
  · obtain ⟨ps, hps⟩ := virtualLeaves_ofList_append (Nat.clog 2 xs.length) xs
      (Nat.le_pow_clog (by decide) _)
    obtain ⟨qs, hqs⟩ := virtualLeaves_ofList_append (Nat.clog 2 xs.length) ys
      (by rw [← hlen]; exact Nat.le_pow_clog (by decide) _)
    rw [hps, hqs] at hvl
    exact Or.inl (List.append_inj hvl hlen).1
  · exact Or.inr c

/-- Between canonical lists of equal enclosing width the merkle root
identifies the list — or two concrete byte strings collide under
double-SHA-256. This is the injectivity the canonicality rule exists to
restore: without `Canonical`, a list extended by its own materialized padding
shares its root (CVE-2012-2459). Equal widths exclude the cross-height
leaf/interior ambiguity (see the module header). -/
theorem root_inj_of_canonical {xs ys : List Hash256}
    (hcx : Canonical xs) (hcy : Canonical ys)
    (h0x : xs ≠ []) (h0y : ys ≠ [])
    (hk : Nat.clog 2 xs.length = Nat.clog 2 ys.length)
    (hroot : root xs = root ys) : xs = ys ∨ Sha256.Collision := by
  have h0x' : 0 < xs.length := List.length_pos_iff.mpr h0x
  have h0y' : 0 < ys.length := List.length_pos_iff.mpr h0y
  rcases Nat.eq_zero_or_pos (Nat.clog 2 xs.length) with hk0 | hkpos
  · -- Width 1: both lists are singletons and the root is the element.
    have hx1 : xs.length = 1 := by
      by_contra hne
      have := Nat.clog_pos (b := 2) (by decide) (n := xs.length) (by omega)
      omega
    have hy1 : ys.length = 1 := by
      by_contra hne
      have := Nat.clog_pos (b := 2) (by decide) (n := ys.length) (by omega)
      omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hx1
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hy1
    rw [root, root, tree, tree, hx1, hy1] at hroot
    exact Or.inl (by simpa [ofList, Nat.clog, Tree.root] using hroot)
  · -- Width ≥ 2: by minimality both trees split at the root; the left halves
    -- are full slices, the right halves carry the spine conditions.
    obtain ⟨j, hj⟩ : ∃ j, Nat.clog 2 xs.length = j + 1 :=
      ⟨Nat.clog 2 xs.length - 1, by omega⟩
    have hxlen : 2 ^ j < xs.length := by
      have h2 : 2 ≤ xs.length := by
        by_contra hlt
        have : Nat.clog 2 xs.length = 0 := Nat.clog_of_right_le_one (by omega) 2
        omega
      have := Nat.pow_pred_clog_lt_self (b := 2) (by decide) (x := xs.length) (by omega)
      rwa [hj, Nat.pred_succ] at this
    have hylen : 2 ^ j < ys.length := by
      have h2 : 2 ≤ ys.length := by
        by_contra hlt
        have : Nat.clog 2 ys.length = 0 := Nat.clog_of_right_le_one (by omega) 2
        omega
      have := Nat.pow_pred_clog_lt_self (b := 2) (by decide) (x := ys.length) (by omega)
      rwa [← hk, hj, Nat.pred_succ] at this
    have hxle : xs.length ≤ 2 ^ (j + 1) := hj ▸ Nat.le_pow_clog (by decide) _
    have hyle : ys.length ≤ 2 ^ (j + 1) := (hk ▸ hj) ▸ Nat.le_pow_clog (by decide) _
    rw [root, root, tree, tree, hj, ← hk, hj] at hroot
    rw [Canonical, canonicalCheck, tree, hj] at hcx
    rw [Canonical, canonicalCheck, tree, ← hk, hj] at hcy
    simp only [ofList, if_neg (by omega : ¬ xs.length ≤ 2 ^ j),
      if_neg (by omega : ¬ ys.length ≤ 2 ^ j), Tree.root] at hroot hcx hcy
    rcases combine_inj hroot with ⟨hl, hr⟩ | c
    · rcases virtualLeaves_eq_of_root_eq j _ _ hl with hvl₁ | c
      · have htake : xs.take (2 ^ j) = ys.take (2 ^ j) := by
          rw [← virtualLeaves_ofList_of_length_eq j (xs.take (2 ^ j))
              (by rw [List.length_take]; omega),
            ← virtualLeaves_ofList_of_length_eq j (ys.take (2 ^ j))
              (by rw [List.length_take]; omega), hvl₁]
        rcases virtualLeaves_eq_of_root_eq j _ _ hr with hvl₂ | c
        · have hdrop : xs.drop (2 ^ j) = ys.drop (2 ^ j) :=
            eq_of_virtualLeaves_eq j _ _
              (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)
              (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)
              hcx hcy hvl₂
          exact Or.inl (by
            rw [← List.take_append_drop (2 ^ j) xs, ← List.take_append_drop (2 ^ j) ys,
              htake, hdrop])
        · exact Or.inr c
      · exact Or.inr c
    · exact Or.inr c

end BtcVerified.Merkle
