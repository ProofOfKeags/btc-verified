import BtcVerified.Crypto.Merkle
/-!
  # Bitcoin Core's `ComputeMerkleRoot`, checked against the spec

  `BtcVerified.Merkle` is the platonic merkle spec: the root is one deterministic
  fold (`computeRoot`) and canonicality is a separate decidable property of the
  leaf list (`Canonical`). This module is not spec — it is *one implementation*,
  Bitcoin Core's, transcribed and checked against that spec. It lives under
  `Impl/BitcoinCore/` to keep the spec apart from the implementations measured
  against it; a second client's algorithm would sit beside it.

  ## The algorithm (Bitcoin Core, src/consensus/merkle.cpp @ d84fc352)

  ```cpp
  uint256 ComputeMerkleRoot(std::vector<uint256> hashes, bool* mutated) {
      bool mutation = false;
      while (hashes.size() > 1) {
          if (mutated) {
              for (size_t pos = 0; pos + 1 < hashes.size(); pos += 2) {
                  if (hashes[pos] == hashes[pos + 1]) mutation = true;
              }
          }
          if (hashes.size() & 1) {
              hashes.push_back(hashes.back());
          }
          SHA256D64(hashes[0].begin(), hashes[0].begin(), hashes.size() / 2);
          hashes.resize(hashes.size() / 2);
      }
      if (mutated) *mutated = mutation;
      if (hashes.size() == 0) return uint256();
      return hashes[0];
  }
  ```

  This is a transcription, not a literal copy: Core mutates a `std::vector` in a
  `while` loop; Lean is functional. The correspondence is *up to the
  imperative-to-functional rendering* — the loop invariant "`hashes` holds the
  current level" becomes the recursion's list argument, and the sticky local
  `bool mutation` becomes the OR of each level's scan, folded up through the
  recursion. One recursive call is one loop iteration; the `size > 1` guard is
  the two-or-more-element pattern. Line by line:

  - `while (hashes.size() > 1)` — the `x :: y :: rest` arm; `[]`/`[x]` exit.
  - `for (pos=0; pos+1<size; pos+=2) if (h[pos]==h[pos+1])` — `levelMutation`
    (the lone odd tail is left unscanned).
  - `if (size & 1) push_back(back())` then `SHA256D64` — `foldLevel`
    (pad-and-combine one level). `SHA256D64` computes double-SHA-256 over each
    64-byte pair; the spec models this abstractly as `combine l r =
    sha256d (l ++ r)`, so the equivalence is independent of which SHA-256 routine
    Core uses, and rides only on the leaf byte order being `uint256::begin()`
    order — fixed in `Crypto/Hash256.lean`, with no reversal, as Core does none
    in the tree.
  - sticky `bool mutation`, OR-ed across iterations — `levelMutation xs || r.2`,
    this level's scan OR-ed with the flag returned from the recursion.
  - `if (size == 0) return uint256()` — `[] => (0, ·)` (`0 : Hash256` is 32 zero
    bytes = `uint256()`); `return hashes[0]` — `[x] => (x, ·)`. Both cases are
    for totality: a consensus block always has a coinbase leaf, so neither the
    empty nor the singleton case arises in block validation.

  We model the `mutated != nullptr` branch — the consensus path. `CheckBlock`
  calls `BlockMerkleRoot(block, &mutated)` and rejects the block when the flag
  comes back set (the CVE-2012-2459 fix); `BlockMerkleRoot` forwards that
  non-null pointer, so the scan always runs. The `nullptr` callers (e.g.
  `BlockWitnessMerkleRoot`) skip the scan; `computeMerkleRoot_fst` shows the root
  is the same either way.

  The load-bearing fidelity point is the *ordering*: Core scans the current level
  for adjacent duplicates **before** it pads, so a duplicate that padding
  synthesizes (the copied last node of an odd level) is never compared to its
  twin — only a duplicate already present as a complete pair trips the flag. This
  is exactly the CVE-2012-2459 defense.
-/

namespace BtcVerified.Impl.BitcoinCore

open BtcVerified BtcVerified.Merkle

/-- One merkle level's pre-padding duplicate-pair scan, exactly Core's
`for (pos = 0; pos + 1 < size; pos += 2) if (hashes[pos] == hashes[pos+1])`:
fires iff some adjacent even-aligned pair is equal. The lone last element of an
odd-length level is never compared (at `pos = size - 1` the guard `pos + 1 <
size` fails), so a duplicate that padding will later synthesize cannot trigger
here — the CVE-2012-2459 defense. -/
def levelMutation : List Hash256 → Bool
  | [] => false
  | [_] => false
  | x :: y :: rest => (x == y) || levelMutation rest

/-- Bitcoin Core's `ComputeMerkleRoot(hashes, &mutated)` on the consensus path:
at each level with two or more nodes (the `while (size > 1)` guard), scan the
current level for an adjacent duplicate (`levelMutation`), pad-and-combine the
level (`foldLevel`), recurse, and OR this level's scan into the flag folded up
from the levels below — Core's sticky `bool mutation`. Returns the root paired
with that flag. -/
def computeMerkleRoot : List Hash256 → Hash256 × Bool
  | [] => (0, false)
  | [x] => (x, false)
  | x :: y :: rest =>
      let r := computeMerkleRoot (foldLevel (x :: y :: rest))
      (r.1, levelMutation (x :: y :: rest) || r.2)
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

/-! ## The mutation check, read off the tree (internal)

  `Canonical` is a right-spine property of the spec's `Tree`, while the scan
  above is a flat fold over the list. They meet through `treeMutation`, the same
  duplicate check read off the tree the fold builds — a genuine interior `node`
  with equal-root children, `pad` nodes exempt. `computeMerkleRoot_snd_eq_treeMutation`
  is the commute triangle relating the two, the mutation analogue of
  `computeRoot_eq_root`. All `private`: durable facts on the way to the public
  results, not part of the surface. -/

/-- The whole-tree image of the `mutated` flag: a tree mutates iff some genuine
interior `node` joins two subtrees with equal roots. A `pad` node contributes no
equality test of its own — mirroring that the padded duplicate is never scanned
— but its child is still walked. -/
private def treeMutation : Tree → Bool
  | .leaf _ => false
  | .pad t => treeMutation t
  | .node l r => (l.root == r.root) || treeMutation l || treeMutation r

/-- A level scan distributes over an append at an even boundary: a duplicate in
`as ++ bs` is a duplicate in `as` or in `bs`, since even length keeps the pairing
aligned across the seam. -/
private theorem levelMutation_append : ∀ (as bs : List Hash256), as.length % 2 = 0 →
    levelMutation (as ++ bs) = (levelMutation as || levelMutation bs)
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | a :: a' :: rest, bs, h => by
    have hrest : rest.length % 2 = 0 := by simp at h; omega
    cases bs with
    | nil => simp [levelMutation]
    | cons b bs' =>
      simp only [List.cons_append, levelMutation,
        levelMutation_append rest (b :: bs') hrest, Bool.or_assoc]

/-- Equal materialized leaf sequences at one width force equal roots: the forward
(collision-free) mirror of the spec's `virtualLeaves_eq_of_root_eq`. Applying
`combine` to equal inputs gives equal outputs, so no hash is ever inverted. -/
private theorem root_eq_of_virtualLeaves_eq :
    ∀ (k : Nat) (xs ys : List Hash256),
      (ofList xs k).virtualLeaves = (ofList ys k).virtualLeaves →
      (ofList xs k).root = (ofList ys k).root := by
  intro k
  induction k with
  | zero =>
    intro xs ys h
    simpa [ofList, Tree.root, Tree.virtualLeaves] using h
  | succ k ih =>
    intro xs ys h
    simp only [ofList] at h ⊢
    by_cases hx : xs.length ≤ 2 ^ k <;> by_cases hy : ys.length ≤ 2 ^ k
    · rw [if_pos hx, if_pos hy] at h ⊢
      rw [Tree.virtualLeaves, Tree.virtualLeaves] at h
      rw [Tree.root, Tree.root]
      have hlen : ((ofList xs k).virtualLeaves).length
          = ((ofList ys k).virtualLeaves).length := by
        rw [length_virtualLeaves_ofList, length_virtualLeaves_ofList]
      rw [ih xs ys (List.append_inj h hlen).1]
    · rw [if_pos hx, if_neg hy] at h ⊢
      rw [Tree.virtualLeaves, Tree.virtualLeaves] at h
      rw [Tree.root, Tree.root]
      have hlen : ((ofList xs k).virtualLeaves).length
          = ((ofList (ys.take (2 ^ k)) k).virtualLeaves).length := by
        rw [length_virtualLeaves_ofList, length_virtualLeaves_ofList]
      obtain ⟨h₁, h₂⟩ := List.append_inj h hlen
      rw [← ih xs (ys.take (2 ^ k)) h₁, ← ih xs (ys.drop (2 ^ k)) h₂]
    · rw [if_neg hx, if_pos hy] at h ⊢
      rw [Tree.virtualLeaves, Tree.virtualLeaves] at h
      rw [Tree.root, Tree.root]
      have hlen : ((ofList (xs.take (2 ^ k)) k).virtualLeaves).length
          = ((ofList ys k).virtualLeaves).length := by
        rw [length_virtualLeaves_ofList, length_virtualLeaves_ofList]
      obtain ⟨h₁, h₂⟩ := List.append_inj h hlen
      rw [ih (xs.take (2 ^ k)) ys h₁, ih (xs.drop (2 ^ k)) ys h₂]
    · rw [if_neg hx, if_neg hy] at h ⊢
      rw [Tree.virtualLeaves, Tree.virtualLeaves] at h
      rw [Tree.root, Tree.root]
      have hlen : ((ofList (xs.take (2 ^ k)) k).virtualLeaves).length
          = ((ofList (ys.take (2 ^ k)) k).virtualLeaves).length := by
        rw [length_virtualLeaves_ofList, length_virtualLeaves_ofList]
      obtain ⟨h₁, h₂⟩ := List.append_inj h hlen
      rw [ih (xs.take (2 ^ k)) (ys.take (2 ^ k)) h₁, ih (xs.drop (2 ^ k)) (ys.drop (2 ^ k)) h₂]

/-- One spec level absorbs one fold level for the whole-tree flag: the
width-`2 ^ (k + 1)` tree over `xs` mutates iff this level's scan fires or the
width-`2 ^ k` tree over `foldLevel xs` mutates. The counterpart of
`ofList_root_foldLevel`, peeling Core's bottom iteration. -/
private theorem treeMutation_ofList_succ :
    ∀ (k : Nat) (xs : List Hash256), 0 < xs.length → xs.length ≤ 2 ^ (k + 1) →
      treeMutation (ofList xs (k + 1))
        = (levelMutation xs || treeMutation (ofList (foldLevel xs) k)) := by
  intro k
  induction k with
  | zero =>
    intro xs h0 h2
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at h2
    cases xs with
    | nil => simp at h0
    | cons x xs' =>
      cases xs' with
      | nil => simp [ofList, foldLevel, treeMutation, levelMutation]
      | cons y xs'' =>
        have hnil : xs'' = [] := by
          simp only [List.length_cons] at h2
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst hnil
        simp [ofList, foldLevel, treeMutation, levelMutation, Tree.root]
  | succ k ih =>
    intro xs h0 h2
    have hpow' : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := Nat.two_pow_succ k
    have hpow2 : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := Nat.two_pow_succ (k + 1)
    by_cases hsplit : xs.length ≤ 2 ^ (k + 1)
    · have hfold : (foldLevel xs).length ≤ 2 ^ k := by rw [foldLevel_length]; omega
      have hL : ofList xs (k + 1 + 1) = .pad (ofList xs (k + 1)) := by rw [ofList, if_pos hsplit]
      have hR : ofList (foldLevel xs) (k + 1) = .pad (ofList (foldLevel xs) k) := by
        rw [ofList, if_pos hfold]
      rw [hL, hR, treeMutation, treeMutation, ih xs h0 hsplit]
    · have hsplit' : 2 ^ (k + 1) < xs.length := by omega
      have htake : (xs.take (2 ^ (k + 1))).length = 2 ^ (k + 1) := by rw [List.length_take]; omega
      have hsplitFold : foldLevel xs = foldLevel (xs.take (2 ^ (k + 1)))
          ++ foldLevel (xs.drop (2 ^ (k + 1))) := by
        rw [← foldLevel_append _ _ (by omega), List.take_append_drop]
      have hfoldTake : (foldLevel (xs.take (2 ^ (k + 1)))).length = 2 ^ k := by
        rw [foldLevel_length, htake]; omega
      have hfoldLen : ¬ (foldLevel xs).length ≤ 2 ^ k := by rw [foldLevel_length]; omega
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
      have hT0 : 0 < (xs.take (2 ^ (k + 1))).length := by rw [htake]; exact Nat.pow_pos (by decide)
      have hTle : (xs.take (2 ^ (k + 1))).length ≤ 2 ^ (k + 1) := by rw [htake]
      have hD0 : 0 < (xs.drop (2 ^ (k + 1))).length := by rw [List.length_drop]; omega
      have hDle : (xs.drop (2 ^ (k + 1))).length ≤ 2 ^ (k + 1) := by rw [List.length_drop]; omega
      have hlm : levelMutation xs
          = (levelMutation (xs.take (2 ^ (k + 1))) || levelMutation (xs.drop (2 ^ (k + 1)))) := by
        conv_lhs => rw [← List.take_append_drop (2 ^ (k + 1)) xs]
        exact levelMutation_append _ _ (by omega)
      have hLr := ofList_root_foldLevel k (xs.take (2 ^ (k + 1))) hT0 hTle
      have hRr := ofList_root_foldLevel k (xs.drop (2 ^ (k + 1))) hD0 hDle
      have hLm := ih (xs.take (2 ^ (k + 1))) hT0 hTle
      have hRm := ih (xs.drop (2 ^ (k + 1))) hD0 hDle
      rw [hL, hR, treeMutation, treeMutation, htakeF, hdropF, hLr, hRr, hLm, hRm, hlm]
      ac_rfl

/-- Core's mutation flag, computed over the list, equals the same duplicate check
read off the tree the fold builds: `(computeMerkleRoot xs).2 = treeMutation
(tree xs)`. The commute triangle between the flat computation and the structural
reading — the mutation analogue of the spec's `computeRoot_eq_root`. -/
private theorem computeMerkleRoot_snd_eq_treeMutation : ∀ xs : List Hash256,
    (computeMerkleRoot xs).2 = treeMutation (tree xs)
  | [] => by simp [computeMerkleRoot, tree, Nat.clog_zero_right, ofList, treeMutation]
  | [_] => by simp [computeMerkleRoot, tree, Nat.clog_one_right, ofList, treeMutation]
  | x :: y :: rest => by
    have hlen : 2 ≤ (x :: y :: rest).length := by simp
    have hclog : Nat.clog 2 (x :: y :: rest).length
        = Nat.clog 2 (((x :: y :: rest).length + 1) / 2) + 1 := by
      rw [Nat.clog_of_two_le (by decide) hlen,
        show (x :: y :: rest).length + 2 - 1 = (x :: y :: rest).length + 1 by omega]
    have hfl : (foldLevel (x :: y :: rest)).length = ((x :: y :: rest).length + 1) / 2 :=
      foldLevel_length _
    simp only [computeMerkleRoot]
    rw [computeMerkleRoot_snd_eq_treeMutation (foldLevel (x :: y :: rest)),
      tree, tree, hfl, hclog,
      treeMutation_ofList_succ (Nat.clog 2 (((x :: y :: rest).length + 1) / 2)) (x :: y :: rest)
        (by simp) (by
          calc (x :: y :: rest).length ≤ 2 ^ Nat.clog 2 (x :: y :: rest).length :=
                Nat.le_pow_clog (by decide) _
            _ = 2 ^ (Nat.clog 2 (((x :: y :: rest).length + 1) / 2) + 1) := by rw [← hclog])]
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

/-- A tree Core accepts (whole-tree flag clear) is spine-canonical: with no
genuine node joining equal-root children, no right-spine node joins two
identical materialized leaf sequences either, since equal sequences at equal
width give equal roots. Stated over `ofList` because that step needs the
children to be width-`2 ^ k` trees, which only the construction guarantees. -/
private theorem spineCanonical_ofList_of_treeMutation :
    ∀ (k : Nat) (xs : List Hash256),
      treeMutation (ofList xs k) = false → (ofList xs k).spineCanonical = true := by
  intro k
  induction k with
  | zero => intro xs _; simp [ofList, Tree.spineCanonical]
  | succ k ih =>
    intro xs hm
    rw [ofList] at hm ⊢
    by_cases hsplit : xs.length ≤ 2 ^ k
    · rw [if_pos hsplit] at hm ⊢
      rw [treeMutation] at hm
      rw [Tree.spineCanonical]
      exact ih xs hm
    · rw [if_neg hsplit] at hm ⊢
      rw [treeMutation] at hm
      rw [Tree.spineCanonical]
      simp only [Bool.or_eq_false_iff] at hm
      obtain ⟨⟨hbeq, _⟩, hRm⟩ := hm
      rw [Bool.and_eq_true]
      refine ⟨?_, ih _ hRm⟩
      rw [bne_iff_ne]
      intro hvl
      rw [root_eq_of_virtualLeaves_eq k (xs.take (2 ^ k)) (xs.drop (2 ^ k)) hvl] at hbeq
      simp at hbeq

/-! ## What is proved -/

/-- Bitcoin Core returns exactly the spec's `computeRoot` in its first component
— unconditionally; the mutated flag does not affect the returned root. -/
theorem computeMerkleRoot_fst : ∀ xs : List Hash256,
    (computeMerkleRoot xs).1 = computeRoot xs
  | [] => by simp [computeMerkleRoot, computeRoot]
  | [_] => by simp [computeMerkleRoot, computeRoot]
  | x :: y :: rest => by
    simp only [computeMerkleRoot]
    rw [computeMerkleRoot_fst (foldLevel (x :: y :: rest))]
    conv_rhs => rw [computeRoot]
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

/-- A leaf list Bitcoin Core accepts (no mutation) is `Canonical` —
unconditionally, with no distinctness hypothesis and no collision caveat. The
converse fails: Core's scan is strictly stronger (e.g. `[a, a]` is canonical yet
mutates), so `Canonical` does not imply non-mutation. -/
theorem canonical_of_not_mutated (xs : List Hash256)
    (hm : (computeMerkleRoot xs).2 = false) : Canonical xs := by
  have hmut : treeMutation (tree xs) = false := by
    rw [← computeMerkleRoot_snd_eq_treeMutation]; exact hm
  have hsc : (tree xs).spineCanonical = true :=
    spineCanonical_ofList_of_treeMutation (Nat.clog 2 xs.length) xs hmut
  unfold Canonical canonicalCheck
  cases htx : tree xs with
  | leaf h => rfl
  | pad t => rfl
  | node l r =>
    rw [htx, Tree.spineCanonical, Bool.and_eq_true] at hsc
    exact hsc.2

/-- If Bitcoin Core accepts two nonempty leaf lists of equal enclosing width (no
mutation) and computes the same merkle root for both, the lists are equal — or
two concrete byte strings collide under double-SHA-256. Core's single fused check
recovers the injectivity `root_inj_of_canonical` provides. -/
theorem eq_of_computeMerkleRoot_eq_of_not_mutated {xs ys : List Hash256}
    (h0x : xs ≠ []) (h0y : ys ≠ [])
    (hk : Nat.clog 2 xs.length = Nat.clog 2 ys.length)
    (hmx : (computeMerkleRoot xs).2 = false)
    (hmy : (computeMerkleRoot ys).2 = false)
    (hroot : (computeMerkleRoot xs).1 = (computeMerkleRoot ys).1) :
    xs = ys ∨ Sha256.Collision := by
  have hrx : (computeMerkleRoot xs).1 = root xs := by
    rw [computeMerkleRoot_fst, computeRoot_eq_root]
  have hry : (computeMerkleRoot ys).1 = root ys := by
    rw [computeMerkleRoot_fst, computeRoot_eq_root]
  exact root_inj_of_canonical (canonical_of_not_mutated xs hmx)
    (canonical_of_not_mutated ys hmy) h0x h0y hk (by rw [← hrx, ← hry, hroot])

end BtcVerified.Impl.BitcoinCore
