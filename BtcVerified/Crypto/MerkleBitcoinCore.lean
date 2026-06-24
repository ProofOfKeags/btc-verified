import BtcVerified.Crypto.Merkle
/-!
  # Bitcoin Core's `ComputeMerkleRoot`, and its non-mutation guarantee

  `BtcVerified.Merkle` factors apart what Bitcoin Core fuses: the merkle root is
  one deterministic fold (`computeRoot`), and canonicality is a separate
  decidable property of the leaf list (`Canonical`). Core, by contrast, computes
  the root and a `mutated` flag in a single bottom-up pass. This module pins the
  two views together: it transcribes Core's algorithm verbatim and proves that
  passing Core's check (`mutated = false`) implies the list is `Canonical` — so
  Core's acceptance recovers the same injectivity `root_inj_of_canonical` gives.

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

  We model the `mutated != nullptr` branch — the consensus-validation path.
  Consensus reaches `ComputeMerkleRoot` through `CheckBlock`, which calls
  `BlockMerkleRoot(block, &mutated)` and rejects the block when the flag comes
  back set (`src/validation.cpp` — the CVE-2012-2459 fix); `BlockMerkleRoot`
  forwards that non-null pointer to `ComputeMerkleRoot`, so the duplicate scan
  always runs on this path. The `nullptr` branch — taken by non-validating
  callers such as `BlockWitnessMerkleRoot` — skips the scan and is not modeled;
  `computeMerkleRoot_fst` shows the returned root is the same either way. The
  C++/Lean correspondence:

  - `while (hashes.size() > 1)` — the `x :: y :: rest` arm (size ≥ 2).
  - `for (pos=0; pos+1<size; pos+=2) if (h[pos]==h[pos+1])` — `levelMutation`
    (the lone odd tail is left unscanned).
  - `if (size & 1) push_back(back())` then `SHA256D64` — `foldLevel`
    (pad-and-combine one level).
  - sticky `mutation` OR-ed across iterations — `levelMutation xs || (recurse).2`.
  - `if (size == 0) return uint256()` — `[] => (0, false)`.
  - `return hashes[0]` — `[x] => (x, false)`, and the `.1` of the recursion.

  The load-bearing fidelity point is the *ordering*: Core scans the current
  level for adjacent duplicates **before** it pads. So a duplicate that padding
  itself synthesizes (the copied last node of an odd level) is never compared to
  its twin — only a duplicate already present as a complete pair triggers the
  flag. This is exactly the CVE-2012-2459 defense, and `Tree.mutation` mirrors it
  structurally: a `pad` node contributes no equality test of its own.

  ## Why non-mutation suffices, and why Core is strictly stronger

  Padding only ever duplicates trailing power-of-two-aligned blocks — the right
  spine — so the only cross-length collision is a trailing block that
  materializes its left sibling. `Canonical` forbids exactly that, on the right
  spine, root-exempt. Core's scan is uniform over the whole tree, so it *also*
  rejects equal-root pairs no padding could produce (e.g. `[a, a]`, canonical
  because the root is exempt, yet mutated). Core is therefore strictly stronger
  than `Canonical`; the implication runs one way only:
  `mutated = false → Canonical`, and that one direction is unconditional and
  collision-free — no transaction-distinctness hypothesis is needed.

  Checked claims:

  * `BitcoinCore.computeMerkleRoot_eq_mutation`: Core's fused computation equals
    the structural fold's root paired with the structural mutation flag — an
    unconditional, hypothesis-free identity.
  * `BitcoinCore.canonical_of_not_mutated`: a leaf list Core accepts (no
    mutation) is `Canonical` — unconditionally.
  * `BitcoinCore.eq_of_computeMerkleRoot_eq_of_not_mutated`: two nonempty
    equal-width leaf lists Core accepts with equal roots are equal — or two
    concrete byte strings collide under double-SHA-256.
-/

namespace BtcVerified.Merkle

open BtcVerified.Serialize

/-- The structural image of Core's accumulated `mutated` flag, read off the tree
the fold builds: a tree mutates iff some genuine interior `node` (never a `pad`)
joins two subtrees with equal roots. A `pad t` contributes no equality test of
its own — its synthetic duplicate is the odd element Core's `pos + 1 < size`
guard never scans — but its child is still walked, since deeper levels are
scanned in full. -/
def Tree.mutation : Tree → Bool
  | .leaf _ => false
  | .pad t => t.mutation
  | .node l r => (l.root == r.root) || l.mutation || r.mutation

namespace BitcoinCore

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

/-- Bitcoin Core's `ComputeMerkleRoot(hashes, &mutated)` on the consensus path
(the `mutated != nullptr` branch, where the scan always runs): at each level,
scan adjacent pairs for a duplicate (`levelMutation`), then pad-and-combine the
level (`foldLevel`), recurse, and OR this level's flag into the accumulator. The
empty input returns `uint256()` (here `0`) with no mutation; a singleton exits
the `while (size > 1)` loop unscanned. Returns the root paired with `mutated`. -/
def computeMerkleRoot : List Hash256 → Hash256 × Bool
  | [] => (0, false)
  | [x] => (x, false)
  | x :: y :: rest =>
      let r := computeMerkleRoot (foldLevel (x :: y :: rest))
      (r.1, levelMutation (x :: y :: rest) || r.2)
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

end BitcoinCore

/-! ## One level: the scan distributes, the structure peels -/

/-- A level scan distributes over an append at an even boundary: a duplicate in
`as ++ bs` is a duplicate in `as` or in `bs`, since even length keeps the pairing
aligned across the seam. -/
theorem levelMutation_append : ∀ (as bs : List Hash256), as.length % 2 = 0 →
    BitcoinCore.levelMutation (as ++ bs)
      = (BitcoinCore.levelMutation as || BitcoinCore.levelMutation bs)
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | a :: a' :: rest, bs, h => by
    have hrest : rest.length % 2 = 0 := by simp at h; omega
    cases bs with
    | nil => simp [BitcoinCore.levelMutation]
    | cons b bs' =>
      simp only [List.cons_append, BitcoinCore.levelMutation,
        levelMutation_append rest (b :: bs') hrest, Bool.or_assoc]

/-- Equal materialized leaf sequences at one width force equal roots: the
forward (collision-free) mirror of `virtualLeaves_eq_of_root_eq`. Applying
`combine` to equal inputs gives equal outputs, so no hash is ever inverted. -/
theorem root_eq_of_virtualLeaves_eq :
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

/-- One spec level absorbs one fold level for the mutation flag: the
width-`2 ^ (k + 1)` tree over `xs` mutates iff this level's scan fires or the
width-`2 ^ k` tree over `foldLevel xs` mutates. The structural counterpart of
`ofList_root_foldLevel`, peeling Core's bottom iteration. -/
theorem Tree.mutation_ofList_succ :
    ∀ (k : Nat) (xs : List Hash256), 0 < xs.length → xs.length ≤ 2 ^ (k + 1) →
      (ofList xs (k + 1)).mutation
        = (BitcoinCore.levelMutation xs || (ofList (foldLevel xs) k).mutation) := by
  intro k
  induction k with
  | zero =>
    intro xs h0 h2
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at h2
    cases xs with
    | nil => simp at h0
    | cons x xs' =>
      cases xs' with
      | nil => simp [ofList, foldLevel, Tree.mutation, BitcoinCore.levelMutation]
      | cons y xs'' =>
        have hnil : xs'' = [] := by
          simp only [List.length_cons] at h2
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst hnil
        simp [ofList, foldLevel, Tree.mutation, BitcoinCore.levelMutation, Tree.root]
  | succ k ih =>
    intro xs h0 h2
    have hpow' : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := Nat.two_pow_succ k
    have hpow2 : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := Nat.two_pow_succ (k + 1)
    by_cases hsplit : xs.length ≤ 2 ^ (k + 1)
    · have hfold : (foldLevel xs).length ≤ 2 ^ k := by rw [foldLevel_length]; omega
      have hL : ofList xs (k + 1 + 1) = .pad (ofList xs (k + 1)) := by rw [ofList, if_pos hsplit]
      have hR : ofList (foldLevel xs) (k + 1) = .pad (ofList (foldLevel xs) k) := by
        rw [ofList, if_pos hfold]
      rw [hL, hR, Tree.mutation, Tree.mutation, ih xs h0 hsplit]
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
      have hlm : BitcoinCore.levelMutation xs
          = (BitcoinCore.levelMutation (xs.take (2 ^ (k + 1)))
              || BitcoinCore.levelMutation (xs.drop (2 ^ (k + 1)))) := by
        conv_lhs => rw [← List.take_append_drop (2 ^ (k + 1)) xs]
        exact levelMutation_append _ _ (by omega)
      have hLr := ofList_root_foldLevel k (xs.take (2 ^ (k + 1))) hT0 hTle
      have hRr := ofList_root_foldLevel k (xs.drop (2 ^ (k + 1))) hD0 hDle
      have hLm := ih (xs.take (2 ^ (k + 1))) hT0 hTle
      have hRm := ih (xs.drop (2 ^ (k + 1))) hD0 hDle
      rw [hL, hR, Tree.mutation, Tree.mutation, htakeF, hdropF, hLr, hRr, hLm, hRm, hlm]
      ac_rfl

/-- The bottom-up fold's accumulated flag is the structural mutation flag of the
tree it builds. The mutation analogue of `computeRoot_eq_root`. -/
theorem BitcoinCore.computeMerkleRoot_snd_eq_treeMutation : ∀ xs : List Hash256,
    (BitcoinCore.computeMerkleRoot xs).2 = (tree xs).mutation
  | [] => by simp [BitcoinCore.computeMerkleRoot, tree, Nat.clog_zero_right, ofList, Tree.mutation]
  | [_] => by simp [BitcoinCore.computeMerkleRoot, tree, Nat.clog_one_right, ofList, Tree.mutation]
  | x :: y :: rest => by
    have hlen : 2 ≤ (x :: y :: rest).length := by simp
    have hclog : Nat.clog 2 (x :: y :: rest).length
        = Nat.clog 2 (((x :: y :: rest).length + 1) / 2) + 1 := by
      rw [Nat.clog_of_two_le (by decide) hlen,
        show (x :: y :: rest).length + 2 - 1 = (x :: y :: rest).length + 1 by omega]
    have hfl : (foldLevel (x :: y :: rest)).length = ((x :: y :: rest).length + 1) / 2 :=
      foldLevel_length _
    simp only [BitcoinCore.computeMerkleRoot]
    rw [BitcoinCore.computeMerkleRoot_snd_eq_treeMutation (foldLevel (x :: y :: rest)),
      tree, tree, hfl, hclog,
      Tree.mutation_ofList_succ (Nat.clog 2 (((x :: y :: rest).length + 1) / 2)) (x :: y :: rest)
        (by simp) (by
          calc (x :: y :: rest).length ≤ 2 ^ Nat.clog 2 (x :: y :: rest).length :=
                Nat.le_pow_clog (by decide) _
            _ = 2 ^ (Nat.clog 2 (((x :: y :: rest).length + 1) / 2) + 1) := by rw [← hclog])]
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

/-- Bitcoin Core returns exactly the repo's `computeRoot` in its first component
— unconditionally; the mutated flag does not affect the returned root. -/
theorem BitcoinCore.computeMerkleRoot_fst : ∀ xs : List Hash256,
    (BitcoinCore.computeMerkleRoot xs).1 = computeRoot xs
  | [] => by simp [BitcoinCore.computeMerkleRoot, computeRoot]
  | [_] => by simp [BitcoinCore.computeMerkleRoot, computeRoot]
  | x :: y :: rest => by
    simp only [BitcoinCore.computeMerkleRoot]
    rw [BitcoinCore.computeMerkleRoot_fst (foldLevel (x :: y :: rest))]
    conv_rhs => rw [computeRoot]
  termination_by xs => xs.length
  decreasing_by simp [foldLevel_length]; omega

/-- Bitcoin Core's `ComputeMerkleRoot` returns exactly the structural fold's root
paired with the structural mutation flag of the tree it builds — an
unconditional, hypothesis-free identity. -/
theorem BitcoinCore.computeMerkleRoot_eq_mutation (xs : List Hash256) :
    BitcoinCore.computeMerkleRoot xs = (computeRoot xs, (tree xs).mutation) := by
  rw [Prod.ext_iff]
  exact ⟨BitcoinCore.computeMerkleRoot_fst xs,
    BitcoinCore.computeMerkleRoot_snd_eq_treeMutation xs⟩

/-! ## Non-mutation implies canonicality -/

/-- A non-mutating `ofList` tree is spine-canonical: with no genuine node
joining equal-root children, no right-spine node joins two identical
materialized leaf sequences either, since equal sequences at equal width give
equal roots (`root_eq_of_virtualLeaves_eq`). Stated for `ofList` because the
equal-leaves-to-equal-roots step needs the children to be width-`2 ^ k` trees,
which only the construction guarantees. -/
theorem spineCanonical_ofList_of_mutation :
    ∀ (k : Nat) (xs : List Hash256),
      (ofList xs k).mutation = false → (ofList xs k).spineCanonical = true := by
  intro k
  induction k with
  | zero => intro xs _; simp [ofList, Tree.spineCanonical]
  | succ k ih =>
    intro xs hm
    rw [ofList] at hm ⊢
    by_cases hsplit : xs.length ≤ 2 ^ k
    · rw [if_pos hsplit] at hm ⊢
      rw [Tree.mutation] at hm
      rw [Tree.spineCanonical]
      exact ih xs hm
    · rw [if_neg hsplit] at hm ⊢
      rw [Tree.mutation] at hm
      rw [Tree.spineCanonical]
      simp only [Bool.or_eq_false_iff] at hm
      obtain ⟨⟨hbeq, _⟩, hRm⟩ := hm
      rw [Bool.and_eq_true]
      refine ⟨?_, ih _ hRm⟩
      rw [bne_iff_ne]
      intro hvl
      rw [root_eq_of_virtualLeaves_eq k (xs.take (2 ^ k)) (xs.drop (2 ^ k)) hvl] at hbeq
      simp at hbeq

/-- A leaf list Bitcoin Core accepts (no mutation) is `Canonical` —
unconditionally, with no distinctness hypothesis and no collision caveat. The
converse fails: Core's scan is strictly stronger (e.g. `[a, a]` is canonical yet
mutates), so `Canonical` does not imply non-mutation. -/
theorem BitcoinCore.canonical_of_not_mutated (xs : List Hash256)
    (hm : (BitcoinCore.computeMerkleRoot xs).2 = false) : Canonical xs := by
  have hmut : (tree xs).mutation = false := by
    rw [← BitcoinCore.computeMerkleRoot_snd_eq_treeMutation]; exact hm
  have hsc : (tree xs).spineCanonical = true :=
    spineCanonical_ofList_of_mutation (Nat.clog 2 xs.length) xs hmut
  unfold Canonical canonicalCheck
  cases htx : tree xs with
  | leaf h => rfl
  | pad t => rfl
  | node l r =>
    rw [htx, Tree.spineCanonical, Bool.and_eq_true] at hsc
    exact hsc.2

/-! ## The injectivity payoff -/

/-- If Bitcoin Core accepts two nonempty leaf lists of equal enclosing width (no
mutation) and computes the same merkle root for both, the lists are equal — or
two concrete byte strings collide under double-SHA-256. Core's single fused
check recovers the injectivity `root_inj_of_canonical` provides. -/
theorem BitcoinCore.eq_of_computeMerkleRoot_eq_of_not_mutated {xs ys : List Hash256}
    (h0x : xs ≠ []) (h0y : ys ≠ [])
    (hk : Nat.clog 2 xs.length = Nat.clog 2 ys.length)
    (hmx : (BitcoinCore.computeMerkleRoot xs).2 = false)
    (hmy : (BitcoinCore.computeMerkleRoot ys).2 = false)
    (hroot : (BitcoinCore.computeMerkleRoot xs).1 = (BitcoinCore.computeMerkleRoot ys).1) :
    xs = ys ∨ Sha256.Collision := by
  have hrx : (BitcoinCore.computeMerkleRoot xs).1 = root xs := by
    rw [BitcoinCore.computeMerkleRoot_fst, computeRoot_eq_root]
  have hry : (BitcoinCore.computeMerkleRoot ys).1 = root ys := by
    rw [BitcoinCore.computeMerkleRoot_fst, computeRoot_eq_root]
  exact root_inj_of_canonical (BitcoinCore.canonical_of_not_mutated xs hmx)
    (BitcoinCore.canonical_of_not_mutated ys hmy) h0x h0y hk
    (by rw [← hrx, ← hry, hroot])

end BtcVerified.Merkle
