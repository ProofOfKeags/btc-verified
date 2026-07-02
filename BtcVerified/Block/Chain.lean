import BtcVerified.Block.BlockHash
/-!
  # The blockchain: header hash linkage and the chain notion

  A blockchain, in this first iteration, is nothing more than a
  *structurally linked* sequence of headers. That weakness is the point:
  every later layer — proof of work, cumulative work, the block tree,
  consensus validity, fork choice — is a refinement of this type, not a
  rewrite of it.

  ## Linkage

  `BlockHeader.Extends h₂ h₁` is the one structural fact everything here is
  built from: `h₂`'s `prevBlockHash` is `h₁`'s hash — `h₂` is a header that
  directly follows `h₁` on a chain.

  ## Representation

  `Chain` is an inductive, **tip-first** (the newest header is the outermost
  constructor, matching how chain reasoning runs: backward from the present,
  not forward from genesis) and **hash-anchored at both ends**:
  `Chain anchor tip` is a segment of linked headers reaching from the block
  hash `anchor` (exclusive — the anchor's own header is not part of the
  segment) up to the tip hash `tip`. The indices themselves carry the
  linkage: `extend` accepts a new tip header exactly when the rest of the
  chain's tip hash is the new header's `prevBlockHash`, so no embedded
  equality proof rides along in the constructor.

  Keeping *both* endpoints in the type is what makes segments compose:
  `Chain.append` stacks a `Chain m t` on top of a `Chain a m`, with `nil` as
  the identity — the segment algebra the block tree (the next structural
  leaf, for fork detection) will reuse for branch paths. The full Bitcoin
  chain is the genesis instantiation `Chain 0 tip`: the zero hash is the
  genesis header's own `prevBlockHash`, so genesis-anchoring is a special
  case of the same type, not a separate treatment. One consequence: the
  empty segment `nil : Chain a a` exists for every anchor, so "nonempty" is
  a hypothesis on theorems that need an actual tip, never a structural
  given.

  ## Scope

  This is the *linear* chain — the structural layer fork-choice reasoning
  sits on, not fork choice itself. Explicitly out of scope for this leaf:
  proof of work (`nBits` → target decoding, the `hash ≤ target` check,
  per-block work), cumulative work and any ordering on chains, the block
  tree (fork *detection*), and all of consensus validity.

  Checked claims:

  * `Chain.toList_append`: stacking chain segments concatenates their header
    lists — composition is compatible with the plain-list view.
  * `Chain.isChain_toList`: a chain's list-of-headers view satisfies the
    decidable linkage predicate `IsChain` the chain's indices guarantee by
    construction.
  * `Chain.tip_commits`: two chains of equal length that share a tip hash
    carry the same header list — or two concrete byte strings collide under
    double-SHA-256. The tip hash commits to the entire history.
-/

namespace BtcVerified

/-! ## Linkage -/

/-- `h₂` directly extends `h₁`: its `prevBlockHash` is `h₁`'s hash — the one
structural fact consecutive headers of a chain satisfy. -/
def BlockHeader.Extends (h₂ h₁ : BlockHeader) : Prop := h₂.prevBlockHash = h₁.hash

/-- Linkage is decidable: both sides are computable digests. -/
instance instDecidableExtends (h₂ h₁ : BlockHeader) : Decidable (h₂.Extends h₁) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## The chain type -/

/-- A structurally linked segment of block headers, tip-first and
hash-anchored at both ends: `Chain anchor tip` reaches from the block hash
`anchor` (exclusive) up to the tip hash `tip`, and the indices carry the
linkage — extending demands the rest's tip hash be the new header's
`prevBlockHash`. The full Bitcoin chain is `Chain 0 tip`, the zero hash
being the genesis header's own `prevBlockHash`. -/
inductive Chain (anchor : Hash256) : Hash256 → Type where
  /-- The empty segment hanging from `anchor`: no headers yet, so its tip
  hash is the anchor itself. The identity for `Chain.append`. -/
  | nil : Chain anchor anchor
  /-- Extend a chain with a new tip header linking to the old tip. -/
  | extend (tip : BlockHeader) (rest : Chain anchor tip.prevBlockHash) :
      Chain anchor tip.hash

/-- The headers of a chain, tip-first (the newest header at the head of the
list) — the cheap, structure-forgetting view into plain list space that
golden vectors and the block tree speak. -/
def Chain.toList {a t : Hash256} : Chain a t → List BlockHeader
  | .nil => []
  | .extend tip rest => tip :: rest.toList

/-- Stack a chain segment on top of another whose tip hash is the upper
segment's anchor. The endpoints compose the way the indices dictate, and
`nil` is the identity. -/
def Chain.append {a m t : Hash256} : Chain m t → Chain a m → Chain a t
  | .nil, c => c
  | .extend tip rest, c => .extend tip (rest.append c)

/-- Stacking chain segments concatenates their header lists: composition is
compatible with the plain-list view. -/
theorem Chain.toList_append {a m t : Hash256} :
    (c₂ : Chain m t) → (c₁ : Chain a m) →
      (c₂.append c₁).toList = c₂.toList ++ c₁.toList
  | .nil, _ => rfl
  | .extend tip rest, c₁ => by
      simp only [Chain.append, Chain.toList, Chain.toList_append rest c₁,
        List.cons_append]

/-! ## The linkage predicate over plain lists -/

/-- The linkage predicate over a plain, tip-first header list: `hs` links
all the way from the tip hash down to `anchor` — the head hashes to the tip,
each header's hash is what the header after it (nearer the tip) points back
to, and an empty segment pins the tip hash to the anchor itself. Exactly
what a `Chain anchor tip`'s `toList` satisfies. -/
def IsChain (anchor : Hash256) : Hash256 → List BlockHeader → Prop
  | tip, [] => tip = anchor
  | tip, hd :: tl => hd.hash = tip ∧ IsChain anchor hd.prevBlockHash tl

/-- `IsChain` is decidable, so real header lists — golden vectors now, block
tree paths later — can be checked directly, without building a `Chain`
term. -/
instance instDecidableIsChain (a : Hash256) :
    (t : Hash256) → (hs : List BlockHeader) → Decidable (IsChain a t hs)
  | t, [] => inferInstanceAs (Decidable (t = a))
  | _, hd :: tl =>
    haveI := instDecidableIsChain a hd.prevBlockHash tl
    inferInstanceAs (Decidable (_ ∧ _))

/-- A chain's list-of-headers view satisfies the linkage predicate the
chain's indices guarantee by construction. -/
theorem Chain.isChain_toList {a : Hash256} :
    {t : Hash256} → (c : Chain a t) → IsChain a t c.toList
  | _, .nil => rfl
  | _, .extend tip rest => ⟨rfl, rest.isChain_toList⟩

/-! ## The tip-commitment theorem -/

/-- Two chains of equal length that share a tip hash carry the same header
list — or two concrete byte strings witness a double-SHA-256 collision. The
tip hash commits to the entire history: peeling the tip (equal hashes give
equal headers, via `BlockHeader.hash_faithful`, or a collision) forces equal
`prevBlockHash`es, and recursing identifies the chains one header at a
time. -/
theorem Chain.tip_commits {a₁ a₂ : Hash256} :
    {t₁ t₂ : Hash256} → (c₁ : Chain a₁ t₁) → (c₂ : Chain a₂ t₂) → t₁ = t₂ →
      c₁.toList.length = c₂.toList.length →
      c₁.toList = c₂.toList ∨ Sha256.Collision
  | _, _, .nil, .nil, _, _ => Or.inl rfl
  | _, _, .nil, .extend .., _, hlen => by
      simp only [Chain.toList, List.length_nil, List.length_cons] at hlen
      exact absurd hlen (by omega)
  | _, _, .extend .., .nil, _, hlen => by
      simp only [Chain.toList, List.length_nil, List.length_cons] at hlen
      exact absurd hlen (by omega)
  | _, _, .extend tip₁ rest₁, .extend tip₂ rest₂, heq, hlen => by
      simp only [Chain.toList, List.length_cons] at hlen
      rcases BlockHeader.hash_faithful heq with htip | hcol
      · rcases Chain.tip_commits rest₁ rest₂
          (congrArg BlockHeader.prevBlockHash htip) (by omega) with heql | hcol
        · refine Or.inl ?_
          simp only [Chain.toList]
          rw [heql, htip]
        · exact Or.inr hcol
      · exact Or.inr hcol

end BtcVerified
