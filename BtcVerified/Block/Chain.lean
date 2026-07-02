import BtcVerified.Block.BlockHash
/-!
  # The blockchain: header linkage and the chain notion

  A blockchain, in this first iteration, is nothing more than a
  *structurally linked* sequence of headers. That weakness is the point:
  every later refinement — proof of work, cumulative work, the block tree,
  consensus validity — builds on this layer instead of rewriting it.

  ## Linkage

  `BlockHeader.Extends h₂ h₁` is the one structural fact everything else
  here is built from: `h₂`'s `prevBlockHash` is `h₁`'s hash, i.e. `h₂` is
  the header that directly follows `h₁` on the chain.

  ## Representation

  `Chain` is an inductive, **tip-first** (the newest header is the outer
  constructor) and **hash-anchored**: `Chain (h : Hash256)` is a chain whose
  next link — real or hypothetical — must carry `h` as its `prevBlockHash`.
  Concretely, `h` is either the anchor of an empty chain (`nil`) or the hash
  of the chain's own outermost header (`extend`).

  This single index does double duty as both "the anchor a segment hangs
  from" and "the tip hash a chain currently offers", which is exactly what
  dissolves the genesis-vs-parameterized tension: the full Bitcoin chain is
  just `Chain 0` (`0`, the zero hash, is the genesis header's own
  `prevBlockHash`), with the genesis header as its deepest link, and a
  segment hanging off any interior block is a `Chain` anchored at that
  block's hash — no separate treatment needed. Tree paths (the next
  structural leaf, for fork detection) will want exactly these segments.

  Tip-first orientation matches how the headline theorem below recurses —
  peel the tip, recurse on what remains — the same direction fork-choice
  reasoning runs in: backward from the present, not forward from genesis.

  One consequence of the hash-anchored `nil`: the empty chain exists for
  every anchor, and is the identity for stacking chain segments (a `Chain
  h₂` on top of a `Chain h₁` whose tip hash is `h₂`). So "nonempty" is a
  hypothesis theorems needing an actual tip must state, not a structural
  given.

  ## Scope

  This is the *linear* chain — the structural layer fork-choice reasoning
  sits on, not fork choice itself. Explicitly out of scope for this leaf:
  proof of work (`nBits` → target, the `hash ≤ target` check, per-block
  work), cumulative work and any ordering on chains, the block tree (fork
  *detection*, which reuses this linkage relation), and all of consensus
  validity. A chain here is only ever structurally linked headers.

  Checked claims:

  * `Chain.isChain_toList`: a chain's list-of-headers view satisfies the
    decidable linkage predicate `IsChain` a chain was built to satisfy.
  * `Chain.tip_commits`: two chains of equal length that share a tip hash
    carry the same header list — or two concrete byte strings collide under
    double-SHA-256. The tip hash commits to the entire history.
-/

namespace BtcVerified

/-! ## Linkage -/

/-- `h₂` directly extends `h₁`: its `prevBlockHash` is `h₁`'s hash — the one
structural fact a chain's consecutive headers satisfy. -/
def BlockHeader.Extends (h₂ h₁ : BlockHeader) : Prop := h₂.prevBlockHash = h₁.hash

instance instDecidableExtends (h₂ h₁ : BlockHeader) : Decidable (h₂.Extends h₁) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## The chain type -/

/-- A structurally linked sequence of block headers, tip-first and
hash-anchored (see the module header for the design rationale). `Chain h`
is a chain whose next link must carry `h` as its `prevBlockHash` — either
because `h` is the anchor of an empty chain, or because `h` is the hash of
the chain's own outermost header. -/
inductive Chain : Hash256 → Type where
  /-- The empty chain hanging from `anchor`: no headers yet, so any header
  whose `prevBlockHash` is `anchor` may extend it directly. The identity for
  stacking chain segments. -/
  | nil (anchor : Hash256) : Chain anchor
  /-- Extend a chain whose current head is `prev` with a new tip header
  linking to it. -/
  | extend (prev : Hash256) (rest : Chain prev) (tip : BlockHeader)
      (linked : tip.prevBlockHash = prev) : Chain tip.hash

/-- The headers of a chain, tip-first (the newest header at the head of the
list) — the cheap, structure-forgetting view into plain list space that
golden vectors and the block tree speak. -/
def Chain.toList {h : Hash256} : Chain h → List BlockHeader
  | .nil _ => []
  | .extend _ rest tip _ => tip :: rest.toList

/-! ## The linkage predicate over plain lists -/

/-- The linkage predicate over a plain, tip-first header list: `hs`'s
headers link all the way down to `h` — each header's hash is what the next
one back points to, and (if `hs` is empty) `h` is left an unconstrained
anchor. Exactly what a `Chain h`'s `toList` satisfies. -/
def IsChain (h : Hash256) : List BlockHeader → Prop
  | [] => True
  | hd :: tl => hd.hash = h ∧ IsChain hd.prevBlockHash tl

/-- `IsChain` is decidable, so real header lists — golden vectors now,
block-tree paths later — can be checked directly, without building a
`Chain` term. -/
instance instDecidableIsChain (h : Hash256) : (hs : List BlockHeader) → Decidable (IsChain h hs)
  | [] => isTrue True.intro
  | hd :: tl =>
    match instDecidableIsChain hd.prevBlockHash tl with
    | isTrue htl =>
      if heq : hd.hash = h then isTrue ⟨heq, htl⟩ else isFalse fun hc => heq hc.1
    | isFalse hntl => isFalse fun hc => hntl hc.2

/-- A chain's list-of-headers view satisfies the linkage predicate it was
built from. -/
theorem Chain.isChain_toList {h : Hash256} : (c : Chain h) → IsChain h c.toList
  | .nil _ => True.intro
  | .extend _ rest tip linked => by
      refine ⟨rfl, ?_⟩
      rw [linked]
      exact rest.isChain_toList

/-! ## The tip-commitment theorem -/

/-- Two chains of equal length that share a tip hash carry the same header
list — or two concrete byte strings witness a double-SHA-256 collision. The
tip hash commits to the entire history: peeling it off (equal hashes give
equal headers, via `BlockHeader.hash_faithful`, or a collision) and
recursing identifies the chains one header at a time. -/
theorem Chain.tip_commits {h₁ h₂ : Hash256} :
    (c₁ : Chain h₁) → (c₂ : Chain h₂) → h₁ = h₂ →
      c₁.toList.length = c₂.toList.length →
      c₁.toList = c₂.toList ∨ Sha256.Collision
  | .nil _, .nil _, _, _ => Or.inl rfl
  | .nil _, .extend .., _, hlen => by
      simp only [Chain.toList, List.length_nil, List.length_cons] at hlen
      exact absurd hlen (by omega)
  | .extend .., .nil _, _, hlen => by
      simp only [Chain.toList, List.length_nil, List.length_cons] at hlen
      exact absurd hlen (by omega)
  | .extend prev₁ rest₁ tip₁ linked₁, .extend prev₂ rest₂ tip₂ linked₂, heq, hlen => by
      rcases BlockHeader.hash_faithful heq with htip | hcol
      · have hprev : prev₁ = prev₂ :=
          linked₁.symm.trans ((congrArg BlockHeader.prevBlockHash htip).trans linked₂)
        have hlen' : rest₁.toList.length = rest₂.toList.length := by
          simp only [Chain.toList, List.length_cons] at hlen
          omega
        rcases Chain.tip_commits rest₁ rest₂ hprev hlen' with heql | hcol
        · exact Or.inl (by simp only [Chain.toList]; rw [htip, heql])
        · exact Or.inr hcol
      · exact Or.inr hcol

end BtcVerified
