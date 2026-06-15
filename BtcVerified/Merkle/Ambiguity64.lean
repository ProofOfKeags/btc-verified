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

open BtcVerified

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

end BtcVerified.Merkle
