import BtcVerified.BitVM.BitCommitment.Bit
import BtcVerified.BitVM.BitCommitment.Opening
import BtcVerified.BitVM.BitCommitment.ValidOpening
import BtcVerified.BitVM.BitCommitment.Collision
import BtcVerified.BitVM.BitCommitment.Equivocation
/-!
  # Abstract BitVM bit commitments

  This leaf models the smallest useful commitment primitive for the BitVM
  verification track. The hash function is intentionally abstract: the point is
  not to verify SHA-256 or any concrete compression function, but to state the
  protocol-level shape that any collision-resistant commitment hash must
  satisfy.

  A commitment is produced by hashing a bit together with a nonce. An
  equivocation is a single commitment with two valid openings to distinct bits.
  The checked proof spine, one type per module:

  * `Bit` / `Opening` — the committed payload and what reveals it; distinct
    opened bits imply distinct openings;
  * `Collision` — two distinct openings with the same digest, and
    `CollisionResistance` ruling them out;
  * `ValidOpening` — an opening with its proof, and the `Binding` goal;
  * `Equivocation` — the binding spine: an equivocation gives a collision, so
    collision resistance forbids equivocation, and non-equivocation makes the
    commitments binding.

  This is deliberately tiny, but it fixes the vocabulary for later BitVM proof
  packets: openings, equivocation, collision resistance, and binding. The track
  is on ice for now; this module is the umbrella over its split parts.
-/
