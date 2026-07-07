# BtcVerified/BitVM

The BitVM verification track, independent of the serialization stack.

## `BtcVerified.BitVM.BitCommitment`

An abstract bit-commitment model for the BitVM verification track.

Checked claims:

- Different opened bits imply different openings.
- An equivocation gives a collision witness.
- Collision resistance implies binding.

Why it matters: this fixes the first vocabulary for later BitVM proof packets:
openings, equivocation, collision resistance, and binding.
