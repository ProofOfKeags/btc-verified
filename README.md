# btc-verified

Verified Bitcoin protocol components in Lean 4.

## Current target

`BtcVerified.CompactSize` — encoder/decoder for Bitcoin's CompactSize varint with
roundtrip, prefix-soundness, and size-bound theorems.

`BtcVerified.BitVM.BitCommitment` — abstract bit-commitment model for the
BitVM track, proving that equivocation yields a collision and collision
resistance implies binding.

## Build

```
lake build
```
