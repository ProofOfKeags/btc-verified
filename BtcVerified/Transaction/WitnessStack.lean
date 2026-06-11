import BtcVerified.Serialize.CountedList
/-!
  # Witness stacks

  SegWit attaches one witness stack to each transaction input: an ordered list
  of opaque stack items. On the wire both the stack and each item are
  CompactSize-prefixed, so the type is two `CountedList`s deep — which is also
  what gives it its codec, by composition alone.
-/

namespace BtcVerified

open BtcVerified.Serialize

/-- The witness stack for a single input: an ordered list of stack items, each an
opaque byte string. SegWit attaches one such stack per transaction input. Both
the stack and each item are CompactSize-prefixed on the wire, so both are
`CountedList`s. -/
abbrev WitnessStack := CountedList (CountedList UInt8)

end BtcVerified
