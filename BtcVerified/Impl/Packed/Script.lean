import BtcVerified.Script.Script
import BtcVerified.Impl.Packed.CountedList
/-!
  # Packed scripts

  The packed `Script` codec (issue #52): the transport of the packed counted
  byte list along the same bijection as the spec codec, so agreement with
  `instCodecScript` holds by construction. The program bytes stay
  uninterpreted, exactly as at the spec layer.
-/

namespace BtcVerified.Impl.Packed

open BtcVerified.Serialize BtcVerified

/-- The packed `Script` codec, agreeing with `instCodecScript` by transport
over the program bytes. -/
instance instPackedCodecScript : PackedCodec Script :=
  PackedCodec.ofEquiv Script.equivCode inferInstance inferInstance

end BtcVerified.Impl.Packed
