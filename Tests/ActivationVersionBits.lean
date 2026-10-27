import BtcVerified.Consensus.Activation.VersionBitsProgress
/-!
  # Header-derived deployment progress

  Chronological synthetic headers exercise partial periods, count reset,
  the MTP window, and minimum-height activation at period boundaries.
-/

namespace Tests.ActivationVersionBits

open BtcVerified BtcVerified.Consensus

set_option linter.hashCommand false

private def params : VersionBitsParams :=
  ⟨⟨2, by decide⟩, 4, by decide, 3, by decide, 10, 20, 0⟩

private def header (version time : UInt32) : BlockHeader :=
  ⟨version, 0, 0, time, 0, 0⟩

end Tests.ActivationVersionBits
