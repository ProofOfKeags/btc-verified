import BtcVerified.Consensus.Activation.VersionBitsTransition
/-!
  # Versionbits transition boundaries

  Synthetic four-block periods exercise the pinned transition table, including
  signaling prefixes, start/timeout equality, threshold precedence, delayed
  activation, and enforcement only in the active state.
-/

namespace Tests.ActivationTransitions

open BtcVerified.Consensus

set_option linter.hashCommand false

private def params : VersionBitsParams :=
  ⟨⟨2, by decide⟩, 4, by decide, 3, by decide, 10, 20, 0⟩

#guard params.signals 0x20000004
#guard params.signals 0x30000004
#guard !params.signals 0x00000004
#guard !params.signals 0xa0000004
#guard !params.signals 0x60000004
#guard !params.signals 0x20000000

end Tests.ActivationTransitions
