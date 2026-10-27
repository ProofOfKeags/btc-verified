import BtcVerified.Block.Chain
import BtcVerified.Consensus.Activation.VersionBitsProgress
/-!
  # Deployment continuation anchored to a chain prefix

  A boundary binds the assumed summary to both its deployment parameters and
  the prefix tip hash. Chain indices enforce linkage of subsequent headers.
  They do not establish the assumed summary, canonical genesis, timestamp validity,
  proof of work, or other consensus facts about the prefix or extension.

-/

namespace BtcVerified.Consensus

/-- An explicitly assumed prefix summary for one fixed deployment and tip hash. -/
structure VersionBitsBoundary where
  /-- The deployment whose state and signal counts the summary describes. -/
  params : VersionBitsParams
  /-- Hash of the last header in the assumed prefix. -/
  anchor : Hash256
  /-- Next height, current deployment state, partial-period count, and MTP window. -/
  progress : VersionBitsProgress

/-- Begin before height zero, with the zero previous-block hash; verifying the actual
network genesis header and chain validity is a separate obligation. -/
def VersionBitsBoundary.initial (params : VersionBitsParams) : VersionBitsBoundary :=
  ⟨params, 0, VersionBitsProgress.initial⟩

/-- Continue over a hash-linked segment anchored at the assumed prefix tip, deriving
all new signal counts and MTP windows from its headers under the same parameters. -/
def VersionBitsBoundary.extend (boundary : VersionBitsBoundary) {tip : Hash256}
    (segment : Chain boundary.anchor tip) : VersionBitsBoundary :=
  { boundary with
    anchor := tip
    progress := boundary.progress.consume boundary.params segment.toList.reverse }

/-- The assumed summary is exactly the model's computation over the given prefix.
This predicate distinguishes an explicit assumption from a supplied witness of it. -/
def VersionBitsBoundary.Summarizes (boundary : VersionBitsBoundary)
    (historyPrefix : Chain 0 boundary.anchor) : Prop :=
  boundary.progress = VersionBitsProgress.initial.consume boundary.params historyPrefix.toList.reverse

end BtcVerified.Consensus
