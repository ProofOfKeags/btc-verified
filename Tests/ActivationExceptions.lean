import BtcVerified.Consensus.Activation.RuleExceptions
import BtcVerified.Consensus.Activation.RuleChoice
import BtcVerified.Crypto.Hash256
/-!
  # Exception and replacement boundary examples

  The historical BIP30 examples use the two exact height/hash identities in
  Core's `IsBIP30Repeat`, pinned at
  https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/validation.cpp#L6207-L6211.
  Hash literals use the existing `Hash256` numeric-literal convention, which
  stores their displayed integer in little-endian byte order.

  Inputs contain a height, block hash, freshness result and an independent
  requirement's result. These examples check exception dispatch, not the UTXO
  scan, block validity, historical disconnect behavior or a Core execution.
  Replacement examples separately show that only the selected requirement
  applies; they do not propose a different BIP30 policy.
-/

namespace Tests.ExceptionExamples

open BtcVerified BtcVerified.Consensus

set_option linter.hashCommand false

private abbrev Input := Nat × Hash256 × Bool × Bool

private def firstRepeat : Hash256 :=
  0x00000000000a4d0a398161ffc163c503763b1f4360639393e0e4c8e300e0caec

private def secondRepeat : Hash256 :=
  0x00000000000743f190a18c5577a3c2d2a1f610ae9601ac046a38084ccb7cd721

private def repeatedCoinbase : Rule Input := Rule.ofDecidable fun input =>
  (input.1 = 91842 ∧ input.2.1 = firstRepeat) ∨
    (input.1 = 91880 ∧ input.2.1 = secondRepeat)

private def freshness : Rule Input := Rule.ofDecidable fun input => input.2.2.1 = true

private def otherRequirement : Rule Input :=
  Rule.ofDecidable fun input => input.2.2.2 = true

private def checkRequirements (input : Input) : Bool :=
  (repeatedCoinbase.unless freshness).check input && otherRequirement.check input

-- Both exact repeats suspend freshness; no height-only exception is allowed.

end Tests.ExceptionExamples
