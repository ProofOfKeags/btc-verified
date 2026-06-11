import BtcVerified.Transaction.TxIn
import BtcVerified.Transaction.WitnessStack
/-!
  # SegWit inputs

  The pairing of a transaction input with the witness that unlocks it. Keeping
  the pair together makes the one-witness-per-input arity structural — a list
  of `SegwitInput` cannot express a count mismatch — while the BIP144 wire
  format's regrouping (all inputs, then all witnesses) is left to the codec
  (`Transaction.TxCodec`). No codec lives here for exactly that reason.
-/

namespace BtcVerified

/-- A transaction input bundled with the witness that unlocks it. SegWit moved
the unlocking data out of the input's `scriptSig` and into this per-input
witness. The wire format groups all witnesses after all inputs, but that
regrouping is the codec's concern: semantically each witness belongs to one
input, so the data model keeps them together. -/
structure SegwitInput where
  /-- The underlying transaction input. -/
  input : TxIn
  /-- The witness stack unlocking this input. -/
  witness : WitnessStack
  deriving DecidableEq

end BtcVerified
