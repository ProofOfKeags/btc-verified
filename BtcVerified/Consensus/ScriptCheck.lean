import BtcVerified.Transaction.Tx
import BtcVerified.Chainstate.Coin
/-!
  # The script-validity parameter

  The consensus layer does not execute scripts — tokenization and execution
  are a later layer — so the transaction rules take script validity as a
  parameter: a judgment that decides, for one input of a spending
  transaction, whether its unlocking data satisfies the spent output's
  script.

  The judgment sees all the coins the transaction spends (in input order),
  the index of the input under judgment, and the spending transaction. The
  coin list is that wide because BIP341 (taproot) signature hashes commit to
  *every* spent output's amount and script, so a taproot-capable judgment
  needs them all. Narrower judgments — legacy signature hashes read no coin
  data at all; BIP143 reads only its own input's amount — are stated at
  their natural scope and embedded here by the widening combinators, with
  the `Tx` argument last so widening is argument-prepending, never
  reshuffling.

  This module ships the type and the combinators only; actual judgments
  arrive with the script layer.
-/

namespace BtcVerified

/-- Judge one input's unlocking data: given all coins the transaction spends
(in input order), the index of the input under judgment, and the spending
transaction, decide whether that input satisfies the script of the output it
spends. -/
abbrev ScriptCheck := List Coin → Nat → Tx → Bool

/-- Widen a judgment that never reads the spent coins (a legacy signature
hash reads no coin data) by prepending the dropped argument. -/
def ScriptCheck.ofCoinFree (f : Nat → Tx → Bool) : ScriptCheck :=
  fun _ => f

/-- Widen a judgment that reads only its own input's coin (BIP143 commits to
the input's own amount alone) by selecting coin `i` from the list; an input
whose coin is missing fails the judgment. -/
def ScriptCheck.ofPerInput (f : Coin → Nat → Tx → Bool) : ScriptCheck :=
  fun coins i tx => ((coins[i]?).map fun coin => f coin i tx).getD false

end BtcVerified
