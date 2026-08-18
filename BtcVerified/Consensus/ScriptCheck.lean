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
  coin list is that wide because Core's BIP341 path precomputes every spent
  output's amount and script ([Bitcoin Core v28.0, `interpreter.cpp` lines
  1398–1445](https://github.com/bitcoin/bitcoin/blob/v28.0/src/script/interpreter.cpp#L1398-L1445)),
  so a taproot-capable judgment needs them all. Narrower judgments — Core's
  legacy signature-hash branch reads no coin data, while its BIP143 branch
  serializes only the current input's amount ([`interpreter.cpp` lines
  1568–1607](https://github.com/bitcoin/bitcoin/blob/v28.0/src/script/interpreter.cpp#L1568-L1607))
  — are stated at their natural scope and embedded here by the widening
  combinators, with the `Tx` argument last so widening is argument-prepending,
  never reshuffling.

  This module ships the type and the combinators only; no formal script
  judgment exists yet. A zipper or other focus-by-construction interface is
  therefore deliberately deferred until the script model can determine the
  interface it actually needs. For the present indexed parameter,
  `Tx.spentCoins_aligned` proves that the coin at each checked index is the
  lookup of the corresponding input's outpoint.
-/

namespace BtcVerified

/-- Judge one input's unlocking data: given all coins the transaction spends
(in input order), the index of the input under judgment, and the spending
transaction, decide whether that input satisfies the script of the output it
spends. -/
abbrev ScriptCheck := List Coin → Nat → Tx → Bool

/-- Widen a judgment that never reads the spent coins (a legacy signature
hash reads no coin data; [Bitcoin Core v28.0, `interpreter.cpp` lines
1568–1620](https://github.com/bitcoin/bitcoin/blob/v28.0/src/script/interpreter.cpp#L1568-L1620))
by prepending the dropped argument. -/
def ScriptCheck.ofCoinFree (f : Nat → Tx → Bool) : ScriptCheck :=
  fun _ => f

/-- Widen a judgment that reads only its own input's coin (BIP143 commits to
the input's own amount alone; [Bitcoin Core v28.0, `interpreter.cpp` lines
1595–1607](https://github.com/bitcoin/bitcoin/blob/v28.0/src/script/interpreter.cpp#L1595-L1607))
by selecting coin `i` from the list; an input whose coin is missing fails the
judgment. -/
def ScriptCheck.ofPerInput (f : Coin → Nat → Tx → Bool) : ScriptCheck :=
  fun coins i tx => ((coins[i]?).map fun coin => f coin i tx).getD false

end BtcVerified
