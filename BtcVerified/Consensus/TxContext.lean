import BtcVerified.Consensus.LockTimeClock
/-!
  # Transaction evaluation context

  Where and when a transaction is being admitted to the chain: the height of
  the admitting block, its header time, and the preceding chain's
  median-time-past. This is
  evaluation context, never activation — the contextual rules read these
  values to decide *this* transaction *here*; "which rules are in force at
  this height" is the ruleset mapping's business (#38).

  Both clocks BIP113 chose between remain present and named here; which one
  measures an absolute lock is `LockTimeClock`'s business
  (`Consensus/LockTimeClock.lean`), read back through `TxContext.timeFor`.
-/

namespace BtcVerified

/-- The context a chain-contextual transaction rule evaluates in: the height
of the admitting block and both clocks consensus rules can name. -/
structure TxContext where
  /-- Height of the block admitting the transaction (Core's `nSpendHeight` in
  [`CheckTxInputs`, Bitcoin Core v28.0, `tx_verify.cpp` lines
  164–180](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L164-L180)). -/
  height : Nat
  /-- The admitting block header's timestamp, used for time locks before BIP113
  ([Bitcoin Core v28.0, `validation.cpp` lines
  4224–4230](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L4224-L4230)). -/
  blockTime : Nat
  /-- The preceding block's median-time-past, used for time locks after BIP113
  ([Bitcoin Core v28.0, `validation.cpp` lines
  4224–4230](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L4224-L4230)). -/
  medianTimePast : Nat
  deriving DecidableEq

/-- Read the named context time selected by the active absolute-lock rule. -/
def TxContext.timeFor (ctx : TxContext) : LockTimeClock → Nat
  | .blockTime => ctx.blockTime
  | .medianTimePast => ctx.medianTimePast

end BtcVerified
