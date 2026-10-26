import BtcVerified.Consensus.LockTimeClock
/-!
  # Transaction evaluation context

  Where and when a transaction is being admitted to the chain: the height of
  the admitting block, its header time, and the preceding chain's
  median-time-past. This is
  evaluation context, including whether relative sequence locks are active.
  The caller supplies that choice; deriving it from network and chain history
  remains the ruleset mapping's business (#38).

  Historical median-time-past is supplied by height for time-based sequence
  locks. This context does not authenticate that history; the caller must
  provide the candidate's parent-chain values (#122).

  Both clocks BIP113 chose between remain present and named here; which one
  measures an absolute lock is `LockTimeClock`'s business
  (`Consensus/LockTimeClock.lean`), read back through `TxContext.timeFor`.
-/

namespace BtcVerified

/-- The admitting height, named clocks, historical median-time-past, and
explicit sequence-lock activation supplied to contextual transaction rules. -/
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
  /-- Whether the admitting block enforces BIP68 sequence locks. The caller
  selects this rule; the transaction version gate is checked separately. -/
  sequenceLocksActive : Bool
  /-- Median-time-past at a height in the candidate's ancestor chain. Time
  locks query the height before a coin's creation, clamped to zero for genesis
  ([pinned Core](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/consensus/tx_verify.cpp#L79-L94)).
  The caller supplies coherent history; no default or fallback is assumed. -/
  medianTimePastAt : Nat → Nat

/-- Read the named context time selected by the active absolute-lock rule. -/
def TxContext.timeFor (ctx : TxContext) : LockTimeClock → Nat
  | .blockTime => ctx.blockTime
  | .medianTimePast => ctx.medianTimePast

end BtcVerified
