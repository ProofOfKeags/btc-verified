/-!
  # Transaction evaluation context

  Where and when a transaction is being admitted to the chain: the height of
  the admitting block, its header time, and the preceding chain's
  median-time-past. This is
  evaluation context, never activation — the contextual rules read these
  values to decide *this* transaction *here*; "which rules are in force at
  this height" is the ruleset mapping's business (#38).

  `LockTimeClock` names the choice BIP113 changed: Core supplies the block's
  own timestamp before activation and the preceding block's median-time-past
  after it, without changing `IsFinalTx` itself ([Bitcoin Core v28.0,
  `validation.cpp` lines 4224–4238](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L4224-L4238)).
  Both values remain present and named in `TxContext`; the ruleset chooses a
  `LockTimeClock` explicitly instead of hiding that activation-sensitive
  decision in an overloaded caller-filled `time` field.
-/

namespace BtcVerified

/-- Which named time in `TxContext` measures an absolute transaction lock.
The height-indexed ruleset in #38 chooses between these cases. -/
inductive LockTimeClock where
  /-- Pre-BIP113 absolute time locks use the admitting block's header time. -/
  | blockTime
  /-- Post-BIP113 absolute time locks use the preceding block's MTP. -/
  | medianTimePast
  deriving DecidableEq

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
