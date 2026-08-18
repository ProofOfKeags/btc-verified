/-!
  # Transaction evaluation context

  Where and when a transaction is being admitted to the chain: the height of
  the admitting block and the time lock times are measured against. This is
  evaluation context, never activation — the contextual rules read these
  values to decide *this* transaction *here*; "which rules are in force at
  this height" is the ruleset mapping's business (#38).

  In particular, BIP113 changed which clock Core passes as the lock-time
  measuring point (the block's own timestamp before, its median-time-past
  after) without changing `IsFinalTx` itself ([Bitcoin Core v28.0,
  `validation.cpp` lines 4224–4238](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L4224-L4238)).
  The rules only compare against `time`; which clock supplies it is exactly the
  kind of choice the activation layer owns.
-/

namespace BtcVerified

/-- The context a chain-contextual transaction rule evaluates in: the height
of the admitting block and the time lock times are measured against. -/
structure TxContext where
  /-- Height of the block admitting the transaction (Core's `nSpendHeight` in
  [`CheckTxInputs`, Bitcoin Core v28.0, `tx_verify.cpp` lines
  164–180](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L164-L180)). -/
  height : Nat
  /-- The time lock-time finality is measured against (Core's `nBlockTime` in
  [`IsFinalTx`, Bitcoin Core v28.0, `tx_verify.cpp` lines
  17–37](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/tx_verify.cpp#L17-L37));
  which clock supplies it is the activation layer's choice). -/
  time : Nat
  deriving DecidableEq

end BtcVerified
