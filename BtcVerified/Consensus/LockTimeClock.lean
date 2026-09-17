/-!
  # The lock-time clock

  Which named time in `TxContext` measures an absolute transaction lock —
  the choice BIP113 changed. Core supplies the block's own timestamp before
  activation and the preceding block's median-time-past after it, without
  changing `IsFinalTx` itself ([Bitcoin Core v28.0, `validation.cpp` lines
  4224–4238](https://github.com/bitcoin/bitcoin/blob/v28.0/src/validation.cpp#L4224-L4238)).
  Both values remain present and named in `TxContext`
  (`Consensus/TxContext.lean`, which reads the selected one via
  `TxContext.timeFor`); the ruleset chooses a `LockTimeClock` explicitly
  instead of hiding that activation-sensitive decision in an overloaded
  caller-filled `time` field.
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

end BtcVerified
