/-!
  # Protocol limits

  The numeric constants Bitcoin's consensus rules compare against, collected in
  one place so every rule cites a named limit instead of a bare literal. Each
  constant corresponds 1:1 to a constant in Bitcoin Core (the file is named in
  the doc-string); none of them carries activation information — a limit is a
  number, and which rules consult it at which heights is the ruleset mapping's
  business.

  Values are `Nat` wherever the rules do arithmetic on them (`Nat` is the
  accounting type throughout `Chainstate/`), and stay in the wire's own type
  where the rules only compare for equality (`sequenceFinal`).
-/

namespace BtcVerified.Consensus

/-- The most satoshis consensus ever admits in an amount or a sum of amounts:
21 million bitcoin (Core's `MAX_MONEY`, `src/consensus/amount.h`). -/
def maxMoney : Nat := 21_000_000 * 100_000_000

/-- How many blocks deep a coinbase-created coin must be before it may be
spent (Core's `COINBASE_MATURITY`, `src/consensus/consensus.h`). -/
def coinbaseMaturity : Nat := 100

/-- The lock-time axis switch: lock times below it are block heights, at or
above it UNIX timestamps (Core's `LOCKTIME_THRESHOLD`, `src/script/script.h`). -/
def lockTimeThreshold : Nat := 500_000_000

/-- The sequence value that opts an input out of lock-time enforcement
(Core's `CTxIn::SEQUENCE_FINAL`, `src/primitives/transaction.h`). -/
def sequenceFinal : UInt32 := 0xffffffff

end BtcVerified.Consensus
