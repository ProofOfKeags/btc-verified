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
21 million bitcoin ([Bitcoin Core v28.0, `amount.h` lines
17–27](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/amount.h#L17-L27)). -/
def maxMoney : Nat := 21_000_000 * 100_000_000

/-- How many blocks deep a coinbase-created coin must be before it may be
spent ([Bitcoin Core v28.0, `COINBASE_MATURITY`, `consensus.h` lines
18–19](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/consensus.h#L18-L19)). -/
def coinbaseMaturity : Nat := 100

/-- The historical ceiling on legacy serialized size: one million bytes.
Before SegWit, Core applied `MAX_BLOCK_SIZE` directly to each transaction's
serialization ([Bitcoin Core v0.12.1, `main.cpp` lines
940–946](https://github.com/bitcoin/bitcoin/blob/v0.12.1/src/main.cpp#L940-L946)),
with the constant defined at [`consensus.h` lines
9–10](https://github.com/bitcoin/bitcoin/blob/v0.12.1/src/consensus/consensus.h#L9-L10).
Current Core preserves the same rule on the stripped serialization, expressed
indirectly in weight units; `Tx.stripped_size_bound_iff_core` proves the two
statements equivalent. -/
def maxLegacySerializedSize : Nat := 1_000_000

/-- The maximum total weight of a block under SegWit
([Bitcoin Core v28.0, `consensus.h` line 15](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/consensus.h#L15)). -/
def maxBlockWeight : Nat := 4_000_000

/-- The scale factor in Bitcoin's weight calculation
([Bitcoin Core v28.0, `consensus.h` line 21](https://github.com/bitcoin/bitcoin/blob/v28.0/src/consensus/consensus.h#L21)). -/
def witnessScaleFactor : Nat := 4

/-- The lock-time axis switch: lock times below it are block heights, at or
above it UNIX timestamps ([Bitcoin Core v28.0, `LOCKTIME_THRESHOLD`, `script.h`
lines 44–46](https://github.com/bitcoin/bitcoin/blob/v28.0/src/script/script.h#L44-L46)). -/
def lockTimeThreshold : Nat := 500_000_000

/-- The sequence value that opts an input out of lock-time enforcement
([Bitcoin Core v28.0, `CTxIn::SEQUENCE_FINAL`, `transaction.h` lines
74–87](https://github.com/bitcoin/bitcoin/blob/v28.0/src/primitives/transaction.h#L74-L87)). -/
def sequenceFinal : UInt32 := 0xffffffff

end BtcVerified.Consensus
