import BtcVerified.Consensus.TxStateless
/-!
  # Coinbase transaction-local premises

  `Tx.Coinbase` classifies a transaction by its single null-prevout input,
  independently of whether its other fields satisfy consensus rules. This is
  Core's [`IsCoinBase`](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/primitives/transaction.h#L341-L344)
  classification, not a statement about its position in a block.

  `Tx.CoinbaseWellFormed` collects the transaction-local coinbase premises of
  [`CheckTransaction`](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/consensus/tx_check.cpp#L19-L67).
  It reuses the output and size predicates from `TxStateless`. The single-input
  shape already ensures nonempty inputs and no duplicate input outpoints.
  Block placement, height commitments, and subsidy plus fees remain outside
  this judgment (#37/#38); passing it does not establish consensus validity.

  Checked claims:

  * `Tx.coinbaseWellFormed_iff`: the specification record holds exactly when
    its six named premises hold. This also supplies its decision procedure;
    the packed kernel checker proves agreement separately.
-/

namespace BtcVerified

/-- The transaction has exactly one input, whose prevout is null. This
classification does not require a valid scriptSig, output list, or block position. -/
def Tx.Coinbase (tx : Tx) : Prop :=
  match tx.body.inputs.val with
  | [input] => input.prevout = OutPoint.null
  | _ => False

/-- Every input's scriptSig has at least `Consensus.minCoinbaseScriptSigSize`
bytes. This alone does not require coinbase shape or even nonempty inputs. -/
def Tx.AllScriptSigSizesGeMinCoinbaseScriptSigSize (tx : Tx) : Prop :=
  ∀ input ∈ tx.body.inputs.val,
    Consensus.minCoinbaseScriptSigSize ≤ input.scriptSig.code.val.length

/-- Every input's scriptSig has at most `Consensus.maxCoinbaseScriptSigSize`
bytes. This alone does not require coinbase shape or even nonempty inputs. -/
def Tx.AllScriptSigSizesLeMaxCoinbaseScriptSigSize (tx : Tx) : Prop :=
  ∀ input ∈ tx.body.inputs.val,
    input.scriptSig.code.val.length ≤ Consensus.maxCoinbaseScriptSigSize

/-- Decide the single-null-prevout-input classification. -/
@[macro_inline]
instance instDecidableCoinbase : DecidablePred Tx.Coinbase :=
  fun tx => by
    unfold Tx.Coinbase
    split <;> infer_instance

/-- Decide the minimum coinbase scriptSig size bound for every input. -/
@[macro_inline]
instance instDecidableAllScriptSigSizesGeMinCoinbaseScriptSigSize :
    DecidablePred Tx.AllScriptSigSizesGeMinCoinbaseScriptSigSize :=
  fun _ => by unfold Tx.AllScriptSigSizesGeMinCoinbaseScriptSigSize; infer_instance

/-- Decide the maximum coinbase scriptSig size bound for every input. -/
@[macro_inline]
instance instDecidableAllScriptSigSizesLeMaxCoinbaseScriptSigSize :
    DecidablePred Tx.AllScriptSigSizesLeMaxCoinbaseScriptSigSize :=
  fun _ => by unfold Tx.AllScriptSigSizesLeMaxCoinbaseScriptSigSize; infer_instance

/-- The transaction-local coinbase premises, one named proposition per field.
This does not include any constraint requiring block or chain context. -/
structure Tx.CoinbaseWellFormed (tx : Tx) : Prop where
  /-- There is exactly one input, and it claims the null outpoint. -/
  coinbase : tx.Coinbase
  /-- At least one output exists. -/
  outputsNonempty : tx.OutputsNonempty
  /-- Total output value is at most `Consensus.maxMoney`. -/
  totalOutputValueLeMaxMoney : tx.TotalOutputValueLeMaxMoney
  /-- Stripped serialization fits within `Consensus.maxStrippedTransactionSize`. -/
  strippedSizeLeMaxStrippedTransactionSize : tx.StrippedSizeLeMaxStrippedTransactionSize
  /-- Every scriptSig meets the minimum coinbase scriptSig size. -/
  allScriptSigSizesGeMinCoinbaseScriptSigSize : tx.AllScriptSigSizesGeMinCoinbaseScriptSigSize
  /-- Every scriptSig meets the maximum coinbase scriptSig size. -/
  allScriptSigSizesLeMaxCoinbaseScriptSigSize : tx.AllScriptSigSizesLeMaxCoinbaseScriptSigSize

/-- Coinbase well-formedness holds exactly when the six named transaction-local
premises hold. -/
theorem Tx.coinbaseWellFormed_iff {tx : Tx} :
    tx.CoinbaseWellFormed ↔
      tx.Coinbase ∧ tx.OutputsNonempty ∧ tx.TotalOutputValueLeMaxMoney ∧
        tx.StrippedSizeLeMaxStrippedTransactionSize ∧
        tx.AllScriptSigSizesGeMinCoinbaseScriptSigSize ∧
        tx.AllScriptSigSizesLeMaxCoinbaseScriptSigSize := by
  constructor
  · rintro ⟨hcoinbase, houtputs, hvalue, hsize, hmin, hmax⟩
    exact ⟨hcoinbase, houtputs, hvalue, hsize, hmin, hmax⟩
  · rintro ⟨hcoinbase, houtputs, hvalue, hsize, hmin, hmax⟩
    exact ⟨hcoinbase, houtputs, hvalue, hsize, hmin, hmax⟩

/-- Decide the coinbase specification using its named premises. The kernel's
packed implementation is connected separately by `Kernel.coinbaseCheck_iff`. -/
instance instDecidableCoinbaseWellFormed : DecidablePred Tx.CoinbaseWellFormed :=
  fun _ => decidable_of_iff _ Tx.coinbaseWellFormed_iff.symm

end BtcVerified
