import BtcVerified.Transaction.TxOut
import BtcVerified.Chainstate.Provenance
/-!
  # Coins: what the UTXO set stores

  A coin is an unspent transaction output together with its `Provenance` —
  the creation height and coinbase-position flag that spend-time guards need
  and the spending transaction cannot supply. This is Bitcoin Core's
  chainstate entry (`CTxOut` + `nHeight` + `fCoinBase`), with the two
  metadata fields bundled as one named concept.

  The `TxOut` is wire data; the provenance is not. A coin is therefore a
  state-layer object with no serialization — the codomain of the UTXO map,
  never a field on the wire.
-/

namespace BtcVerified

/-- An unspent transaction output as the UTXO set stores it: the output
itself plus the provenance its spend-time guards will consult. -/
structure Coin where
  /-- The unspent output: amount and locking script. -/
  output : TxOut
  /-- Where the output came from: creation height and coinbase-position
  flag. -/
  provenance : Provenance
deriving DecidableEq

end BtcVerified
