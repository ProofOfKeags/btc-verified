/-!
  # Coin provenance

  Where an unspent output came from: the height of the block that created it,
  and whether it was created in that block's coinbase position.

  Both fields exist for guards that run at *spend* time, arbitrarily many
  blocks after creation. The spending transaction carries no trace of its
  inputs' origins, so the UTXO set must remember them: coinbase maturity
  needs the pair together (an output created in a coinbase position is
  spendable only once 100 blocks deep), and BIP68 relative locktimes measure
  from the creation height. This mirrors the height/`fCoinBase` metadata
  Bitcoin Core keeps per coin in its chainstate.

  Coinbase-ness is *positional* — a property of sitting first in a block, not
  of the transaction's own bytes — so the flag is supplied by whoever knows
  the position (the block-application layer), never computed from the
  transaction. `Provenance` is bookkeeping of the state layer, not a wire
  structure: nothing here serializes, so there is no `Codec`.
-/

namespace BtcVerified

/-- Where a coin came from: the height of the block that created it and
whether it sat in that block's coinbase position. Recorded at creation,
consumed by spend-time guards (coinbase maturity, BIP68 relative locktimes)
that the spending transaction alone cannot decide. -/
structure Provenance where
  /-- Height of the block the creating transaction is applied in. -/
  height : Nat
  /-- Whether the creating transaction occupies the block's coinbase
  position. Positional, so supplied by the block layer. -/
  coinbase : Bool
deriving DecidableEq

end BtcVerified
