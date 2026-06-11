/-!
  # The 256-bit hash type

  Txids, block hashes, and merkle nodes are all 256-bit digests; this fixes
  the one type they share. Hashing itself stays abstract at this layer —
  nothing here computes SHA-256, and nothing downstream may assume more about
  a `Hash256` than its width.
-/

namespace BtcVerified

/-- A 256-bit hash: txid, block hash, or merkle node. -/
abbrev Hash256 := BitVec 256

end BtcVerified
