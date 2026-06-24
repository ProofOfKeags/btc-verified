import BtcVerified
/-!
  # Golden vectors

  The codec proofs verify the encoder and decoder against each other; nothing
  internal can catch the model itself diverging from Bitcoin's actual wire
  format (a swapped field, the wrong endianness). These vectors close that
  loop: real mainnet bytes, decoded by the verified decoder, spot-checked
  against independently known facts, and re-encoded byte-for-byte.

  Each `#guard` runs at build time, so `lake build Tests` fails if the model
  stops matching the chain.
-/

namespace Tests.GoldenVectors

open BtcVerified BtcVerified.Serialize

set_option linter.hashCommand false

/-! ## Hex parsing -/

/-- The value of one hexadecimal digit, given as an ASCII byte. -/
def hexDigit? (b : UInt8) : Option UInt8 :=
  if 0x30 ≤ b ∧ b ≤ 0x39 then some (b - 0x30)        -- '0'..'9'
  else if 0x61 ≤ b ∧ b ≤ 0x66 then some (b - 0x61 + 10)  -- 'a'..'f'
  else if 0x41 ≤ b ∧ b ≤ 0x46 then some (b - 0x41 + 10)  -- 'A'..'F'
  else none

/-- Parse an even-length hex string into bytes. Tail-recursive over the UTF-8
bytes, so it handles megabyte fixture files, not just inline literals. -/
def hexBytes? (s : String) : Option (List UInt8) :=
  go (s.toUTF8) 0 []
where
  /-- Walk the ASCII bytes a digit pair at a time, consing onto `acc`. -/
  go (u : ByteArray) (i : Nat) (acc : List UInt8) : Option (List UInt8) :=
    if i = u.size then
      some acc.reverse
    else if i + 1 < u.size then
      match hexDigit? (u.get! i), hexDigit? (u.get! (i + 1)) with
      | some hi, some lo => go u (i + 2) ((hi <<< 4 ||| lo) :: acc)
      | _, _ => none
    else none
  termination_by u.size - i

#guard hexBytes? "00ff10" == some [0x00, 0xff, 0x10]
#guard hexBytes? "0" == none
#guard hexBytes? "0g" == none

/-- A hash from its conventional display hex (big-endian): parse and reverse to
the raw digest bytes a `Hash256` holds. Total — malformed input yields the
zero hash, never reached by the literal vectors below. -/
def hashOfDisplay (s : String) : Hash256 :=
  match (hexBytes? s).map List.reverse with
  | some bs => (Hash256.ofBytes? bs).getD 0
  | none => 0

/-- Decode a transaction from hex and check it consumed every byte and
re-encodes to exactly the input — then apply the vector's own spot-checks. -/
def checksOut (hex : String) (spot : Tx → Bool) : Bool :=
  match hexBytes? hex with
  | none => false
  | some bytes =>
    match Codec.decode (α := Tx) bytes with
    | none => false
    | some (tx, rest) => rest == [] && Codec.encode tx == bytes && spot tx

/-! ## The first Bitcoin payment (legacy)

  Txid `f4184fc596403b9d638783cf57adfe4c75c605f6356fbc91338530e9831e9e16`,
  block 170 (2009-01-12): Satoshi's 10 BTC payment to Hal Finney, the first
  transaction ever to spend a coinbase. Spends output 0 of the block-9
  coinbase `0437cd7f8525ceed2324359c2d0ba26006d92d856a9c20fa0241106ee5a597c9`.
-/

/-- Raw wire bytes of txid `f4184f…9e16`, fetched from blockstream.info. -/
def firstBitcoinPaymentHex : String :=
  "0100000001c997a5e56e104102fa209c6a852dd90660a20b2d9c352423edce25\
   857fcd3704000000004847304402204e45e16932b8af514961a1d3a1a25fdf3f\
   4f7732e9d624c6c61548ab5fb8cd410220181522ec8eca07de4860a4acdd1290\
   9d831cc56cbbac4622082221a8768d1d0901ffffffff0200ca9a3b0000000043\
   4104ae1a62fe09c5f51b13905f07f06b99a2f7159b2225f374cd378d71302fa2\
   8414e7aab37397f554a7df5f142c21c1b7303b8a0626f1baded5c72a704f7e6c\
   d84cac00286bee0000000043410411db93e1dcdb8a016b49840f8c53bc1eb68a\
   382e97b1482ecad7b148a6909a5cb2e0eaddfb84ccf9744464f82e160bfa9b8b\
   64f9d4c03f999b8643f656b412a3ac00000000"

#guard checksOut firstBitcoinPaymentHex fun tx =>
  !tx.isSegWit
  && tx.body.version == 1
  && tx.body.lockTime == 0
  && tx.body.outputs.val.length == 2
  && (match tx.body.inputs.val with
      | [i] =>
        -- The display txid is the raw digest bytes reversed; `hashOfDisplay`
        -- reverses back to what the byte-native `Hash256` stores.
        i.prevout.txid
          == hashOfDisplay "0437cd7f8525ceed2324359c2d0ba26006d92d856a9c20fa0241106ee5a597c9"
        && i.prevout.vout == 0
        && i.sequence == 0xffffffff
      | _ => false)
  -- 10 BTC to Hal, 40 BTC change.
  && (match tx.body.outputs.val with
      | [o1, o2] => o1.value == 1_000_000_000 && o2.value == 4_000_000_000
      | _ => false)

/-! ## The SegWit activation coinbase

  Txid `da917699942e4a96272401b534381a75512eeebe8403084500bd637bd47168b3`,
  the coinbase of block 481824 (2017-08-24), the first block mined under
  BIP141 rules. SegWit-serialized: its one input carries the 32-zero-byte
  witness reserved value, and its second output is the witness commitment.
-/

/-- Raw wire bytes of txid `da9176…68b3`, fetched from blockstream.info. -/
def segwitCoinbaseHex : String :=
  "0100000000010100000000000000000000000000000000000000000000000000\
   00000000000000ffffffff6403205a07f4d3f9da09acf878c2c9c96c410d6975\
   8f0eae0e479184e0564589052e832c42899c867100010000000000000000db99\
   01006052ce25d80acfde2f425443432f20537570706f7274202f4e59412f0000\
   0000000000000000000000000000000000000000025d322c57000000001976a9\
   142c30a6aaac6d96687291475d7d52f4b469f665a688ac000000000000000026\
   6a24aa21a9ed6c3c4dff76b5760d58694147264d208689ee07823e5694c4872f\
   856eacf5a5d80120000000000000000000000000000000000000000000000000\
   000000000000000000000000"

#guard checksOut segwitCoinbaseHex fun tx =>
  tx.isSegWit
  && tx.body.lockTime == 0
  && (match tx with
      | .segwit version ins outs _ =>
        version == 1 && outs.val.length == 2
        && (match ins.val with
            | [si] =>
              si.input.prevout.txid == (0 : Hash256)
              && si.input.prevout.vout == 0xffffffff
              -- One witness item: the 32-zero-byte reserved value.
              && (match si.witness.val with
                  | [item] => item.val == List.replicate 32 (0 : UInt8)
                  | _ => false)
            | _ => false)
      | .legacy .. => false)

/-! ## The first SegWit spend

  Txid `c586389e5e4b3acb9d6c8be1c19ae8ab2795397633176f5a6442a261bbdefc3a`,
  block 481824: the first transaction to spend an output under the new
  witness rules — a P2SH-wrapped P2WPKH spend with a two-item witness
  (signature, then compressed public key).
-/

/-- Raw wire bytes of txid `c58638…fc3a`, fetched from blockstream.info. -/
def firstSegwitSpendHex : String :=
  "0200000000010140d43a99926d43eb0e619bf0b3d83b4a31f60c176beecfb9d3\
   5bf45e54d0f7420100000017160014a4b4ca48de0b3fffc15404a1acdc8dbaae\
   226955ffffffff0100e1f5050000000017a9144a1154d50b03292b3024370901\
   711946cb7cccc387024830450221008604ef8f6d8afa892dee0f31259b6ce02d\
   d70c545cfcfed8148179971876c54a022076d771d6e91bed212783c9b06e0de6\
   00fab2d518fad6f15a2b191d7fbd262a3e0121039d25ab79f41f75ceaf882411\
   fd41fa670a4c672c23ffaf0e361a969cde0692e800000000"

#guard checksOut firstSegwitSpendHex fun tx =>
  tx.isSegWit
  && tx.body.version == 2
  && tx.body.lockTime == 0
  && tx.body.outputs.val.length == 1
  && (match tx with
      | .segwit _ ins _ _ =>
        (match ins.val with
         | [si] =>
           si.input.prevout.txid
             == hashOfDisplay "42f7d0545ef45bd3b9cfee6b170cf6314a3bd8b3f09b610eeb436d92993ad440"
           && si.input.prevout.vout == 1
           -- Witness: 72-byte DER signature, then 33-byte compressed pubkey.
           && (match si.witness.val with
               | [sig, pubkey] => sig.val.length == 72 && pubkey.val.length == 33
               | _ => false)
         | _ => false)
      | .legacy .. => false)

/-! ## Blocks -/

/-- Decode a block from hex and check it consumed every byte and re-encodes to
exactly the input — then apply the vector's own spot-checks. -/
def blockChecksOut (hex : String) (spot : Block → Bool) : Bool :=
  match hexBytes? hex with
  | none => false
  | some bytes =>
    match Codec.decode (α := Block) bytes with
    | none => false
    | some (b, rest) => rest == [] && Codec.encode b == bytes && spot b

/-! ## The genesis block

  Block 0 (2009-01-03), hash
  `000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f`:
  285 bytes, one transaction — the unspendable coinbase carrying the Times
  headline.
-/

/-- Raw wire bytes of the genesis block, fetched from blockstream.info. -/
def genesisBlockHex : String :=
  "0100000000000000000000000000000000000000000000000000000000000000\
   000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa\
   4b1e5e4a29ab5f49ffff001d1dac2b7c01010000000100000000000000000000\
   00000000000000000000000000000000000000000000ffffffff4d04ffff001d\
   0104455468652054696d65732030332f4a616e2f32303039204368616e63656c\
   6c6f72206f6e206272696e6b206f66207365636f6e64206261696c6f75742066\
   6f722062616e6b73ffffffff0100f2052a01000000434104678afdb0fe554827\
   1967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4\
   f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5fac00000000"

#guard blockChecksOut genesisBlockHex fun b =>
  b.header.version == 1
  && b.header.prevBlockHash == (0 : Hash256)
  -- Displayed hashes are the wire bytes reversed, so the little-endian decode
  -- equals the display hex read as a number.
  && b.header.merkleRoot
    == hashOfDisplay "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"
  && b.header.time == 1231006505
  && b.header.bits == 0x1d00ffff
  && b.header.nonce == 2083236893
  && (match b.txs.val with
      | [tx] =>
        !tx.isSegWit
        -- The 77-byte coinbase scriptSig carrying the Times headline.
        && (match tx.body.inputs.val with
            | [i] => i.scriptSig.code.val.length == 77
            | _ => false)
        -- The 50 BTC genesis coinbase output.
        && (match tx.body.outputs.val with
            | [o] => o.value == 5_000_000_000
            | _ => false)
      | _ => false)

/-! ## Block 170

  Block 170 (2009-01-12), hash
  `00000000d1145790a8694403d4063f323d499e655c83426834d4ce2f8dd4a2ee`:
  the first block with a non-coinbase transaction — Satoshi's payment to Hal
  Finney, the standalone vector above. Its embedded copy must re-encode to
  exactly the standalone vector's bytes.
-/

/-- Raw wire bytes of block 170, fetched from blockstream.info. -/
def block170Hex : String :=
  "0100000055bd840a78798ad0da853f68974f3d183e2bd1db6a842c1feecf222a\
   00000000ff104ccb05421ab93e63f8c3ce5c2c2e9dbb37de2764b3a3175c8166\
   562cac7d51b96a49ffff001d283e9e7002010000000100000000000000000000\
   00000000000000000000000000000000000000000000ffffffff0704ffff001d\
   0102ffffffff0100f2052a01000000434104d46c4968bde02899d2aa0963367c\
   7a6ce34eec332b32e42e5f3407e052d64ac625da6f0718e7b302140434bd7257\
   06957c092db53805b821a85b23a7ac61725bac000000000100000001c997a5e5\
   6e104102fa209c6a852dd90660a20b2d9c352423edce25857fcd370400000000\
   4847304402204e45e16932b8af514961a1d3a1a25fdf3f4f7732e9d624c6c615\
   48ab5fb8cd410220181522ec8eca07de4860a4acdd12909d831cc56cbbac4622\
   082221a8768d1d0901ffffffff0200ca9a3b00000000434104ae1a62fe09c5f5\
   1b13905f07f06b99a2f7159b2225f374cd378d71302fa28414e7aab37397f554\
   a7df5f142c21c1b7303b8a0626f1baded5c72a704f7e6cd84cac00286bee0000\
   000043410411db93e1dcdb8a016b49840f8c53bc1eb68a382e97b1482ecad7b1\
   48a6909a5cb2e0eaddfb84ccf9744464f82e160bfa9b8b64f9d4c03f999b8643\
   f656b412a3ac00000000"

#guard blockChecksOut block170Hex fun b =>
  b.header.version == 1
  && b.header.prevBlockHash
    == hashOfDisplay "000000002a22cfee1f2c846adbd12b3e183d4f97683f85dad08a79780a84bd55"
  && b.header.merkleRoot
    == hashOfDisplay "7dac2c5666815c17a3b36427de37bb9d2e2c5ccec3f8633eb91a4205cb4c10ff"
  && b.header.time == 1231731025
  && b.header.bits == 0x1d00ffff
  && (match b.txs.val with
      | [coinbase, payment] =>
        !coinbase.isSegWit
        -- The block's second transaction is the first Bitcoin payment:
        -- byte-identical to the standalone transaction vector.
        && some (Codec.encode payment) == hexBytes? firstBitcoinPaymentHex
      | _ => false)

/-! ## CompactSize boundary values -/

#guard CompactSize.encode 0 == [0x00]
#guard CompactSize.encode 252 == [0xfc]
#guard CompactSize.encode 253 == [0xfd, 0xfd, 0x00]
#guard CompactSize.encode 0xffff == [0xfd, 0xff, 0xff]
#guard CompactSize.encode 0x10000 == [0xfe, 0x00, 0x00, 0x01, 0x00]
#guard CompactSize.encode 0x100000000 == [0xff, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00]
-- Non-shortest forms are rejected.
#guard CompactSize.decode [0xfd, 0xfc, 0x00] == none
#guard CompactSize.decode [0xfe, 0xff, 0xff, 0x00, 0x00] == none

/-! ## SHA-256 known-answer vectors

  The hash is concrete and computable, so it is checked the same way as the wire
  format: against the published FIPS 180-4 and Bitcoin test vectors, evaluated at
  build time. -/

#guard some (Sha256.sha256 []) ==
  hexBytes? "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard some (Sha256.sha256 [0x61, 0x62, 0x63]) ==
  hexBytes? "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
-- Bitcoin's double-SHA-256 of the empty string.
#guard some (Sha256.sha256d []) ==
  hexBytes? "5df6e0e2761359d30a8275058e299fcc0381534545f55cf43e41983f5d4c9456"
-- Padding boundaries: 55 bytes fits one block; 56 and 64 force a second block.
#guard some (Sha256.sha256 (List.replicate 55 0x61)) ==
  hexBytes? "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"
#guard some (Sha256.sha256 (List.replicate 56 0x61)) ==
  hexBytes? "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"
#guard some (Sha256.sha256 (List.replicate 64 0x61)) ==
  hexBytes? "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"

/-! ## Transaction ids

  Txids of the standalone transaction vectors against their well-known
  display hashes. The displayed hex is the digest bytes reversed, so the
  little-endian `Hash256` value equals the display hex read as a number —
  the same convention the prevout-txid spot-checks above already pin. -/

-- The first Bitcoin payment; legacy, so wtxid = txid.
#guard match hexBytes? firstBitcoinPaymentHex >>= Codec.decode (α := Tx) with
  | some (tx, _) =>
    tx.txid == hashOfDisplay "f4184fc596403b9d638783cf57adfe4c75c605f6356fbc91338530e9831e9e16"
    && tx.wtxid == tx.txid
  | none => false

-- The genesis coinbase: its txid is the genesis merkle root.
#guard match hexBytes? genesisBlockHex >>= Codec.decode (α := Block) with
  | some (b, _) => match b.txs.val with
    | [coinbase] =>
      coinbase.txid
        == hashOfDisplay "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"
      && coinbase.txid == b.header.merkleRoot
    | _ => false
  | none => false

-- The SegWit activation coinbase: the witness makes wtxid ≠ txid.
#guard match hexBytes? segwitCoinbaseHex >>= Codec.decode (α := Tx) with
  | some (tx, _) =>
    tx.txid == hashOfDisplay "da917699942e4a96272401b534381a75512eeebe8403084500bd637bd47168b3"
    && tx.wtxid != tx.txid
  | none => false

/-! ## The merkle commitment

  The padding ambiguity and its canonicality fence on synthetic leaves, then
  the real commitment on real blocks: txids → merkle root → header. -/

-- Materializing the padding of a three-leaf list collides at the root
-- (CVE-2012-2459); canonicality is what separates the two lists.
#guard Merkle.computeRoot ([1, 2, 3] : List Hash256)
  == Merkle.computeRoot ([1, 2, 3, 3] : List Hash256)
#guard Merkle.canonicalCheck ([1, 2, 3] : List Hash256)
#guard !Merkle.canonicalCheck ([1, 2, 3, 3] : List Hash256)
-- A duplicated run of length two only surfaces one level up the tree.
#guard Merkle.computeRoot ([1, 2, 3, 4, 5, 6] : List Hash256)
  == Merkle.computeRoot ([1, 2, 3, 4, 5, 6, 5, 6] : List Hash256)
#guard !Merkle.canonicalCheck ([1, 2, 3, 4, 5, 6, 5, 6] : List Hash256)
-- A pair-aligned duplicate in the middle is honest content: no shorter list
-- shares its root, so it stays canonical (Core's uniform scan would reject
-- it, but such a block has a duplicate txid and dies at transaction
-- validity instead).
#guard Merkle.canonicalCheck ([1, 1, 2, 3] : List Hash256)

-- Bitcoin Core's `ComputeMerkleRoot`, run on the same vectors. The root always
-- matches `computeRoot`, and the `mutated` flag fires on exactly the
-- materialized-padding lists — distinct leaves never trip it.
#guard (Merkle.BitcoinCore.computeMerkleRoot ([1, 2, 3] : List Hash256)).1
  == Merkle.computeRoot ([1, 2, 3] : List Hash256)
#guard !(Merkle.BitcoinCore.computeMerkleRoot ([1, 2, 3] : List Hash256)).2
#guard (Merkle.BitcoinCore.computeMerkleRoot ([1, 2, 3, 3] : List Hash256)).2
#guard !(Merkle.BitcoinCore.computeMerkleRoot ([1, 2, 3, 4, 5] : List Hash256)).2
-- A duplicated run trips it one level up, where the pair aligns.
#guard (Merkle.BitcoinCore.computeMerkleRoot ([1, 2, 3, 4, 5, 6, 5, 6] : List Hash256)).2
-- Core is strictly stronger than canonicality: a duplicate node is canonical
-- when it sits at the root (a shorter list of the same width must still split
-- there, so it is honest content — a duplicate txid dies at transaction
-- validity, not the merkle layer) yet Core flags it. So non-mutation implies
-- canonicality, but not conversely. The minimal case `[a, a]`, and the same at
-- an interior pair `[1, 1, 2, 3]`:
#guard Merkle.canonicalCheck ([7, 7] : List Hash256)
#guard (Merkle.BitcoinCore.computeMerkleRoot ([7, 7] : List Hash256)).2
#guard (Merkle.BitcoinCore.computeMerkleRoot ([1, 1, 2, 3] : List Hash256)).2

-- The genesis block commits to its single transaction (root = txid).
#guard match hexBytes? genesisBlockHex >>= Codec.decode (α := Block) with
  | some (b, _) => decide b.merkleCommits
  | none => false

-- Block 170 commits to its two transactions (one real combine).
#guard match hexBytes? block170Hex >>= Codec.decode (α := Block) with
  | some (b, _) => decide b.merkleCommits
  | none => false

end Tests.GoldenVectors
