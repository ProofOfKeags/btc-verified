import Tests.GoldenVectors
/-!
  # Block fixtures

  The inline golden vectors stay small enough to read; a full real block does
  not. This module checks fixture blocks — raw mainnet bytes — through the
  verified block codec: decode, spot-check, re-encode byte-for-byte.

  A block is public chain data, reconstructible from any Bitcoin node, so
  fixtures are not committed: the test driver fetches each one on first run
  (from an esplora HTTP endpoint, by block hash) and caches it under
  `Tests/fixtures/`, which is gitignored. The download is authenticated as
  far as the current leaves allow: the decoded header must double-SHA-256 to
  the requested block hash (so the 80 header bytes carry their proof of
  work), and the spot-checks pin the transaction count and the embedded
  transactions they name byte-for-byte. Full authentication of every
  transaction byte is the merkle-commitment leaf's job, once it lands.

  The one fixture so far is block 481824, the SegWit activation block: 1866
  transactions mixing the legacy and SegWit serializations, the SegWit
  coinbase, multi-input and multi-output spends, and CompactSize counts past
  the `0xfd` marker — every parsing corner a real block can exercise at once.

  Fetching and reading files is `IO`, so these checks run in the `tests`
  executable (`lake test`), not as elaboration-time `#guard`s.
-/

namespace Tests.BlockFixtures

open Tests.GoldenVectors BtcVerified BtcVerified.Serialize

/-- The bytes of a `ByteArray` as a list, in order. Tail-recursive (walks
backward, consing forward), so megabyte arrays are fine. -/
def byteArrayToList (u : ByteArray) : List UInt8 :=
  go u.size []
where
  /-- Cons `u[i-1] :: … :: u[size-1]` onto `acc`, from the back. -/
  go (i : Nat) (acc : List UInt8) : List UInt8 :=
    match i with
    | 0 => acc
    | i + 1 => go i (u.get! i :: acc)

/-- Decode a fixture block and check that it consumed every byte, that it
re-encodes to exactly the input, and that its header double-SHA-256s to the
expected block hash (given in display order, i.e. byte-reversed) — then apply
the fixture's own spot-checks. -/
def blockFixtureChecksOut (displayHash : String) (bytes : List UInt8)
    (spot : Block → Bool) : Bool :=
  match hexBytes? displayHash, Codec.decode (α := Block) bytes with
  | some hashBytes, some (b, rest) =>
    rest == []
    && Codec.encode b == bytes
    && Sha256.sha256d (Codec.encode b.header) == hashBytes.reverse
    && spot b
  | _, _ => false

/-- Spot-checks for block 481824 (2017-08-24), hash
`0000000000000000001c8018d9cb3b742ef25114f27563e3fc4a1902167f9893` — the
SegWit activation block. Header facts are from the block explorer; the
coinbase and the first SegWit spend must be byte-identical to the standalone
transaction vectors, tying the fixture to the inline `#guard`s. -/
def block481824Checks (b : Block) : Bool :=
  b.header.version == 0x20000002
  && b.header.prevBlockHash
    == 0x000000000000000000cbeff0b533f8e1189cf09dfbebf57a8ebe349362811b80#256
  && b.header.merkleRoot
    == 0x6438250cad442b982801ae6994edb8a9ec63c0a0ba117779fbe7ef7f07cad140#256
  && b.header.time == 1503539857
  && b.header.bits == 0x18013ce9
  && b.header.nonce == 575995682
  && b.txs.val.length == 1866
  -- The coinbase is the standalone SegWit-coinbase vector, byte for byte.
  && (match b.txs.val with
      | coinbase :: _ => some (Codec.encode coinbase) == hexBytes? segwitCoinbaseHex
      | _ => false)
  -- The first SegWit spend is one of this block's transactions, byte for byte.
  && (match hexBytes? firstSegwitSpendHex with
      | some spend => b.txs.val.any fun tx => Codec.encode tx == spend
      | none => false)
  -- Both serialization eras appear in the same block.
  && b.txs.val.any Tx.isSegWit
  && (b.txs.val.any fun tx => !tx.isSegWit)
  -- The header commits to all 1866 transaction ids through the merkle root,
  -- and the txid list is canonical. With the header-hash check above, every
  -- transaction byte in the fixture is now pinned: txids → merkle root →
  -- header → proof-of-work hash.
  && decide b.merkleCommits

/-- Where a fixture block is cached locally, by display hash. Gitignored. -/
def fixturePath (blockHash : String) : System.FilePath :=
  System.FilePath.mk "Tests" / "fixtures" / s!"block-{blockHash}.bin"

/-- The URL serving a block's raw bytes. Any esplora instance (or any Bitcoin
node via REST) serves the same bytes; blockstream.info is just a default. -/
def fixtureUrl (blockHash : String) : String :=
  s!"https://blockstream.info/api/block/{blockHash}/raw"

/-- Fetch a block's raw bytes into the local fixture cache if not already
present. Uses `curl`, since core Lean has no HTTP client. -/
def fetchFixture (blockHash : String) : IO System.FilePath := do
  let path := fixturePath blockHash
  if ← path.pathExists then
    return path
  if let some dir := path.parent then
    IO.FS.createDirAll dir
  let url := fixtureUrl blockHash
  IO.println s!"fetching block {blockHash}\n  from {url}\n  into {path}"
  let out ← IO.Process.output {
    cmd := "curl"
    args := #["--silent", "--show-error", "--fail", "--location",
              "--max-time", "120", "--output", path.toString, url]
  }
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"could not fetch fixture block {blockHash} (is the network up? is \
         curl installed?): {out.stderr}"
  return path

/-- Fetch (or reuse) a fixture block and run it through
`blockFixtureChecksOut`, reporting the result on stdout/stderr. Returns
`true` on success. -/
def checkFixture (blockHash : String) (spot : Block → Bool) : IO Bool := do
  let path ← fetchFixture blockHash
  let bytes ← IO.FS.readBinFile path
  if blockFixtureChecksOut blockHash (byteArrayToList bytes) spot then
    IO.println s!"block {blockHash}: decoded, header hash verified, \
                  spot-checked, re-encoded byte-for-byte"
    return true
  else
    IO.eprintln s!"block {blockHash}: FAILED (cached at {path})"
    return false

end Tests.BlockFixtures
