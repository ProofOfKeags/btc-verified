import Tests.BlockFixtures
/-!
  # Codec benchmarks

  Times the spec (`List UInt8`) and packed (`ByteArray`) block codecs
  against each other on the block-481824 fixture: decode and re-encode
  through both paths, checking they agree while measuring. Run with
  `lake exe bench`.

  Issue #52's success criterion — measured improvement over the list
  codec — is reported here, not asserted: timings vary by machine, so the
  benchmark prints and only agreement failures make it exit non-zero.
-/

namespace Tests.Bench

open BtcVerified BtcVerified.Serialize BtcVerified.Impl.Packed Tests.BlockFixtures

/-- Wall-clock a computation, returning its result and elapsed nanoseconds.
`IO.lazyPure` sequences the evaluation between the two clock reads — a plain
pure `let` would let the compiler float the work out of the timed window. -/
def time {α : Type} (act : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure act
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- Nanoseconds rendered as milliseconds with two decimals. -/
def ms (ns : Nat) : String :=
  s!"{ns / 1000000}.{ns / 10000 % 100} ms"

/-- The speedup of `fast` over `slow`, rendered with one decimal. -/
def speedup (slow fast : Nat) : String :=
  if fast == 0 then "∞" else s!"{slow / fast}.{slow * 10 / fast % 10}x"

/-- Decode and re-encode a fixture block through the spec and packed codecs,
timing each path and checking the results agree. Exits non-zero only on
disagreement — which the agreement theorems rule out for the *proved* code,
so a failure here would implicate the compiled pipeline. -/
def benchBlock (path : System.FilePath) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  IO.println s!"fixture: {path} ({bytes.size} bytes)"
  let (byteList, tToList) ← time fun _ => byteArrayToList bytes
  IO.println s!"ByteArray → List UInt8:  {ms tToList}"
  let (specParse, tSpecDecode) ← time fun _ => Codec.decode (α := Block) byteList
  let (packedParse, tPackedDecode) ← time fun _ => PackedCodec.decode (α := Block) bytes
  match specParse, packedParse with
  | some (specBlock, specRest), some (packedBlock, packedRest) =>
    unless specRest.isEmpty && packedRest.length == 0 do
      IO.eprintln "FAILED: a decoder left unconsumed bytes"
      return 1
    unless packedBlock == specBlock do
      IO.eprintln "FAILED: spec and packed decoders disagree on the block"
      return 1
    let (specBytes, tSpecEncode) ← time fun _ => Codec.encode specBlock
    let (packedBytes, tPackedEncode) ← time fun _ => PackedCodec.encode packedBlock
    unless specBytes == byteList && packedBytes == bytes do
      IO.eprintln "FAILED: a re-encoding differs from the input bytes"
      return 1
    IO.println s!"decode  spec:   {ms tSpecDecode}"
    IO.println s!"decode  packed: {ms tPackedDecode}  ({speedup tSpecDecode tPackedDecode} vs spec)"
    IO.println s!"encode  spec:   {ms tSpecEncode}"
    IO.println s!"encode  packed: {ms tPackedEncode}  ({speedup tSpecEncode tPackedEncode} vs spec)"
    return 0
  | _, _ =>
    IO.eprintln "FAILED: a decoder rejected the fixture block"
    return 1

end Tests.Bench
