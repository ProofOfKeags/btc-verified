import Tests.GoldenVectors
/-!
  # Transaction conformance inputs

  The conformance runner calls `Conformance.generateSeeds` to write small
  mutation seeds to `seeds/` and deterministic stripped-size boundary cases to
  `large/`. These are inputs, not an oracle: the runner compares both kernel
  implementations on their observations.

  Historical bytes and their provenance remain in `Tests.GoldenVectors`; the
  large cases are deliberately plain wire constructions, not spec round trips.
-/

namespace Conformance

private def fromHex (hex : String) : IO ByteArray :=
  match Tests.GoldenVectors.hexBytes? hex with
  | some bytes => pure bytes.toByteArray
  | none => throw <| IO.userError "Invalid hex in a conformance seed"

private def filled (size : Nat) (byte : UInt8) : ByteArray :=
  ⟨Array.replicate size byte⟩

-- One ordinary input and one output; only the output script's length changes.
-- Fixed fields total 59 bytes. These script lengths require a five-byte
-- CompactSize prefix, so the complete (also stripped) size is scriptSize + 64.
-- The enormous script is intentional: script execution/policy is not checked
-- by CheckTransaction. It isolates the inclusive 1,000,000-byte stripped limit.
private def largeTransaction (totalSize : Nat) : ByteArray :=
  let scriptSize := totalSize - 64
  ByteArray.mk #[1, 0, 0, 0, 1]                 -- version 1; one input
    ++ filled 32 1                              -- non-null previous txid
    ++ ByteArray.mk #[0, 0, 0, 0, 0]            -- output index 0; empty scriptSig
    ++ ByteArray.mk #[0xff, 0xff, 0xff, 0xff, 1] -- final sequence; one output
    ++ ByteArray.mk #[1, 0, 0, 0, 0, 0, 0, 0]   -- one satoshi
    ++ BtcVerified.Packed.pushCompactSize (UInt64.ofNat scriptSize) ByteArray.empty
    ++ filled scriptSize 0                      -- scriptPubKey bytes
    ++ ByteArray.mk #[0, 0, 0, 0]               -- locktime 0

private def writeInputs (directory : System.FilePath)
    (inputs : Array (String × ByteArray)) : IO Unit := do
  IO.FS.createDirAll directory
  for (name, bytes) in inputs do
    IO.FS.writeBinFile (directory / name) bytes

/-- Generate deterministic files for regression replay and the bounded campaign. -/
def generateSeeds (destination : System.FilePath) : IO Unit := do
  let payment ← fromHex Tests.GoldenVectors.firstBitcoinPaymentHex
  let spend ← fromHex Tests.GoldenVectors.firstSegwitSpendHex
  let coinbase ← fromHex Tests.GoldenVectors.segwitCoinbaseHex
  let emptyTransaction ← fromHex Tests.GoldenVectors.coreEmptyTxHex
  writeInputs (destination / "seeds") #[
    ("legacy-payment", payment),
    ("segwit-spend", spend),
    ("segwit-coinbase", coinbase),
    ("empty-input", ByteArray.empty),
    ("empty-transaction", emptyTransaction), -- parses, but no inputs or outputs
    ("truncated-locktime", payment.extract 0 (payment.size - 1)),
    ("unknown-witness-flag", coinbase.set! 5 0x03), -- retain witness bit; add unknown bit
    ("trailing-bytes", payment ++ ByteArray.mk #[0xde, 0xad])]
  -- Guard the fixture arithmetic before persisting inputs used as boundaries.
  let large ← #[999_999, 1_000_000, 1_000_001].mapM fun size => do
    let bytes := largeTransaction size
    unless bytes.size == size do
      throw <| IO.userError s!"Incorrect boundary fixture size: {size}"
    pure (s!"stripped-{size}", bytes)
  writeInputs (destination / "large") large

end Conformance
