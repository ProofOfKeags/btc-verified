import Tests.GoldenVectors
/-!
  # Transaction conformance seeds

  Materialize the repository's existing transaction vectors as raw binary
  inputs for libFuzzer. Generated seeds live separately from the evolving
  corpus, under the gitignored `.lake/fuzz/` directory. An optional first
  argument selects the output directory; it defaults to `.lake/fuzz/seeds`.
-/

open Tests.GoldenVectors

/-- Write existing golden vectors and a few malformed boundary cases as raw
transaction inputs, failing if a vector cannot be decoded from hex. -/
def main (args : List String) : IO Unit := do
  let directory : System.FilePath :=
    match args with
    | path :: _ => path
    | [] => ".lake/fuzz/seeds"
  IO.FS.createDirAll directory
  let vectors := [
    ("first-payment", firstBitcoinPaymentHex),
    ("segwit-coinbase", segwitCoinbaseHex),
    ("first-segwit-spend", firstSegwitSpendHex),
    ("superfluous-witness", superfluousWitnessHex),
    ("empty-transaction", "01000000000000000000"),
    ("unknown-witness-flag", "010000000002"),
    ("noncanonical-input-count", "01000000fd0100")]
  for (name, hex) in vectors do
    let some bytes := hexBytes? hex
      | throw <| IO.userError s!"Invalid seed hex: {name}"
    IO.FS.writeBinFile (directory / name) bytes.toByteArray
  let some payment := hexBytes? firstBitcoinPaymentHex
    | throw <| IO.userError "Invalid first-payment seed"
  IO.FS.writeBinFile (directory / "truncated-payment") (payment.dropLast.toByteArray)
  IO.FS.writeBinFile (directory / "payment-with-suffix")
    ((payment ++ [0xde, 0xad]).toByteArray)
  IO.println s!"Wrote {vectors.length + 2} transaction seeds to {directory}"
