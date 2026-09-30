import Kernel.Transaction
import KernelTests.AxiomAudit
import Tests.GoldenVectors
/-!
  # Independent examples at the Lean kernel boundary

  Four cases anchor the kernel to known wire data and protocol expectations.
  Each section states the claim, the source of its expected answer, and why
  the fixture distinguishes it. Every successful observation requires `some`;
  a failed parse cannot accidentally satisfy an expected rejection by `check`.

  General decoder, checker, and witness contracts are proved in
  `Kernel.Transaction` and audited in `KernelTests.AxiomAudit`, rather than
  sampled repeatedly here. Specification-rule examples live separately in
  `Tests.TransactionRules`. These fixed examples execute Lean code, not Core
  or the C ABI, and do not establish script or block validity.
-/

namespace KernelTests

open BtcVerified

set_option linter.hashCommand false

private def decodeHex (hex : String) : Option Tx :=
  (Tests.GoldenVectors.hexBytes? hex).bind fun bytes => Kernel.decode bytes.toByteArray

/-! ## A real legacy payment retains its amounts and identity

  The first Bitcoin payment paid 10 BTC to Hal Finney and returned 40 BTC as
  change. Its two output amounts and published txid are independent answers,
  not values computed by our encoder or specification. Its inclusion in block
  170 supplies the positive transaction-local checker expectation.

  Source: [the transaction on Blockstream](https://blockstream.info/tx/f4184fc596403b9d638783cf57adfe4c75c605f6356fbc91338530e9831e9e16).
  Raw bytes are shared with `Tests.GoldenVectors`; its `hashOfDisplay` only
  converts the published hex digest to raw byte order, without computing a hash.
-/

private def firstPayment : Option Tx :=
  decodeHex Tests.GoldenVectors.firstBitcoinPaymentHex

#guard firstPayment.map (fun tx => (Kernel.outputs tx).map Kernel.outputAmount) ==
  some #[1_000_000_000, 4_000_000_000]
#guard firstPayment.map Kernel.txid == some
  (Tests.GoldenVectors.hashOfDisplay
    "f4184fc596403b9d638783cf57adfe4c75c605f6356fbc91338530e9831e9e16").val.toByteArray
#guard firstPayment.map Kernel.check == some true

/-! ## A real SegWit coinbase retains its witness and stripped identity

  Block 481824's coinbase has one input, whose witness contains one item:
  the 32-zero-byte reserved value. Its published txid commits to the stripped
  transaction, not the witness-inclusive bytes. This independently anchors
  witness extraction and hashing, while its checker verdict exercises the
  coinbase branch on an accepted mainnet transaction.

  Source: [the transaction on Blockstream](https://blockstream.info/tx/da917699942e4a96272401b534381a75512eeebe8403084500bd637bd47168b3).
-/

private def activationCoinbase : Option Tx :=
  decodeHex Tests.GoldenVectors.segwitCoinbaseHex

#guard activationCoinbase.map Kernel.witnesses ==
  some #[#[(List.replicate 32 (0 : UInt8)).toByteArray]]
#guard activationCoinbase.map Kernel.txid == some
  (Tests.GoldenVectors.hashOfDisplay
    "da917699942e4a96272401b534381a75512eeebe8403084500bd637bd47168b3").val.toByteArray
#guard activationCoinbase.map Kernel.check == some true

/-! ## An unknown flag rejects an otherwise accepted encoding

  Use the passing coinbase above as the control. After the four-byte version
  and zero marker, byte 5 is flag 01. Change only that byte to 03: the witness
  bit stays set, but an unsupported bit is added. Nothing is truncated and
  all transaction fields stay intact. Core rejects unconsumed flag bits in
  [`UnserializeTransaction`](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/primitives/transaction.h#L222-L235);
  the decoder must not silently ignore this one.
-/

#guard match Tests.GoldenVectors.hexBytes? Tests.GoldenVectors.segwitCoinbaseHex with
  | some bytes => (Kernel.decode (bytes.set 5 0x03).toByteArray).isNone
  | none => false

/-! ## Parsing is not transaction-local acceptance

  The ten bytes `01000000 00 00 00000000` encode version 1, empty inputs and
  optional-data flag, and locktime 0. They decode to the empty object, which
  fails checking because it has no inputs or outputs. Unlike the unknown-flag
  case, rejection must happen AFTER successful parsing. `Tests.GoldenVectors`
  documents the encoding and cites Core's parser and `CheckTransaction`.
-/

private def emptyTransaction : Option Tx :=
  decodeHex Tests.GoldenVectors.coreEmptyTxHex

#guard emptyTransaction == some (Tx.empty 1 0)
#guard emptyTransaction.map Kernel.check == some false

end KernelTests
