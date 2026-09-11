# BtcVerified/Script

The `Script` type: a Bitcoin Script program as it exists on the wire — raw,
CompactSize-length-prefixed bytes, type-distinct from anonymous byte strings
like witness items. `TxIn.scriptSig` and `TxOut.scriptPubKey` are `Script`s.

Checked claims:

- `instCodecScript`: the script codec satisfies round-trip and canonicality,
  inherited from the counted byte list.
- `Packed.instPackedCodecScript`: the packed encoder and decoder agree with
  the specification, inherited from the packed counted-list codec. Both
  instances live beside `Script` in `Script.lean`.

Keeping the program text raw is a protocol fact, not a simplification: Bitcoin
tokenizes a script only at execution time, and consensus never requires the
bytes to tokenize. Mainnet relies on this — most current coinbase scriptSigs
do not tokenize (pool tags whose bytes read as truncated pushes), and an
output script that fails to tokenize is merely unspendable, not invalid. So
the wire layer accepts every byte string, and tokenization will enter as the
first, fallible stage of the execution layer.

Why it matters: scripts are where transaction validity ultimately gets decided.
Giving programs their own type now — with the protocol's real
syntax/execution boundary built in — is the anchor the script-language layer
attaches to without touching the serialization stack.
