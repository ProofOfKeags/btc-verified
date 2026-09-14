# Context-free transaction differential checks

This target compares btc-verified's executable, proved packed transaction
decoder and transaction-local checker with the public C API of the exact
Bitcoin Core revision in [`../fuzz.toml`](../fuzz.toml). It is deliberately
narrower than transaction acceptance in a mempool or block: it uses Core's
`btck_transaction_check`, which wraps `CheckTransaction` and consults neither
chainstate nor script execution.

Within a configured campaign's input domain, both implementations independently
produce a canonical observation or reject parsing, and the harness requires the
results to agree. A successful observation contains:

1. the context-free check verdict;
2. canonical transaction serialization;
3. input count, output count, and locktime;
4. every input's previous txid bytes, output index, sequence, scriptSig, and
   witness items; and
5. every output's signed amount bit pattern and scriptPubKey.

All transcript integers are written independently of the transaction codecs.
This prevents a matching decode/encode mistake, such as using the wrong byte
order in both directions, from cancelling itself out. Core's validation mode
and reason category are also checked for consistency with its boolean result.
The public API does not expose the transaction version as a field; it remains
covered by parsing and reserialization. Transaction-id hashing is outside this
target's structural-check boundary.

Core's generic deserializer rejects CompactSize container lengths above
`0x02000000`, an implementation resource ceiling that btc-verified's protocol
codec does not impose ([pinned `MAX_SIZE`](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/serialize.h#L35),
[range check](https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/serialize.h#L333-L363)).
Complete encodings above that length are therefore a known parser-domain
difference. The campaigns documented here stay below that ceiling—the largest
fixed case is 4,000,069 bytes—and make their `-max_len` explicit. This target
does not claim parser equivalence above the stated campaign domain.

## Model boundary

`Tx.isWellFormed` is intentionally the regular-transaction projection of
Core's checker: it rejects every null prevout because coinbase validity is a
block-position rule in the consensus model. The fuzz adapter adds Core's
standalone coinbase branch—exactly one null input and a 2–100 byte scriptSig—so
the two executable observations implement the same `CheckTransaction` predicate
within the stated parser domain. This does not change the consensus model or
claim that a passing transaction can be admitted to a block.

The regular adapter uses the packed transaction-body length in place of the
specification list encoder's length. Its equality to `Tx.isWellFormed` is proved
from `PackedCodec.toList_encode`; this keeps million-byte test cases on the
proved packed implementation instead of overflowing the native stack in the
list-based specification encoder.

## Building and running

The build helper requires Python 3.11+, the pinned Lean toolchain with this
project's packages already present, a clean Core checkout at the revision in
`fuzz.toml`, and an existing static Core build configured with
`BUILD_KERNEL_LIB=ON`, `BUILD_FOR_FUZZING=OFF`, and
`SANITIZERS=fuzzer,address`. It performs no checkout, dependency download,
configuration, or fuzz execution. It verifies those existing inputs before
linking. This is the local macOS build used for the recorded run:

```sh
python3 -B Fuzz/build.py \
  --core-build .lake/fuzz/core-build-asan-apple21 \
  --fuzzer-library /opt/homebrew/opt/llvm@17/lib/clang/17/lib/darwin/libclang_rt.fuzzer_osx.a \
  --macos-deployment-target 26.5
```

Run the bounded deterministic contract suites independently of libFuzzer:

```sh
.lake/fuzz/transaction --regression=small
.lake/fuzz/transaction --regression=large
```

The large suite explicitly exercises stripped sizes 999,999, 1,000,000, and
1,000,001 bytes, large witness data that does not count toward that limit, and
CompactSize boundaries. Generate those cases as corpus inputs if desired:

```sh
.lake/fuzz/transaction --regression=large --write-corpus=.lake/fuzz/generated-corpus
```

A campaign's maximum input size is explicit rather than compiled into the
oracle. A fast pull-request campaign can stay small; periodic campaigns can use
a larger `-max_len`. The deterministic large suite ensures the one-million-byte
consensus branch is still checked even when ordinary mutation is capped:

```sh
lake env lean --run Fuzz/SeedCorpus.lean
mkdir -p .lake/fuzz/corpus .lake/fuzz/artifacts

.lake/fuzz/transaction \
  -seed=1 -runs=100000 -max_len=4096 -timeout=10 -rss_limit_mb=2048 \
  -use_value_profile=1 -artifact_prefix=.lake/fuzz/artifacts/ \
  .lake/fuzz/corpus .lake/fuzz/seeds
```

An empty artifact directory and a completed campaign mean no disagreement was
found in the executed inputs. They are evidence for this stated boundary, not
proof of equivalence to Core, full transaction validity, or block validity.
