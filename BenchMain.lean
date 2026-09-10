import Tests.Bench
/-!
  # The benchmark driver

  Fetches (or reuses) the block-481824 fixture and times the spec and
  packed block codecs on it. Invoked by `lake exe bench`.
-/

open Tests.BlockFixtures Tests.Bench

/-- Run the codec benchmark on the fixture block; exit non-zero only if the
spec and packed paths disagree. -/
def main : IO UInt32 := do
  let path ← fetchFixture
    "0000000000000000001c8018d9cb3b742ef25114f27563e3fc4a1902167f9893"
  benchBlock path
