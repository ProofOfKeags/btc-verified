import Tests.BlockFixtures
/-!
  # The test driver

  Runs the fixture checks that need `IO` — fetching blocks into the local
  fixture cache and decoding them (the inline golden vectors run as
  elaboration-time `#guard`s and need no driver). Invoked by `lake test`.
-/

open Tests.BlockFixtures

/-- Run every fixture check; exit non-zero if any fails. -/
def main : IO UInt32 := do
  let ok ← checkFixture
    "0000000000000000001c8018d9cb3b742ef25114f27563e3fc4a1902167f9893"
    block481824Checks
  return if ok then 0 else 1
