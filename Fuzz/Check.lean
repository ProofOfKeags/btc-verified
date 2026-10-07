import Fuzz.Build
import Fuzz.Seeds

/-!
  # Bounded public-ABI transaction conformance

  Rebuild current sources, replay inputs, mutate a fresh corpus, and check the
  disagreement detector is live. Reports survive failed phases. This is bounded
  experimental evidence, not a theorem or a replacement for Lean-side proofs.
-/

open System Lean Lake Conformance

/-- Load and range-check the bounded libFuzzer campaign parameters. -/
private def campaign : IO (Array (String × Nat)) := do
  let path := "Fuzz/campaign.toml"
  let .ok table ← (Toml.loadToml (Parser.mkInputContext (← IO.FS.readFile path) path)).toBaseIO
    | throw <| IO.userError "Invalid campaign TOML"
  #[(`seed, 1, 2147483647), (`runs, 1, 10000000), (`max_len, 1, 33554432),
    (`timeout, 1, 300), (`rss_limit_mb, 1, 16384)].mapM fun (key, low, high) => do
      let some (.integer _ value) := table.find? key
        | throw <| IO.userError s!"Missing campaign integer: {key}"
      unless value >= low && value <= high do
        throw <| IO.userError s!"Campaign {key} must be between {low} and {high}"
      return (key.toString, value.toNat)

/-- List a directory's input paths in deterministic order. -/
private def files (directory : FilePath) : IO (Array String) := do
  let entries ← directory.readDir
  return (entries.map fun entry => entry.path.toString).qsort (· < ·)

/-- Read libFuzzer's executed-unit count from its final statistics. -/
private def executedCount (output : String) : Option Nat := do
  let line ← (output.splitOn "\n").find? (·.startsWith "stat::number_of_executed_units:")
  let value ← (line.splitOn ":").getLast?
  value.trimAscii.toString.toNat?

/-- Require an injected disagreement to fail and preserve its reproduction artifacts. -/
private def requireMismatch (output : IO.Process.Output) (directory : FilePath)
    (expected : ByteArray) : IO Unit := do
  unless output.exitCode != 0 &&
      output.stderr.contains "injected mismatch: verified check verdict" &&
      output.stderr.contains "conformance mismatch: check verdict" do
    throw <| IO.userError "Negative control did not fail for the injected disagreement"
  unless (← IO.FS.readBinFile (directory / "mismatch.input")) == expected do
    throw <| IO.userError "Negative control did not preserve the complete input"
  for name in #["core.txt", "core.bytes", "verified.txt", "verified.bytes"] do
    unless ← (directory / name).pathExists do
      throw <| IO.userError s!"Negative control omitted {name}"

/-- Durable evidence locations and in-memory report state for one invocation. -/
private structure RunContext where
  /-- Canonical repository root used to resolve build artifacts. -/
  root : FilePath
  /-- Run directory relative to the root, used in portable replay commands. -/
  relativeDirectory : FilePath
  /-- Absolute directory containing this invocation's durable evidence. -/
  directory : FilePath
  /-- Directory containing subprocess invocations and output. -/
  logs : FilePath
  /-- Directory containing mismatch reproduction artifacts. -/
  failures : FilePath
  /-- Evidence fields accumulated before each report snapshot. -/
  report : IO.Ref (List (String × Json))

namespace RunContext

/-- Allocate durable report, log, and failure locations for one invocation. -/
private def create : IO RunContext := do
  let root ← IO.FS.realPath "."
  let relativeDirectory := FilePath.mk ".lake/conformance/runs" / s!"{← IO.monoNanosNow}"
  let directory := root / relativeDirectory
  let logs := directory / "logs"
  let failures := directory / "failures"
  IO.FS.createDirAll logs
  IO.FS.createDirAll failures
  let report ← IO.mkRef ([] : List (String × Json))
  return { root, relativeDirectory, directory, logs, failures, report }

/-- Add one evidence field to the eventual run report. -/
private def record (context : RunContext) (key : String) (value : Json) : IO Unit :=
  context.report.modify ((key, value) :: ·)

/-- Persist the current evidence with the run's lifecycle status. -/
private def save (context : RunContext) (status : String) : IO Unit := do
  IO.FS.writeFile (context.directory / "report.json") <|
    (Json.mkObj (("status", toJson status) :: (← context.report.get))).pretty

/-- Record the archived input and exact command needed to replay it. -/
private def recordReplay (context : RunContext) (relative : FilePath) : IO Unit := do
  let input := context.relativeDirectory / relative
  let command := "nix develop -c lake run transaction-conformance --replay " ++
    (toJson input.toString).compress
  context.record "replayInput" (toJson relative.toString)
  context.record "replayCommand" (toJson command)

/-- Preserve failure evidence, emit the error, and return a failing exit code. -/
private def fail (context : RunContext) (error : IO.Error) : IO UInt32 := do
  if ← (context.failures / "mismatch.input").pathExists then
    context.recordReplay (FilePath.mk "failures" / "mismatch.input")
  context.record "error" (toJson error.toString)
  context.save "failed"
  IO.eprintln error.toString
  return 1

end RunContext

/-- Paths to the two providers and their shared conformance driver. -/
private structure Harness where
  /-- Instrumented Bitcoin Core bitcoinkernel library. -/
  core : FilePath
  /-- Instrumented btc-verified bitcoinkernel library. -/
  verified : FilePath
  /-- libFuzzer driver that compares both libraries. -/
  binary : FilePath

/-- Parse an optional single-input replay request. -/
private def replayArgument (args : List String) : IO (Option FilePath) := do
  match args with
  | [] => pure none
  | ["--replay", path] => pure (some (← IO.FS.realPath path))
  | _ => throw <| IO.userError "Usage: lake run transaction-conformance [--replay INPUT]"

/-- Record the provenance and campaign bounds available for interpreting a run. -/
private def recordRunMetadata (context : RunContext) : IO (Array (String × Nat)) := do
  context.record "revision"
    (toJson (← checked context.logs "revision" "git" #["rev-parse", "HEAD"]))
  let dirty ← checked context.logs "status" "git" #["status", "--porcelain"]
  context.record "localChanges" (toJson dirty)
  context.record "cleanWorktree" (toJson dirty.isEmpty)
  -- A patch aids review, but untracked files and dirty dependency trees are
  -- not reconstructed. Reproduction also requires the pinned clean dependencies.
  discard <| checked context.logs "local-diff" "git" #["diff", "HEAD", "--binary"]
  context.record "coreRevision" (toJson (← coreRevision))
  let limits ← campaign
  context.record "campaign" (Json.mkObj (limits.toList.map fun (key, value) => (key, toJson value)))
  context.record "leanVersion"
    (toJson (← checked context.logs "lean-version" "lean" #["--version"]))
  context.record "lakeVersion"
    (toJson (← checked context.logs "lake-version" "lake" #["--version"]))
  context.record "instrumentation" (toJson "libFuzzer coverage: Core, btc-verified generated \
    Lean C, C boundary, and driver; dependencies and Lean runtime are uninstrumented; \
    no address/leak analysis")
  return limits

/-- Require one object or library to reference SanitizerCoverage callbacks. -/
private def requireCoverage (logs : FilePath) (label description : String)
    (object : FilePath) : IO Unit := do
  let symbols ← checked logs label "nm" #["-u", object.toString]
  unless symbols.contains "__sanitizer_cov_" do
    throw <| IO.userError s!"{description} lacks SanitizerCoverage callbacks"

/-- Build btc-verified separately so coverage flags never contaminate ordinary Lake objects. -/
private def buildVerified (context : RunContext) (cc : String) : IO FilePath := do
  context.record "coverageCompilerVersion" (toJson
    (← checked context.logs "coverage-compiler-version" cc #["--version"]))
  let ccHash ← digest context.logs "coverage-compiler-hash" (FilePath.mk cc)
  -- A distinct config filename gives coverage builds their own Lake config
  -- cache as well as their own object directory.
  let coverageLakefile := context.root / ".lake/conformance/lakefile.coverage.lean"
  IO.FS.writeFile coverageLakefile (← IO.FS.readFile (context.root / "lakefile.lean"))
  discard <| checked context.logs "verified-build" "lake"
    #["-R", "-f", coverageLakefile.toString, "-K", "transactionCoverage=true",
      "-K", s!"transactionCoverageCompiler={ccHash}", "build", "kernel"]
    #[ ("CC", some cc), ("LEAN_CC", some cc) ]
  let verified := context.root / ".lake/conformance/verified-build/lib" /
    s!"libbtc_verified_kernel.{if Platform.isOSX then "dylib" else "so"}"
  for (label, object) in #[
      ("verified-kernel-coverage", context.root /
        ".lake/conformance/verified-build/ir/Kernel/Transaction.c.o.export"),
      ("verified-model-coverage", context.root /
        ".lake/conformance/verified-build/ir/BtcVerified/Packed/Codec.c.o.export"),
      ("verified-boundary-coverage", context.root /
        ".lake/conformance/verified-build/kernel/bitcoinkernel.o")] do
    requireCoverage context.logs label label object
  requireCoverage context.logs "verified-coverage-symbols" "Verified kernel" verified
  return verified

/-- Compile the coverage-guided driver that loads and compares both providers. -/
private def buildDriver (context : RunContext) (cc : String) : IO FilePath := do
  let binary := context.directory / "transaction"
  let linker := if Platform.isOSX then #[] else #["-ldl", "-rdynamic"]
  discard <| checked context.logs "driver-build" cc
    (#["-std=c11", "-O1", "-g", "-Wall", "-Wextra", "-Werror", "-fsanitize=fuzzer",
      "-I", ".lake/build/kernel/include", "Fuzz/transaction.c"] ++ linker ++
      #["-o", binary.toString])
  return binary

/-- Build both providers and the one coverage-guided driver that compares them. -/
private def buildHarness (context : RunContext) : IO Harness := do
  let core ← buildCore context.logs
  let cc ← compiler context.logs "FUZZ_CC" "clang"
  let verified ← buildVerified context cc
  let binary ← buildDriver context cc
  for (name, path) in #[("core", core), ("verified", verified), ("driver", binary)] do
    context.record s!"{name}Sha256" (toJson (← digest context.logs s!"{name}-hash" path))
  return { core, verified, binary }

/-- Translate campaign limits into libFuzzer mutation flags. -/
private def mutationFlags (limits : Array (String × Nat)) : Array String :=
  limits.map fun (key, value) => s!"-{key}={value}"

/-- Derive single-execution flags that preserve complete replay inputs. -/
private def replayFlags (limits : Array (String × Nat)) : Array String :=
  -- File mode repeats EACH file and truncates it to max_len. Replay exactly
  -- once, without truncation; retain the timeout/RSS bounds for large inputs.
  (limits.filter fun p => p.1 != "runs" && p.1 != "max_len").map
    (fun (key, value) => s!"-{key}={value}") |>.append #["-runs=1", "-max_len=0"]

/-- Select both providers and request libFuzzer's final statistics. -/
private def providerArguments (harness : Harness) : Array String :=
  #[s!"--core={harness.core}", s!"--verified={harness.verified}", "-print_final_stats=1"]

/-- Add ordinary failure-artifact paths to the provider arguments. -/
private def normalArguments (context : RunContext) (harness : Harness) : Array String :=
  providerArguments harness ++ #[s!"--artifacts={context.failures}",
    s!"-artifact_prefix={context.failures}/"]

/-- Re-run one archived input without mutation or the campaign's size cap. -/
private def replaySavedInput (context : RunContext) (harness : Harness)
    (limits : Array (String × Nat)) (input : FilePath) : IO Unit := do
  let archived := context.directory / "replay.input"
  IO.FS.writeBinFile archived (← IO.FS.readBinFile input)
  context.recordReplay "replay.input"
  discard <| checked context.logs "replay" harness.binary.toString
    (normalArguments context harness ++ replayFlags limits ++ #[archived.toString])

/-- Replay small transaction fixtures and large size boundaries before mutation. -/
private def replayRegressions (context : RunContext) (harness : Harness)
    (limits : Array (String × Nat)) (seeds : FilePath) : IO Unit := do
  let arguments := normalArguments context harness ++ replayFlags limits
  discard <| checked context.logs "small-replay" harness.binary.toString
    (arguments ++ (← files seeds))
  discard <| checked context.logs "large-replay" harness.binary.toString
    (arguments ++ (← files (context.directory / "large")))

/-- Mutate a fresh corpus and require feedback from the driver and both providers. -/
private def runMutationCampaign (context : RunContext) (harness : Harness)
    (limits : Array (String × Nat)) (seeds corpus : FilePath) : IO Unit := do
  let fuzz ← run context.logs "campaign" harness.binary.toString
    (normalArguments context harness ++ mutationFlags limits ++ #[corpus.toString, seeds.toString])
  let count := executedCount fuzz.stderr
  context.record "executedUnits" (toJson count)
  unless fuzz.exitCode == 0 && count == (limits.find? (·.1 == "runs")).map (·.2) &&
      fuzz.stderr.contains "INFO: Loaded 3 modules" &&
      fuzz.stderr.contains "INFO: Loaded 3 PC tables" do
    throw <| IO.userError s!"Campaign failed or execution count missing; \
      coverage modules may also be unregistered; see {context.logs / "campaign.log"}"

/-- Verify the harness notices, preserves, and reproduces an injected disagreement. -/
private def verifyMismatchDetector (context : RunContext) (harness : Harness)
    (limits : Array (String × Nat)) (seeds : FilePath) : IO Unit := do
  let fixture ← IO.FS.readBinFile (seeds / "legacy-payment")
  let negative := context.directory / "negative"
  let reproduced := context.directory / "negative-replay"
  IO.FS.createDirAll negative
  IO.FS.createDirAll reproduced
  let providers := providerArguments harness
  let replay := replayFlags limits
  let injected := providers ++ replay ++ #["--inject-mismatch",
    s!"--artifacts={negative}", s!"-artifact_prefix={negative}/",
    (seeds / "legacy-payment").toString]
  requireMismatch (← run context.logs "negative" harness.binary.toString injected) negative fixture
  let saved := negative / "mismatch.input"
  discard <| checked context.logs "negative-clean-replay" harness.binary.toString
    (normalArguments context harness ++ replay ++ #[saved.toString])
  requireMismatch (← run context.logs "negative-injected-replay" harness.binary.toString
    (providers ++ replay ++ #["--inject-mismatch", s!"--artifacts={reproduced}",
      s!"-artifact_prefix={reproduced}/", saved.toString])) reproduced fixture
  context.record "negativeControl" (toJson "baseline agreed; injected mismatch saved; \
    clean and injected replay verified")

/-- Run deterministic regressions, bounded mutation, and the detector control. -/
private def runCampaign (context : RunContext) (harness : Harness)
    (limits : Array (String × Nat)) : IO Unit := do
  generateSeeds context.directory
  let seeds := context.directory / "seeds"
  let corpus := context.directory / "corpus"
  IO.FS.createDirAll corpus
  replayRegressions context harness limits seeds
  runMutationCampaign context harness limits seeds corpus
  verifyMismatchDetector context harness limits seeds

/-- Execute the requested campaign or replay with durable status updates. -/
private def execute (context : RunContext) (replay : Option FilePath) : IO Unit := do
  let limits ← recordRunMetadata context
  context.save "building"
  let harness ← buildHarness context
  context.save "running"
  match replay with
  | some input => replaySavedInput context harness limits input
  | none => runCampaign context harness limits
  context.save "passed"

/-- Run the same comparison locally and in CI, or replay one saved input. -/
def main (args : List String) : IO UInt32 := do
  let replay ← replayArgument args
  let context ← RunContext.create
  let result ← try
    execute context replay
    pure 0
  catch error => context.fail error
  IO.println s!"Conformance report: {context.directory / "report.json"}"
  return result
