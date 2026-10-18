import Lake
import Lake.Toml

/-!
  # Pinned Core build for transaction conformance

  Provision only the kernel shared library. Commands and toolchain identities
  are logged; build directories are content-keyed and never committed.
-/

open System Lean Lake

namespace Conformance

/-- Isolate host tools from the shared-library paths that Lake installs. -/
def toolEnvironment : Array (String × Option String) :=
  #[("LD_LIBRARY_PATH", none), ("DYLD_LIBRARY_PATH", none)]

/-- Capture both pipes without blocking, logging stderr as its lines arrive. -/
private def outputWithProgress (args : IO.Process.SpawnArgs) (log : IO.FS.Handle)
    (onStderrLine : String → IO Unit) : IO IO.Process.Output := do
  let child ← IO.Process.spawn { args with stdin := .null, stdout := .piped, stderr := .piped }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  try
    let mut lines : Array String := #[]
    repeat
      let line ← child.stderr.getLine
      if line.isEmpty then break
      log.putStr line
      log.flush
      lines := lines.push line
      onStderrLine line
    let exitCode ← child.wait
    let stdout ← IO.ofExcept stdout.get
    log.putStr stdout
    return { stdout, stderr := String.join lines.toList, exitCode }
  catch error =>
    -- A failed output sink must not leave the fuzzing child running.
    try child.kill catch _ => pure ()
    try discard <| child.wait catch _ => pure ()
    try discard <| IO.ofExcept stdout.get catch _ => pure ()
    throw error

/-- Run a command and preserve its invocation, output, and exit status. -/
def run (logs : FilePath) (label command : String) (args : Array String)
    (env : Array (String × Option String) := #[])
    (onStderrLine : Option (String → IO Unit) := none) : IO IO.Process.Output := do
  IO.FS.createDirAll logs
  let invocation := Json.mkObj [("command", toJson command), ("args", toJson args)]
  let path := logs / s!"{label}.log"
  IO.FS.writeFile path (invocation.pretty ++ "\n")
  IO.FS.withFile path .append fun log => do
    let spawnArgs : IO.Process.SpawnArgs := { cmd := command, args, env := toolEnvironment ++ env }
    let output ← match onStderrLine with
      | some progress => outputWithProgress spawnArgs log progress
      | none => do
        let output ← IO.Process.output spawnArgs
        log.putStr (output.stdout ++ output.stderr)
        pure output
    log.putStr s!"\nexit={output.exitCode}\n"
    return output

/-- Fail a phase on nonzero exit, pointing at its complete log. -/
def checked (logs : FilePath) (label command : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO String := do
  let output ← run logs label command args env
  unless output.exitCode == 0 do
    throw <| IO.userError s!"{label} failed ({output.exitCode}); see {logs / s!"{label}.log"}"
  return output.stdout.trimAscii.toString

/-- Read the exact Core revision from the public ABI's single source of truth. -/
def coreRevision : IO String := do
  let path := "Kernel/abi.toml"
  let .ok table ← (Toml.loadToml (Parser.mkInputContext (← IO.FS.readFile path) path)).toBaseIO
    | throw <| IO.userError "Invalid Kernel/abi.toml"
  let some (.string _ revision) := table.find? `revision
    | throw <| IO.userError "Missing Core revision"
  unless revision.length == 40 && revision.toList.all Char.isHexDigit do
    throw <| IO.userError "Core revision must be a full commit SHA"
  return revision.toLower

/-- SHA-256 identities keep incompatible Core build trees separate. -/
def digest (logs : FilePath) (label : String) (path : FilePath) : IO String := do
  let output ← if Platform.isOSX then checked logs label "shasum" #["-a", "256", path.toString]
    else checked logs label "sha256sum" #[path.toString]
  let hash := (output.splitOn " ").headD ""
  unless hash.length == 64 && hash.toList.all Char.isHexDigit do
    throw <| IO.userError "Invalid SHA-256 output"
  return hash

/-- Use explicit host compilers, never Lean's restricted-sysroot C compiler. -/
def compiler (logs : FilePath) (envName fallback : String) : IO String := do
  let name := (← IO.getEnv envName).getD fallback
  checked logs envName "which" #[name]

/-- Fetch or validate pinned Core and reuse only a matching instrumented build.
An optional existing checkout is read-only and must be clean. Two build workers
bound local resource use. Coverage instrumentation is not leak analysis. -/
def buildCore (logs : FilePath) : IO FilePath := do
  let root ← IO.FS.realPath "."
  let revision ← coreRevision
  let cache := root / ".lake/conformance"
  let ready := cache / "core-cache-ready"
  if ← ready.pathExists then IO.FS.removeFile ready
  let override ← IO.getEnv "BTC_VERIFIED_CORE_SOURCE"
  let source := FilePath.mk (override.getD (cache / "sources" / revision).toString)
  unless ← source.pathExists do
    if override.isSome then throw <| IO.userError "BTC_VERIFIED_CORE_SOURCE does not exist"
    IO.FS.createDirAll source
  if override.isNone then
    discard <| checked logs "core-init" "git" #["init", source.toString]
    -- Retry an interrupted first fetch; never reset an existing checkout.
    let initialized ← run logs "core-head-probe" "git" #["-C", source.toString, "rev-parse", "--verify", "HEAD"]
    if initialized.exitCode != 0 then
      discard <| checked logs "core-fetch" "git" #["-C", source.toString, "fetch", "--depth=1",
        "https://github.com/bitcoin/bitcoin", revision]
      discard <| checked logs "core-checkout" "git" #["-C", source.toString, "checkout", "--detach", revision]
  let source ← IO.FS.realPath source
  let head ← checked logs "core-revision" "git" #["-C", source.toString, "rev-parse", "HEAD"]
  let dirty ← checked logs "core-status" "git" #["-C", source.toString, "status", "--porcelain"]
  unless head == revision && dirty.isEmpty do
    throw <| IO.userError "Core checkout must be clean at Kernel/abi.toml's revision"
  let cc ← compiler logs "FUZZ_CC" "clang"
  let cxx ← compiler logs "FUZZ_CXX" "clang++"
  let ccVersion ← checked logs "cc-version" cc #["--version"]
  let cxxVersion ← checked logs "cxx-version" cxx #["--version"]
  let cmakeVersion ← checked logs "cmake-version" "cmake" #["--version"]
  let ninjaVersion ← checked logs "ninja-version" "ninja" #["--version"]
  let platform ← checked logs "platform" "uname" #["-sm"]
  let mut options := #["-G", "Ninja", s!"-DCMAKE_C_COMPILER={cc}", s!"-DCMAKE_CXX_COMPILER={cxx}",
    "-DCMAKE_BUILD_TYPE=RelWithDebInfo", "-DBUILD_SHARED_LIBS=ON", "-DBUILD_KERNEL_LIB=ON",
    "-DBUILD_BITCOIN_BIN=OFF", "-DBUILD_DAEMON=OFF", "-DBUILD_GUI=OFF", "-DBUILD_CLI=OFF",
    "-DBUILD_TESTS=OFF", "-DBUILD_TX=OFF", "-DBUILD_UTIL=OFF", "-DBUILD_KERNEL_TEST=OFF",
    "-DBUILD_BENCH=OFF", "-DBUILD_FUZZ_BINARY=OFF", "-DENABLE_WALLET=OFF",
    "-DENABLE_IPC=OFF", "-DWITH_ZMQ=OFF", "-DWITH_USDT=OFF", "-DINSTALL_MAN=OFF",
    "-DWITH_CCACHE=OFF", "-DSANITIZERS=fuzzer"]
  if Platform.isOSX then
    let sdk ← checked logs "sdk" "xcrun" #["--show-sdk-path"]
    let deployment ← checked logs "deployment" "sw_vers" #["-productVersion"]
    options := options ++ #[s!"-DCMAKE_OSX_SYSROOT={sdk}", s!"-DCMAKE_OSX_DEPLOYMENT_TARGET={deployment}"]
  let recipe ← IO.FS.readFile "Fuzz/Build.lean"
  let flake ← IO.FS.readFile "flake.nix"
  let lock ← IO.FS.readFile "flake.lock"
  let environment ← #["CMAKE_PREFIX_PATH", "CMAKE_TOOLCHAIN_FILE", "CFLAGS", "CXXFLAGS",
    "CPPFLAGS", "LDFLAGS", "PKG_CONFIG_PATH", "SDKROOT", "MACOSX_DEPLOYMENT_TARGET",
    "NIX_CFLAGS_COMPILE", "NIX_LDFLAGS", "CPATH", "LIBRARY_PATH"].mapM fun name => do
      pure (name, toJson (← IO.getEnv name))
  let identity := logs / "core-build-identity.json"
  IO.FS.writeFile identity <| (Json.mkObj [
    ("revision", toJson revision), ("source", toJson source.toString), ("root", toJson root.toString),
    ("platform", toJson platform), ("cc", toJson ccVersion), ("cxx", toJson cxxVersion),
    ("cmake", toJson cmakeVersion), ("ninja", toJson ninjaVersion),
    ("environment", Json.mkObj environment.toList),
    ("options", toJson options), ("recipe", toJson recipe),
    ("flake", toJson flake), ("nixLock", toJson lock)]).pretty
  let key ← digest logs "core-build-key" identity
  let build := cache / "builds" / key
  discard <| checked logs "core-configure" "cmake"
    (#["-S", source.toString, "-B", build.toString] ++ options)
  discard <| checked logs "core-build" "cmake"
    #["--build", build.toString, "--target", "bitcoinkernel", "--parallel", "2"]
  let library := build / "lib" / s!"libbitcoinkernel.{if Platform.isOSX then "dylib" else "so"}"
  unless ← library.pathExists do throw <| IO.userError s!"Missing {library}"
  IO.FS.writeFile ready (key ++ "\n")
  return library

end Conformance
