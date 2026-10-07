import Lake
import Lake.Toml

open Lake DSL System Lean

/-!
  # Project and native kernel build

  Lake tracks both Lean and C inputs. The optional native target authenticates
  Core's pinned public header; it never builds or executes Core.
-/

package «btc-verified» where
  version := v!"0.1.0"
  license := "Apache-2.0"
  testDriver := "tests"
  lintDriver := "batteries/runLinter"
  leanOptions := #[⟨`weak.linter.mathlibStandardSet, true⟩]
  -- Sanitizer-dependent objects must never replace ordinary Lake artifacts.
  buildDir := if (get_config? transactionCoverage) == some "true" then
    ".lake/conformance/verified-build"
  else
    defaultBuildDir

require "leanprover-community" / "mathlib"

private def transactionCoverage : Bool :=
  (get_config? transactionCoverage) == some "true"

private def transactionCoverageArgs : Array String :=
  if transactionCoverage then
    -- This inert define makes the selected compiler binary part of Lake's trace.
    #["-O1", "-g", "-fno-omit-frame-pointer", "-fsanitize=fuzzer-no-link",
      s!"-DBTC_VERIFIED_COVERAGE_COMPILER={
        (get_config? transactionCoverageCompiler).getD "unrecorded"}"]
  else
    #[]

@[default_target] lean_lib BtcVerified where
  moreLeancArgs := transactionCoverageArgs
@[default_target] lean_lib ModuleAudit
@[default_target] lean_lib Tests
@[default_target] lean_lib Kernel where
  roots := #[`Kernel.Transaction]
  moreLeancArgs := transactionCoverageArgs
@[default_target] lean_lib KernelTests

lean_exe tests where
  root := `TestsMain
lean_exe «module-audit» where
  root := `ModuleAuditMain
  supportInterpreter := true
lean_exe bench where
  root := `BenchMain

@[default_target] lean_lib Fuzz where
  roots := #[`Fuzz.Build, `Fuzz.Seeds]
lean_exe «core-build» where
  root := `Fuzz.CoreMain
lean_exe «transaction-conformance-runner» where
  root := `Fuzz.Check

/-- Bootstrap Lean dependencies before building and running the native comparison. -/
script «transaction-conformance» args do
  let cache ← IO.Process.spawn {cmd := "lake", args := #["exe", "cache", "get"]}
  let status ← cache.wait
  if status != 0 then return status
  let check ← IO.Process.spawn {cmd := "lake", args := #["exe", "transaction-conformance-runner"] ++ args.toArray}
  return ← check.wait

namespace KernelBuild

-- Lake adds Lean's shared-library directories to the loader environment.
-- External programs must not accidentally load Lean's bundled LLVM instead
-- of their own. The produced library carries its runtime paths explicitly.
private def toolEnvironment : Array (String × Option String) :=
  #[("DYLD_LIBRARY_PATH", none), ("LD_LIBRARY_PATH", none)]

private def run (command : String) (args : Array String) : IO String := do
  let output ← IO.Process.output {cmd := command, args, env := toolEnvironment}
  unless output.exitCode == 0 do
    throw <| IO.userError s!"{command} {args.toList}\n{output.stdout}{output.stderr}"
  return output.stdout

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def writeChanged (path : FilePath) (bytes : ByteArray) : IO Unit := do
  if ← path.pathExists then
    if (← IO.FS.readBinFile path) == bytes then return
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes

private def hexOfLength (length : Nat) (value : String) : Bool :=
  value.length == length && value.toList.all Char.isHexDigit

private def sha256 (path : FilePath) : IO String := do
  let output ← if Platform.isOSX then run "shasum" #["-a", "256", path.toString]
    else run "sha256sum" #[path.toString]
  let digest := ((output.splitOn " ").headD "").trimAscii.toString.toLower
  ensure (hexOfLength 64 digest) s!"Invalid SHA-256 output for {path}"
  return digest

private def stringAt (table : Toml.Table) (key : Name) : IO String := do
  let some (.string _ value) := table.find? key
    | throw <| IO.userError s!"Missing Kernel/abi.toml string: {key}"
  return value

private def readAbiConfig (root : FilePath) : IO Toml.Table := do
  let config := root / "Kernel/abi.toml"
  let contents ← IO.FS.readFile config
  let .ok table ← (Toml.loadToml (Parser.mkInputContext contents config.toString)).toBaseIO
    | throw <| IO.userError "Invalid Kernel/abi.toml"
  return table

private def authenticateHeader (root : FilePath) : IO FilePath := do
  let table ← readAbiConfig root
  let repository ← stringAt table `repository
  let revision := (← stringAt table `revision).toLower
  let headerPath ← stringAt table `header_path
  let digest := (← stringAt table `header_sha256).toLower
  ensure (repository == "https://github.com/bitcoin/bitcoin") "Unexpected Core repository"
  ensure (hexOfLength 40 revision) "Core revision must be a full commit SHA"
  ensure (headerPath == "src/kernel/bitcoinkernel.h") "Unexpected Core header path"
  ensure (hexOfLength 64 digest) "Header SHA-256 must contain 64 hexadecimal characters"
  let destination := root / ".lake/build/kernel/include/bitcoinkernel.h"
  if let some source ← IO.getEnv "BTC_VERIFIED_KERNEL_CORE_SOURCE" then
    let head := (← run "git" #["-C", source, "rev-parse", "HEAD"]).trimAscii.toString
    ensure (head.toLower == revision) "Core checkout HEAD differs from Kernel/abi.toml"
    let committed ← run "git" #["-C", source, "show", s!"{revision}:{headerPath}"]
    let working := FilePath.mk source / headerPath
    ensure ((← IO.FS.readBinFile working) == committed.toUTF8)
      "Core header differs from the pinned Git object"
    ensure ((← sha256 working) == digest) "Core header SHA-256 mismatch"
    writeChanged destination committed.toUTF8
  else
    let cached ← if ← destination.pathExists then pure ((← sha256 destination) == digest)
      else pure false
    unless cached do
      IO.FS.createDirAll (root / ".lake/build/kernel/include")
      let download := destination.addExtension "download"
      let url := s!"https://raw.githubusercontent.com/bitcoin/bitcoin/{revision}/{headerPath}"
      discard <| run "curl" #["--fail", "--location", "--silent", "--show-error",
        "--proto", "=https", "--proto-redir", "=https", "--max-time", "30",
        "--output", download.toString, url]
      ensure ((← sha256 download) == digest) "Downloaded Core header SHA-256 mismatch"
      writeChanged destination (← IO.FS.readBinFile download)
      IO.FS.removeFile download
  ensure ((← sha256 destination) == digest) "Cached Core header SHA-256 mismatch"
  return destination

private def readExports (root : FilePath) : IO (Array String) := do
  let table ← readAbiConfig root
  let some (.array _ values) := table.find? `exports
    | throw <| IO.userError "Missing Kernel/abi.toml exports array"
  let names ← values.mapM fun value => do
    let .string _ name := value
      | throw <| IO.userError "Kernel/abi.toml exports must contain only strings"
    pure name
  ensure (!names.isEmpty && names.all fun name => name.startsWith "btck_" &&
    name.toList.all fun c => c.toNat < 128 && (c.isAlphanum || c == '_'))
    "Invalid kernel export manifest"
  ensure (names.toList.eraseDups.length == names.size) "Duplicate kernel export"
  return names

private def compileShim (root buildDir : FilePath) (lean : LeanInstall) (cc : String)
    (coverage : Bool) : JobM FilePath := do
  let output := buildDir / "kernel/bitcoinkernel.o"
  let coverageArgs := if coverage then #["-fsanitize=fuzzer-no-link"] else #[]
  let args := #["-std=c11", "-O2", "-g", "-fPIC", "-pthread", "-fvisibility=hidden",
    "-Wall", "-Wextra", "-Werror",
    "-DBITCOINKERNEL_BUILD", "-I", (root / ".lake/build/kernel/include").toString,
    "-I", lean.includeDir.toString, "-c", (root / "Kernel/bitcoinkernel.c").toString,
    "-o", output.toString] ++ coverageArgs
  addLeanTrace
  addPlatformTrace
  addPureTrace (cc, ← run cc #["--version"], args) "C compiler"
  let artifact ← buildArtifactUnlessUpToDate output (ext := "o") (restore := true) do
    proc {cmd := cc, args, env := toolEnvironment}
  return artifact.path

private def linkKernel (root buildDir libDir : FilePath) (lean : LeanInstall) (cc : String)
    (objects : Array FilePath) (shim generated : FilePath) (coverage : Bool) : JobM FilePath := do
  let names ← readExports root
  let dir := buildDir / "kernel"
  let control := dir / if Platform.isOSX then "exports.list" else "exports.map"
  let text := if Platform.isOSX then String.join (names.toList.map fun name => s!"_{name}\n")
    else "{\n  global:\n" ++ String.join (names.toList.map fun name => s!"    {name};\n") ++
      "  local: *;\n};\n"
  writeChanged control text.toUTF8
  let response := dir / "lean-objects.rsp"
  writeChanged response (String.intercalate "\n"
    (objects.toList.map fun path => (toJson path.toString).compress) ++ "\n").toUTF8
  let library := s!"libbtc_verified_kernel.{sharedLibExt}"
  let output := libDir / library
  let platformFlags := if Platform.isOSX then
    #["-dynamiclib", s!"-Wl,-install_name,@rpath/{library}",
      s!"-Wl,-exported_symbols_list,{control}"]
    else #["-shared", s!"-Wl,-soname,{library}", s!"-Wl,--version-script={control}"]
  -- Lean's static runtime uses executable-only TLS on Linux. Use its shared
  -- runtime explicitly: this library must work in a plain C host, not just as
  -- a plugin loaded into Lean. Put strict checks last because Lean's macOS
  -- shared flags otherwise allow unresolved symbols via dynamic_lookup.
  -- The coverage build intentionally leaves SanitizerCoverage callbacks for
  -- the libFuzzer executable to provide when it loads this library.
  let undefinedFlags := if coverage then
      if Platform.isOSX then #["-Wl,-undefined,dynamic_lookup"] else #[]
    else if Platform.isOSX then #["-Wl,-undefined,error"] else #["-Wl,-z,defs"]
  let args := platformFlags ++ #["-pthread", shim.toString, s!"@{response}",
    "-L", lean.leanLibDir.toString, "-L", lean.systemLibDir.toString,
    s!"-Wl,-rpath,{lean.leanLibDir}", s!"-Wl,-rpath,{lean.systemLibDir}"] ++
    lean.linkSharedFlags ++ #["-lleanshared"] ++ undefinedFlags ++ #["-o", output.toString]
  addLeanTrace
  addPlatformTrace
  addPureTrace (cc, ← run cc #["--version"], args) "C linker"
  let artifact ← buildArtifactUnlessUpToDate output (ext := sharedLibExt) (restore := true) do
    -- Compile the generated Lean definitions with the bridge declarations in
    -- scope, so changes to exported Lean calling conventions fail the build.
    proc {
      cmd := cc
      env := toolEnvironment
      args := #["-std=c11", "-fsyntax-only", "-I", lean.includeDir.toString,
        "-include", (root / "Kernel/lean_bridge.h").toString, generated.toString]}
    proc {cmd := cc, args, env := toolEnvironment}
  return artifact.path

end KernelBuild

/-- Build the pinned-header-compatible transaction library, without building Core. -/
target kernel pkg : FilePath := do
  let root ← IO.FS.realPath pkg.dir
  let buildDir := pkg.buildDir
  let libDir := pkg.sharedLibDir
  unless !Platform.isWindows do error "The kernel target supports macOS and Linux"
  IO.FS.createDirAll (buildDir / "kernel")
  IO.FS.createDirAll libDir
  let lean ← getLeanInstall
  -- Lean's bundled compiler has a restricted sysroot intended for generated C.
  -- The C11 boundary needs the host headers (notably pthreads). The link flags
  -- still come from Lean, which owns its runtime and C++ support dependencies.
  let cc := (← IO.getEnv "CC").getD "cc"
  let header ← Job.async do
    let path ← KernelBuild.authenticateHeader root
    addTrace (← computeTrace path)
    return path
  let configs := Job.mixArray (← #["lakefile.lean", "Kernel/abi.toml",
    "Kernel/lean_bridge.h", "lean-toolchain"].mapM fun path => inputTextFile (root / FilePath.mk path))
  let source ← inputTextFile (root / "Kernel/bitcoinkernel.c")
  let shim ← (source.mix (header.mix configs)).mapM fun _ =>
    KernelBuild.compileShim root buildDir lean cc transactionCoverage
  let some mod ← findModule? `Kernel.Transaction
    | error "Kernel.Transaction is not registered with Lake"
  let generated ← mod.c.fetch
  let mut jobs := #[← mod.oExport.fetch]
  let .ok imports _ ← (← mod.transImports.fetch).wait
    | error "Unable to resolve Kernel.Transaction's imports"
  for imported in imports do jobs := jobs.push (← imported.o.fetch)
  let objects := Job.collectArray jobs
  let inputs := objects.zipWith (fun objects shim => (objects, shim)) shim
    |>.zipWith (fun pair generated => (pair.1, pair.2, generated)) generated
  -- Compiling the shim replaces its dependency trace with the object hash.
  -- Keep configuration inputs in the link trace too: an export-list change
  -- can require relinking even when the compiled shim is byte-for-byte equal.
  (inputs.zipWith (fun input _ => input) configs).mapM fun (objects, shim, generated) =>
    KernelBuild.linkKernel root buildDir libDir lean cc objects shim generated transactionCoverage

/-- Build the C library and smoke-test calls to its supported public symbols. -/
script «kernel-check» args do
  unless args.isEmpty do throw <| IO.userError "Usage: lake run kernel-check"
  let root ← IO.FS.realPath (← getRootPackage).dir
  let dir := root / ".lake/build/kernel"
  IO.FS.createDirAll dir
  -- Create the log before running commands; a failing compiler/test still
  -- leaves diagnostics available for CI artifact upload.
  let log := dir / "abi-test.log"
  IO.FS.writeFile log "Native kernel ABI callability smoke test\n"
  let execute := fun (command : String) (arguments : Array String) => do
    let output ← IO.Process.output {
      cmd := command
      args := arguments
      env := KernelBuild.toolEnvironment}
    let entry := s!"$ {command} {arguments.toList}\n{output.stdout}{output.stderr}exit={output.exitCode}\n"
    IO.FS.withFile log .append fun handle => handle.putStr entry
    unless output.exitCode == 0 do throw <| IO.userError entry
    return output.stdout
  -- Tee Lake's build diagnostics as well as the client commands below. A
  -- compiler/linker failure must leave its actual error in the CI artifact.
  let workspace ← getWorkspace
  IO.FS.withFile log .append fun handle => do
    let stderr ← IO.getStderr
    let output : IO.FS.Stream := {
      stderr with
      putStr := fun text => do
        handle.putStr text
        stderr.putStr text
      flush := do
        handle.flush
        stderr.flush }
    discard <| workspace.runBuild kernel.fetch {
      out := .stream output
      ansiMode := .noAnsi }
  let cc := (← IO.getEnv "CC").getD "cc"
  let compileArgs := #["-std=c11", "-Wall", "-Wextra", "-Werror",
    "-I", (dir / "include").toString]
  let linkArgs := #["-L", (root / ".lake/build/lib").toString,
    "-lbtc_verified_kernel", s!"-Wl,-rpath,{root / ".lake/build/lib"}"]
  let client := dir / "abi-test"
  discard <| execute cc (compileArgs ++ #[(root / "Kernel/tests/abi.c").toString] ++
    linkArgs ++ #["-o", client.toString])
  IO.print (← execute client.toString #[])
  return 0
