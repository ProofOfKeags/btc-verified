import Lake
import Lake.Toml

open Lake DSL System Lean

/-!
  # Project and native kernel build

  Lake owns the Lean/C dependency graph. The native target authenticates only
  Core's public header; it never builds or executes Core. Operational audits
  and standalone C-client tests are performed by `lake exe kernel-check`.
-/

package «btc-verified» where
  version := v!"0.1.0"
  license := "Apache-2.0"
  testDriver := "tests"
  lintDriver := "batteries/runLinter"
  leanOptions := #[⟨`weak.linter.mathlibStandardSet, true⟩]

require "leanprover-community" / "mathlib"

@[default_target] lean_lib BtcVerified
@[default_target] lean_lib ModuleAudit
@[default_target] lean_lib Tests
lean_lib Fuzz where
  roots := #[`Fuzz.Transaction]
@[default_target] lean_lib FuzzTests
lean_lib Kernel where
  roots := #[`Kernel.Transaction]
@[default_target] lean_lib KernelTests
@[default_target] lean_lib KernelTools where
  -- Check imports every tooling module, so Batteries needs only one lint pass.
  -- Keep all tooling modules in the library's build and discovery set.
  roots := #[`Kernel.Tools.Check]
  globs := #[.submodules `Kernel.Tools]
@[default_target] lean_lib KernelToolsTests

lean_exe tests where
  root := `TestsMain
lean_exe «module-audit» where
  root := `ModuleAuditMain
  supportInterpreter := true
lean_exe bench where
  root := `BenchMain
lean_exe «kernel-check» where
  root := `KernelCheck

namespace KernelBuild

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

-- Lake's loader paths select the libraries bundled with Lean. External tools
-- must use their own runtime search paths: mixing their LLVM with Lean's LLVM
-- can fail before the tool even reaches main.
private def externalToolEnvironment : Array (String × Option String) :=
  #[("DYLD_LIBRARY_PATH", none), ("LD_LIBRARY_PATH", none)]

private def run (command : String) (args : Array String := #[]) : IO String := do
  let output ← IO.Process.output {cmd := command, args, env := externalToolEnvironment}
  unless output.exitCode == 0 do
    throw <| IO.userError s!"{command} {args.toList}\n{output.stdout}{output.stderr}"
  return output.stdout

private def writeChanged (path : FilePath) (bytes : ByteArray) : IO Unit := do
  if ← path.pathExists then
    if (← IO.FS.readBinFile path) == bytes then return
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes

private def writeJson (path : FilePath) (value : Json) : IO Unit :=
  writeChanged path (value.pretty ++ "\n").toUTF8

private def loadToml (path : FilePath) : IO Toml.Table := do
  let contents ← IO.FS.readFile path
  match ← (Toml.loadToml (Parser.mkInputContext contents path.toString)).toBaseIO with
  | .ok table => return table
  | .error messages =>
    throw <| IO.userError <| "Invalid TOML: " ++
      String.intercalate "\n" (← messages.toList.mapM (·.toString))

private def stringAt (table : Toml.Table) (key : Name) : IO String := do
  let some (.string _ value) := table.find? key
    | throw <| IO.userError s!"Missing TOML string {key}"
  return value

private def hexOfLength (length : Nat) (value : String) : Bool :=
  value.length == length && value.toList.all Char.isHexDigit

private structure Pins where
  revision : String
  repository : String
  headerPath : String
  digest : String
  version : Json

private def readPins (root : FilePath) : IO Pins := do
  let fuzz ← loadToml (root / "fuzz.toml")
  let some (.table _ core) := fuzz.find? `bitcoinkernel
    | throw <| IO.userError "fuzz.toml needs [bitcoinkernel]"
  let abi ← loadToml (root / "Kernel/abi.toml")
  let revision ← stringAt core `rev
  let repository ← stringAt core `repository
  let headerPath ← stringAt abi `header_path
  let digest ← stringAt abi `header_sha256
  ensure (hexOfLength 40 revision) "Core revision must contain exactly 40 hexadecimal characters"
  ensure (hexOfLength 64 digest) "Header SHA-256 must contain exactly 64 hexadecimal characters"
  ensure (headerPath == "src/kernel/bitcoinkernel.h") "Unexpected kernel header path"
  let version ← match abi.find? `version with
    | none => pure Json.null
    | some (.integer _ n) => pure (toJson n)
    | _ => throw <| IO.userError "ABI version must be an integer when present"
  return {revision := revision.toLower, repository, headerPath, digest := digest.toLower, version}

private def headerUrl (pins : Pins) : IO String := do
  let repository := if pins.repository.endsWith ".git" then
    (pins.repository.dropEnd 4).toString else pins.repository
  let urlPrefix := "https://github.com/"
  ensure (repository.startsWith urlPrefix) "Core repository must be a canonical HTTPS GitHub URL"
  let parts := ((repository.drop urlPrefix.length).toString.splitOn "/")
  ensure (parts.length == 2 && parts.all fun part =>
    !part.isEmpty && part.toList.all fun c => c.isAlphanum || "-_.".contains c)
    "Core repository must be github.com/owner/repository"
  return s!"https://raw.githubusercontent.com/{String.intercalate "/" parts}/{pins.revision}/{pins.headerPath}"

private def sha256 (path : FilePath) : IO String := do
  let output ← if Platform.isOSX then
    run "shasum" #["-a", "256", path.toString]
  else run "sha256sum" #[path.toString]
  let digest := ((output.splitOn " ").headD "").trimAscii.toString
  ensure (hexOfLength 64 digest) s!"Invalid SHA-256 tool output for {path}"
  return digest.toLower

private def authenticateHeader (root coreSource : FilePath) : IO (FilePath × Json) := do
  let pins ← readPins root
  let url ← headerUrl pins
  let destination := root / ".lake/kernel/include/kernel/bitcoinkernel.h"
  let checkoutHeader := coreSource / pins.headerPath
  let source ← if ← checkoutHeader.pathExists then do
    let head := (← run "git" #["-C", coreSource.toString, "rev-parse", "HEAD"]).trimAscii.toString
    ensure (head.toLower == pins.revision) "Core checkout HEAD differs from fuzz.toml"
    discard <| run "git" #["-C", coreSource.toString, "cat-file", "-e", s!"{pins.revision}^\u007bcommit\u007d"]
    let committed ← run "git" #["-C", coreSource.toString, "show", s!"{pins.revision}:{pins.headerPath}"]
    let working ← IO.FS.readBinFile checkoutHeader
    ensure (working == committed.toUTF8) "Core header differs from the exact pinned Git object"
    ensure ((← sha256 checkoutHeader) == pins.digest) "Pinned header SHA-256 mismatch"
    writeChanged destination working
    pure [("kind", toJson "git-checkout"), ("checkout", toJson coreSource.toString),
      ("git_revision_verified", toJson true)]
  else do
    let cached ← if ← destination.pathExists then pure ((← sha256 destination) == pins.digest)
      else pure false
    unless cached do
      IO.FS.createDirAll (root / ".lake/kernel/include/kernel")
      let download := destination.addExtension "download"
      discard <| run "curl" #["--fail", "--location", "--silent", "--show-error",
        "--proto", "=https", "--proto-redir", "=https", "--max-time", "30",
        "--output", download.toString, url]
      ensure ((← sha256 download) == pins.digest) "Downloaded header SHA-256 mismatch"
      writeChanged destination (← IO.FS.readBinFile download)
      IO.FS.removeFile download
    pure [("kind", toJson (if cached then "authenticated-header-cache" else "header-only-download")),
      ("url", toJson url),
      ("git_revision_verified", toJson false),
      ("revision_evidence", toJson "commit-addressed HTTPS URL plus pinned SHA-256")]
  ensure ((← sha256 destination) == pins.digest) "Copied header SHA-256 mismatch"
  return (destination, Json.mkObj <| source ++ [
    ("revision", toJson pins.revision), ("header_path", toJson pins.headerPath),
    ("sha256", toJson pins.digest), ("copied_header", toJson destination.toString)])

private def resolveCompiler (lean : LeanInstall) (override : Option String) : IO FilePath := do
  let requested := override.or (← IO.getEnv "CC")
  let candidates := requested.toArray ++ if requested.isSome then #[] else #["clang", "cc", "gcc"]
  let paths := ((← IO.getEnv "PATH").getD "").splitOn (if Platform.isWindows then ";" else ":")
  let bundledBin ← IO.FS.realPath lean.binDir
  for candidate in candidates do
    if candidate.contains '/' then
      if ← (FilePath.mk candidate).pathExists then return ← IO.FS.realPath candidate
    else
      for dir in paths do
        let directory := FilePath.mk (if dir.isEmpty then "." else dir)
        if ← directory.pathExists then
          -- `lake exe` prepends Lean's bin directory to PATH. Its bundled
          -- clang requires Lean-specific internal sysroot flags, so an
          -- unqualified compiler name must resolve to the external C toolchain.
          if (← IO.FS.realPath directory) != bundledBin then
            let path := directory / candidate
            if ← path.pathExists then return ← IO.FS.realPath path
  throw <| IO.userError s!"No C compiler found: {candidates.toList}"

private def deploymentTarget (override : Option String) : IO (Option String) := do
  if !Platform.isOSX then
    ensure override.isNone "A macOS deployment override is available only on macOS"
    return none
  let version ← match override with
    | some version => pure version
    | none => return (← run "sw_vers" #["-productVersion"]).trimAscii.toString
  let parts := version.splitOn "."
  ensure (parts.length ≥ 1 && parts.length ≤ 3 && parts.all fun part =>
    !part.isEmpty && part.toList.all Char.isDigit) "Invalid macOS deployment target"
  return some version

private def readExports (path : FilePath) : IO (Array String) := do
  let names := ((← IO.FS.readFile path).splitOn "\n").toArray.map
    (fun line => ((line.splitOn "#").headD "").trimAscii.toString)
    |>.filter (!·.isEmpty)
  ensure (!names.isEmpty && names.all fun name => name.startsWith "btck_" && name.length > 5 &&
    name.toList.all fun c => c.toNat < 128 && (c.isAlphanum || c == '_'))
    "Invalid kernel export manifest"
  ensure (names.toList.eraseDups.length == names.size) "Duplicate kernel export"
  return names

private def controlText (names : Array String) : String :=
  if Platform.isOSX then String.join (names.toList.map fun name => s!"_{name}\n")
  else "{\n  global:\n" ++ String.join (names.toList.map fun name => s!"    {name};\n") ++
    "  local:\n    *;\n};\n"

private def runtimeReport (lean : LeanInstall) (flags : Array String) : IO Json := do
  let libraries := flags.filterMap fun flag =>
    if flag.startsWith "-l" then some (flag.drop 2).toString else none
  let mut resolved := []
  for library in libraries do
    let mut found := false
    for dir in #[lean.leanLibDir, lean.systemLibDir] do
      for ext in #["a", "dylib", "so"] do
        let path := dir / s!"lib{library}.{ext}"
        if !found && (← path.pathExists) then
          resolved := resolved ++ [(library, toJson path.toString)]
          found := true
  return Json.mkObj [
    ("handwritten_source_language", toJson "C11"), ("link_driver_language", toJson "C"),
    ("runtime_c_only", toJson false),
    ("link_flags_source", toJson "Lean.Compiler.FFI.getLinkerFlags (same API as leanc --print-ldflags)"),
    ("lean_link_flags", toJson flags), ("link_libraries", toJson libraries),
    ("resolved_lean_toolchain_libraries", Json.mkObj resolved),
    ("detected_cxx_support_libraries", toJson <| libraries.filter
      (#["c++", "c++abi", "stdc++", "supc++", "leancpp"].contains ·)),
    ("note", toJson "Project-owned C11 code inherits the pinned Lean runtime and its C++ support.")]

private structure NativeConfig where
  root : FilePath
  artifacts : FilePath
  cc : FilePath
  compilerVersion : String
  compilerEnvironment : Array (String × Option String)
  deployment : Option String
  lean : LeanInstall

private def NativeConfig.deploymentFlags (cfg : NativeConfig) : Array String :=
  cfg.deployment.toArray.map ("-mmacosx-version-min=" ++ ·)

private def NativeConfig.leanFlags (cfg : NativeConfig) : Array String :=
  Lean.Compiler.FFI.getLinkerFlags cfg.lean.sysroot

private def NativeConfig.compileArgs (cfg : NativeConfig) : Array String :=
  #["-std=c11", "-O2", "-g", "-fPIC", "-pthread", "-fvisibility=hidden"] ++
    cfg.deploymentFlags ++ #["-DBITCOINKERNEL_BUILD", "-I", (cfg.artifacts / "include").toString,
      "-I", cfg.root.toString, "-I", cfg.lean.includeDir.toString,
      "-c", (cfg.root / "Kernel/bitcoinkernel.c").toString,
      "-o", (cfg.artifacts / "bitcoinkernel.o").toString]

private def NativeConfig.signatureArgs (cfg : NativeConfig) (generated : FilePath) : Array String :=
  #["-std=c11", "-fsyntax-only", "-I", cfg.lean.includeDir.toString,
    "-include", (cfg.root / "Kernel/lean_bridge.h").toString, generated.toString]

private def nativeConfig (root : FilePath) (lean : LeanInstall)
    (ccOverride deploymentOverride : Option String) : IO NativeConfig := do
  unless Platform.isOSX do
    ensure (!Platform.isWindows && (← run "uname" #["-s"]).trimAscii.toString == "Linux")
      "The native kernel build supports macOS and Linux only"
  let cc ← resolveCompiler lean ccOverride
  let environment ← #["SDKROOT", "MACOSX_DEPLOYMENT_TARGET", "CPATH", "C_INCLUDE_PATH",
    "LIBRARY_PATH", "NIX_CFLAGS_COMPILE", "NIX_LDFLAGS"].mapM fun name => do
      return (name, ← IO.getEnv name)
  let compilerVersion ← run cc.toString #["--version"]
  let deployment ← deploymentTarget deploymentOverride
  return {
    root := root
    artifacts := root / ".lake/kernel"
    cc := cc
    compilerVersion := compilerVersion
    compilerEnvironment := environment
    deployment := deployment
    lean := lean
  }

private def compilerTrace (cfg : NativeConfig) (args : Array String) : JobM Unit := do
  addLeanTrace
  addPlatformTrace
  addPureTrace (cfg.cc.toString, cfg.compilerVersion, cfg.compilerEnvironment, args) "C toolchain"

private def compileShim (cfg : NativeConfig) : JobM FilePath := do
  compilerTrace cfg cfg.compileArgs
  let artifact ← buildArtifactUnlessUpToDate (cfg.artifacts / "bitcoinkernel.o")
      (ext := "o") (restore := true) do
    proc {cmd := cfg.cc.toString, args := cfg.compileArgs, env := externalToolEnvironment}
  return artifact.path

private def checkSignatures (cfg : NativeConfig) (generated : FilePath) : JobM FilePath := do
  let command := cfg.signatureArgs generated
  compilerTrace cfg command
  let stamp := cfg.artifacts / "signature.checked"
  discard <| buildArtifactUnlessUpToDate stamp (text := true) (restore := true) do
    proc {cmd := cfg.cc.toString, args := command, env := externalToolEnvironment}
    IO.FS.writeFile stamp "Lean export signatures agree.\n"
  return generated

private def writeNativeReport (cfg : NativeConfig) (objects : Array FilePath)
    (header output response control generated : FilePath) (linkArgs : Array String) : IO Unit := do
  let pins ← readPins cfg.root
  let provenance ← IO.ofExcept <| Json.parse (← IO.FS.readFile (cfg.artifacts / "header-source.json"))
  let inherited ← runtimeReport cfg.lean cfg.leanFlags
  writeJson (cfg.artifacts / "native-build.json") <| Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("status", toJson "pass"),
    ("command", toJson #["lake", "build", "kernel"]),
    ("core_revision", toJson pins.revision), ("core_repository", toJson pins.repository),
    ("abi_config_version", pins.version), ("header_source", provenance),
    ("canonical_header", toJson header.toString), ("output", toJson output.toString),
    ("output_sha256", toJson (← sha256 output)), ("compiler", toJson cfg.cc.toString),
    ("compiler_version", toJson cfg.compilerVersion.trimAscii.toString),
    ("compiler_environment", toJson cfg.compilerEnvironment),
    ("external_tool_environment", toJson externalToolEnvironment),
    ("handwritten_source_language", toJson "C11"), ("link_driver_language", toJson "C"),
    ("macos_deployment_target", toJson cfg.deployment),
    ("lean_prefix", toJson cfg.lean.sysroot.toString),
    ("lean_object_count", toJson objects.size), ("root_object_facet", toJson "o.export"),
    ("import_object_facet", toJson "o"), ("response_file", toJson response.toString),
    ("export_control", toJson control.toString), ("inherited_runtime", inherited),
    ("compile_command", toJson (#[cfg.cc.toString] ++ cfg.compileArgs)),
    ("link_command", toJson (#[cfg.cc.toString] ++ linkArgs)),
    ("lean_signature_command", toJson (#[cfg.cc.toString] ++ cfg.signatureArgs generated))]

private def linkKernel (cfg : NativeConfig) (objects : Array FilePath)
    (native generated header : FilePath) : JobM FilePath := do
  let names ← readExports (cfg.root / "Kernel/exports.txt")
  let control := cfg.artifacts / if Platform.isOSX then "exported_symbols.list" else "exports.map"
  writeChanged control (controlText names).toUTF8
  let controlFlags := if Platform.isOSX then
    #[s!"-Wl,-exported_symbols_list,{control}", "-Wl,-undefined,error"]
    else #[s!"-Wl,--version-script={control}", "-Wl,-z,defs"]
  let output := cfg.artifacts / if Platform.isOSX then "libbitcoinkernel.dylib" else "libbitcoinkernel.so"
  let response := cfg.artifacts / "lean-objects.rsp"
  writeChanged response (String.intercalate "\n"
    (objects.toList.map fun path => (toJson path.toString).compress) ++ "\n").toUTF8
  let platformFlags := if Platform.isOSX then
    #["-dynamiclib", "-pthread"] ++ cfg.deploymentFlags ++
      #["-Wl,-install_name,@rpath/libbitcoinkernel.dylib"]
    else #["-shared", "-Wl,-soname,libbitcoinkernel.so", "-pthread"]
  let linkArgs := platformFlags ++ #[native.toString, s!"@{response}"] ++ controlFlags ++
    #["-L", cfg.lean.systemLibDir.toString] ++ cfg.leanFlags ++ #["-o", output.toString]
  compilerTrace cfg linkArgs
  discard <| buildArtifactUnlessUpToDate output (ext := sharedLibExt) (restore := true) do
    proc {cmd := cfg.cc.toString, args := linkArgs, env := externalToolEnvironment}
  writeNativeReport cfg objects header output response control generated linkArgs
  return output

private def headerJob (root coreSource : FilePath) : SpawnM (Job FilePath) := Job.async do
  let (header, provenance) ← authenticateHeader root coreSource
  writeJson (root / ".lake/kernel/header-source.json") provenance
  -- Cache acquisition details are report data, not semantic build inputs.
  addPureTrace coreSource.toString "header source"
  addTrace (← computeTrace header)
  return header

/-- Build the authenticated public header and independently implemented native library. -/
def build (pkg : Package) (coreOverride ccOverride deploymentOverride : Option String)
    : FetchM (Job FilePath) := do
  let root ← IO.FS.realPath pkg.dir
  let artifacts := root / ".lake/kernel"
  IO.FS.createDirAll artifacts
  writeJson (artifacts / "native-build.json") <| Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("status", toJson "running"),
    ("command", toJson #["lake", "build", "kernel"])]
  let cfg ← nativeConfig root (← getLeanInstall) ccOverride deploymentOverride
  let source := (coreOverride.map FilePath.mk).getD (root / ".lake/fuzz/core")
  let header ← headerJob root (if source.isAbsolute then source else root / source)
  let configs := Job.mixArray (← #[root / "lakefile.lean", root / "fuzz.toml",
    root / "Kernel/abi.toml", root / "lean-toolchain", root / "Kernel/lean_bridge.h",
    root / "Kernel/exports.txt"].mapM fun path => inputTextFile path)
  let source ← inputTextFile (root / "Kernel/bitcoinkernel.c")
  let native ← (source.mix (header.mix configs)).mapM fun _ => compileShim cfg
  let some mod ← findModule? `Kernel.Transaction
    | error "Kernel.Transaction is not registered with Lake"
  let generated ← mod.c.fetch
  let signatures ← (generated.zipWith (fun path _ => path) configs).mapM (checkSignatures cfg)
  let mut objectJobs := #[← mod.oExport.fetch]
  let .ok imports _ ← (← mod.transImports.fetch).wait
    | error "Unable to resolve Kernel.Transaction's imports"
  for imported in imports do objectJobs := objectJobs.push (← imported.o.fetch)
  let objects := Job.collectArray objectJobs
  let linkInputs := objects.zipWith (fun objects native => (objects, native)) native
    |>.zipWith (fun pair generated => (pair.1, pair.2, generated)) signatures
    |>.zipWith (fun triple header => (triple.1, triple.2.1, triple.2.2, header)) header
  linkInputs.mapM fun (objects, native, generated, header) =>
    linkKernel cfg objects native generated header

end KernelBuild

/-- Independently implemented kernel library. Runtime environment overrides avoid
baking per-invocation CLI choices into Lake's cached configuration. -/
target kernel pkg : FilePath := do
  let coreSource ← IO.getEnv "BTC_VERIFIED_KERNEL_CORE_SOURCE"
  let compiler ← IO.getEnv "BTC_VERIFIED_KERNEL_CC"
  let deployment ← IO.getEnv "BTC_VERIFIED_KERNEL_MACOS_DEPLOYMENT_TARGET"
  KernelBuild.build pkg coreSource compiler deployment
