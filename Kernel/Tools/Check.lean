import Kernel.Tools.Options
import Kernel.Tools.Symbols
/-!
  # Standalone kernel check runner

  Lake owns the dependency-tracked native build. This executable runs the
  symbol audit and ordinary C clients, recording each completed stage and
  subprocess output. It does not import transaction semantics, build Core,
  or execute the differential harness.
-/

namespace Kernel.Tools

open Lean System

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def writeJson (path : FilePath) (value : Json) : IO Unit := do
  let temporary := path.addExtension "tmp"
  IO.FS.writeFile temporary (value.pretty ++ "\n")
  IO.FS.rename temporary path

private def appendLog (log : FilePath) (text : String) : IO Unit :=
  IO.FS.withFile log .append fun handle => handle.putStr text

private def commandJson (command : String) (args : Array String) : Json :=
  toJson (#[command] ++ args)

private def runLogged (root log : FilePath) (command : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let invocation := (commandJson command args).compress
  IO.println s!"+ {invocation}"
  appendLog log s!"+ {invocation}\n"
  -- Lake injects its own shared-library directories for Lean executables.
  -- External compilers must use their own runtime libraries, not Lean's LLVM.
  let toolEnv := #[("DYLD_LIBRARY_PATH", none), ("LD_LIBRARY_PATH", none)] ++ env
  let result ← IO.Process.output { cmd := command, args, cwd := some root, env := toolEnv }
  appendLog log s!"stdout:\n{result.stdout}\nstderr:\n{result.stderr}\nexit: {result.exitCode}\n"
  unless result.stdout.isEmpty do IO.print result.stdout
  unless result.stderr.isEmpty do (← IO.getStderr).putStr result.stderr
  return result

private def run (root log : FilePath) (command : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO String := do
  let result ← runLogged root log command args env
  require (result.exitCode == 0)
    s!"{command} exited with {result.exitCode}; see {log}"
  return result.stdout.trimAscii.toString

private def field (report : Json) (name : String) : IO String :=
  IO.ofExcept ((report.getObjVal? name).bind Json.getStr?)

private def sha256 (root log path : FilePath) : IO String := do
  let output ← if Platform.isOSX then
    run root log "shasum" #["-a", "256", path.toString]
  else
    run root log "sha256sum" #[path.toString]
  let digest := ((output.splitOn " ").headD "").toLower
  require (digest.length == 64 && digest.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))
    s!"invalid SHA-256 tool output for {path}"
  return digest

private def nativeTests (root artifacts log : FilePath) (metadata : Json)
    (saveTest : Json → IO Unit) : IO Unit := do
  let cc ← field metadata "compiler"
  let deployment := metadata.getObjValD "macos_deployment_target"
  let deploymentFlags ← if deployment.isNull then pure #[] else do
    let value ← IO.ofExcept deployment.getStr?
    pure #[s!"-mmacosx-version-min={value}"]
  let includeDir := artifacts / "include"
  let testDir := artifacts / "tests"
  IO.FS.createDirAll testDir
  let linkFlags := #["-L", artifacts.toString, "-lbitcoinkernel",
    s!"-Wl,-rpath,{artifacts}"]
  let libraryPathVariable := if Platform.isOSX then "DYLD_LIBRARY_PATH" else "LD_LIBRARY_PATH"
  let env := #[(libraryPathVariable, some artifacts.toString)]
  for name in ["threads", "abi"] do
    let source := root / "Kernel/tests" / s!"{name}.c"
    let executable := testDir / name
    let args := #["-std=c11", "-pthread"] ++ deploymentFlags ++
      #["-Wall", "-Wextra", "-I", includeDir.toString, source.toString] ++
      linkFlags ++ #["-o", executable.toString]
    discard <| run root log cc args
    let output ← run root log executable.toString #[] env
    saveTest <| Json.mkObj [
      ("name", toJson name), ("source", toJson source.toString),
      ("executable", toJson executable.toString), ("command", commandJson cc args),
      ("language_standard", toJson "C11"), ("stdout", toJson output),
      ("status", toJson "pass")]
  let source := root / "Kernel/tests/unsupported.c"
  let object := testDir / "unsupported.o"
  let executable := testDir / "unsupported"
  let compileArgs := #["-std=c11"] ++ deploymentFlags ++
    #["-I", includeDir.toString, "-c", source.toString, "-o", object.toString]
  discard <| run root log cc compileArgs
  if ← executable.pathExists then IO.FS.removeFile executable
  let linkArgs := deploymentFlags ++ #[object.toString] ++ linkFlags ++
    #["-o", executable.toString]
  let result ← runLogged root log cc linkArgs
  require (result.exitCode != 0) "unsupported btck_context_create unexpectedly linked"
  let diagnostic := result.stdout ++ result.stderr
  require ((diagnostic.splitOn "btck_context_create").length > 1)
    "negative link failed for an unrelated reason; btck_context_create was not diagnosed"
  saveTest <| Json.mkObj [
    ("name", toJson "unsupported-symbol-negative-link"), ("source", toJson source.toString),
    ("compile_command", commandJson cc compileArgs), ("link_command", commandJson cc linkArgs),
    ("link_exit_code", toJson result.exitCode.toNat), ("diagnostic", toJson diagnostic),
    ("status", toJson "pass")]

/-- Build and audit the kernel, optionally run standalone C tests, and persist pass/fail evidence. -/
def runCheck (args : List String) : IO UInt32 := do
  let options ← match Options.parse args with
    | .ok options => pure options
    | .error error =>
      (← IO.getStderr).putStrLn error
      return 2
  if options.help then
    IO.print Options.usage
    return 0
  let root ← IO.FS.realPath (← IO.Process.getCurrentDir)
  let artifacts := root / ".lake/kernel"
  IO.FS.createDirAll artifacts
  let reportPath := artifacts / "build.json"
  let log := artifacts / "check.log"
  IO.FS.writeFile log ""
  let initial := Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("status", toJson "running"),
    ("command", toJson (#["lake", "exe", "kernel-check"] ++ args.toArray)),
    ("build_environment", toJson options.buildEnvironment),
    ("log", toJson log.toString), ("tests", toJson (#[] : Array Json))]
  let report ← IO.mkRef initial
  let update := fun (changes : Json) => do
    report.modify (·.mergeObj changes)
    writeJson reportPath (← report.get)
  writeJson reportPath initial
  try
    require (← (root / "Kernel/abi.toml").pathExists)
      "run kernel-check from the btc-verified repository root"
    update <| Json.mkObj [("stage", toJson "build")]
    let lake := (← IO.getEnv "LAKE").getD "lake"
    discard <| run root log lake Options.lakeArgs options.buildEnvironment
    let nativePath := artifacts / "native-build.json"
    let native ← IO.ofExcept <| Json.parse (← IO.FS.readFile nativePath)
    require ((← field native "status") == "pass") "native Lake build report is not a pass"
    update <| native.mergeObj (Json.mkObj [
      ("status", toJson "running"), ("stage", toJson "symbols"),
      ("command", initial.getObjValD "command"),
      ("native_build_command", commandJson lake Options.lakeArgs),
      ("native_build_report", toJson nativePath.toString)])
    let header : FilePath := ← field native "canonical_header"
    let library : FilePath := ← field native "output"
    let headerSource ← IO.ofExcept (native.getObjVal? "header_source")
    let digest ← sha256 root log header
    require (digest == (← field headerSource "sha256"))
      "authenticated header changed after the native build"
    let symbols ← makeSymbolReport header library (root / "Kernel/exports.txt") digest options.nm
    writeSymbolReport symbols (artifacts / "symbols.json") (artifacts / "symbols.md")
    update <| Json.mkObj [
      ("symbol_report", toJson (artifacts / "symbols.json").toString),
      ("output_sha256", toJson (← sha256 root log library))]
    require ((← field symbols "status") == "pass")
      "dynamic exports differ from Kernel/exports.txt; see .lake/kernel/symbols.md"
    if options.test then
      update <| Json.mkObj [("stage", toJson "tests")]
      nativeTests root artifacts log native fun test => do
        let tests ← IO.ofExcept (((← report.get).getObjVal? "tests").bind Json.getArr?)
        update <| Json.mkObj [("tests", toJson (tests.push test))]
    update <| Json.mkObj [("status", toJson "pass"), ("stage", toJson "complete")]
    IO.println s!"Kernel check passed; report: {reportPath}"
    return 0
  catch error =>
    let message := error.toString
    appendLog log s!"kernel check failed: {message}\n"
    update <| Json.mkObj [("status", toJson "fail"), ("error", toJson message)]
    (← IO.getStderr).putStrLn s!"kernel check failed: {message}"
    return 1

end Kernel.Tools
