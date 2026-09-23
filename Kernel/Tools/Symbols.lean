import Kernel.Tools.SymbolReport

/-!
  # Kernel public-symbol audit

  Parsing and comparison are pure; filesystem reads, `nm`, and report writes are
  confined to the outer boundary. The declaration parser deliberately recognizes
  the pinned header's macro-prefixed C declarations, not arbitrary C syntax.
  The caller must authenticate the header before using it as the ABI contract.
-/

namespace Kernel.Tools

open Lean System

private def trim (text : String) : String := text.trimAscii.toString

private def identifierChar (char : Char) : Bool :=
  char.isAlphanum && char.toNat < 128 || char == '_'

private def publicSymbol (text : String) : Bool :=
  text.startsWith "btck_" && text.length > 5 && text.toList.all identifierChar

private def distinctSorted (values : Array String) : Array String :=
  let distinct := values.foldl
    (fun seen value => if seen.contains value then seen else seen.push value) #[]
  distinct.qsort (· < ·)

/-- Read a nonempty, duplicate-free allowlist, ignoring blank lines and `#` comments. -/
def readExpectedText (text : String) : Except String (Array String) := do
  let symbols ← (text.splitOn "\n").zipIdx.foldlM (init := #[]) fun symbols (raw, index) => do
    let line := trim ((raw.splitOn "#").headD "")
    if line.isEmpty then return symbols
    if !publicSymbol line then
      throw s!"line {index + 1}: invalid exported symbol {line}"
    if symbols.contains line then
      throw s!"line {index + 1}: duplicate exported symbol {line}"
    return symbols.push line
  if symbols.isEmpty then throw "expected-symbol allowlist is empty"
  return symbols

private def declarationStart (line : String) : Bool :=
  line == "BITCOINKERNEL_API" || line.startsWith "BITCOINKERNEL_API " ||
    line.startsWith "BITCOINKERNEL_API\t"

private def functionNames (declaration : String) : Array String :=
  let candidates := (declaration.splitOn "(").dropLast.map fun leading =>
    (((trim leading).splitOn " ").flatMap (·.splitOn "\t")).getLast?.getD ""
  candidates.toArray.filter publicSymbol

private def parseDeclaration (declaration : String) : Except String String := do
  let parts := declaration.splitOn ";"
  if parts.length != 2 || !(trim (parts.getLast?.getD "")).isEmpty then
    throw s!"malformed API declaration: {declaration}"
  -- Parenthesis balance catches truncated parameters/attributes without
  -- pretending to validate all of C's declaration grammar.
  let balance ← declaration.toList.foldlM (init := 0) fun depth char =>
    if char == '(' then pure (depth + 1)
    else if char == ')' then
      if depth == 0 then throw "unbalanced API declaration" else pure (depth - 1)
    else pure depth
  if balance != 0 then throw s!"unbalanced API declaration: {declaration}"
  let names := functionNames declaration
  match names.toList with
  | [name] => return name
  | _ => throw s!"could not identify one function in API declaration: {declaration}"

/-- Extract unique API names; reject empty headers and malformed macro-prefixed declarations. -/
def headerSymbols (text : String) : Except String (Array String) := do
  let (symbols, pending) ← (text.splitOn "\n").foldlM (init := (#[], none))
      fun (symbols, pending) raw => do
    let line := trim raw
    if pending.isSome && declarationStart line then
      throw "unterminated API declaration before next BITCOINKERNEL_API"
    let declaration := match pending with
      | some previous => some (previous ++ " " ++ line)
      | none => if declarationStart line then some line else none
    match declaration with
    | none => return (symbols, none)
    | some current =>
      if !(current.contains ';') then return (symbols, some current)
      let symbol ← parseDeclaration current
      if symbols.contains symbol then throw s!"duplicate API declaration: {symbol}"
      return (symbols.push symbol, none)
  if pending.isSome then throw "unterminated API declaration at end of header"
  if symbols.isEmpty then throw "canonical header contains no API declarations"
  return symbols.qsort (· < ·)

private def exportIdentifier (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
    (first.isAlpha && first.toNat < 128 || first == '_') &&
      rest.all (fun char => identifierChar char || char == '$' || char == '.')

/-- Normalize defined `nm` output, including Darwin prefixes and ELF symbol versions. -/
def normalizeExports (darwin : Bool) (text : String) : Array String :=
  distinctSorted <| (text.splitOn "\n").toArray.filterMap fun line =>
    let fields := ((line.splitOn " ").flatMap (·.splitOn "\t")).filter (!·.isEmpty)
    if fields.length < 2 then none else
      let name := (((fields.getLast?.getD "").splitOn "@").headD "")
      let name := if darwin && name.startsWith "_" then String.ofList name.toList.tail else name
      if exportIdentifier name then some name else none

private def expect (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

/-- Read the inventories and invoke only `nm`; the caller supplies the authenticated header hash. -/
def makeSymbolReport (header library expectedPath : FilePath) (headerSha256 : String)
    (nm : String := "nm") (requiredCanonicalCount : Option Nat := some 136) : IO Json := do
  let canonical ← expect <| headerSymbols (← IO.FS.readFile header)
  let expected ← expect <| readExpectedText (← IO.FS.readFile expectedPath)
  let darwin := System.Platform.isOSX || library.extension == some "dylib"
  let args := if darwin then #["-gU", library.toString]
    else #["-D", "--defined-only", library.toString]
  -- Do not let Lake's runtime search paths redirect an external LLVM nm to
  -- Lean's bundled libLLVM. The tool resolves its own libraries via its rpaths.
  let output ← IO.Process.output {
    cmd := nm
    args := args
    env := #[("DYLD_LIBRARY_PATH", none), ("LD_LIBRARY_PATH", none)] }
  if output.exitCode != 0 then
    throw <| IO.userError s!"symbol audit: {nm} exited {output.exitCode}: {output.stderr}"
  let report := compareSymbols canonical expected (normalizeExports darwin output.stdout)
    requiredCanonicalCount
  return report.toJson (← IO.FS.realPath header).toString headerSha256
    (← IO.FS.realPath library).toString (← IO.FS.realPath expectedPath).toString
    (#[nm] ++ args)

/-- Save deterministic JSON and Markdown audit artifacts, including failed comparisons. -/
def writeSymbolReport (report : Json) (jsonPath markdownPath : FilePath) : IO Unit := do
  let markdown ← expect <| symbolReportMarkdown report
  for path in [jsonPath, markdownPath] do
    if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile jsonPath (report.pretty ++ "\n")
  IO.FS.writeFile markdownPath markdown

end Kernel.Tools
