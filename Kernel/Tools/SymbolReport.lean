import Lean.Data.Json

/-!
  # Kernel symbol comparison

  A pure comparison of the authenticated public header, the supported-symbol
  allowlist, and a library's exported names. Unsupported canonical functions
  remain explicitly visible rather than being silently stubbed out.
-/

namespace Kernel.Tools

open Lean

/-- The three independently obtained symbol inventories and required header size. -/
structure SymbolReport where
  /-- Function names in the pinned, authenticated public header. -/
  canonical : Array String
  /-- Public function names the implementation promises to support. -/
  expected : Array String
  /-- All defined dynamic exports observed in the built library. -/
  exported : Array String
  /-- An optional guard against accidentally parsing an incomplete header. -/
  requiredCanonicalCount : Option Nat
  deriving BEq

/-- Compare symbol inventories, sorting them for reproducible reports. -/
def compareSymbols (canonical expected exported : Array String)
    (requiredCanonicalCount : Option Nat := some 136) : SymbolReport :=
  { canonical := canonical.qsort (· < ·)
    expected := expected.qsort (· < ·)
    exported := exported.qsort (· < ·)
    requiredCanonicalCount }

/-- Promised exports absent from the actual library. -/
def SymbolReport.missingExpected (report : SymbolReport) : Array String :=
  report.expected.filter (!report.exported.contains ·)

/-- Actual exports outside the supported-symbol allowlist. -/
def SymbolReport.unexpectedExports (report : SymbolReport) : Array String :=
  report.exported.filter (!report.expected.contains ·)

/-- Promised exports that do not exist in the canonical C API. -/
def SymbolReport.expectedNotInHeader (report : SymbolReport) : Array String :=
  report.expected.filter (!report.canonical.contains ·)

/-- Canonical API functions absent from the actual library. -/
def SymbolReport.missingFromLibrary (report : SymbolReport) : Array String :=
  report.canonical.filter (!report.exported.contains ·)

/-- Canonical API functions deliberately excluded from the supported slice. -/
def SymbolReport.unsupportedCanonical (report : SymbolReport) : Array String :=
  report.canonical.filter (!report.expected.contains ·)

/-- Whether the required header count and all promised exports match exactly. -/
def SymbolReport.passed (report : SymbolReport) : Bool :=
  report.missingExpected.isEmpty && report.unexpectedExports.isEmpty &&
    report.expectedNotInHeader.isEmpty &&
    report.requiredCanonicalCount.all (· == report.canonical.size)

/-- Render the established machine-readable schema; file metadata is supplied by IO. -/
def SymbolReport.toJson (report : SymbolReport) (header headerSha256 library expectedPath : String)
    (nmCommand : Array String) : Json :=
  Json.mkObj [
    ("schema_version", Lean.toJson (1 : Nat)),
    ("status", Lean.toJson (if report.passed then "pass" else "fail")),
    ("header", Lean.toJson header),
    ("header_sha256", Lean.toJson headerSha256),
    ("library", Lean.toJson library),
    ("expected_allowlist", Lean.toJson expectedPath),
    ("nm_command", Lean.toJson nmCommand),
    ("required_canonical_symbol_count", Lean.toJson report.requiredCanonicalCount),
    ("canonical_symbol_count", Lean.toJson report.canonical.size),
    ("expected_symbol_count", Lean.toJson report.expected.size),
    ("exported_symbol_count", Lean.toJson report.exported.size),
    ("canonical_symbols", Lean.toJson report.canonical),
    ("expected_symbols", Lean.toJson report.expected),
    ("exported_symbols", Lean.toJson report.exported),
    ("missing_expected", Lean.toJson report.missingExpected),
    ("unexpected_exports", Lean.toJson report.unexpectedExports),
    ("expected_not_in_header", Lean.toJson report.expectedNotInHeader),
    ("missing_from_library", Lean.toJson report.missingFromLibrary),
    ("unsupported_canonical", Lean.toJson report.unsupportedCanonical)]

/-- Render a validated symbol-report JSON object as a human-readable artifact. -/
def symbolReportMarkdown (report : Json) : Except String String := do
  let status ← report.getObjValAs? String "status"
  let canonicalCount ← report.getObjValAs? Nat "canonical_symbol_count"
  let expectedCount ← report.getObjValAs? Nat "expected_symbol_count"
  let exportedCount ← report.getObjValAs? Nat "exported_symbol_count"
  let hash ← report.getObjValAs? String "header_sha256"
  let heading := ["# Kernel ABI symbol audit", "", s!"Status: **{status.toUpper}**", "",
    s!"- Canonical header functions: {canonicalCount}",
    s!"- Expected transaction-slice exports: {expectedCount}",
    s!"- Dynamic library exports: {exportedCount}", s!"- Header SHA-256: `{hash}`"]
  let sections := [
    ("Missing expected exports", "missing_expected"),
    ("Unexpected exports", "unexpected_exports"),
    ("Expected names absent from the canonical header", "expected_not_in_header"),
    ("Canonical functions intentionally unsupported", "unsupported_canonical")]
  let rendered ← sections.mapM fun (title, key) => do
    let values ← report.getObjValAs? (Array String) key
    let body := if values.isEmpty then ["None."] else values.toList.map (s!"- `{·}`")
    pure (["", s!"## {title}", ""] ++ body)
  return String.intercalate "\n" (heading ++ rendered.flatten) ++ "\n"

end Kernel.Tools
