import Kernel.Tools.Symbols
import Kernel.Tools.Options

/-!
  # Kernel tooling regression tests

  These deterministic, pure checks cover malformed inputs and negative audit
  controls. They neither load nor execute a kernel library or fuzz harness.
-/

namespace KernelToolsTests

open Kernel.Tools

#guard (Options.parse []).toOption == some {}
#guard (Options.parse ["--test"]).toOption == some { test := true }
#guard !(Options.parse ["--unknown"]).isOk
#guard !(Options.parse ["--cc"]).isOk
#guard !(Options.parse ["--cc="]).isOk
#guard !(Options.parse ["--cc", "--test"]).isOk
#guard (Options.parse ["--cc=/compiler path/clang", "--test"]).toOption ==
  some { compiler := some "/compiler path/clang", test := true }
private def optionsWithSpaces : Options := {
  coreSource := some "/a path/core"
  compiler := some "/compiler path/clang"
  macosDeploymentTarget := some "14.0" }

#guard Options.lakeArgs ==
  #["build", "kernel", "KernelTests", "KernelToolsTests"]
#guard optionsWithSpaces.buildEnvironment ==
  #[("BTC_VERIFIED_KERNEL_CORE_SOURCE", some "/a path/core"),
    ("BTC_VERIFIED_KERNEL_CC", some "/compiler path/clang"),
    ("BTC_VERIFIED_KERNEL_MACOS_DEPLOYMENT_TARGET", some "14.0")]
#guard ({} : Options).buildEnvironment.isEmpty

#guard (readExpectedText "# comment\n btck_second # supported\n\nbtck_first\n").toOption ==
  some #["btck_second", "btck_first"]
#guard !(readExpectedText "# only a comment").isOk
#guard !(readExpectedText "btck_").isOk
#guard !(readExpectedText "btck_bad-name").isOk
#guard !(readExpectedText "btck_é").isOk
#guard !(readExpectedText "btck_first\nbtck_first").isOk

private def header := "#define BITCOINKERNEL_API __attribute__((visibility(\"default\")))\n" ++
  "BITCOINKERNEL_API void btck_second(\n const void* arg) BITCOINKERNEL_ARG_NONNULL(1);\n" ++
  "BITCOINKERNEL_API int btck_first();\n"

#guard (headerSymbols header).toOption == some #["btck_first", "btck_second"]
#guard !(headerSymbols "not a header").isOk
#guard !(headerSymbols "BITCOINKERNEL_API void btck_bad(").isOk
#guard !(headerSymbols "BITCOINKERNEL_API void btck_bad(;\n").isOk
#guard !(headerSymbols "BITCOINKERNEL_API void btck_bad());\n").isOk
#guard !(headerSymbols "BITCOINKERNEL_API void btck_one() btck_two();").isOk
#guard !(headerSymbols "BITCOINKERNEL_API int btck_not_a_function;").isOk
#guard !(headerSymbols
  "BITCOINKERNEL_API int btck_first();\nBITCOINKERNEL_API int btck_first();").isOk
#guard !(headerSymbols "BITCOINKERNEL_API void btck_bad(\nBITCOINKERNEL_API void btck_next();").isOk
#guard (headerSymbols "BITCOINKERNEL_API int btck_first (void);").toOption == some #["btck_first"]

#guard normalizeExports true "000123 T _btck_first\n000124 T _btck_second\nfoo.a:\n" ==
  #["btck_first", "btck_second"]
#guard normalizeExports false
  "000123 T btck_first@@BASE\n000124 T btck_first\n000125 T other$symbol\n" ==
  #["btck_first", "other$symbol"]
#guard normalizeExports true "000123 T __private\n000124 T _btck_first\n" ==
  #["_private", "btck_first"]

private def valid := compareSymbols #["btck_second", "btck_first"]
  #["btck_first"] #["btck_first"] (some 2)

#guard valid.passed
#guard valid.unsupportedCanonical == #["btck_second"]
#guard valid.missingFromLibrary == #["btck_second"]
#guard valid.missingExpected.isEmpty
#guard !(compareSymbols #["btck_first"] #["btck_first"] #[] (some 1)).passed
#guard (compareSymbols #["btck_first"] #["btck_first"] #[] (some 1)).missingExpected ==
  #["btck_first"]
#guard !(compareSymbols #["btck_first"] #["btck_first"] #["btck_first", "private"] (some 1)).passed
#guard (compareSymbols #["btck_first"] #["btck_bad"] #["btck_bad"] none).expectedNotInHeader ==
  #["btck_bad"]
#guard !(compareSymbols #["btck_first"] #["btck_first"] #["btck_first"] (some 136)).passed
#guard (compareSymbols #["btck_first"] #["btck_first"] #["btck_first"] none).passed
#guard (valid.toJson "header.h" "hash" "library.so" "exports.txt" #["nm"]
  |>.getObjValAs? String "status").toOption == some "pass"
#guard (symbolReportMarkdown <|
  valid.toJson "header.h" "hash" "library.so" "exports.txt" #["nm"]).isOk

end KernelToolsTests
