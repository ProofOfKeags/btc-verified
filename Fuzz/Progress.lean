import Lean

/-!
  # Readable libFuzzer progress

  Translate libFuzzer's compact progress and final statistics without changing
  their meaning. Missing or unfamiliar fields remain absent; raw subprocess
  logs remain the harness's responsibility. These counters describe executions
  and coverage feedback, not unique transactions or a coverage percentage.
-/

namespace Conformance

private def progressTokens (line : String) : List String :=
  ((line.split Char.isWhitespace).toList.map (·.toString)).filter (!·.isEmpty)

private def progressField (tokens : List String) (name : String) : Option String :=
  ((tokens.dropWhile (· != name)).drop 1).head?

private def progressNumber (tokens : List String) (name : String) : Option Nat :=
  (progressField tokens name).bind String.toNat?

private def formatCorpusSize (size : String) : Option String := do
  let unit ← ["Kb", "KB", "Mb", "MB", "b", "B"].find? (fun unit => size.endsWith unit)
  let count ← (size.dropEnd unit.length).toString.toNat?
  return s!"{count}{unit}"

private def formatCorpus (value : String) : Option String := do
  match value.splitOn "/" with
  | [count] => return s!"corpus: {← count.toNat?} inputs"
  | [count, size] => return s!"corpus: {← count.toNat?} inputs / {← formatCorpusSize size}"
  | _ => none

private def formatMemory (value : String) : Option String := do
  unless value.endsWith "Mb" || value.endsWith "MB" do none
  let megabytes ← (value.dropEnd 2).toString.toNat?
  return s!"peak memory: {megabytes} MB"

/-- Translate one recognized libFuzzer event into execution progress and the
available coverage, corpus, speed, and memory statistics. The percentage is
progress toward the requested execution count, never a coverage percentage.
Unknown lines return `none`; missing or malformed optional fields are omitted.
A zero target omits the denominator and percentage. -/
def formatProgress (target : Nat) (line : String) : Option String := do
  let countToken :: event :: fields := progressTokens line | none
  let count ← ((countToken.dropPrefix? "#").map (·.toString)).bind String.toNat?
  unless ["READ", "INITED", "NEW", "REDUCE", "pulse", "DONE", "RELOAD"].contains event do none
  let progress := if target == 0 then s!"{count} executions"
    else s!"{count} / {target} executions ({count * 100 / target}%)"
  let statistics := [
    (progressNumber fields "cov:").map (fun n => s!"coverage blocks/edges: {n}"),
    (progressNumber fields "ft:").map (fun n => s!"features: {n}"),
    (progressField fields "corp:").bind formatCorpus,
    (progressNumber fields "exec/s:").map (fun n => s!"speed: {n}/s"),
    (progressField fields "rss:").bind formatMemory].filterMap id
  return String.intercalate "; " (progress :: statistics)

private def formatFinalStat (line : String) : Option String := do
  let [name, value] := progressTokens line | none
  let count ← value.toNat?
  match name with
  | "stat::number_of_executed_units:" => some s!"Fuzz executions: {count}"
  | "stat::average_exec_per_sec:" => some s!"Average speed: {count} executions/s"
  | "stat::new_units_added:" => some s!"New corpus additions: {count}"
  | "stat::peak_rss_mb:" => some s!"Peak memory: {count} MB"
  | _ => none

/-- Translate available libFuzzer final statistics from complete stderr into
readable lines. Corpus additions count discoveries during the run and can
exceed the final retained corpus size; executed inputs need not be unique.
Unrecognized and malformed lines are omitted without inventing zero values. -/
def formatFinalStats (output : String) : Array String :=
  ((output.splitOn "\n").filterMap formatFinalStat).toArray

end Conformance
