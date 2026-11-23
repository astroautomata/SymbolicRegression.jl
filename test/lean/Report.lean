import SymReg
import SymReg.Registry
import SymReg.Registry.Generality

/-! Print the registry as tab-separated rows (the format of the DynamicExpressions
formalization's `registry.tsv`): id, status, kind, number of universally quantified data
variables, Julia file, statement, preconditions. Run with `lake env lean -M8000 Report.lean`. -/

open Lean Meta

#eval show MetaM Unit from do
  for e in SymReg.Registry.all do
    let status := match e.status with
      | .todo => "todo" | .stuck => "stuck" | .proven => "proven" | .refuted => "refuted"
    let clean (s : String) := (s.replace "\t" " ").replace "\n" " "
    let n ← SymReg.Registry.countForallData 6 (mkConst e.prop)
    let kind := if SymReg.Registry.staticFacts.contains e.id then "static" else "general"
    IO.println s!"{e.id}\t{status}\t{kind}\t{n}\t{e.juliaFile}\t{clean e.statement}\t{clean e.preconditions}"
