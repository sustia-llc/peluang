import Lean

/-!
Imports the modules named on the command line at the private olean level and, for every loaded
module whose name has the given prefix, prints one `MODULE` row, one `CONST` row per entry of
`constNames`, one `EXTRA` row per entry of `extraConstNames` and one `ENTRIES` row per environment
extension with a non-empty entry array, then a final `DONE` row. Rows are tab-separated.

Usage: `lake env lean --run ImportCheck.lean <Prefix> <Module>...`
-/

open Lean

/-- Prints the rows for every loaded module under `pre` in the environment importing `mods`. -/
def report (pre : Name) (mods : Array Name) : IO Unit := do
  let env ← importModules (mods.map fun m => { module := m }) {}
  let names := env.header.moduleNames
  for h : i in [:names.size] do
    let m := names[i]
    if pre.isPrefixOf m then
      let some d := env.header.moduleData[i]? | throw <| IO.userError s!"no module data for {m}"
      IO.println s!"MODULE\t{m}"
      for n in d.constNames do
        IO.println s!"CONST\t{m}\t{n}"
      for n in d.extraConstNames do
        IO.println s!"EXTRA\t{m}\t{n}"
      for (ext, es) in d.entries do
        if es.size > 0 then
          IO.println s!"ENTRIES\t{m}\t{ext}\t{es.size}"
  IO.println "DONE"

/-- Entry point: the first argument is the module prefix, the rest are the modules to import. -/
def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | pre :: mods@(_ :: _) =>
    report pre.toName (mods.toArray.map String.toName)
    return 0
  | _ =>
    IO.eprintln "usage: ImportCheck.lean <Prefix> <Module>..."
    return 2
