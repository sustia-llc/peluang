import Lean

/-!
Re-elaborates one Lean source file as module `<Module>`, with info trees enabled and with the
options given as `name=value` arguments (parsed as the `-D` options of `lean`, a `weak.` prefix
included), and prints tab-separated rows:
* `OPTION`: each option argument, with `set` when its name (without a `weak.` prefix) is a
  registered option after the file's imports, else `dropped`;
* `FINAL`: each constant the file adds to its final environment, with its `collectAxioms`;
* `HIDDEN`: each constant present in a command-context environment saved in a command's info tree
  but absent from the final environment, once per command tree, with the line of the command and
  its `collectAxioms` in that saved environment;
* `EXAMPLES`: the number of `example` declarations in the parsed commands;
* `MSG`: each message of the elaboration, with its severity, line and text (backslash, newline,
  tab and carriage return escaped);
* `DONE` last.

Usage: `lake env lean --run ExampleCheck.lean <file> <Module> [<name>=<value>]...`
-/

open Lean Elab

/-- Every command-context environment saved in an info tree. -/
partial def collectEnvs : InfoTree → Array Environment → Array Environment
  | .context (.commandCtx ci) t, acc => collectEnvs t (acc.push ci.env)
  | .context _ t, acc => collectEnvs t acc
  | .node _ cs, acc => cs.foldl (fun acc c => collectEnvs c acc) acc
  | .hole _, acc => acc

/-- The position of the first syntax node of an info tree. -/
partial def firstPos? : InfoTree → Option String.Pos.Raw
  | .context _ t => firstPos? t
  | .node i _ => i.stx.getPos?
  | .hole _ => none

/-- The number of `declaration` nodes in `stx` whose declaration is an `example`. -/
partial def exampleCount (stx : Syntax) : Nat :=
  if stx.isOfKind ``Parser.Command.declaration then
    if stx[1].isOfKind ``Parser.Command.example then 1 else 0
  else
    stx.getArgs.foldl (fun n a => n + exampleCount a) 0

/-- The constants added to `env` by the module being elaborated. -/
def localNames (env : Environment) : Array Name :=
  env.constants.map₂.foldl (fun acc n _ => acc.push n) #[]

/-- The axioms `collectAxioms` reports for `n` in `env`, comma-separated. -/
def axiomsIn (env : Environment) (n : Name) : IO String := do
  let (axs, _) ← (collectAxioms n : CoreM _).toIO
    { fileName := "<ExampleCheck>", fileMap := default } { env := env }
  return ",".intercalate (axs.toList.map toString)

/-- The options of `-D` arguments `name=value`, unparsed, split at the first `=`. -/
def rawOptions (args : List String) : IO Options :=
  args.foldlM (init := {}) fun opts a =>
    match a.splitOn "=" with
    | k :: v :: rest => pure <| opts.insert k.toName (.ofString ("=".intercalate (v :: rest)))
    | _ => throw <| IO.userError s!"bad option argument {a}"

/-- Prints the rows for the file at `path` elaborated as `mainModule` under the options `raw`. -/
def processFile (path : System.FilePath) (mainModule : Name) (raw : Options) : IO Unit := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header raw messages inputCtx (mainModule := mainModule)
  let decls ← getOptionDecls
  for (name, _) in raw do
    let known := (decls.find? (name.replacePrefix `weak Name.anonymous)).isSome
    IO.println s!"OPTION\t{mainModule}\t{name.toString (escape := false)}\t{if known then "set" else "dropped"}"
  let opts ← Language.Lean.reparseOptions raw
  let cmdState := { Command.mkState env messages opts with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState cmdState
  let finalEnv := s.commandState.env
  let finalNames := localNames finalEnv
  for n in finalNames do
    IO.println s!"FINAL\t{mainModule}\t{n}\t{← axiomsIn finalEnv n}"
  let finalSet : NameSet := finalNames.foldl (·.insert ·) {}
  for tree in s.commandState.infoState.trees.toArray do
    let line := ((firstPos? tree).map (inputCtx.fileMap.toPosition · |>.line)).getD 0
    let mut seen : NameSet := {}
    for e in collectEnvs tree #[] do
      for n in localNames e do
        unless finalSet.contains n || seen.contains n do
          seen := seen.insert n
          IO.println s!"HIDDEN\t{mainModule}\t{line}\t{n}\t{← axiomsIn e n}"
  let examples := s.commands.foldl (fun n c => n + exampleCount c) 0
  IO.println s!"EXAMPLES\t{mainModule}\t{examples}"
  for m in s.commandState.messages.toList do
    let text := (← m.data.toString).trimAscii.toString.replace "\\" "\\\\" |>.replace "\n" "\\n"
      |>.replace "\t" "\\t" |>.replace "\r" "\\r"
    IO.println s!"MSG\t{mainModule}\t{m.severity}\t{m.pos.line}\t{text}"
  IO.println s!"DONE\t{mainModule}"

/-- Entry point: elaborates exactly one file. -/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  match args with
  | file :: mod :: opts =>
    processFile file mod.toName (← rawOptions opts)
    return 0
  | _ =>
    IO.eprintln "usage: ExampleCheck.lean <file> <Module> [<name>=<value>]..."
    return 2
