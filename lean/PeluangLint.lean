/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.Parser.Module
public import Mathlib.Init

/-!
# PeluangTest linter

Two command linters, active in every `PeluangTest` module (`PeluangTest` or `PeluangTest.*`) that
imports this module:

* Check A (`exampleAxiomsLinter`): for every `commandCtx` environment in the command's info trees,
  each constant of the current module that is absent from the post-command environment is an error
  if it depends on an axiom outside `allowedAxioms`, and an error if its name, without a private
  prefix, has no `_example` component.
* Check B (a stateful linter): a command after which the current module holds a constant
  (`env.constants.map₂`) that it did not hold before the command is an error.

With `linter.peluangTest.verbose` set, Check A logs one info message per inspected hidden constant.

In every `PeluangTest` module that imports this module, `#guard_msgs` and `#guard_panic` are errors
unless the module is in the plant list `plants`.

The command `#peluang_test_audit` checks the `.lean` files of the `PeluangTest` library, the module
data of the imported `PeluangTest` modules, and the commands of the file that runs it.
-/

meta section

open Lean Elab Command Linter

namespace Peluang.Linter

/-- Logs one info message per hidden constant that Check A inspects. -/
public register_option linter.peluangTest.verbose : Bool := {
  defValue := false
  descr := "log one info message per hidden constant inspected by the PeluangTest linter"
}

/-- The axioms an inspected constant may depend on: the elements of `allowedAxioms.ordered`. -/
public def allowedAxioms : NameSet :=
  ordered.foldl (·.insert ·) {}
where
  /-- The allowed axioms, in the order that `allowedAxiomsText` prints. -/
  ordered : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `allowedAxioms.ordered` as `[a, b, c]`. -/
def allowedAxiomsText : String :=
  "[" ++ ", ".intercalate (allowedAxioms.ordered.map (·.toString)) ++ "]"

/-- Pushes onto `acc` the environment of every `commandCtx` node of `t`. -/
partial def ctxEnvs : InfoTree → Array Environment → Array Environment
  | .context (.commandCtx ci) t, acc => ctxEnvs t (acc.push ci.env)
  | .context _ t, acc => ctxEnvs t acc
  | .node _ cs, acc => cs.foldl (fun acc c => ctxEnvs c acc) acc
  | .hole _, acc => acc

/-- The axioms `n` depends on, computed in the environment `env`. -/
def axiomsIn (env : Environment) (n : Name) : CommandElabM (Array Name) :=
  withoutModifyingEnv do
    setEnv env
    collectAxioms n

/-- Whether `n`, without a private prefix, has a component `_example`. -/
def hasExampleComponent (n : Name) : Bool :=
  (privateToUserName n).components.contains `_example

/-- Whether the current module is `PeluangTest` or `PeluangTest.*`. -/
def inTestLibrary : CommandElabM Bool :=
  return (← getEnv).header.mainModule.getRoot == `PeluangTest

/-- Check A, in every `PeluangTest` module that imports this module: every constant of the
current module that is present in an info-tree command-context environment but absent from the
post-command environment depends only on axioms in `allowedAxioms`, and has an `_example` name
component. -/
def exampleAxiomsLinter : Linter where run stx := do
  unless ← inTestLibrary do return
  let verbose := getLinterValue linter.peluangTest.verbose (← getLinterOptions)
  let post ← getEnv
  let mut seen : NameSet := {}
  for tree in (← getInfoTrees) do
    for env in ctxEnvs tree #[] do
      for (n, _) in env.constants.map₂ do
        if post.contains n || seen.contains n then continue
        seen := seen.insert n
        let axs ← axiomsIn env n
        if verbose then
          logInfoAt stx m!"peluangTest: hidden constant {n} axioms {axs}"
        unless hasExampleComponent n do
          logErrorAt stx m!"peluangTest: hidden constant {n} has no `_example` name component"
        let bad := axs.filter (!allowedAxioms.contains ·)
        unless bad.isEmpty do
          logErrorAt stx m!"peluangTest: hidden constant {n} depends on axioms outside \
            {allowedAxiomsText}: {bad}"

initialize addLinter exampleAxiomsLinter

/-- Check B, in every `PeluangTest` module that imports this module: the `post` phase of a
stateful linter whose state is the set of constants of the current module after the previous
command; a constant not in that set is an error. -/
def newConstantsPost (stx : Syntax) (prev : NameSet) (_ : Option Unit) (_ : PrevStateFn)
    (_ : PreStateFn) : CommandElabM NameSet := do
  unless ← inTestLibrary do return prev
  let mut cur : NameSet := {}
  let mut added : Array Name := #[]
  for (n, _) in (← getEnv).constants.map₂ do
    cur := cur.insert n
    unless prev.contains n do added := added.push n
  unless added.isEmpty do
    logErrorAt stx m!"peluangTest: the command adds constants to the module: {added}"
  return cur

initialize
  discard <| registerStatefulLinter (σ := NameSet) (τ := Unit) {} (post := newConstantsPost)

/-- The linter module that every `PeluangTest` module imports directly. -/
def linterModule : Name := `PeluangLint

public section

/-- `#peluang_test_audit` runs `audit` in the environment of the current file. -/
syntax (name := peluangTestAudit) "#peluang_test_audit" : command

end

/-- The extensions in which a `PeluangTest` module may hold entries. -/
def allowedExtensions : NameSet :=
  ({} : NameSet) |>.insert `Lean.moduleDocExt |>.insert `Lean.modPkgExt
    |>.insert `Lean.extraModUses |>.insert `Lean.deprecatedModuleExt

/-- A plant module, the constant it holds (if any), and the extension entries it adds:
extension name without a private prefix, and entry count. -/
structure Plant where
  /-- The plant module. -/
  module : Name
  /-- The one constant the plant module holds, if any. -/
  const : Option Name := none
  /-- The extensions in which the plant module holds entries, each with its entry count. -/
  entries : List (Name × Nat) := []

/-- The plants: the axiom plant, and the declaration plants in `module` form and plain form.
Only these modules may run `#guard_msgs` and `#guard_panic`. -/
def plants : List Plant := [
  { module := `PeluangTest.Plant.Axiom },
  { module := `PeluangTest.Plant.ModuleTheorem
    const := `PeluangTest.Plant.moduleTheorem
    entries := [(`Lean.declRangeExt, 1), (`Lean.namespacesExt, 2),
      (`Lean.exportedAxiomsExt, 1), (`Lean.privateConstKindsExt, 1)] },
  { module := `PeluangTest.Plant.PlainTheorem
    const := `PeluangTest.Plant.plainTheorem
    entries := [(`Lean.declRangeExt, 1), (`Lean.namespacesExt, 2),
      (`Lean.exportedAxiomsExt, 1)] }]

/-- Whether `m` is a module of `plants`. -/
def isPlant (m : Name) : Bool :=
  plants.any (·.module == m)

/-- The module name of the source file `p`, relative to the source root `root`. -/
def moduleOfPath (root p : System.FilePath) : Option Name := do
  let rel ← (p.toString.dropPrefix? (root.toString ++ "/")).map (·.toString)
  guard (rel.endsWith ".lean")
  let parts := (System.FilePath.mk rel).withExtension "" |>.components
  return parts.foldl Name.str .anonymous

/-- The commands of the source file `path` after its header up to the end of input, `#exit`
included, parsed with Lean's parser in `env`, and the parser messages. -/
def parseCommands (env : Environment) (path : System.FilePath) :
    IO (Parser.InputContext × Array Syntax × MessageLog) := do
  let ictx := Parser.mkInputContext (← IO.FS.readFile path) path.toString
  let (_, st, msgs) ← Parser.parseHeader ictx
  let mut st := st
  let mut msgs := msgs
  let mut cmds : Array Syntax := #[]
  repeat
    let (cmd, st', msgs') := Parser.parseCommand ictx { env, options := {} } st msgs
    st := st'
    msgs := msgs'
    if cmd.isOfKind ``Lean.Parser.Command.eoi then break
    cmds := cmds.push cmd
  return (ictx, cmds, msgs)

/-- The audit: every `.lean` file of the `PeluangTest` library is a loaded module; every loaded
`PeluangTest` module imports the linter module directly, holds no constant and no extension
entry outside `allowedExtensions`, except that a module of `plants` holds exactly its
constant and its listed entries; every `.lean` file under `PeluangTest/Plant/` is a module of
`plants`, and every module of `plants` is imported; the running file imports the linter module,
parses without a parser message, and holds, after its header, only module docstrings and
exactly one `#peluang_test_audit` command. Each violation is an error; one info message states
the number of files and of audited modules. -/
def audit (stx : Syntax) : CommandElabM Unit := do
  let env ← getEnv
  let main := env.header.mainModule
  let root := main.getRoot
  unless env.header.imports.any (·.module == linterModule) do
    logErrorAt stx m!"peluangTest audit: {main} does not import {linterModule}"
  let file ← IO.FS.realPath (← getFileName)
  let some srcRoot := (List.range main.components.length).foldlM
      (fun (p : System.FilePath) _ => p.parent) file
    | throwErrorAt stx m!"peluangTest audit: no source root for {file} and module {main}"
  let dir := srcRoot / root.toString
  let files := (← dir.walkDir).filter (·.extension == some "lean") |>.push (dir.addExtension "lean")
  let plantDir := (dir / "Plant").toString ++ "/"
  for f in files do
    let some m := moduleOfPath srcRoot f
      | logErrorAt stx m!"peluangTest audit: no module name for {f}"
    if m != main && (env.header.moduleNames.contains m).not then
      logErrorAt stx m!"peluangTest audit: {f} (module {m}) is not imported by {main}"
    if f.toString.startsWith plantDir && !isPlant m then
      logErrorAt stx m!"peluangTest audit: {f} (module {m}) is not a listed plant"
  for p in plants do
    unless env.header.moduleNames.contains p.module do
      logErrorAt stx m!"peluangTest audit: plant {p.module} is not imported by {main}"
  let (ictx, cmds, msgs) ← parseCommands env file
  for msg in msgs.toList do
    logErrorAt stx m!"peluangTest audit: {file}: parse error: {← msg.toString}"
  let mut audits : Nat := 0
  for c in cmds do
    if c.isOfKind ``peluangTestAudit then
      audits := audits + 1
    else unless c.isOfKind ``Lean.Parser.Command.moduleDoc do
      let line := (ictx.fileMap.toPosition (c.getPos?.getD 0)).line
      logErrorAt stx m!"peluangTest audit: {file}:{line}: command {c.getKind} in the audit file"
  unless audits == 1 do
    logErrorAt stx m!"peluangTest audit: {file}: {audits} `#peluang_test_audit` commands, not 1"
  let mut audited : Nat := 0
  for h : i in [:env.header.modules.size] do
    let m := env.header.modules[i].module
    unless root.isPrefixOf m do continue
    audited := audited + 1
    let some d := env.header.moduleData[i]?
      | logErrorAt stx m!"peluangTest audit: no module data for {m}"
    unless d.imports.any (·.module == linterModule) do
      logErrorAt stx m!"peluangTest audit: {m} does not import {linterModule}"
    let plant := plants.find? (·.module == m)
    let plantConst (n : Name) : Bool := plant.any (·.const == some n)
    for n in d.constNames do
      unless plantConst n do
        logErrorAt stx m!"peluangTest audit: {m} defines constant {n}"
    for n in d.extraConstNames do
      unless plantConst n do
        logErrorAt stx m!"peluangTest audit: {m} defines extra constant {n}"
    for (ext, es) in d.entries do
      let e := privateToUserName ext
      let plantEntry := plant.any (·.entries.contains (e, es.size))
      if es.size > 0 && !allowedExtensions.contains e && !plantEntry then
        logErrorAt stx m!"peluangTest audit: {m} adds {es.size} entries to extension {ext}"
    if let some p := plant then
      if let some c := p.const then
        unless d.constNames.contains c do
          logErrorAt stx m!"peluangTest audit: plant {m} does not define {c}"
      for (e, c) in p.entries do
        unless d.entries.any fun (ext, es) => privateToUserName ext == e && es.size == c do
          logErrorAt stx m!"peluangTest audit: plant {m} does not add {c} entries to {e}"
  logInfoAt stx m!"peluangTest audit: {files.size} files, {audited} imported {root} modules"

public section

/-- The elaborator of `#peluang_test_audit`. -/
@[command_elab peluangTestAudit]
def elabPeluangTestAudit : CommandElab := audit

/-- In a `PeluangTest` module that is not in `plants`, an error naming the command `cmd` and the
module; in every other module, defers to the builtin elaborator of `cmd`. -/
def plantOnly (cmd : String) : CommandElab := fun _ => do
  let m := (← getEnv).header.mainModule
  unless (← inTestLibrary) && !isPlant m do throwUnsupportedSyntax
  throwError m!"peluangTest: `{cmd}` in {m}, which is not a listed plant"

/-- In a `PeluangTest` module, `#guard_msgs` runs only in a module of `plants`. -/
@[command_elab Lean.guardMsgsCmd]
def elabGuardMsgsPlantOnly : CommandElab := plantOnly "#guard_msgs"

/-- In a `PeluangTest` module, `#guard_panic` runs only in a module of `plants`. -/
@[command_elab Lean.guardPanicCmd]
def elabGuardPanicPlantOnly : CommandElab := plantOnly "#guard_panic"

end

end Peluang.Linter
