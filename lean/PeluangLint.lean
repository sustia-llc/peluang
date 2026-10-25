/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public import Mathlib.Init

/-!
# PeluangTest linter

Two command linters, active in every file that imports this module:

* Check A (`exampleAxiomsLinter`): for every `commandCtx` environment in the command's info
  trees, each constant of the current module that is absent from the post-command environment
  is an error if it depends on an axiom outside `{propext, Classical.choice, Quot.sound}`, and an
  error if its name, without a private prefix, has no `_example` component.
* Check B (a stateful linter): a command after which the current module holds a constant
  (`env.constants.map₂`) that it did not hold before the command is an error.

With `linter.peluangTest.verbose` set, Check A logs one info message per inspected hidden
constant.

The command `#peluang_test_audit` checks the `.lean` files of the `PeluangTest` library and the
module data of the imported `PeluangTest` modules.
-/

meta section

open Lean Elab Command Linter

namespace Peluang.Linter

/-- Logs one info message per hidden constant that Check A inspects. -/
public register_option linter.peluangTest.verbose : Bool := {
  defValue := false
  descr := "log one info message per hidden constant inspected by the PeluangTest linter"
}

/-- The axioms an inspected constant may depend on. -/
def allowedAxioms : NameSet :=
  ({} : NameSet) |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound

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

/-- Check A: every constant of the current module that is present in an info-tree
command-context environment but absent from the post-command environment depends only on
`propext`, `Classical.choice` and `Quot.sound`, and has an `_example` name component. -/
def exampleAxiomsLinter : Linter where run stx := do
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
            [propext, Classical.choice, Quot.sound]: {bad}"

initialize addLinter exampleAxiomsLinter

/-- Check B, the `post` phase of a stateful linter whose state is the set of constants of the
current module after the previous command: a constant not in that set is an error. -/
def newConstantsPost (stx : Syntax) (prev : NameSet) (_ : Option Unit) (_ : PrevStateFn)
    (_ : PreStateFn) : CommandElabM NameSet := do
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

/-- The extensions in which a `PeluangTest` module may hold entries. -/
def allowedExtensions : NameSet :=
  ({} : NameSet) |>.insert `Lean.moduleDocExt |>.insert `Lean.modPkgExt
    |>.insert `Lean.extraModUses |>.insert `Lean.deprecatedModuleExt

/-- A declaration plant module, the one constant it holds, and the extension entries it adds:
extension name without a private prefix, and entry count. -/
structure DeclPlant where
  /-- The plant module. -/
  module : Name
  /-- The constant the plant module holds. -/
  const : Name
  /-- The extensions in which the plant module holds entries, each with its entry count. -/
  entries : List (Name × Nat)

/-- The two declaration plants: the `module` form and the plain form. -/
def declPlants : List DeclPlant := [
  { module := `PeluangTest.Plant.ModuleTheorem
    const := `PeluangTest.Plant.moduleTheorem
    entries := [(`Lean.declRangeExt, 1), (`Lean.namespacesExt, 2),
      (`Lean.exportedAxiomsExt, 1), (`Lean.privateConstKindsExt, 1)] },
  { module := `PeluangTest.Plant.PlainTheorem
    const := `PeluangTest.Plant.plainTheorem
    entries := [(`Lean.declRangeExt, 1), (`Lean.namespacesExt, 2),
      (`Lean.exportedAxiomsExt, 1)] }]

/-- The module name of the source file `p`, relative to the source root `root`. -/
def moduleOfPath (root p : System.FilePath) : Option Name := do
  let rel ← (p.toString.dropPrefix? (root.toString ++ "/")).map (·.toString)
  guard (rel.endsWith ".lean")
  let parts := (System.FilePath.mk rel).withExtension "" |>.components
  return parts.foldl Name.str .anonymous

/-- The audit: every `.lean` file of the `PeluangTest` library is a loaded module; every loaded
`PeluangTest` module imports the linter module directly, holds no constant and no extension
entry outside `allowedExtensions`, except that a module of `declPlants` holds exactly its
constant and its listed entries; the running file imports the linter module. Each violation is
an error; one info message states the number of files and of audited modules. -/
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
  for f in files do
    let some m := moduleOfPath srcRoot f
      | logErrorAt stx m!"peluangTest audit: no module name for {f}"
    if m != main && (env.header.moduleNames.contains m).not then
      logErrorAt stx m!"peluangTest audit: {f} (module {m}) is not imported by {main}"
  let mut audited : Nat := 0
  for h : i in [:env.header.modules.size] do
    let m := env.header.modules[i].module
    unless root.isPrefixOf m do continue
    audited := audited + 1
    let some d := env.header.moduleData[i]?
      | logErrorAt stx m!"peluangTest audit: no module data for {m}"
    unless d.imports.any (·.module == linterModule) do
      logErrorAt stx m!"peluangTest audit: {m} does not import {linterModule}"
    let plant := declPlants.find? (·.module == m)
    let plantConst (n : Name) : Bool := plant.any (·.const == n)
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
      unless d.constNames.contains p.const do
        logErrorAt stx m!"peluangTest audit: plant {m} does not define {p.const}"
      for (e, c) in p.entries do
        unless d.entries.any fun (ext, es) => privateToUserName ext == e && es.size == c do
          logErrorAt stx m!"peluangTest audit: plant {m} does not add {c} entries to {e}"
  logInfoAt stx m!"peluangTest audit: {files.size} files, {audited} imported {root} modules"

public section

/-- `#peluang_test_audit` runs `audit` in the environment of the current file. -/
syntax (name := peluangTestAudit) "#peluang_test_audit" : command

/-- The elaborator of `#peluang_test_audit`. -/
@[command_elab peluangTestAudit]
def elabPeluangTestAudit : CommandElab := audit

end

end Peluang.Linter
