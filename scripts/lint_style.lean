/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lake.CLI.Main
import Lean.Elab.ParseImportsFast
import Batteries.Data.String.Basic
import Mathlib.Tactic.Linter.TextBased
import ImportGraph.Imports.FromSource
import Cli.Basic

/-!
# Text-based style linters

This file defines the `lint-style` executable which runs Mathlib's text-based
style linters over the VCVio libraries. The linters themselves are defined in
`Mathlib/Tactic/Linter/TextBased.lean` (trailing whitespace, Windows line
endings, disallowed unicode, a space before a semicolon, and `Adaptation note`
phrasing), together with the module-name checks `modulesNotUpperCamelCase` and
`modulesOSForbidden`.

The in-build syntax linters (`linter.style.*`, enabled through
`linter.mathlibStandardSet` in `lakefile.lean`) run during `lake build` and are
not repeated here.

Adapted from Mathlib's `scripts/lint-style.lean`, trimmed to the checks relevant
to a project downstream of Mathlib. Invoked as `lake exe lint-style`.
-/

open Cli Lean.Linter Mathlib.Linter.TextBased System.FilePath

/-- The library roots that `lint-style` checks when no modules are given on the
command line: every non-test VCVio library. -/
def defaultLibraryRoots : Array Lean.Name :=
  #[`ToMathlib, `VCVio, `FFI, `LatticeCrypto, `Examples, `VCVioWidgets, `Interop]

/-- Get the root package of the Lake workspace we are running in. -/
def getWorkspaceRoot : IO Lake.Package := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
  let config ← Lake.MonadError.runEIO <|
    Lake.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← Lake.loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  return workspace.root

section LinterSetsElab

open Lean

instance {α : Type} [ToExpr α] : ToExpr (NameMap α) where
  toExpr s := mkApp4 (.const ``Std.TreeMap.ofArray [.zero, .zero])
    (toTypeExpr Name) (toTypeExpr α)
    (toExpr s.toArray)
    (.const ``Lean.Name.quickCmp [])
  toTypeExpr := .const ``LinterSets []

instance : ToExpr LinterSets := inferInstanceAs <| ToExpr (NameMap _)

/-- Return the linter sets defined at this point of elaborating the current file. -/
elab "linter_sets%" : term => do
  return toExpr <| linterSetsExt.getState (← getEnv)

end LinterSetsElab

/-- Convert the options that Lake knows into the option that Lean knows. -/
def toLeanOptions (opts : Lean.LeanOptions) : Lean.Options := Id.run do
  let mut out := Lean.Options.empty
  for ⟨name, value⟩ in opts.values do
    -- Strip off the `weak.` prefix, like Lean does when parsing command line arguments.
    if name.getRoot == `weak then
      out := out.insert (name.replacePrefix `weak Lean.Name.anonymous) value.toDataValue
    else
      out := out.insert name value.toDataValue
  return out

/-- Determine the `Lean.Options` from the Lakefile of the current project.

We have to do this since style linters do not run in the `CoreM`/`CommandElabM` monads,
and so they do not get access to the options in scope. -/
def getLakefileLeanOptions : IO Lean.Options := do
  let root ← getWorkspaceRoot
  -- Some projects declare options in the root package.
  let rootOpts := root.leanOptions
  -- Other projects declare options in the targets; include the default targets too.
  let defaultOpts := root.defaultTargets.flatMap fun target ↦
    if let some lib := root.findLeanLib? target then
      lib.config.leanOptions
    else if let some exe := root.findLeanExe? target then
      exe.config.leanOptions
    else
      #[]
  return toLeanOptions (rootOpts.appendArray defaultOpts)

/-- Implementation of the `lint-style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let opts : LinterOptions := {
    toOptions := ← getLakefileLeanOptions,
    linterSets := linter_sets%,
  }
  let style : ErrorFormat := match args.hasFlag "github" with
    | true => ErrorFormat.github
    | false => ErrorFormat.humanReadable
  let fix := args.hasFlag "fix"
  -- The modules to lint: the command-line arguments, or every VCVio library otherwise.
  let originModules ← match args.variableArgsAs! String with
  | #[] => pure defaultLibraryRoots
  | mods => do
    let mut result := #[]
    for mod in mods do
      let modParse := Lean.ParseImports.moduleIdent mod {}
      match modParse.error? with
      | none => result := result.append <| modParse.imports.map Lean.Import.module
      | some err => throw <| IO.userError s!"could not parse module name {mod}: {err}"
    pure result
  -- Smoke test against accidentally disabling all the linters: require a nonempty module set.
  if originModules.isEmpty then
    throw <| IO.userError "lint-style: no modules to lint."
  -- Gather every module reachable from these library roots, restricted to the same packages.
  let pkgs := originModules.map (·.components.head!)
  Lean.initSearchPath (← Lean.findSysroot)
  let searchPath ← Lean.getSrcSearchPath
  let allModuleNames ← originModules.flatMapM fun mod => do
    let imports ← match ← searchPath.findWithExt "lean" mod with
    | some file => findImportsFromSource file
    | none => throw <| IO.userError s!"could not find module with name {mod}"
    pure <| imports.filter (·.components.head! ∈ pkgs)
  -- Read the `nolints` file, with manual exceptions for the linter.
  -- We pass these to `lintModules` explicitly (rather than letting it read the file)
  -- to avoid cache-invalidation surprises.
  let filename : System.FilePath := ("scripts" / "nolints-style.txt")
  let nolints ← try
    IO.FS.lines filename
  catch _ =>
    IO.eprintln s!"warning: nolints file could not be read; treating as empty: {filename}"
    pure #[]
  let numberErrors := (← lintModules opts nolints allModuleNames style fix)
    + (← modulesNotUpperCamelCase opts allModuleNames).toUInt32
    + (← modulesOSForbidden opts allModuleNames).toUInt32
  -- With `--fix`, return a zero exit code; otherwise cap the exit code at 125 for shell use.
  if args.hasFlag "fix" then
    return 0
  else return min numberErrors 125

/-- Setting up command line options and help text for `lake exe lint-style`. -/
def lintStyle : Cmd := `[Cli|
  «lint-style» VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in the VCVio libraries.
  Print errors about any unexpected style errors to standard output."
  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    fix;        "Automatically fix the style error, if possible"
  ARGS:
    ...modules : String; "Which modules, and their imports, will be linted.\n\
                          If no modules are specified, the linter runs on every VCVio library."
]

/-- The entry point to the `lake exe lint-style` command. -/
def main (args : List String) : IO UInt32 := do lintStyle.validate args
