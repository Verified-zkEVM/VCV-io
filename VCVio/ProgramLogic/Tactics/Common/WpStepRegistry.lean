/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import Lean.Meta.Sym.Pattern
import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Elab.Tactic.Do.Attr
import VCVio.ProgramLogic.Tactics.Common.Core

/-!
# `@[wpStep]` Registry

Discrimination-tree backed registry for the equational `wp comp post = …`
rewrites used by the inner driver of `vcstep` / `vcgen` for raw `wp`-shaped
goals.

Each `@[wpStep]` rule is compiled once, at attribute-registration time, into
a `Sym.Pattern` keyed on just the `comp` argument of the LHS
(`Sym.mkPatternFromDeclWithKey`). That pattern lives in a `Sym.DiscrTree` so
a goal `wp oa post` can be answered by normalizing `oa` and querying the
tree: the handful of candidate rules that come back are fed to the dispatch
tactic which tries `rw` / `simp only` in the `TacticM` layer.

We deliberately do *not* pre-compile a `Sym.Simp.Theorem` bundle here: that
bundle is only needed by a future `SymM`-based rewrite loop (see the
deferred `mvcgen'` bridge notes in `docs/agents/program-logic.md`), and
eagerly computing one per registered rule both bloats oleans and drags
several `Sym.Simp.*` modules into the import closure of every downstream
tactic consumer. The dispatch tactic today works off the comp-keyed tree
alone. If a `SymM` migration later needs the theorem bundle, it can be
rebuilt on demand from `getAllWpStepEntries` via `Sym.Simp.mkTheoremFromDecl`.

## Entry layout

`WpStepEntry` mirrors the `Lean.Elab.Tactic.Do.SpecAttr.SpecTheorem` layout
where the shapes line up: `proof : SpecProof` captures the origin (global
decl / local hyp / raw proof) and supports a future `SpecTheorem` bridge,
`compPattern : Sym.Pattern` carries the comp-keyed pattern, and
`priority : Nat` mirrors core's default.

The dispatch tactic `runWpStepRules`, together with the canonical
registrations for every shipped `wp_*` lemma, lives in
`VCVio.ProgramLogic.Tactics.Common.WpStepDispatch`.

## Future-proofing note

`Lean.Meta.Sym.Pattern` and `Lean.Meta.Sym.Simp.DiscrTree` are under active
development upstream. If a toolchain bump breaks the registry, the affected
surface is confined to the selector in `buildWpStepEntry` and the lookup
path in `getRegisteredWpStepEntries`; downstream tactic dispatch works
through `WpStepEntry.declName?` and is insulated from `Sym` API churn. -/

open Lean Elab Meta Lean.Meta
open Lean.Elab.Tactic.Do.SpecAttr (SpecProof)

namespace OracleComp.ProgramLogic

/-- A registered `@[wpStep]` lemma.

Layout mirrors `Lean.Elab.Tactic.Do.SpecAttr.SpecTheorem` as much as the
VCVio-specific shape (equational `wp` rewrites rather than Hoare triples)
allows. We store only the comp-keyed `Sym.Pattern` and an origin marker;
the theorem's full LHS pattern is reconstructible on demand via
`Sym.Simp.mkTheoremFromDecl` for any future `SymM` rewrite path. -/
structure WpStepEntry where
  /-- Origin of the proof; currently always `.global declName` for
  attribute-registered rules, but kept as a `SpecProof` for future local
  hypothesis support and core interop. -/
  proof : SpecProof
  /-- Sym-level pattern keyed on the `comp` argument of the LHS.
  This is the key `runWpStepRules` dispatch uses, which indexes goals by
  their `wp`-argument. -/
  compPattern : Lean.Meta.Sym.Pattern
  /-- User-supplied priority, matching core's convention. -/
  priority : Nat := eval_prio default
  deriving Inhabited

instance : BEq WpStepEntry where
  beq a b := a.proof == b.proof

/-- Global declaration name of a `@[wpStep]` entry, if any. -/
def WpStepEntry.declName? (entry : WpStepEntry) : Option Name :=
  match entry.proof with
  | .global n => some n
  | _ => none

/-- Extract the global declaration name, assuming the entry was registered
via `@[wpStep]` on a global theorem. Returns `Name.anonymous` for non-global
proofs (safe: such entries are not produced today). -/
def WpStepEntry.theoremName! (entry : WpStepEntry) : Name :=
  entry.declName?.getD Name.anonymous

/-- Persistent state for the `@[wpStep]` registry.

* `all` retains insertion order, exposed for diagnostics / tooling.
* `compTree` is the comp-keyed discrimination tree consulted by the
  current `runWpStepRules` dispatch. -/
structure WpStepRegistry where
  all : Array WpStepEntry := #[]
  compTree : DiscrTree WpStepEntry := .empty

instance : Inhabited WpStepRegistry := ⟨{}⟩

private def WpStepRegistry.addToCompTree
    (tree : DiscrTree WpStepEntry) (entry : WpStepEntry) :
    DiscrTree WpStepEntry :=
  Lean.Meta.Sym.insertPattern tree entry.compPattern entry

initialize wpStepRegistry :
    SimpleScopedEnvExtension WpStepEntry WpStepRegistry ←
  registerSimpleScopedEnvExtension {
    addEntry := fun registry entry =>
      { registry with
          all := registry.all.push entry
          compTree := WpStepRegistry.addToCompTree registry.compTree entry }
    initial := {}
  }

/-- Selector for `Sym.mkPatternFromDeclWithKey`: extract the `comp` argument
from the LHS of a `wp comp post = …` equation.

After `Sym.preprocessType`, the abbrev `OracleComp.ProgramLogic.wp` has been
unfolded to either `MAlgOrdered.wp` (legacy structural form) or
`Std.Do'.wp _ _ Order.bot` (Loom2-routed form, the canonical post-cutover
shape). All three heads are accepted; the `comp` argument is positionally:
* `MAlgOrdered.wp m l … oa post` → 2nd-to-last explicit argument.
* `OracleComp.ProgramLogic.wp ι spec … oa post` → 2nd-to-last explicit argument.
* `Std.Do'.wp m Pred EPred α … oa post epost` → 3rd-to-last explicit argument. -/
private def selectWpStepLhsComp (body : Expr) : MetaM (Expr × Unit) := do
  let body := body.consumeMData
  unless body.isAppOfArity ``Eq 3 do
    throwError m!"@[wpStep] expects an equational target; got:{indentExpr body}"
  let lhs := (body.getArg! 1).consumeMData
  let fn := lhs.getAppFn
  let n := lhs.getAppNumArgs
  if fn.isConstOf ``Std.Do'.wp then
    unless n ≥ 3 do
      throwError m!"@[wpStep] `Std.Do'.wp` LHS has too few arguments:{indentExpr lhs}"
    return (lhs.getArg! (n - 3), ())
  unless fn.isConstOf ``MAlgOrdered.wp || fn.isConstOf ``OracleComp.ProgramLogic.wp do
    throwError m!"@[wpStep] expects an `wp _ _` LHS; got:{indentExpr lhs}"
  unless n ≥ 2 do
    throwError m!"@[wpStep] LHS has too few arguments:{indentExpr lhs}"
  let oa := lhs.getArg! (n - 2)
  return (oa, ())

/-- Construct a registry entry from a theorem declaration. Runs the
`Sym.Pattern` pipeline once, keyed on the `comp` argument. -/
private def buildWpStepEntry (decl : Name) (priority : Nat) : MetaM WpStepEntry := do
  let (compPattern, _) ← Lean.Meta.Sym.mkPatternFromDeclWithKey decl selectWpStepLhsComp
  return { proof := .global decl, compPattern, priority }

initialize registerBuiltinAttribute {
  name := `wpStep
  descr := "Register an equational `wp comp post = …` rule for the runWpStepRules planner."
  add := fun decl stx kind => MetaM.run' do
    let prio ← getAttrParamOptPrio stx[1]
    let entry ← buildWpStepEntry decl prio
    wpStepRegistry.add entry kind
}

/-- Retrieve all registered `@[wpStep]` entries in insertion order. -/
def getAllWpStepEntries : CoreM (Array WpStepEntry) := do
  return (wpStepRegistry.getState (← getEnv)).all

/-- Retrieve the `@[wpStep]` entries whose `comp` pattern matches `oa`.

The goal's `oa` is first instantiated and `withReducible whnf`-normalized
so its head agrees with the registered patterns (which were unfolded once
via `Sym.preprocessType` at registration time). The actual tree traversal
is the pure `Sym.DiscrTree.getMatch`, which already wildcards proof /
instance positions and de Bruijn pattern variables.

Returned candidates are still validated by the dispatch tactic when it
tries each rewrite, so over-approximation here is harmless. -/
def getRegisteredWpStepEntries (oa : Expr) : MetaM (Array WpStepEntry) := do
  let oa ← instantiateMVars oa
  let oa ← withReducible <| whnf oa
  let registry := wpStepRegistry.getState (← getEnv)
  return Lean.Meta.Sym.getMatch registry.compTree oa

end OracleComp.ProgramLogic
