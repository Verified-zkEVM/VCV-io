/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import Lean.Meta.Sym.Pattern
import Lean.Meta.Sym.Simp.DiscrTree
import VCVio.ProgramLogic.Tactics.Common.Core

/-!
# `@[wpStep]` Registry

Discrimination-tree backed registry for the equational `wp _ _ = …` rewrites used by
the inner driver of `vcstep` / `vcgen` for raw `wp`-shaped goals.

A `@[wpStep]` lemma has shape `wp comp post = …`; the registry indexes it by the
discrimination-tree path of its `comp` argument. Pattern construction goes through
`Lean.Meta.Sym.mkPatternFromDeclWithKey`, so leading universal binders are
internalized as de Bruijn variables and reducibles are unfolded once during
preprocessing. Insertion uses `Sym.insertPattern`, which automatically wildcards
proof / instance argument positions in the discrimination-tree key. Lookup is the
pure `Sym.DiscrTree.getMatch`, run in `MetaM` only to read the persistent
environment and to run a `withReducible whnf` on the goal's `comp` so the head
agrees with the preprocessed pattern.

The dispatch tactic `runWpStepRules`, together with the canonical registrations
for every shipped `wp_*` lemma, lives in
`VCVio.ProgramLogic.Tactics.Common.WpStepDispatch`.
-/

open Lean Elab Meta Lean.Meta

namespace OracleComp.ProgramLogic

/-- A registered `@[wpStep]` lemma: its declaration name plus the preprocessed
`Sym.Pattern` keyed on the LHS computation of the rule. -/
structure WpStepEntry where
  decl : Name
  pattern : Lean.Meta.Sym.Pattern
  deriving Inhabited

instance : BEq WpStepEntry where
  beq a b := a.decl == b.decl

/-- Persistent state for the `@[wpStep]` registry.

* `all` retains insertion order, exposed for diagnostics / tooling.
* `tree` is the discrimination tree consulted by `getRegisteredWpStepEntries`. -/
structure WpStepRegistry where
  all : Array WpStepEntry := #[]
  tree : DiscrTree WpStepEntry := .empty
  deriving Inhabited

private def WpStepRegistry.addToTree (tree : DiscrTree WpStepEntry) (entry : WpStepEntry) :
    DiscrTree WpStepEntry :=
  Lean.Meta.Sym.insertPattern tree entry.pattern entry

initialize wpStepRegistry :
    SimpleScopedEnvExtension WpStepEntry WpStepRegistry ←
  registerSimpleScopedEnvExtension {
    addEntry := fun registry entry =>
      { registry with
          all := registry.all.push entry
          tree := WpStepRegistry.addToTree registry.tree entry }
    initial := {}
  }

/-- Selector for `Sym.mkPatternFromDeclWithKey`: extract the `comp` argument from
the LHS of a `wp comp post = …` equation.

After `Sym.preprocessType`, the abbrev `OracleComp.ProgramLogic.wp` has been
unfolded to `MAlgOrdered.wp`. Both forms are accepted defensively in case a rule
has been written for the more general algebra interface. The `comp` is the
second-to-last explicit argument of the wp head application. -/
private def selectWpStepLhsComp (body : Expr) : MetaM (Expr × Unit) := do
  let body := body.consumeMData
  unless body.isAppOfArity ``Eq 3 do
    throwError m!"@[wpStep] expects an equational target; got:{indentExpr body}"
  let lhs := (body.getArg! 1).consumeMData
  let fn := lhs.getAppFn
  unless fn.isConstOf ``MAlgOrdered.wp || fn.isConstOf ``OracleComp.ProgramLogic.wp do
    throwError m!"@[wpStep] expects an `wp _ _` LHS; got:{indentExpr lhs}"
  let n := lhs.getAppNumArgs
  unless n ≥ 2 do
    throwError m!"@[wpStep] LHS has too few arguments:{indentExpr lhs}"
  let oa := lhs.getArg! (n - 2)
  return (oa, ())

private def buildWpStepEntry (decl : Name) : MetaM WpStepEntry := do
  let (pattern, _) ← Lean.Meta.Sym.mkPatternFromDeclWithKey decl selectWpStepLhsComp
  return { decl, pattern }

initialize registerBuiltinAttribute {
  name := `wpStep
  descr := "Register an equational `wp comp post = …` rule for the runWpStepRules planner."
  add := fun decl _ kind => MetaM.run' do
    let entry ← buildWpStepEntry decl
    wpStepRegistry.add entry kind
}

/-- Retrieve the `@[wpStep]` entries whose LHS pattern matches `oa` in the
discrimination tree.

The goal's `oa` is first instantiated and `withReducible whnf`-normalized so its
head agrees with the registered patterns (which were unfolded once via
`Sym.preprocessType` at registration time). The actual tree traversal is the
pure `Sym.DiscrTree.getMatch`, which already wildcards proof / instance
positions and de Bruijn pattern variables.

Returned candidates are still validated by the dispatch tactic when it tries
each rewrite, so over-approximation here is harmless. -/
def getRegisteredWpStepEntries (oa : Expr) : MetaM (Array WpStepEntry) := do
  let oa ← instantiateMVars oa
  let oa ← withReducible <| whnf oa
  let registry := wpStepRegistry.getState (← getEnv)
  return Lean.Meta.Sym.getMatch registry.tree oa

end OracleComp.ProgramLogic
