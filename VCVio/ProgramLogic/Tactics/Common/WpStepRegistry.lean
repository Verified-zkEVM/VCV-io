/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import Lean.Meta.Sym.Pattern
import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Simp.Main
import Lean.Meta.Sym.SymM
import Lean.Elab.Tactic.Do.Attr
import VCVio.ProgramLogic.Tactics.Common.Core

/-!
# `@[wpStep]` Registry

Structural-simplifier backed registry for the equational `wp comp post = …`
rewrites used by the inner driver of `vcstep` / `vcgen` for raw `wp`-shaped
goals.

Each `@[wpStep]` rule is compiled into two aligned artefacts:

* A `Lean.Meta.Sym.Simp.Theorem` produced by `Sym.Simp.mkTheoremFromDecl`.
  The theorem packages the proof expression, a `Sym.Pattern` keyed on the
  *full* `wp comp post` LHS, and the equation's RHS pre-extracted for fast
  substitution. Theorems are collected into a `Sym.Simp.Theorems` bundle so
  downstream code can hand the bundle directly to
  `Sym.Simp.Theorems.rewrite` (the pattern-based rewriter that avoids
  metavariable-heavy `isDefEq` work) without per-rule rewiring.
* A `Sym.DiscrTree` keyed on just the `comp` argument of the LHS, produced
  by `Sym.mkPatternFromDeclWithKey`. This is the index `runWpStepRules`
  consults today: given a goal `wp oa post`, we normalize `oa` and hit the
  tree to pull candidate rules. This shape is what Phases 2-B verified end
  to end and is what the examples exercise.

Both indices are populated from the same rule; the comp-keyed tree drives
the current `TacticM` dispatch (safe, stable, battle-tested) while the
Sym.Simp bundle is the substrate on which later phases can wire a real
`SymM` rewrite loop (`runSymM <| Sym.Simp.Theorems.rewrite …`). That
migration is deferred precisely because `Sym.Simp.Theorems.rewrite` lives
in `SimpM`, and the `SymM → TacticM` proof-application bridge needs a
little more plumbing (see the "Future-proofing note" below).

## Entry layout

`WpStepEntry` mirrors the `Lean.Elab.Tactic.Do.SpecAttr.SpecTheorem`
layout where the shapes line up: `proof : SpecProof` captures the origin
(global decl / local hyp / raw proof), `priority : Nat` carries the
attribute priority, `simpThm : Sym.Simp.Theorem` packages the Sym-side
rewrite data, and `compPattern : Sym.Pattern` carries the comp-keyed
pattern that drives current lookups. For Phase F interop we expose
`declName?` / `theoremName!` helpers.

The dispatch tactic `runWpStepRules`, together with the canonical
registrations for every shipped `wp_*` lemma, lives in
`VCVio.ProgramLogic.Tactics.Common.WpStepDispatch`.

## Future-proofing note

`Lean.Meta.Sym.Simp` is under active development. `Sym.Simp.Theorem`,
`Sym.Simp.Theorems.rewrite`, and the `SymM` / `SimpM` monads may see
minor shape changes between Lean releases. If a toolchain bump breaks the
registry, the affected surface is confined to the `Sym.Simp.mkTheoremFromDecl`
call in `buildWpStepEntry`; the `TacticM` dispatch path (comp-keyed tree)
is independent and will continue to work. -/

open Lean Elab Meta Lean.Meta
open Lean.Elab.Tactic.Do.SpecAttr (SpecProof)

namespace OracleComp.ProgramLogic

/-- A registered `@[wpStep]` lemma.

Layout mirrors `Lean.Elab.Tactic.Do.SpecAttr.SpecTheorem` as much as the
VCVio-specific shape (equational `wp` rewrites rather than Hoare triples)
allows: `proof` reuses `SpecProof`, `simpThm` carries the Sym-side
`{expr, pattern, rhs}` bundle keyed on the full LHS, `compPattern` carries
the comp-keyed pattern that drives current lookups, and `priority` uses
the shared default. -/
structure WpStepEntry where
  /-- Origin of the proof; currently always `.global declName` for
  attribute-registered rules, but kept as a `SpecProof` for future local
  hypothesis support and core interop. -/
  proof : SpecProof
  /-- Compiled Sym simp theorem: theorem expression, pattern keyed on the
  full LHS (`wp comp post`), and pre-extracted RHS. Consumed by
  `Sym.Simp.Theorems.rewrite` in future phases. The field is named
  `simpThm` because `theorem` is a reserved keyword in Lean 4. -/
  simpThm : Lean.Meta.Sym.Simp.Theorem
  /-- Sym-level pattern keyed on just the `comp` argument of the LHS.
  This is the key used by the current `runWpStepRules` dispatch, which
  indexes goals by their `wp`-argument. -/
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
  current `runWpStepRules` dispatch.
* `theorems` is the `Sym.Simp.Theorems` bundle for downstream SymM
  rewriting. -/
structure WpStepRegistry where
  all : Array WpStepEntry := #[]
  compTree : DiscrTree WpStepEntry := .empty
  theorems : Lean.Meta.Sym.Simp.Theorems := {}

instance : Inhabited WpStepRegistry := ⟨{}⟩

private def WpStepRegistry.addToCompTree
    (tree : DiscrTree WpStepEntry) (entry : WpStepEntry) :
    DiscrTree WpStepEntry :=
  Lean.Meta.Sym.insertPattern tree entry.compPattern entry

private def WpStepRegistry.addTheorem
    (thms : Lean.Meta.Sym.Simp.Theorems) (entry : WpStepEntry) :
    Lean.Meta.Sym.Simp.Theorems :=
  thms.insert entry.simpThm

initialize wpStepRegistry :
    SimpleScopedEnvExtension WpStepEntry WpStepRegistry ←
  registerSimpleScopedEnvExtension {
    addEntry := fun registry entry =>
      { registry with
          all := registry.all.push entry
          compTree := WpStepRegistry.addToCompTree registry.compTree entry
          theorems := WpStepRegistry.addTheorem registry.theorems entry }
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

/-- Construct a registry entry from a theorem declaration.

Populates both sides of the registry: the Sym-simp theorem bundle
(keyed on the full `wp comp post` LHS) and the comp-keyed pattern used
by the current dispatch. -/
private def buildWpStepEntry (decl : Name) (priority : Nat) : MetaM WpStepEntry := do
  let thm ← Lean.Meta.Sym.Simp.mkTheoremFromDecl decl
  let lhsFn := thm.pattern.pattern.getAppFn
  unless lhsFn.isConstOf ``MAlgOrdered.wp || lhsFn.isConstOf ``OracleComp.ProgramLogic.wp do
    throwError
      m!"@[wpStep] expects an equational `wp _ _ = …` rule; got LHS:\
      {indentExpr thm.pattern.pattern}"
  let (compPattern, _) ← Lean.Meta.Sym.mkPatternFromDeclWithKey decl selectWpStepLhsComp
  return { proof := .global decl, simpThm := thm, compPattern, priority }

initialize registerBuiltinAttribute {
  name := `wpStep
  descr := "Register an equational `wp comp post = …` rule for the runWpStepRules planner."
  add := fun decl stx kind => MetaM.run' do
    let prio ← getAttrParamOptPrio stx[1]
    let entry ← buildWpStepEntry decl prio
    wpStepRegistry.add entry kind
}

/-- Retrieve the `Sym.Simp.Theorems` bundle accumulated by `@[wpStep]`.

The bundle is environment-level data; it is cheap to fetch and is shared
across tactic invocations. This is the entry point Phase F-ish migrations
would use to drive the goal via `Sym.Simp.Theorems.rewrite` directly,
once the `SymM → TacticM` proof-application bridge lands. -/
def getWpStepTheorems : MetaM Lean.Meta.Sym.Simp.Theorems := do
  return (wpStepRegistry.getState (← getEnv)).theorems

/-- Retrieve all registered `@[wpStep]` entries in insertion order. -/
def getAllWpStepEntries : CoreM (Array WpStepEntry) := do
  return (wpStepRegistry.getState (← getEnv)).all

/-- Retrieve the `@[wpStep]` entries whose `comp` pattern matches `oa`.

The goal's `oa` is first instantiated and `withReducible whnf`-normalized
so its head agrees with the registered patterns (which were unfolded once via
`Sym.preprocessType` at registration time). The actual tree traversal is the
pure `Sym.DiscrTree.getMatch`, which already wildcards proof / instance
positions and de Bruijn pattern variables.

Returned candidates are still validated by the dispatch tactic when it tries
each rewrite, so over-approximation here is harmless. -/
def getRegisteredWpStepEntries (oa : Expr) : MetaM (Array WpStepEntry) := do
  let oa ← instantiateMVars oa
  let oa ← withReducible <| whnf oa
  let registry := wpStepRegistry.getState (← getEnv)
  return Lean.Meta.Sym.getMatch registry.compTree oa

end OracleComp.ProgramLogic
