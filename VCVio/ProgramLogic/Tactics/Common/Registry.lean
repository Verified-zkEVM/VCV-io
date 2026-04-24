/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import VCVio.ProgramLogic.Tactics.Common.SpecIR

/-!
# VCSpec Registry

Discrimination-tree backed registry for `@[vcspec]` lemmas used by the unary and relational
program-logic tactics.

The registry indexes each registered theorem by the *computation* sub-expression
of its conclusion: for unary triples / `wp` goals this is the `OracleComp` argument,
and for relational triples / `RelWP` / `eRelTriple` goals this is the left-hand
computation. A separate constant-name filter on the right-hand head keeps relational
lookups precise without paying for two structural matches.

Two concrete benefits over the previous `NameMap` storage:

1. Multi-level structural discrimination: rules whose computation has the same head but
   different argument structure (e.g. different inner heads under `Bind.bind`) can be
   distinguished at lookup time, and rules whose head only appears under a coercion are
   matched naturally because `DiscrTree.getMatch` runs `withReducible` whnf on subterms.
2. Sub-linear lookup: the discrimination tree shares prefixes of keys across rules,
   so adding more rules does not slow down dispatch on unrelated heads.
-/

open Lean Elab Meta Lean.Meta

namespace OracleComp.ProgramLogic

/-- Pre-computed discrimination-tree keys for the indexed sub-expression of a
`@[vcspec]` theorem (the unary `comp` or the relational `oa`). -/
abbrev VCSpecPatternKeys := Array DiscrTree.Key

/-- A registered `@[vcspec]` lemma together with everything the planner needs:
its declaration name, the normalized IR description, the discrimination-tree
keys for fast structural lookup, and (for relational entries) the head
constant of the right-hand computation used as a secondary filter. -/
structure VCSpecEntry where
  decl : Name
  spec : NormalizedVCSpec
  patternKeys : VCSpecPatternKeys
  rightHead? : Option Name := none
  deriving Inhabited, BEq, Repr

def VCSpecEntry.kind (entry : VCSpecEntry) : VCSpecKind :=
  entry.spec.kind

def VCSpecEntry.lookupKey (entry : VCSpecEntry) : VCSpecLookupKey :=
  entry.spec.lookupKey

/-- Persistent state for the `@[vcspec]` registry.

* `all` retains insertion order, used by `kind`-indexed iteration helpers.
* `unary` indexes unary entries by their `comp` discrimination-tree path.
* `relational` indexes relational entries by their `oa` discrimination-tree path;
  the right-hand head check happens at lookup time. -/
structure VCSpecRegistry where
  all : Array VCSpecEntry := #[]
  unary : DiscrTree VCSpecEntry := .empty
  relational : DiscrTree VCSpecEntry := .empty
  deriving Inhabited

private def VCSpecRegistry.addToTree (tree : DiscrTree VCSpecEntry) (entry : VCSpecEntry) :
    DiscrTree VCSpecEntry :=
  if entry.patternKeys.isEmpty then tree
  else tree.insertKeyValue entry.patternKeys entry

initialize vcSpecRegistry :
    SimpleScopedEnvExtension
      VCSpecEntry
      VCSpecRegistry ←
  registerSimpleScopedEnvExtension {
    addEntry := fun registry entry =>
      let registry := { registry with all := registry.all.push entry }
      match entry.lookupKey with
      | .unary _ =>
          { registry with unary := VCSpecRegistry.addToTree registry.unary entry }
      | .relational _ _ =>
          { registry with
              relational := VCSpecRegistry.addToTree registry.relational entry }
    initial := {}
  }

/-- Build a registry entry for `decl` from its type by extracting the indexed
sub-expressions and converting them into `DiscrTree` keys.

The `comp` / `oa` expressions live in the metavariable context introduced by
`forallMetaTelescopeReducing` inside `normalizeAndExtractVCSpecTarget`, so all
key computation happens before the surrounding `MetaM.run'` finishes. -/
private def buildVCSpecEntry (decl : Name) (declTy : Expr) : MetaM VCSpecEntry := do
  let (spec, idx) ← normalizeAndExtractVCSpecTarget `vcspec declTy
  let (patternKeys, rightHead?) ← match idx.comp?, idx.pair? with
    | some comp, _ => do
        let keys ← DiscrTree.mkPath comp
        pure (keys, none)
    | _, some (oa, ob) => do
        let keys ← DiscrTree.mkPath oa
        let obWhnf ← whnfReducible ob
        pure (keys, headConstName? obWhnf)
    | _, _ =>
        throwError m!"@[vcspec] internal error: no indexed sub-expression for `{decl}`"
  return { decl, spec, patternKeys, rightHead? }

initialize registerBuiltinAttribute {
  name := `vcspec
  descr := "Register a unary or relational program-logic theorem for vcgen/rvcgen lookup."
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let entry ← buildVCSpecEntry decl declTy
    vcSpecRegistry.add entry kind
}

private def headOfWhnf (e : Expr) : MetaM (Option Name) := do
  let e ← whnfReducible (← instantiateMVars e)
  return headConstName? e

def getRegisteredUnaryVCSpecEntries (comp : Expr) : MetaM (Array VCSpecEntry) := do
  let comp ← instantiateMVars comp
  let registry := vcSpecRegistry.getState (← getEnv)
  registry.unary.getMatch comp

def getRegisteredRelationalVCSpecEntries (oa ob : Expr) : MetaM (Array VCSpecEntry) := do
  let oa ← instantiateMVars oa
  let some rightHead ← headOfWhnf ob | return #[]
  let registry := vcSpecRegistry.getState (← getEnv)
  let candidates ← registry.relational.getMatch oa
  return candidates.filter fun entry =>
    match entry.rightHead? with
    | some h => h == rightHead
    | none => false

def getRegisteredUnaryVCSpecTheorems (comp : Expr) : MetaM (Array Name) := do
  return (← getRegisteredUnaryVCSpecEntries comp).map (·.decl)

def getRegisteredRelationalVCSpecTheorems (oa ob : Expr) : MetaM (Array Name) := do
  return (← getRegisteredRelationalVCSpecEntries oa ob).map (·.decl)

def getVCSpecEntriesOfKind (kind : VCSpecKind) : CoreM (Array VCSpecEntry) := do
  let registry := vcSpecRegistry.getState (← getEnv)
  return registry.all.filter (·.kind == kind)

def getVCSpecTheoremsOfKind (kind : VCSpecKind) : CoreM (Array Name) := do
  return (← getVCSpecEntriesOfKind kind).map (·.decl)

def getNormalizedUnaryVCSpecs (comp : Expr) : MetaM (Array NormalizedVCSpec) := do
  return (← getRegisteredUnaryVCSpecEntries comp).map (·.spec)

def getNormalizedRelationalVCSpecs (oa ob : Expr) : MetaM (Array NormalizedVCSpec) := do
  return (← getRegisteredRelationalVCSpecEntries oa ob).map (·.spec)

end OracleComp.ProgramLogic
