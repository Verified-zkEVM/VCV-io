/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
import Lean
public import Loom.Tactic.Attr
public import Loom.Triple.Basic

public section

namespace Loom.Tactic.FindSpec

open Lean Meta Loom Lean.Order Sym
open Loom.Tactic.SpecAttr

/-- Extract the program expression from a spec conclusion (Triple or ⊑ wp form). -/
private def selectProg (type : Expr) : MetaM (Expr × Unit) := do
  let type ← whnfR type
  if type.isAppOfArity ``Triple 12 then
    return (type.getArg! 9, ())
  else if type.isAppOfArity ``PartialOrder.rel 4 then
    let rhs := type.getArg! 3
    let_expr wp _m _l _e _monad _instAL _instEAL _wpInst _α prog _post _epost := rhs
      | throwError "RHS of ⊑ is not a wp application{indentExpr rhs}"
    return (prog, ())
  else
    throwError "expected Triple or ⊑ wp{indentExpr type}"

/-- Create a `Sym.Pattern` for a `SpecTheorem` by extracting the program from the proof type. -/
private def mkSpecPattern (proof : SpecProof) : SymM Sym.Pattern := do
  match proof with
  | .global declName =>
    Prod.fst <$> Sym.mkPatternFromDeclWithKey declName selectProg
  | .local fvarId =>
    let e := mkFVar fvarId
    Prod.fst <$> Sym.mkPatternFromExprWithKey e [] selectProg
  | .stx _ _ proof =>
    Prod.fst <$> Sym.mkPatternFromExprWithKey proof [] selectProg

/--
Migrate a `SpecTheorems` database by computing `Sym.Pattern`s for each spec theorem
and rebuilding the discrimination tree using pattern-derived keys.
-/
def migrateSpecTheoremsDatabase (database : SpecTheorems) : SymM SpecTheorems := do
  let oldSpecs := database.specs.values
  let mut newSpecs : DiscrTree SpecTheorem := DiscrTree.empty
  for spec in oldSpecs do
    if database.erased.contains spec.proof then continue
    try
      let pattern ← mkSpecPattern spec.proof
      let newSpec := { spec with pattern := some pattern }
      newSpecs := Sym.insertPattern newSpecs pattern newSpec
    catch _ =>
      -- Fall back to old keys if pattern creation fails
      newSpecs := newSpecs.insertKeyValue spec.keys spec
  return { database with specs := newSpecs }

/--
Look up spec theorems matching program `e` using pattern-based matching.
Returns `.ok spec` on the first match, or `.error candidates` if no spec matches.
-/
def findSpecs (database : SpecTheorems) (e : Expr) :
    SymM (Except (Array SpecTheorem) SpecTheorem) := do
  let e ← instantiateMVars e
  -- Eta-reduce to match disc tree keys (patterns are preprocessed with etaReduceAll)
  let e ← shareCommon e
  let candidates := Sym.getMatch database.specs e
  let candidates := candidates.filter (!database.erased.contains ·.proof)
  if h : candidates.size = 1 then return .ok candidates[0]
  let candidates := candidates.insertionSort (·.priority > ·.priority)
  for spec in candidates do
    match spec.pattern with
    | some pattern =>
      let some _res ← pattern.match? e | continue
      return .ok spec
    | none =>
      -- Fallback for specs without patterns (shouldn't happen after migration)
      return .ok spec
  return .error candidates

end Loom.Tactic.FindSpec

end -- public section
