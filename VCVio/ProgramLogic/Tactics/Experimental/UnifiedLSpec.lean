/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import Lean.Meta.Sym.Pattern
import Lean.Meta.Sym.Simp.DiscrTree
import VCVio.ProgramLogic.Unary.HoareTriple
import VCVio.ProgramLogic.Relational.Quantitative
import VCVio.ProgramLogic.Relational.Loom.Quantitative

/-!
# Unified `@[lspec_spike]` Attribute (spike, attr defs)

**Status: experimental spike. Not exported via `VCVio.lean`.**

This file defines the attribute and its registry. The demo
(actual `attribute [lspec_spike] …` registrations) lives in
`Experimental/UnifiedLSpecDemo.lean`, because Lean does not allow
calling an `[init]` env-extension's `add` handler from inside the
same module that defined it.

See `UnifiedLSpecDemo.lean` for the design discussion and rationale.
-/

open Lean Elab Meta
open Lean.Meta (DiscrTree)
open Lean.Elab.Tactic.Do.SpecAttr (SpecProof)

namespace OracleComp.ProgramLogic.Experimental

/-! ## Data model -/

inductive LSpecKind where
  | unary
  | relational (rightHead : Name)
  deriving Inhabited, BEq, Repr

structure LSpecEntry where
  proof : SpecProof
  pattern : Lean.Meta.Sym.Pattern
  kind : LSpecKind
  priority : Nat := eval_prio default
  deriving Inhabited

instance : BEq LSpecEntry where
  beq a b := a.proof == b.proof

structure LSpecRegistry where
  all : Array LSpecEntry := #[]
  tree : DiscrTree LSpecEntry := .empty
  deriving Inhabited

private def LSpecRegistry.add' (registry : LSpecRegistry) (entry : LSpecEntry) :
    LSpecRegistry :=
  let registry := { registry with all := registry.all.push entry }
  { registry with tree := Lean.Meta.Sym.insertPattern registry.tree entry.pattern entry }

initialize lspecRegistry :
    SimpleScopedEnvExtension LSpecEntry LSpecRegistry ←
  registerSimpleScopedEnvExtension {
    addEntry := fun registry entry => registry.add' entry
    initial := {}
  }

/-! ## Shape recognizers -/

private def stdDoTripleArity : Nat := 4
private def stdDoWpArity : Nat := 3
private def stdDoRelTripleArity : Nat := 6
private def stdDoRwpArity : Nat := 5

private def trailingArgsN? (e : Expr) (n : Nat) : Option (Array Expr) :=
  let args := e.getAppArgs
  if n ≤ args.size then some <| args.extract (args.size - n) args.size else none

private def matchStdDoTriple? (body : Expr) : Option (Expr × Expr × Expr) := do
  unless body.getAppFn.isConstOf ``Std.Do'.Triple do none
  let args ← trailingArgsN? body stdDoTripleArity
  let #[pre, oa, post, _epost] := args | none
  some (pre, oa, post)

private def matchStdDoWp? (body : Expr) : Option (Expr × Expr) := do
  unless body.getAppFn.isConstOf ``Std.Do'.wp do none
  let args ← trailingArgsN? body stdDoWpArity
  let #[oa, post, _epost] := args | none
  some (oa, post)

private def matchStdDoRelTriple? (body : Expr) :
    Option (Expr × Expr × Expr × Expr) := do
  unless body.getAppFn.isConstOf ``Std.Do'.RelTriple do none
  let args ← trailingArgsN? body stdDoRelTripleArity
  let #[pre, x, y, post, _e₁, _e₂] := args | none
  some (pre, x, y, post)

private def matchStdDoRwp? (body : Expr) : Option (Expr × Expr × Expr) := do
  unless body.getAppFn.isConstOf ``Std.Do'.rwp do none
  let args ← trailingArgsN? body stdDoRwpArity
  let #[x, y, post, _e₁, _e₂] := args | none
  some (x, y, post)

inductive LeForm where
  | unary (pre oa post : Expr)
  | relational (pre x y post : Expr)

private def matchLeBody? (body : Expr) : Option LeForm := Id.run do
  let mut rhs : Expr := default
  let mut pre : Expr := default
  if body.isAppOfArity ``LE.le 4 then
    pre := body.getArg! 2
    rhs := body.getArg! 3
  else if body.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
    pre := body.getArg! 2
    rhs := body.getArg! 3
  else
    return none
  if let some (oa, post) := matchStdDoWp? rhs then
    return some (.unary pre oa post)
  if let some (x, y, post) := matchStdDoRwp? rhs then
    return some (.relational pre x y post)
  return none

/-! ## Key selector -/

private def relRightHead? (y : Expr) : MetaM Name := do
  match y.getAppFn.constName? with
  | some n => return n
  | none =>
    throwError m!"lspec_spike: relational right program lacks a constant head{indentExpr y}"

private def selectLSpecKey (body : Expr) : MetaM (Expr × LSpecKind) := do
  let body := body.consumeMData
  if let some (_pre, oa, _post) := matchStdDoTriple? body then
    return (oa, .unary)
  if let some (_pre, x, y, _post) := matchStdDoRelTriple? body then
    let rightHead ← relRightHead? y
    return (x, .relational rightHead)
  if let some f := matchLeBody? body then
    match f with
    | .unary _ oa _ => return (oa, .unary)
    | .relational _ x y _ =>
        let rightHead ← relRightHead? y
        return (x, .relational rightHead)
  throwError m!"@[lspec_spike] expects a Triple, RelTriple, or ⊑/≤-form lemma; \
                got:{indentExpr body}"

private def buildEntry (decl : Name) (priority : Nat) : MetaM LSpecEntry := do
  let (pattern, kind) ←
    Lean.Meta.Sym.mkPatternFromDeclWithKey decl selectLSpecKey
  return { proof := .global decl, pattern, kind, priority }

initialize registerBuiltinAttribute {
  name := `lspec_spike
  descr := "Register a unary or relational program-logic theorem (spike)."
  add := fun decl stx kind => MetaM.run' do
    let prio ← getAttrParamOptPrio stx[1]
    let entry ← buildEntry decl prio
    lspecRegistry.add entry kind
}

/-! ## Lookup -/

def lookup (target : Expr) : MetaM (Array LSpecEntry) := do
  let target ← instantiateMVars target
  let body := target.consumeMData
  match matchLeBody? body with
  | none => return #[]
  | some (.unary _ oa _) => do
      let oa ← preprocessKey oa
      let registry := lspecRegistry.getState (← getEnv)
      let candidates := Lean.Meta.Sym.getMatch registry.tree oa
      return candidates.filter fun e =>
        match e.kind with
        | .unary => true
        | _ => false
  | some (.relational _ x y _) => do
      match y.getAppFn.constName? with
      | none => return #[]
      | some goalRightHead =>
        let x ← preprocessKey x
        let registry := lspecRegistry.getState (← getEnv)
        let candidates := Lean.Meta.Sym.getMatch registry.tree x
        return candidates.filter fun e =>
          match e.kind with
          | .relational rh => rh == goalRightHead
          | _ => false
where
  /-- Mirror the registration-time normalization done by
  `Sym.preprocessType` on the lookup key, so `Sym.getMatch` keys
  agree with the patterns that were inserted. -/
  preprocessKey (e : Expr) : MetaM Expr := do
    let e ← Lean.Meta.Sym.unfoldReducible e
    let e ← Core.betaReduce e
    Lean.Meta.Sym.etaReduceAll e

end OracleComp.ProgramLogic.Experimental
