/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Lean.Meta.Tactic.Simp
public import Lean.Meta.Sym.Pattern
public import Loom.Triple.Basic
import Init.Syntax
import Init.While

public section

namespace Loom.Tactic.SpecAttr

open Lean Meta Loom Std.Do' Lean.Order

syntax (name := lspec) "lspec" (ppSpace prio)? : attr

/--
  This attribute should not be used directly.
  It is an implementation detail of loom2 tactics.
-/
initialize lspecSimpExt : Meta.SimpExtension ←
  Meta.registerSimpAttr `lspec_simp "simp theorems internally used by loom2 tactics"

/--
  The simp set accumulated by the `@[lspec]` attribute.
  (This does not include Hoare triple specs.)
-/
def getSpecSimpTheorems : CoreM SimpTheorems :=
  lspecSimpExt.getTheorems

inductive SpecProof where
  | global (declName : Name)
  | local (fvarId : FVarId)
  | stx (id : Name) (ref : Syntax) (proof : Expr)
  deriving Inhabited, BEq

/-- A unique identifier corresponding to the origin. -/
def SpecProof.key : SpecProof → Name
  | .global declName => declName
  | .local fvarId => fvarId.name
  | .stx id _ _ => id

instance : Hashable SpecProof where
  hash sp := hash sp.key

private def tripleToWpProof? (proof type : Expr) : MetaM (Expr × Expr) := do
  let type ← whnfR type
  if type.isAppOfArity ``Triple 12 then
    let .const _ lvls := type.getAppFn
      | return (proof, type)
    let args := type.getAppArgs
    -- Triple inductive param order:  m l e α Monad AL EAL WP pre x post epost
    -- Triple.iff theorem param order: m l e Monad AL EAL WP α x pre post epost
    let tripleIff := mkAppN (mkConst ``Triple.iff lvls)
      #[args[0]!, args[1]!, args[2]!, args[4]!, args[5]!, args[6]!, args[7]!, args[3]!, args[9]!, args[8]!, args[10]!, args[11]!]
    let proof ← mkAppM ``Iff.mp #[tripleIff, proof]
    let type ← instantiateMVars (← inferType proof)
    return (proof, type)
  else
    return (proof, type)

def SpecProof.instantiate (proof : SpecProof) : MetaM (Array Expr × Array BinderInfo × Expr × Expr) := do
  let prf ← match proof with
    | .global declName => mkConstWithFreshMVarLevels declName
    | .local fvarId => pure <| mkFVar fvarId
    | .stx _ _ proof => pure proof
  let type ← instantiateMVars (← inferType prf)
  let (xs, bs, type) ← forallMetaTelescope type
  let prf := prf.beta xs
  let (prf, type) ← tripleToWpProof? prf type
  return (xs, bs, prf, type)

instance : ToMessageData SpecProof where
  toMessageData := fun
    | .global declName => m!"SpecProof.global {declName}"
    | .local fvarId => m!"SpecProof.local {mkFVar fvarId}"
    | .stx _ ref proof => m!"SpecProof.stx _ {ref} {proof}"

structure SpecTheorem where
  keys : Array DiscrTree.Key
  /--
  Expr key tested for matching, in ∀-quantified form.
  `keys = (← mkPath (← forallMetaTelescope prog).2.2)`.
  -/
  prog : Expr
  /-- Pattern for matching the program expression. Populated by `migrateSpecTheoremsDatabase`. -/
  pattern : Option Sym.Pattern := none
  /-- The proof for the theorem. -/
  proof : SpecProof
  priority : Nat := eval_prio default
  deriving Inhabited

instance : BEq SpecTheorem where
  beq a b := a.keys == b.keys && a.prog == b.prog && a.proof == b.proof && a.priority == b.priority

abbrev SpecEntry := SpecTheorem

structure SpecTheorems where
  specs : DiscrTree SpecTheorem := DiscrTree.empty
  erased : PHashSet SpecProof := {}
  deriving Inhabited

def SpecTheorems.add (d : SpecTheorems) (e : SpecTheorem) : SpecTheorems :=
  { d with specs := d.specs.insertKeyValue e.keys e }

def SpecTheorems.isErased (d : SpecTheorems) (thmId : SpecProof) : Bool :=
  d.erased.contains thmId

def SpecTheorems.erase (d : SpecTheorems) (thmId : SpecProof) : SpecTheorems :=
  { d with erased := d.erased.insert thmId }

abbrev SpecExtension := SimpleScopedEnvExtension SpecEntry SpecTheorems

private def mkSpecTheorem (type : Expr) (proof : SpecProof) (prio : Nat) : MetaM SpecTheorem := do
  let type ← instantiateMVars type
  unless (← isProp type) do
    throwError "invalid 'lspec', proposition expected{indentExpr type}"
  withNewMCtxDepth do
  let (xs, _, type) ← withSimpGlobalConfig (forallMetaTelescopeReducing type)
  let type ← whnfR type
  let prog ←
    if type.isAppOfArity ``Triple 12 then
      pure (type.getArg! 9)
    else if type.isAppOfArity ``PartialOrder.rel 4 then do
      let rhs := type.getArg! 3
      let_expr wp _m _l _e _monad _instAL _instEAL _wpInst _α prog _post _epost := rhs
        | throwError "RHS of ⊑ is not a wp application{indentExpr rhs}"
      pure prog
    else
      throwError "unexpected kind of spec theorem; expected Triple or ⊑ wp{indentExpr type}"
  let keys ← DiscrTree.mkPath prog (noIndexAtArgs := false)
  return { keys, prog := (← mkForallFVars xs prog), proof, priority := prio }

def mkSpecTheoremFromConst (declName : Name) (prio : Nat := eval_prio default) : MetaM SpecTheorem := do
  let cinfo ← getConstInfo declName
  let us := cinfo.levelParams.map mkLevelParam
  let val := mkConst declName us
  let type ← inferType val
  mkSpecTheorem type (.global declName) prio

def mkSpecTheoremFromLocal (fvar : FVarId) (prio : Nat := eval_prio default) : MetaM SpecTheorem := do
  let some decl ← fvar.findDecl? | throwError "invalid 'lspec', local declaration {fvar.name} not found"
  mkSpecTheorem decl.type (.local fvar) prio

def mkSpecTheoremFromStx (ref : Syntax) (proof : Expr) (prio : Nat := eval_prio default) : MetaM SpecTheorem := do
  let type ← inferType proof
  mkSpecTheorem type (.stx (← mkFreshId) ref proof) prio

def SpecExtension.addSpecTheoremFromConst (ext : SpecExtension) (declName : Name) (prio : Nat) (attrKind : AttributeKind) : MetaM Unit := do
  let thm ← mkSpecTheoremFromConst declName prio
  ext.add thm attrKind

def SpecExtension.addSpecTheoremFromLocal (ext : SpecExtension) (fvar : FVarId) (prio : Nat := eval_prio default) : MetaM Unit := do
  let thm ← mkSpecTheoremFromLocal fvar prio
  ext.add thm .local

def mkSpecExt : SimpleScopedEnvExtension.Descr SpecEntry SpecTheorems where
  name     := `lspecMap
  initial  := {}
  addEntry := fun d e => d.add e

initialize lspecAttr : SpecExtension ← registerSimpleScopedEnvExtension mkSpecExt

def mkLSpecAttr (ext : SpecExtension) : AttributeImpl where
  name  := `lspec
  descr := "Marks Hoare triple specifications and simp theorems for use with loom2 tactics"
  applicationTime := AttributeApplicationTime.afterCompilation
  add   := fun declName stx attrKind => do
    let go : MetaM Unit := do
      let _info ← getConstInfo declName
      let prio ← getAttrParamOptPrio stx[1]
      try
        ext.addSpecTheoremFromConst declName prio attrKind
      catch _ =>
      let env ← getEnv
      let impl ← IO.ofExcept (getAttributeImpl env `lspec_simp)
      try
        let newStx ← `(attr| lspec_simp)
        let newStx := newStx.raw.setArg 3 stx[1]
        impl.add declName newStx attrKind
      catch e =>
      trace[Loom.Tactic.lspecAttr] "Reason for failure to apply lspec attribute: {e.toMessageData}"
      throwError "Invalid 'lspec': target was neither a Hoare triple specification nor a 'simp' lemma"
    discard <| go.run {} {}

initialize registerBuiltinAttribute (mkLSpecAttr lspecAttr)

def SpecExtension.getTheorems (ext : SpecExtension) : CoreM SpecTheorems :=
  return ext.getState (← getEnv)

def getSpecTheorems : CoreM SpecTheorems :=
  lspecAttr.getTheorems

end Loom.Tactic.SpecAttr
