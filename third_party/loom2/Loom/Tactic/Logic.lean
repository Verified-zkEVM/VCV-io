/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public meta import Lean
public import Loom.Tactic.Attr
public meta import Loom.Tactic.ShareExt
public import Loom.WP.Lemmas
public import Loom.Frame

public section

open Lean Meta Sym Sym.Internal Loom Lean.Order

namespace Loom

inductive LogicOp where
  | And
  | Imp
  | Pure
  -- Temporarily disabled:
  -- | Forall (n : Name)

/-- Map lattice connective declaration names to supported `LogicOp`s. -/
def _root_.Lean.Name.toLogicOp? : Name → Option LogicOp
  | ``meet => some .And
  | ``himp => some .Imp
  | ``CompleteLattice.pure => some .Pure
  | _ => none

meta def LogicOp.mkLatticeExpr (as : Array Expr) (resultType? : Option Expr := none) : LogicOp → MetaM Expr
  | .And => mkAppM ``meet as
  | .Imp => mkAppM ``himp as
  | .Pure => mkAppOptM ``CompleteLattice.pure #[resultType?, none, some as[0]!]

/-- Map a logic operator to its corresponding `*_fun_apply` lemma. -/
meta def LogicOp.toApplyLemma : LogicOp → Name
  | .And => ``meet_fun_apply
  | .Imp => ``himp_fun_apply
  | .Pure => ``pure_fun_apply

/-- Map a logic operator to its corresponding proposition-level equivalence lemma. -/
meta def LogicOp.toPropLemma : LogicOp → Name
  | .And => ``meet_prop_eq_and
  | .Imp => ``himp_prop_eq_imp
  | .Pure => ``LE.pure_intro

/-- Map a logic operator to its `⊑`-form splitting lemma. -/
meta def LogicOp.toRelLemma : LogicOp → Name
  | .And => ``le_meet       -- le_meet (x y z) : x ⊑ y → x ⊑ z → x ⊑ y ⊓ z
  | .Imp => ``himp_complete  -- himp_complete (x a b) : a ⊓ x ⊑ b → x ⊑ a ⇨ b
  | .Pure => ``le_pure       -- le_pure (x p) : p → x ⊑ ⌜p⌝

/-- Lift an equality `lhs = rhs` to `(lhs args...) = (rhs args...)`. -/
private meta def liftEqByArgs (eqPrf : Expr) (args : List Expr) : MetaM Expr := do
  if args.isEmpty then
    return eqPrf
  let eqTy ← inferType eqPrf
  let some (_, lhs, _rhs) := eqTy.eq?
    | throwError "Expected equality proof, got {indentExpr eqTy}"
  let lhsTy ← inferType lhs
  let context ← withLocalDecl `x .default lhsTy fun x => do
    let app := mkAppN x args.toArray
    mkLambdaFVars #[x] app
  mkCongrArg context eqPrf

/--
Apply a function-extensional lemma (`*_fun_apply`) repeatedly over all excess
arguments, producing an equality at the fully applied level.

Example (`lop = .And`, `stepThm = ``meet_fun_apply`, `as = #[a, b]`,
`ss = [s₁, s₂]`): the resulting proof has type
`((a ⊓ b) s₁ s₂) = (a s₁ s₂ ⊓ b s₁ s₂)`.
-/
meta partial def LogicOp.mkApplyEq
    (stepThm : Name) (lop : LogicOp)
    (as : Array Expr) (ss : List Expr) (resultType? : Option Expr := none) : MetaM Expr := do
  match ss with
  | [] => mkEqRefl =<< lop.mkLatticeExpr as resultType?
  | s :: ss' =>
    let args := as.push s |>.map some
    let rt := resultType?.map .bindingBody!
    let step ← mkAppOptM stepThm <| #[none, rt, none] ++ args
    if ss'.isEmpty then
      return step
    let stepLift ← liftEqByArgs step ss'
    let as := as.map (mkApp · s)
    let rest ← lop.mkApplyEq stepThm as ss' rt
    mkEqTrans stepLift rest

/-- Like `mkGoalPremiseEq` but only distributes through function applications
    via `*_fun_apply` lemmas, staying at the lattice level (no Prop simplification).
    Returns `((a ⊓ b) s₁...sₙ, (a s₁...sₙ ⊓ b s₁...sₙ), eq)`. -/
meta def LogicOp.mkDistributeEq
    (lop : LogicOp) (as ss : Array Expr) (resultType? : Option Expr := none) : SymM (Expr × Expr) := do
  let applyLemma := lop.toApplyLemma
  let lat ← lop.mkLatticeExpr as resultType?
  let goal ← mkAppNS lat ss
  let eqFun ← lop.mkApplyEq applyLemma as ss.toList resultType?
  return (goal, eqFun)

-- #check forallMeta

/--
Creates a reusable backward rule for a lattice logic expression in `⊑` form.
Chains distribution (`*_fun_apply`) with the split lemma (`le_meet`/`himp_complete`).

For `And`, produces:
```
∀ (a b : l) (s₁ : σ₁) ... (sₙ : σₙ) (pre : l'),
  pre ⊑ a s₁...sₙ → pre ⊑ b s₁...sₙ → pre ⊑ (a ⊓ b) s₁...sₙ
```
For `Imp`, produces:
```
∀ (a b : l) (s₁ : σ₁) ... (sₙ : σₙ) (pre : l'),
  a s₁...sₙ ⊓ pre ⊑ b s₁...sₙ → pre ⊑ (a ⇨ b) s₁...sₙ
```
Works for any `CompleteLattice`, not just `Prop`.
-/
meta def LogicOp.mkBackwardRule
    (lop : LogicOp) (as : Array Expr) (excessArgs : Array Expr)
    (resultType? : Option Expr := none)
    : SymM BackwardRule := do
  let as ← as.mapM fun arg => do
    mkFreshExprMVar (userName := `a) (← Sym.inferType arg)
  -- dbg_trace "as"
  let ss ← excessArgs.mapM fun arg => do
    mkFreshExprMVar (userName := `s) (← Sym.inferType arg)

  let (goal, eqGoalDistributed) ← lop.mkDistributeEq as ss resultType?

  let goalTy ← Meta.inferType goal
  let pre ← mkFreshExprMVar (userName := `pre) goalTy

  -- Lift equality through `pre ⊑ ·`: (pre ⊑ goal) = (pre ⊑ distributed)
  -- Use partial application (not lambda) to avoid beta redexes
  let relPreGoal ← mkAppM ``PartialOrder.rel #[pre]
  let relEq ← mkCongrArg relPreGoal eqGoalDistributed
  let relEqSymm ← mkEqSymm relEq
  -- eqMp : (pre ⊑ distributed) → (pre ⊑ goal)
  let eqMp ← mkAppM ``Eq.mp #[relEqSymm]

  -- Instantiate the split lemma (le_meet / himp_complete) via meta telescope
  let splitLemma ← mkConstWithFreshMVarLevels lop.toRelLemma
  let (xs, _, body) ← forallMetaTelescope (← Meta.inferType splitLemma)
  -- Unify conclusion with eqMp's domain to assign param mvars
  unless ← isDefEq body (← Meta.inferType eqMp).bindingDomain! do
    throwError "Expected {← Meta.inferType eqMp}.bindingDomain! = {← Meta.inferType body}"
  -- Compose (abstractMVars handles instantiation of assigned mvars)
  let prf := mkApp eqMp (mkAppN splitLemma xs)

  let res ← abstractMVars prf
  let type ← preprocessExpr (← Meta.inferType res.expr)
  let prf ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl prf

/-! ## Tests -/

section Test

/-- Test helper: run `mkBackwardRuleForLogicRel` and return the generated rule type. -/
meta def testLogicBackwardRuleRel
    (lop : LogicOp)
    (as excessArgs : Array Expr) (resultType? : Option Expr := none) : MetaM Expr := do
  let rule ← SymM.run do lop.mkBackwardRule as excessArgs resultType?
  inferType rule.expr

-- Test 1: And on Nat → Prop, n = 1 excess arg
-- Should produce: ∀ (a b : Nat → Prop) (s : Nat) (pre : Prop),
--   pre ⊑ (a s ⊓ b s) → pre ⊑ (a ⊓ b) s
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let l ← mkArrow nat (mkSort 0)
  withLocalDeclD `a l fun a => do
    withLocalDeclD `b l fun b => do
      withLocalDeclD `s nat fun s => do
        let ty ← testLogicBackwardRuleRel .And #[a, b] #[s]
        logInfo m!"Test Rel-And (Nat→Prop, n=1): {ty}"

-- Test 2: Imp on Nat → Prop, n = 1 excess arg
-- Should produce: ∀ (a b : Nat → Prop) (s : Nat) (pre : Prop),
--   pre ⊑ (a s ⇨ b s) → pre ⊑ (a ⇨ b) s
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let l ← mkArrow nat (mkSort 0)
  withLocalDeclD `a l fun a => do
    withLocalDeclD `b l fun b => do
      withLocalDeclD `s nat fun s => do
        let ty ← testLogicBackwardRuleRel .Imp #[a, b] #[s]
        logInfo m!"Test Rel-Imp (Nat→Prop, n=1): {ty}"

-- Test 3: And on Prop, n = 0 excess args
-- Should produce: ∀ (a b : Prop) (pre : Prop),
--   pre ⊑ (a ⊓ b) → pre ⊑ (a ⊓ b)  (identity — no distribution needed)
#eval! show MetaM Unit from do
  let l := mkSort 0
  withLocalDeclD `a l fun a => do
    withLocalDeclD `b l fun b => do
      let ty ← testLogicBackwardRuleRel .And #[a, b] #[]
      logInfo m!"Test Rel-And (Prop, n=0): {ty}"

-- Test 4: End-to-end And rule application
-- Goal: True ⊑ (a ⊓ b) s, should produce True ⊑ a s and True ⊑ b s
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let l ← mkArrow nat (mkSort 0)
  withLocalDeclD `a l fun a => do
    withLocalDeclD `b l fun b => do
      withLocalDeclD `s nat fun s => do
        let rule ← SymM.run do LogicOp.mkBackwardRule .And #[a, b] #[s]
        let meetAB ← mkAppM ``meet #[a, b]
        let target ← mkAppM ``PartialOrder.rel #[mkConst ``True, mkApp meetAB s]
        let goalExpr ← mkFreshExprSyntheticOpaqueMVar target
        let .mvar goal := goalExpr | throwError "expected mvar"
        let .goals goals ← SymM.run do rule.apply goal
          | throwError "Test 4: rule application failed"
        for g in goals do
          logInfo m!"Test 4 subgoal: {← g.getType}"

-- Test 5: End-to-end Imp rule application with pre = True
-- Goal: True ⊑ (a ⇨ b) s, should produce a s ⊓ True ⊑ b s
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let l ← mkArrow nat (mkSort 0)
  withLocalDeclD `a l fun a => do
    withLocalDeclD `b l fun b => do
      withLocalDeclD `s nat fun s => do
        let rule ← SymM.run do LogicOp.mkBackwardRule .Imp #[a, b] #[s]
        let himpAB ← mkAppM ``himp #[a, b]
        let target ← mkAppM ``PartialOrder.rel #[mkConst ``True, mkApp himpAB s]
        let goalExpr ← mkFreshExprSyntheticOpaqueMVar target
        let .mvar goal := goalExpr | throwError "expected mvar"
        let .goals goals ← SymM.run do rule.apply goal
          | throwError "Test 5: rule application failed"
        for g in goals do
          logInfo m!"Test 5 subgoal: {← g.getType}"

-- Test 6: Pure on Nat → Prop, n = 1 excess arg
-- Should produce: ∀ (p : Prop) (s : Nat) (pre : Prop),
--   p → pre ⊑ (⌜p⌝) s
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let l ← mkArrow nat (mkSort 0)
  withLocalDeclD `p (mkSort 0) fun p => do
    withLocalDeclD `s nat fun s => do
      let ty ← testLogicBackwardRuleRel .Pure #[p] #[s] (some l)
      logInfo m!"Test Rel-Pure (Nat→Prop, n=1): {ty}"

-- Test 7: Pure on Prop, n = 0 excess args
#eval! show MetaM Unit from do
  withLocalDeclD `p (mkSort 0) fun p => do
    let ty ← testLogicBackwardRuleRel .Pure #[p] #[] (some (mkSort 0))
    logInfo m!"Test Rel-Pure (Prop, n=0): {ty}"

-- Test 8: End-to-end Pure rule application
-- Goal: True ⊑ (⌜p⌝) s, should produce p
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let l ← mkArrow nat (mkSort 0)
  withLocalDeclD `p (mkSort 0) fun p => do
    withLocalDeclD `s nat fun s => do
      let rule ← SymM.run do LogicOp.mkBackwardRule .Pure #[p] #[s] (some l)
      let pureP ← mkAppOptM ``CompleteLattice.pure #[some l, none, some p]
      let target ← mkAppM ``PartialOrder.rel #[mkConst ``True, mkApp pureP s]
      let goalExpr ← mkFreshExprSyntheticOpaqueMVar target
      let .mvar goal := goalExpr | throwError "expected mvar"
      let .goals goals ← SymM.run do rule.apply goal
        | throwError "Test Pure: rule application failed"
      for g in goals do
        logInfo m!"Test Pure subgoal: {← g.getType}"

end Test

end Loom

end -- public section
