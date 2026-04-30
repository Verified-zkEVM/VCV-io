/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
import Lean
import Loom.Tactic.Attr
import Loom.Tactic.Spec
import Loom.Tactic.ShareExt
import Lean.Elab.Tactic.Do.VCGen.Split

open Lean Parser Meta Elab Tactic Sym Loom Lean.Order

namespace Loom.VCGen

open Lean.Elab.Tactic.Do in
/-- Creates a reusable backward rule for splitting `ite`, `dite`, or matchers.

Uses `SplitInfo.withAbstract` to introduce abstract fvars for the split components,
then `SplitInfo.splitWith` to build the splitting proof. Hypothesis types are
discovered via `rwIfOrMatcher` inside the splitter telescope. -/
meta def mkBackwardRuleForSplit
    (splitInfo : SplitInfo) (wpHead m Pred errTy monadInst instAL instEAL instWP : Expr)
    (excessArgs : Array Expr) : SymM BackwardRule := do
  let mTy ← Sym.inferType m
  let some aTy := if mTy.isForall then some mTy.bindingDomain! else none
    | throwError "Expected monad type constructor at {indentExpr m}"
  let prf ←
    withLocalDeclD `a aTy fun a => do
    let ma ← shareCommon <| mkApp m a
    splitInfo.withAbstract ma fun abstractInfo splitFVars => do
    -- Eta-reduce matcher alts for the backward rule pattern to avoid expensive
    -- higher-order unification. The alts are eta-expanded by `withAbstract` so that
    -- `splitWith`/`matcherApp.transform` can `instantiateLambda` them directly.
    let abstractProg := match abstractInfo with
      | .ite e | .dite e => e
      | .matcher matcherApp =>
        { matcherApp with alts := matcherApp.alts.map Expr.eta }.toExpr
    let excessArgNamesTypes ← excessArgs.mapM fun arg =>
      return (`s, ← Sym.inferType arg)
    withLocalDeclsDND excessArgNamesTypes fun ss => do
    withLocalDeclD `post (← shareCommon (← mkArrow a Pred)) fun post => do
    withLocalDeclD `epost errTy fun epost => do
    let mkWP (prog : Expr) : Expr :=
      mkAppN (mkAppN wpHead #[m, Pred, errTy, monadInst, instAL, instEAL, instWP, a, prog, post, epost]) ss
    let Pred' ← Sym.inferType (mkWP abstractProg)
    withLocalDeclD `pre Pred' fun pre => do
    let sampleGoal ← mkAppM ``PartialOrder.rel #[pre, mkWP abstractProg]
    let relArgs := sampleGoal.getAppArgs
    let relHead := mkAppN sampleGoal.getAppFn (relArgs.extract 0 3)
    let mkGoal (prog : Expr) : Expr := mkApp relHead (mkWP prog)
    -- Use synthetic opaque mvars so that `rwIfOrMatcher`'s `assumption` cannot
    -- accidentally assign our subgoal metavariables.
    let subgoals ← splitInfo.altInfos.mapM fun _ =>
      liftMetaM <| mkFreshExprSyntheticOpaqueMVar (mkSort 0)
    let namedSubgoals := subgoals.mapIdx fun i mv => ((`h).appendIndexAfter (i+1), mv)
    withLocalDeclsDND namedSubgoals fun subgoalHyps => do
    let prf ← liftMetaM <|
      abstractInfo.splitWith
        (useSplitter := true)
        (mkGoal abstractProg)
        (fun _name bodyType idx altFVars => do
          -- Extract the program from `bodyType` (the substituted alt goal type).
          -- For matchers, `bodyType` has the discriminant replaced by the constructor
          -- pattern (e.g., `Nat.zero` instead of `discr`), which is required for
          -- `rwMatcher` to discharge the equality hypotheses of congr equation theorems.
          -- For ite/dite, `bodyType` equals `mkGoal abstractProg` so this is equivalent.
          let prog := bodyType.getArg! 3 |>.getArg! 8
          let res ← rwIfOrMatcher idx prog
          if res.proof?.isNone then
            throwError "mkBackwardRuleForSplit: rwIfOrMatcher failed for alt {idx}"
          let altParams := altFVars.all
          subgoals[idx]!.mvarId!.assign (← mkForallFVars altParams (mkGoal res.expr))
          let context ← withLocalDecl `x .default ma fun x =>
            mkLambdaFVars #[x] (mkGoal x)
          let eqProof ← mkAppM ``congrArg #[context, res.proof?.get!]
          mkEqMPR eqProof (mkAppN subgoalHyps[idx]! altParams))
    let prf ← liftMetaM <| instantiateMVars prf
    mkLambdaFVars (#[a] ++ splitFVars ++ ss ++ #[post, epost, pre] ++ subgoalHyps) prf
  let prf ← instantiateMVars prf
  let res ← abstractMVars prf
  let type ← preprocessExpr (← Meta.inferType res.expr)
  let prf ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl prf

/-! ## Tests -/

section Test

open Lean.Elab.Tactic.Do Std.Do'

/-- Test helper: build `wp` head and all args for a given monad setup, then
    get the `SplitInfo` from `prog`, call `mkBackwardRuleForSplit`, and return
    the generated backward rule type. -/
private meta def testSplitBackwardRule
    (m Pred errTy monadInst instAL instEAL instWP : Expr) (prog : Expr) (excessArgs : Array Expr)
    : MetaM Expr := do
  let some splitInfo ← getSplitInfo? prog
    | throwError "testSplitBackwardRule: no split info for {indentExpr prog}"
  let wpHead := mkConst ``wp [.zero, .zero, .zero, .zero]
  let rule ← SymM.run do
    mkBackwardRuleForSplit splitInfo wpHead m Pred errTy monadInst instAL instEAL instWP excessArgs
  inferType rule.expr

/-- Set up StateM Nat monad infrastructure and run a test body. -/
private meta def withStateMNat (k : Expr → Expr → Expr → Expr → Expr → Expr → Expr → MetaM α) : MetaM α := do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let Pred ← mkArrow nat (mkSort 0)
  let errTy := mkConst ``EPost.nil
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instAL ← synthInstance (mkApp (mkConst ``Assertion [.zero]) Pred)
  let instEAL ← synthInstance (mkApp (mkConst ``Assertion [.zero]) errTy)
  let instWP ← synthInstance (mkAppN (mkConst ``WP [.zero, .zero, .zero, .zero]) #[m, Pred, errTy, monadM, instAL, instEAL])
  k m Pred errTy monadM instAL instEAL instWP

-- Test 1: ite split for StateM Nat
-- `ite c (alt₁ : StateM Nat Unit) (alt₂ : StateM Nat Unit)` with 1 excess arg
#eval! show MetaM Unit from withStateMNat fun m Pred errTy monadInst instAL instEAL instWP => do
  let nat := mkConst ``Nat
  let mUnit ← mkAppM ``StateM #[nat, mkConst ``Unit]
  withLocalDeclD `c (mkSort 0) fun c => do
  withLocalDecl `inst .instImplicit (← mkAppM ``Decidable #[c]) fun inst => do
  withLocalDeclD `alt₁ mUnit fun alt₁ => do
  withLocalDeclD `alt₂ mUnit fun alt₂ => do
  withLocalDeclD `s nat fun s => do
    -- @ite (StateM Nat Unit) c inst alt₁ alt₂
    let prog := mkAppN (mkConst ``ite [.succ .zero]) #[mUnit, c, inst, alt₁, alt₂]
    let ty ← testSplitBackwardRule m Pred errTy monadInst instAL instEAL instWP prog #[s]
    logInfo m!"Test 1 (ite, StateM Nat, n=1): {ty}"

-- Test 2: dite split for StateM Nat
-- `dite c (alt₁ : c → StateM Nat Unit) (alt₂ : ¬c → StateM Nat Unit)` with 1 excess arg
#eval! show MetaM Unit from withStateMNat fun m Pred errTy monadInst instAL instEAL instWP => do
  let nat := mkConst ``Nat
  let mUnit ← mkAppM ``StateM #[nat, mkConst ``Unit]
  withLocalDeclD `c (mkSort 0) fun c => do
  withLocalDecl `inst .instImplicit (← mkAppM ``Decidable #[c]) fun inst => do
  let cToM ← mkArrow c mUnit
  let notC ← mkAppM ``Not #[c]
  let notCToM ← mkArrow notC mUnit
  withLocalDeclD `alt₁ cToM fun alt₁ => do
  withLocalDeclD `alt₂ notCToM fun alt₂ => do
  withLocalDeclD `s nat fun s => do
    -- @dite (StateM Nat Unit) c inst alt₁ alt₂
    let prog := mkAppN (mkConst ``dite [.succ .zero]) #[mUnit, c, inst, alt₁, alt₂]
    let ty ← testSplitBackwardRule m Pred errTy monadInst instAL instEAL instWP prog #[s]
    logInfo m!"Test 2 (dite, StateM Nat, n=1): {ty}"

-- Test 3: Nat.casesOn matcher for StateM Nat
-- `match v with | 0 => alt₁ | n+1 => alt₂ n` with 1 excess arg
-- Uses an actual Lean `match` compiled to a matcher application.
private noncomputable def matchProg (v : Nat) (alt₁ : StateM Nat Unit) (alt₂ : Nat → StateM Nat Unit)
    : StateM Nat Unit :=
  match v with
  | 0 => alt₁
  | n+1 => alt₂ n

#eval! show MetaM Unit from withStateMNat fun m Pred errTy monadInst instAL instEAL instWP => do
  let nat := mkConst ``Nat
  let mUnit ← mkAppM ``StateM #[nat, mkConst ``Unit]
  withLocalDeclD `v nat fun v => do
  withLocalDeclD `alt₁ mUnit fun alt₁ => do
  let alt₂Ty ← mkArrow nat mUnit
  withLocalDeclD `alt₂ alt₂Ty fun alt₂ => do
  withLocalDeclD `s nat fun s => do
    -- Build the match expression by unfolding `matchProg`
    let prog ← whnf (mkAppN (mkConst ``matchProg) #[v, alt₁, alt₂])
    let ty ← testSplitBackwardRule m Pred errTy monadInst instAL instEAL instWP prog #[s]
    logInfo m!"Test 3 (match Nat, StateM Nat, n=1): {ty}"

end Test

end Loom.VCGen
