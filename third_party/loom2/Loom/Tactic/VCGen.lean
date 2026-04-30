/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
import Lean
import Loom.Tactic.Attr
import Loom.Tactic.Spec
import Loom.Tactic.Logic
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas
import Loom.WP.Lemmas
import Loom.Frame
import Loom.Tactic.ShareExt
import Loom.Tactic.Match
import Loom.Tactic.Intros
import Loom.Tactic.VCGenTime

open Lean Parser Meta Elab Tactic Sym Sym.Internal Loom Lean.Order Lean.Meta.Sym
open Loom.Tactic.SpecAttr
open Std.Do'
open Grind (GrindM)

namespace Loom

initialize registerTraceClass `Loom.Tactic.vcgen
initialize registerTraceClass `Loom.Tactic.vcgen.simp

inductive VCGen.dischargeTactic where
  | none
  | grind
  | tactic (tactic : Syntax)
  deriving Repr

def VCGen.dischargeTactic.isGrind : VCGen.dischargeTactic → Bool
  | .grind => true
  | _      => false

def VCGen.dischargeTactic.eval (goal : MVarId) : VCGen.dischargeTactic → MetaM (List MVarId)
  | .none => return [goal]
  | .grind => unreachable!
  | .tactic tac => do
    let (goals, _) ← runTactic goal tac
    return goals

/-! ## VCGen monad and caching -/

structure VCGen.Context where
  specThms     : SpecTheorems
  introRules   : IntroRules
  elimPreRule  : BackwardRule
  simpMethods  : Option Sym.Simp.Methods := none
  disch        : dischargeTactic := .none

structure VCGen.State where
  specBackwardRuleCache  : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  splitBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  logicBackwardRuleCache : Std.HashMap (Name × Array Expr × Nat) BackwardRule := {}
  simpState              : Sym.Simp.State := {}
  invariants             : Array MVarId := #[]
  vcs                    : Array MVarId := #[]

abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State GrindM)

namespace VCGen

/-! ## Backward rule construction -/

/-- Cached version of `tryMkBackwardRuleFromSpec`.
    Cache key: `(proof key, instWP, excessArgs.size)`. -/
def mkBackwardRuleFromSpecCached (specThm : SpecTheorem)
    (l instWP : Expr) (excessArgs : Array Expr)
    : OptionT VCGenM BackwardRule := do
    let key := (specThm.proof.key, instWP, excessArgs.size)
    let s := (← get).specBackwardRuleCache
    match s[key]? with
    | some rule => return rule
    | none =>
      let some rule ← (withNewMCtxDepth
          (tryMkBackwardRuleFromSpec specThm l instWP excessArgs).run : SymM _)
        | failure
      modify fun st => { st with specBackwardRuleCache := st.specBackwardRuleCache.insert key rule }
      return rule


open Lean.Elab.Tactic.Do in
def mkBackwardRuleForSplitCached
    (splitInfo : SplitInfo) (wpHead m l errTy monadInst instAL instEAL instWP : Expr)
    (excessArgs : Array Expr) : VCGenM BackwardRule := do
  let cacheKey := match splitInfo with
    | .ite .. => ``ite
    | .dite .. => ``dite
    | .matcher matcherApp => matcherApp.matcherName
  let s := (← get).splitBackwardRuleCache
  match s[(cacheKey, instWP, excessArgs.size)]? with
  | some rule => return rule
  | none =>
    let rule ← mkBackwardRuleForSplit splitInfo wpHead m l errTy monadInst instAL instEAL instWP excessArgs
    modify ({ · with splitBackwardRuleCache := s.insert (cacheKey, instWP, excessArgs.size) rule })
    return rule

def mkBackwardRuleForLogicCached
    (lop : LogicOp) (as excessArgs : Array Expr) (resultType? : Option Expr := none) : VCGenM BackwardRule := do
  let s := (← get).logicBackwardRuleCache
  let asTypes ← (as.mapM Sym.inferType : SymM (Array Expr))
  let key := (lop.toApplyLemma, asTypes, excessArgs.size)
  match s[key]? with
  | some rule => return rule
  | none =>
    let rule ← LogicOp.mkBackwardRule lop as excessArgs resultType?
    modify ({ · with logicBackwardRuleCache := s.insert key rule })
    return rule

/-! ## Simplification and intros -/

/-- Simplify `goal` with the given `methods`, threading `simpState` through
    `VCGenM`'s state to reuse the persistent cache across calls.
    Returns `none` if simp closes the goal; otherwise returns the (possibly
    unchanged) goal. -/
def VCGenM.simpGoal (methods : Sym.Simp.Methods) (goal : Grind.Goal)
    : VCGenM (Option Grind.Goal) := do
  let decl ← goal.mvarId.getDecl
  let (result, simpState') ← Sym.Simp.SimpM.run (Sym.Simp.simp decl.type)
    methods {} (← get).simpState
  modify fun s => { s with simpState := simpState' }
  match ← result.toSimpGoalResult goal.mvarId with
  | .closed       => return none
  | .goal mvarId' => return some { goal with mvarId := mvarId' }
  | .noProgress   => return some goal

/-- Simplify the goal with `Sym.Simp.simpTelescope`
    (if simp methods are configured), then intro forall-bound variables.
    Returns `none` if simp closes the goal. -/
def introsAndSimp (goal : Grind.Goal) : VCGenM (Option Grind.Goal) := do
  let mut goal := goal
  if let some methods := (← read).simpMethods then
    let some goal' ← VCGenM.simpGoal { methods with pre := Sym.Simp.simpTelescope } goal
      | return none
    goal := goal'
  if (← goal.mvarId.getType).isForall then
    let .goal _ goal' ← goal.intros #[] | failure
    goal := goal'
  return some goal

/-! ## Goal classification -/

/-- Result of trying to solve a single goal of the form `pre ⊑ wp prog post epost`. -/
inductive SolveResult where
  /-- The RHS was neither a WP goal nor a supported lattice goal. -/
  | noProgramOrLatticeFoundInTarget (T : Expr)
  /-- Don't know how to handle `e` in `pre ⊑ wp e post epost`. -/
  | noStrategyForProgram (e : Expr)
  /-- Did not find a spec for `e` in `pre ⊑ wp e post epost`. -/
  | noSpecFoundForProgram (e : Expr) (monad : Expr) (thms : Array SpecTheorem)
  /-- Successfully decomposed the goal. These are the subgoals. -/
  | goals (subgoals : List MVarId)

/-- High-level classifier for the RHS of a `pre ⊑ rhs` goal. -/
inductive GoalKind where
  /-- RHS is `True`; dischargeable via `le_top` or similar. -/
  | TrivialTrue
  /-- RHS is a concrete EPost component; stores selected component and its excess args. -/
  | EPostVC (relConst : Expr) (α inst : Expr) (pre : Expr) (epost : Expr) (excessArgs : Array Expr)
  /-- RHS is a lattice connective application (`meet`/`himp`/`pure`) with optional excess args. -/
  | Lattice (lop : LogicOp) (as : Array Expr) (excessArgs : Array Expr) (resultType? : Option Expr := none)
  /-- `pre ⊑ @wp ... (letE _ _ val body) appArgs post epost excessArgs`, non-dependent let. -/
  | Let (head : Expr) (m l errTy monadInst instAL instEAL instWP α post epost : Expr)
        (val body : Expr) (appArgs : Array Expr) (excessArgs : Array Expr)
  /-- `pre ⊑ @wp ... e ... excessArgs` where `e` is `ite`/`dite`/`match`. -/
  | Match (info : Do.SplitInfo) (head : Expr)
          (m l errTy monadInst instAL instEAL instWP : Expr)
          (e : Expr) (args : Array Expr) (excessArgs : Array Expr)
  /-- `pre ⊑ @wp ... e ... excessArgs` where `e.getAppFn` is `const`/`fvar` — apply a spec. -/
  | Spec (e : Expr) (m l instWP : Expr) (excessArgs : Array Expr)
  /-- RHS is a WP application but doesn't match Let/Match/Spec. -/
  | WP (e : Expr)
  /-- Lattice type is Prop and precondition is not `True`; intro the pre. -/
  | IntroPre
  /-- RHS is neither a recognized WP nor a recognized lattice connective. -/
  | Unknown

/-! ## Private helpers -/

/-- Get the `index`-th component from an `EPost` target. -/
private def mkEPostAtIndex (target : Expr) (index : Nat) : SymM Expr := do
  let mut curr := target
  for _ in [:index] do
    let_expr EPost.cons.mk _ _ _ tail := curr
      | throwError "Expected EPost.cons.mk, got {curr}"
    curr := tail
  let_expr EPost.cons.mk _ _ head _ := curr
    | throwError "Expected EPost.cons.mk, got {curr}"
  return head

/-- Peel a chain of `.tail` projections, returning the base `EPost` and the number of tails. -/
private partial def peelEPostTailChain (curr : Expr) (idx : Nat := 0) : Expr × Nat :=
  curr.consumeMData.withApp fun fn args =>
    if fn.isConstOf ``EPost.cons.tail && args.size > 0 then
      peelEPostTailChain args[args.size - 1]! (idx + 1)
    else
      (curr, idx)

/-! ## Core logic -/

/-- Classify the RHS of a `pre ⊑ rhs` goal. If the target is not in `⊑` form,
    falls back to classifying the target directly. -/
def classifyGoalKind (target : Expr) : VCGenM GoalKind := do
  match_expr target with
  | PartialOrder.rel α inst pre rhs =>

    if !pre.isConstOf ``True && α.isProp then return .IntroPre

    rhs.withApp fun head args => do
      match_expr head with
      | EPost.cons.head =>
        let some epostArg := args[2]?
          | return .Unknown
        let (epostTarget, index) := peelEPostTailChain epostArg
        let epost ← mkEPostAtIndex epostTarget index
        return .EPostVC target.getAppFn α inst pre epost (args.extract 3 args.size)
      | wp =>
        let_expr wp m l errTy monadInst instAL instEAL instWP α e post epost :=
          mkAppN head <| args.take 11
          | return .Unknown
        let excessArgs := args.extract 11 args.size
        if let .letE _x _ty val body _nonDep := e.getAppFn then
          return .Let head m l errTy monadInst instAL instEAL instWP α post epost
            val body e.getAppRevArgs excessArgs
        if let some info ← Do.getSplitInfo? e then
          return .Match info head m l errTy monadInst instAL instEAL instWP
            e args excessArgs
        if e.getAppFn.isConst || e.getAppFn.isFVar then
          return .Spec e m l instWP excessArgs
        return .WP e
      | meet =>
        let excessArgs := args.drop 4
        let as := args.extract 2 4
        return .Lattice .And as excessArgs
      | himp =>
        let excessArgs := args.drop 4
        let as := args.extract 2 4
        return .Lattice .Imp as excessArgs
      | CompleteLattice.pure =>
        let excessArgs := args.drop 3
        let as := args.extract 2 3
        return .Lattice .Pure as excessArgs args[0]!
      | _ => return .Unknown
  | _ => return .Unknown

/-- Main solve step for a goal of the form `pre ⊑ rhs`. -/
def solve (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  let mut goal := goal
  let mut target ← goal.getType
  if target.hasExprMVar then
    target ← instantiateMVars target
    goal ← goal.replaceTargetDefEq target
  let kind ← classifyGoalKind target
  match kind with
  | .TrivialTrue => do
      throwError "TrivialTrue not yet implemented in VCGen'"
  | .IntroPre => do
      goal ← introMeetPre (← read).introRules goal
      return .goals [goal]
  | .Lattice lop as excessArgs resultType? => do
      trace[Loom.Tactic.vcgen] "Applying logic rule for {target}. Excess args: {excessArgs}"
      let rule ← mkBackwardRuleForLogicCached lop as excessArgs resultType?
      let .goals goals ← rule.apply goal
        | throwError "Failed to apply logic rule at {indentExpr target}"
      return .goals goals
  | .Let head m l errTy monadInst instAL instEAL instWP α post epost val body appArgs excessArgs => do
      let body' ← Sym.instantiateRevBetaS body #[val]
      let e' ← mkAppRevS body' appArgs
      let wp ← mkAppS₁₁ head m l errTy monadInst instAL instEAL instWP α e' post epost
      let rhs ← mkAppNS wp excessArgs
      let_expr PartialOrder.rel l cl pre _rhs := target
        | throwError "expected ⊑ goal but got {target}"
      let newTarget ← mkAppNS (mkConst ``PartialOrder.rel) #[l, cl, pre, rhs]
      goal ← goal.replaceTargetDefEq newTarget
      return .goals [goal]
  | .Match info head m l errTy monadInst instAL instEAL instWP e args excessArgs => do
      -- For matchers, try reduceRecMatcher? to reduce known discriminants
      if let .matcher .. := info then
        if let some e' ← reduceRecMatcher? e then
          trace[Loom.Tactic.vcgen] "reduceRecMatcher simplified match in {e}"
          let e' ← shareCommon e'
          let rhs ← mkAppNS head <| args.set! 8 e'
          let relArgs := target.getAppArgs
          let newTarget ← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) rhs)
          goal ← goal.replaceTargetDefEq newTarget
          return .goals [goal]
      trace[Loom.Tactic.vcgen] "Applying split rule for {e}. Excess args: {excessArgs}"
      let rule ← mkBackwardRuleForSplitCached info head m l errTy monadInst instAL instEAL instWP excessArgs
      let .goals goals ← rule.apply goal
        | throwError "Failed to apply split rule for {indentExpr e}"
      let goals ← goals.mapM fun g => do
        let .goal _ g ← Sym.intros g
          | throwError "Failed to intro split parameters"
        return g
      return .goals goals
  | .Spec e m l instWP excessArgs => do
      trace[Loom.Tactic.vcgen] "Applying a spec for {e}. Excess args: {excessArgs}"
      match ← findSpecs (← read).specThms e with
      | .error thms => return .noSpecFoundForProgram e m thms
      | .ok thm =>
      trace[Loom.Tactic.vcgen] "Spec for {e}: {thm.proof}"
      let some rule ← (mkBackwardRuleFromSpecCached thm l instWP excessArgs).run
        | return .noSpecFoundForProgram e m #[thm]
      trace[Loom.Tactic.vcgen] "Applying rule {rule.pattern.pattern} at {target}"
      let .goals goals ← rule.apply goal
        | throwError "Failed to apply rule {thm.proof} for {indentExpr e}"
      return .goals goals
  | .WP e => do
      return .noStrategyForProgram e
  | .EPostVC relConst α inst pre epost excessArgs => do
      let rhs ← betaRevS epost excessArgs.reverse
      let newTarget ← mkAppNS relConst #[α, inst, pre, rhs]
      goal ← goal.replaceTargetDefEq newTarget
      return .goals [goal]
  | _ =>
    return .noProgramOrLatticeFoundInTarget target

/-- Emit a VC for a goal that cannot be further decomposed.
    If the goal is `True ⊑ x` (on Prop), first eliminate the `True ⊑` wrapper. -/
meta def emitVC (goal : Grind.Goal) : VCGenM Unit := do
  let mut goal := goal
  let ty ← goal.mvarId.getType
  if let some (_, _, Expr.const ``True _, _) := ty.app4? ``PartialOrder.rel then
    let rule := (← read).elimPreRule
    let .goals [goal'] ← goal.apply rule
      | throwError "Failed to apply elim_pre rule"
    goal := goal'
  let disch := (← read).disch
  let mut goals := [goal.mvarId]
  match disch with
  | .grind =>
    match ← goal.timedTryGrind with
    | none => goals := []
    | some sub => goals := [sub]
  | _ => goals ← disch.eval goal.mvarId
  for g in goals do g.setKind .syntheticOpaque
  modify fun s => { s with vcs := s.vcs ++ goals }

/-- Main work loop: decompose the goal repeatedly. -/
meta def work (goal : MVarId) : VCGenM Unit := do
  let goal ← Grind.mkGoal goal
  let rules := (← read).introRules
  let goal ← unfoldTriple rules goal
  let mut worklist := Std.Queue.empty.enqueue goal
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    let some goal ← introsAndSimp goal | continue
    -- Unfold Triple goals that arise from subgoals (e.g., loop invariant specs)
    let goal ← unfoldTriple rules goal
    let res ← solve goal.mvarId
    match res with
    | .noProgramOrLatticeFoundInTarget .. =>
      emitVC goal
    | .noSpecFoundForProgram prog _ #[] =>
      throwError "No spec found for program {prog}."
    | .noSpecFoundForProgram prog monad thms =>
      throwError "No spec matching the monad {monad} found for program {prog}. Candidates were {thms.map (·.proof)}."
    | .noStrategyForProgram prog =>
      throwError "Did not know how to decompose weakest precondition for {prog}"
    | .goals subgoals =>
      -- if we have multiple subgoals, before running the VCGen
      -- we need to share the grind context first.
      -- TODO: I am afraid of excessive copying of the grind context.
      let mut grindSharedGoal := goal
      if (← read).disch.isGrind && subgoals.length > 1 then
        grindSharedGoal ← goal.timedInternalizeAll
      worklist := worklist.enqueueAll <| subgoals.map ({ grindSharedGoal with mvarId := · })

public structure Result where
  invariants : Array MVarId
  vcs : Array MVarId

/-- Generate VCs for a goal of the form `Triple pre e post epost`, keeping subgoals in `⊑` form. -/
public meta partial def main (goal : MVarId) (ctx : Context) : GrindM Result := do
  let doTime := vcgen.time.get (← getOptions)
  if doTime then vcgenTimingRef.set {}
  let ((), state) ← StateRefT'.run (ReaderT.run (work goal) ctx) {}
  for h : idx in [:state.invariants.size] do
    let mv := state.invariants[idx]
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  for h : idx in [:state.vcs.size] do
    let mv := state.vcs[idx]
    mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
  return { invariants := state.invariants, vcs := state.vcs }

syntax (name := mvcgen') "mvcgen'"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")?
  (&" simplifying_assumptions" (ppSpace colGt ident)? (" [" ident,* "]")?)?
  (&" with " tactic)? : tactic

def elabDischTactic (withClause : Syntax) : MetaM VCGen.dischargeTactic := do
  let .some tac := withClause[1]? | return .none
  if tac.isMissing then return .none
  return if tac.getKind == ``Parser.Tactic.grind then .grind else .tactic tac

/-- Parse grind configuration from the `with grind ...` clause and build `Grind.Params`.
Overrides the internal simp step limit to accommodate large unrolled goals. -/
private meta def elabGrindParams (grindStx : Syntax) (goal : MVarId) : TacticM Grind.Params := do
  let `(tactic| grind $config:optConfig $[only%$only]? $[ [$grindParams:grindParam,*] ]? $[=> $_:grindSeq]?) := grindStx
    | throwUnsupportedSyntax
  let grindConfig ← elabGrindConfig config
  let params ← mkGrindParams grindConfig only.isSome (grindParams.getD {}).getElems goal
  -- FIXME: Expose grind's internal simp step limit as a user-facing option instead of hardcoding.
  -- Grind's `simpCore` uses the default `Simp.Config.maxSteps` (100k) which is too low for large
  -- unrolled goals (fails around n=400 for GetThrowSet).
  return { params with norm := ← params.norm.setConfig { params.norm.config with maxSteps := 10000000 } }


-- /--
/--
Build `Sym.Simp.Methods` from a variant name and extra theorems.
Supports the anonymous (default) variant. Named variants require a public
`elabSimpMethods` API in `Lean.Elab.Tactic.Grind.Sym` (see TODO below).
-/
private meta def elabSymSimpParts
    (variantId? : Option (TSyntax `ident))
    (extraIds? : Option (Array (TSyntax `ident)))
    : TacticM Sym.Simp.Methods := do
  let variantName := variantId?.map (·.getId) |>.getD .anonymous
  if !variantName.isAnonymous then
    -- TODO: `resolveExtraTheorems`, `elabVariant`, and `elabSymSimproc` in
    -- `Lean.Elab.Tactic.Grind.Sym` are module-private (non-`public section`).
    -- To support named variants here, we need a public API such as:
    --   `public def elabSymSimp (syn : Syntax) : GrindTacticM (Sym.Simp.Methods × ...)`
    -- exposed from that module, plus a lightweight `GrindTacticM` runner
    -- (the simproc elaborators only use `CoreM`/`MetaM` capabilities).
    throwError "named Sym.simp variants are not yet supported in `mvcgen'`; \
      use `mvcgen' simplifying_assumptions [thm₁, thm₂, ...]` with the default variant instead"
  -- Resolve extra theorems (local hypotheses first, then global constants)
  let mut extraThms : Array Simp.Theorem := #[]
  if let some ids := extraIds? then
    for id in ids do
      let declName ← realizeGlobalConstNoOverload id
      extraThms := extraThms.push (← Simp.mkTheoremFromDecl declName)
  -- Build methods
  let pre := Simp.simpControl >> Simp.simpArrowTelescope
  let mut post : Sym.Simp.Simproc := Simp.evalGround
  unless extraThms.isEmpty do
    let mut thms : Simp.Theorems := {}
    for thm in extraThms do thms := thms.insert thm
    post := post >> thms.rewrite
  return { pre, post }

private meta def elabSimplifyingAssumptions (simpClause : Syntax) : OptionT TacticM Sym.Simp.Methods := do
  if simpClause.getNumArgs == 0 then failure
  let variantId? := if simpClause[1].getNumArgs != 0 then some ⟨simpClause[1][0]⟩ else none
  let extraIds? := if simpClause[2].getNumArgs != 0
    then some (simpClause[2][1].getSepArgs.map (⟨·⟩)) else none
  elabSymSimpParts variantId? extraIds?

@[tactic mvcgen']
public meta def VCGen.elab : Tactic := fun stx => withMainContext do
  let ctx ← getSpecTheorems
  let goal ← getMainGoal

  let withClause := stx[3]
  let hasWithClause := withClause.getNumArgs != 0
  let mut disch ← elabDischTactic withClause
  let mut params ← Grind.mkDefaultParams {}

  if let .grind := disch then
    let grindStx := withClause[1]
    params ← elabGrindParams grindStx goal

  let simpMethods ← elabSimplifyingAssumptions stx[2]
  -- dbg_trace "disch: {repr disch}"
  let { invariants, vcs } ← Grind.GrindM.run (params := params) do
    let migratedCtx ← migrateSpecTheoremsDatabase ctx
    let introRules ← IntroRules.mk'
    let elimPreRule ← mkBackwardRuleFromDecl ``prop_pre_elim
    VCGen.main goal { specThms := migratedCtx, introRules, elimPreRule, simpMethods, disch }
  replaceMainGoal (invariants ++ vcs).toList

end VCGen

end Loom
