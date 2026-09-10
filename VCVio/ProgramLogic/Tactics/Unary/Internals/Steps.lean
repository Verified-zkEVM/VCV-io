/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import VCVio.ProgramLogic.Tactics.Common
public import VCVio.ProgramLogic.Relational.Basic
public meta import VCVio.ProgramLogic.Tactics.Relational.Internals
public import Loom.Triple.SpecLemmas
public meta import VCVio.ProgramLogic.Tactics.Unary.Internals.Rules
import all VCVio.ProgramLogic.Tactics.Unary.Internals.Rules

/-!
# Unary VCGen step implementations
-/

public meta section

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic
namespace TacticInternals
namespace Unary

universe u v

/-! ## `vcspec_simp` normalization set

Centralized registration of the transformer-`wp` peel lemmas, `*.run`
projections, monadic-algebra rewrites, and the `Loom.wp_eq_mAlgOrdered_wp`
bridges that the unary tactic uses to expose spec-applicable goal shapes.
The single simp set is consumed by `runVCSpecSimp`. New normalization rewrites
should be tagged here (or at definition) rather than inserted into a
tactic-local `simp only [...]` list. -/

attribute [vcspec_simp]
  -- `Std.Do'` transformer apply_wp / `*.run` peeling
  Std.Do'.StateT.apply_wp
  Std.Do'.ReaderT.apply_wp
  Std.Do'.WriterT.apply_wp
  StateT.run_bind StateT.run_pure StateT.run_get StateT.run_set
  StateT.run_modifyGet StateT.run_monadLift StateT.run_map StateT.run_lift
  ReaderT.run_bind ReaderT.run_pure ReaderT.run_monadLift ReaderT.run_read
  ReaderT.run_map
  WriterT.run_bind WriterT.run_pure WriterT.run_tell WriterT.run_monadLift
  WriterT.run_liftM WriterT.run_map
  OptionT.run_bind OptionT.run_pure OptionT.run_lift OptionT.run_failure
  OptionT.run_map
  ExceptT.run_bind ExceptT.run_pure ExceptT.run_lift ExceptT.run_throw
  ExceptT.run_map
  -- VCVio Loom bridges and the underlying quantitative `MAlgOrdered.wp`
  OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp
  OracleComp.ProgramLogic.Loom.wp_eq_mAlgOrdered_wp_epost
  MAlgOrdered.wp_bind MAlgOrdered.wp_pure MAlgOrdered.wp_map
  -- VCVio per-transformer `Loom.wp_*` peeling lemmas
  OracleComp.ProgramLogic.Loom.wp_StateT_bind
  OracleComp.ProgramLogic.Loom.wp_StateT_bind'
  OracleComp.ProgramLogic.Loom.wp_StateT_pure
  OracleComp.ProgramLogic.Loom.wp_StateT_get
  OracleComp.ProgramLogic.Loom.wp_StateT_set
  OracleComp.ProgramLogic.Loom.wp_StateT_modifyGet
  OracleComp.ProgramLogic.Loom.wp_StateT_monadLift
  OracleComp.ProgramLogic.Loom.wp_OptionT_bind
  OracleComp.ProgramLogic.Loom.wp_OptionT_pure
  OracleComp.ProgramLogic.Loom.wp_OptionT_failure
  OracleComp.ProgramLogic.Loom.wp_OptionT_monadLift
  OracleComp.ProgramLogic.Loom.wp_OptionT_lift
  OracleComp.ProgramLogic.Loom.wp_OptionT_map
  OracleComp.ProgramLogic.Loom.wp_ExceptT_bind
  OracleComp.ProgramLogic.Loom.wp_ExceptT_pure
  OracleComp.ProgramLogic.Loom.wp_ExceptT_throw
  OracleComp.ProgramLogic.Loom.wp_ExceptT_monadLift
  OracleComp.ProgramLogic.Loom.wp_ReaderT_bind
  OracleComp.ProgramLogic.Loom.wp_ReaderT_pure
  OracleComp.ProgramLogic.Loom.wp_ReaderT_read
  OracleComp.ProgramLogic.Loom.wp_ReaderT_monadLift
  OracleComp.ProgramLogic.Loom.WriterT.wp_bind
  OracleComp.ProgramLogic.Loom.WriterT.wp_pure
  OracleComp.ProgramLogic.Loom.WriterT.wp_tell
  OracleComp.ProgramLogic.Loom.WriterT.wp_monadLift
  OracleComp.ProgramLogic.Loom.WriterT.wp_map
  -- VCVio transformer-internal layer lemmas from `Unary.Internals.Rules`
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_StateT_get_layer
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_StateT_get_layer'
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_StateT_run_get_layer
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_StateT_run_get_layer'
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_StateT_set_layer
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_StateT_run_set_layer
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_StateT_run_set_layer'
  OracleComp.ProgramLogic.TacticInternals.Unary.mAlgOrdered_wp_OptionT_run_StateT_get
  OracleComp.ProgramLogic.TacticInternals.Unary.mAlgOrdered_wp_OptionT_run_StateT_set
  OracleComp.ProgramLogic.TacticInternals.Unary.mAlgOrdered_wp_OptionT_run_lift
  mAlgOrdered_wp_OptionT_run_StateT_monadLift_lift
  mAlgOrdered_wp_OptionT_run_StateT_monadLift_lift_map
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_StateT_OptionT_monadLift_lift
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_StateT_map_layer
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_ReaderT_read_layer
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_ReaderT_read_layer'
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_ReaderT_run_read_layer
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_ReaderT_run_read_layer'
  OracleComp.ProgramLogic.TacticInternals.Unary.wp_ReaderT_map_layer
  -- Algebraic monad/`EPost`/scalar rewrites used by both peel and close passes
  Std.Do'.EPost.cons.pushOption
  Std.Do'.EPost.cons.pushExcept
  Option.elimM
  pure_bind
  bind_pure_comp
  bind_map_left
  map_bind
  bind_assoc
  map_pure
  Functor.map_map
  MonadLift.monadLift
  monadLift_self
  monadLift_eq_self
  one_mul
  mul_one
  mul_assoc

private def mkVCGenPlannedStep (label replayText : String) (run : TacticM Bool) : PlannedStep :=
  { label, replayText, run }

private def hasProbGoal (target : Expr) : Bool :=
  (findAppWithHead? ``probEvent target).isSome || (findAppWithHead? ``probOutput target).isSome

/-- Report why the current weakest-precondition goal admits no selected structural step. -/
def throwWpStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match wpGoalComp? target with
  | none =>
      throwError "vcstep: expected a goal containing `wp`; got:{indentExpr target}"
  | some comp =>
      let comp ← instantiateMVars comp
      throwError
        "vcstep: found a `wp` goal, but none of the current single-step rules apply to:\n\
        {indentExpr comp}\n\
        Current rules handle bind, pure, `replicate`, `List.mapM`, `List.foldlM`, query, `if`, \
        uniform sampling, `map`, `simulateQ`, `simulateQ ... run'`, and `liftComp`."

/-- Apply a unary structural rule using the supplied intermediate assertion. -/
def runHoareStepRuleUsing (cut : TSyntax `term) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  match tripleGoalComp? target with
  | some comp =>
      let comp ← instantiateMVars comp
      if isBindExpr comp then
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.triple_bind (cut := $cut)))
      else
        return false
  | none => return false

/-- Check whether an expression (possibly under `∀` quantifiers and `mdata`) contains
 a unary triple application as its head. -/
private def hasTripleHead (e : Expr) : Bool :=
  let rec go : Expr → Bool
    | .forallE _ _ body _ => go body
    | .mdata _ e => go e
    | e => (tripleGoalComp? e).isSome
  go e

/-- Extract the head function of the computation argument from a unary triple
application, after stripping `∀` quantifiers and `mdata`. -/
private def tripleCompFn? (e : Expr) : Option Expr :=
  let rec go : Expr → Option Expr
    | .forallE _ _ body _ => go body
    | .mdata _ e => go e
    | e => do
        let comp ← tripleGoalComp? e
        some comp.consumeMData.getAppFn
  go e

/-- Try to close a `Triple` goal by targeted application of local hypotheses
whose type (possibly under `∀` quantifiers) has `Triple` as head and whose
computation argument structurally matches the goal's computation.
Much faster than `assumption` + `solve_by_elim` when the goal has unresolved metavariables,
because it skips expensive `isDefEq` checks against non-matching hypotheses. -/
private def tryApplyTripleHyp : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some goalCompFn := tripleCompFn? target | return false
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hypType ← instantiateMVars ldecl.type
    unless hasTripleHead hypType do continue
    let some hypCompFn := tripleCompFn? hypType | continue
    unless goalCompFn == hypCompFn do continue
    if ← tryEvalTacticSyntax (← `(tactic| exact $(mkIdent ldecl.userName))) then
      return true
    if hypType.isForall then
      let saved ← saveState
      if ← tryEvalTacticSyntax
          (← `(tactic| apply $(mkIdent ldecl.userName) <;> assumption)) then
        return true
      saved.restore
  return false

/-- Peel known transformer `wp` layers in the current goal via the cached
`vcspec_simp` simp set. Always succeeds (errors and unchanged-goal results are
swallowed), since callers always `discard` the outcome and rely on later
structural dispatch to decide whether the goal can close. -/
private def peelKnownTransformerWPInGoal : TacticM Unit :=
  runVCSpecSimp

/-- Class-method unfolds used by the close passes to expose `apply_wp` /
`*.run` projections through overloaded `Monad{State,Reader,Writer}Of` /
`StateT.{get,set,lift}` calls, plus the `Lean.Order.PartialOrder.rel` head
needed for the final `le_refl` step. Kept inline (rather than in
`vcspec_simp`) to avoid eager class-projection unfolding outside of close
contexts. -/
private def runVCSpecCloseUnfolds : TacticM Unit := do
  discard <| tryEvalTacticSyntax (← `(tactic|
    simp only [Lean.Order.PartialOrder.rel,
      MonadStateOf.get, MonadStateOf.set, MonadReaderOf.read, MonadWriter.tell,
      StateT.get, StateT.set, StateT.lift, ReaderT.read, WriterT.tell]))

private def tryCloseNormalizedTransformerWP : TacticM Bool := do
  let saved ← saveState
  let target ← instantiateMVars (← getMainTarget)
  unless (tripleGoalComp? target).isSome do
    return false
  -- Overloaded operations such as `MonadStateOf.get` may not expose their
  -- concrete transformer type until the triple theorem has been applied.
  -- Speculate cheaply, then restore if the layer peeler cannot close.
  if ← tryEvalTacticSyntax (← `(tactic| refine Std.Do'.Triple.iff.mpr ?_)) then
    discard <| tryEvalTacticSyntax (← `(tactic| repeat intro _))
    runVCSpecCloseUnfolds
    runVCSpecSimp
    if (← getGoals).isEmpty then
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      return true
    if ← tryEvalTacticSyntax (← `(tactic| exact le_refl _)) then
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      return true
    runVCSpecCloseUnfolds
    runVCSpecSimp
    discard <| tryEvalTacticSyntax (← `(tactic| repeat intro _))
    if (← getGoals).isEmpty then
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      return true
    if ← tryEvalTacticSyntax (← `(tactic| exact le_refl _)) then
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      return true
  saved.restore
  return false

private def tryApplySpecThenPeel (stx : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  if ← tryEvalTacticSyntax stx then
    discard <| tryEvalTacticSyntax (← `(tactic| repeat intro _))
    peelKnownTransformerWPInGoal
    discard <| tryEvalTacticSyntax (← `(tactic| repeat intro _))
    runVCSpecCloseUnfolds
    runVCSpecSimp
    if (← getGoals).isEmpty then
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      return true
    if ← tryEvalTacticSyntax (← `(tactic| exact le_refl _)) then
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      return true
  saved.restore
  return false

/-- Try to close the current goal using only immediate local information.
This is intentionally cheap: it is used while speculating on `triple_bind`, so it must not
launch expensive proof search on goals with unresolved cut metavariables. -/
def tryCloseSpecGoalImmediate : TacticM Bool := do
  tryApplyTripleHyp <||>
  tryCloseNormalizedTransformerWP <||>
  tryApplySpecThenPeel (← `(tactic| apply
    OracleComp.ProgramLogic.TacticInternals.Unary.stdDoTriple_StateT_get_of_rel)) <||>
  tryApplySpecThenPeel (← `(tactic| apply
    OracleComp.ProgramLogic.TacticInternals.Unary.stdDoTriple_ReaderT_read_of_rel)) <||>
  tryApplySpecThenPeel (← `(tactic| apply Std.Do'.Spec.get_StateT)) <||>
  tryApplySpecThenPeel (← `(tactic| apply Std.Do'.Spec.set_StateT)) <||>
  tryApplySpecThenPeel (← `(tactic| apply Std.Do'.Spec.modifyGet_StateT)) <||>
  tryApplySpecThenPeel (← `(tactic| apply Std.Do'.Spec.monadLift_StateT)) <||>
  tryApplySpecThenPeel (← `(tactic| apply Std.Do'.Spec.read_ReaderT)) <||>
  tryApplySpecThenPeel (← `(tactic| apply Std.Do'.Spec.monadLift_ReaderT)) <||>
  tryEvalTacticSyntax (← `(tactic| assumption)) <||>
  tryEvalTacticSyntax (← `(tactic| solve_by_elim (maxDepth := 2))) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_pure _ _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_zero _ _)) <||>
  tryEvalTacticSyntax (← `(tactic| exact le_refl _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_ofLE le_rfl))

/-- Try bounded local proof search on a closed goal.
We only invoke `solve_by_elim` once the target has no unresolved expression metavariables; this
avoids pathological search on speculative intermediate cuts introduced by `triple_bind`. -/
def tryCloseSpecGoalSearch : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if target.hasExprMVar then
    return false
  tryEvalTacticSyntax (← `(tactic| (
    repeat intro
    simp only [OracleComp.ProgramLogic.triple_iff_le_wp] at *
    solve_by_elim (maxDepth := 6) [OracleComp.ProgramLogic.wp_mono, le_trans]
  )))

private def closeTheoremStepGoals : TacticM Unit := do
  let goals ← getGoals
  let mut remaining : List MVarId := []
  for goal in goals do
    if ← goal.isAssigned then continue
    setGoals [goal]
    unless ← tryCloseSpecGoalImmediate do
      remaining := remaining ++ [goal]
  setGoals remaining
  unless remaining.isEmpty do
    discard <| tryEvalTacticSyntax (← `(tactic|
      all_goals first
        | assumption
        | simp [Lean.Order.PartialOrder.rel]
        | (repeat intro; split_ifs <;> simp_all [Lean.Order.PartialOrder.rel])
        | (
            repeat intro
            simp only [OracleComp.ProgramLogic.triple_iff_le_wp] at *
            solve_by_elim (maxDepth := 4) [OracleComp.ProgramLogic.wp_mono, le_trans]
          )))

private def runVCGenStepWithTheoremDirect
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let saved ← saveState
  let ok ←
    match ← observing? do
      evalTactic (← `(tactic| apply $thm))
      closeTheoremStepGoals
    with
    | some _ => pure true
    | none => pure false
  if ok && (!(requireClosed) || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

private def runVCGenStepWithTheoremConseq
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  unless (tripleGoalComp? target).isSome do
    return false
  let saved ← saveState
  let ok ←
    match ← observing? do
      evalTactic (← `(tactic| refine OracleComp.ProgramLogic.triple_conseq le_rfl ?_ $thm))
      closeTheoremStepGoals
    with
    | some _ => pure true
    | none => pure false
  if ok && (!(requireClosed) || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

/-- Apply a `@[vcspec]` unary rule to the current goal.
Default `vcstep` first tries the cached rule directly. For folded unary
`Triple` goals, a global declaration can also be applied under `triple_conseq`,
which lets a registered concrete postcondition theorem feed a weaker goal
postcondition. -/
private def runUnaryVCSpecRule
    (entry : VCSpecEntry) (requireClosed : Bool := false) : TacticM Bool := do
  if entry.kind == .unaryWP then
    let saved ← saveState
    let ok ←
      match ← observing? do
        unless ← runVCSpecEntryRawUnaryConsequence entry do
          throwError "vcstep: raw unary `@[vcspec]` consequence did not apply"
        closeTheoremStepGoals
      with
      | some _ => pure true
      | none => pure false
    if ok && (!(requireClosed) || (← getGoals).isEmpty) then
      return true
    saved.restore
  let saved ← saveState
  let ok ←
    match ← observing? do
      unless ← runVCSpecEntryCachedBackward entry do
        throwError "vcstep: registered `@[vcspec]` rule did not apply"
      closeTheoremStepGoals
    with
    | some _ => pure true
    | none => pure false
  if ok && (!(requireClosed) || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false

/-- Apply an explicit unary theorem/assumption step and try to close any easy side goals.
When `requireClosed` is true, the step only succeeds if no goals remain afterwards. -/
def runVCGenStepWithTheorem (thm : TSyntax `term) (requireClosed : Bool := false) :
    TacticM Bool := do
  if ← runVCGenStepWithTheoremDirect thm requireClosed then
    return true
  runVCGenStepWithTheoremConseq thm requireClosed

/-- Try to close the current goal (typically a `Triple` subgoal) using direct hypotheses,
canonical leaf rules, or bounded local consequence search. -/
def tryCloseSpecGoal : TacticM Bool := do
  tryCloseSpecGoalImmediate <||> tryCloseSpecGoalSearch

/-- Normalize Loom's unary triple head to VCVio's quantitative `Triple` abbrev.

The two goals are definitionally equal for `OracleComp` with the no-exception
postcondition, but proof terms produced directly against the `Std.Do'.Triple`
head can trip Lean's kernel on anonymous proofs. Normalizing before structural
steps keeps the Loom notation surface while making the unary tactic operate on
its historical canonical head. -/
private def normalizeStdDoTripleGoal : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  unless (findAppWithHead? ``Std.Do'.Triple target).isSome do
    return false
  tryEvalTacticSyntax (← `(tactic| change OracleComp.ProgramLogic.Triple _ _ _))

/-- Finish-only closure step: includes the support-sensitive leaf rules that are too expensive
for the default `vcstep` hot path. -/
def tryCloseSpecGoalFinal : TacticM Bool := do
  tryApplyTripleHyp <||>
  tryCloseNormalizedTransformerWP <||>
  tryEvalTacticSyntax (← `(tactic| assumption)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_pure _ _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_zero _ _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    classical
    exact OracleComp.ProgramLogic.triple_support _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_propInd_of_support _ _ (by assumption))) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_probEvent_eq_one _ _ (by assumption))) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_probOutput_eq_one _ _ (by assumption))) <||>
  tryEvalTacticSyntax (← `(tactic| exact le_refl _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.triple_ofLE le_rfl)) <||>
  tryCloseSpecGoalSearch

/-- Run one bounded finish/closure pass across all current goals. -/
def runVCGenClosePass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    if ← withVCGenCloseTiming tryCloseSpecGoalFinal then
      progress := true
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals ++ [goal]
  setGoals newGoals
  return progress

/-- Try to decompose a `match` expression in the computation by case-splitting
on its discriminant(s). Only fires when the computation is a compiled matcher
(detected via `matchMatcherApp?`). Delegates to `split` which handles the actual
case analysis. -/
def tryMatchDecomp (comp : Expr) : TacticM Bool := do
  let some _ ← Lean.Meta.matchMatcherApp? comp | return false
  tryEvalTacticSyntax (← `(tactic| split))

/-- Check if an expression is a lambda whose body does not use the bound variable
(i.e. a constant function `fun _ => c`). -/
def isConstantLambda (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ body _ => !body.hasLooseBVar 0
  | _ => false

/-- Try the strongest automatic bind step: `triple_bind` plus immediate closure of the
spec side-goal. -/
def tryBindImmediate (comp : Expr) : TacticM Bool := do
  if !isBindExpr comp then
    return false
  match ← observing? do
    evalTactic (← `(tactic|
      first
        | apply OracleComp.ProgramLogic.triple_bind
        | apply Std.Do'.Triple.bind))
    unless ← tryCloseSpecGoalImmediate do throwError "" with
  | some _ => return true
  | none => return false

/-- Try only the automatic loop-invariant rules, without the structural fallback rules. -/
def tryLoopInvariantRuleAuto (comp : Expr) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, _comp, post) := tripleGoalParts? target | return false
  if isReplicateHead comp then
    if isConstantLambda post then
      match ← observing? do
        evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_replicate_inv))
        unless ← tryCloseSpecGoalImmediate do throwError "" with
      | some _ => return true
      | none => pure ()
  if isListFoldlMHead comp then
    match ← observing? do
      evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_list_foldlM_inv))
      unless ← tryCloseSpecGoalImmediate do throwError "" with
    | some _ => return true
    | none => pure ()
  if isListMapMHead comp then
    if isConstantLambda post then
      match ← observing? do
        evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_list_mapM_inv))
        unless ← tryCloseSpecGoalImmediate do throwError "" with
      | some _ => return true
      | none => pure ()
  return false

/-- Try only the structural loop fallback rules (`succ` / `cons`) after invariant search. -/
def tryLoopFallback (comp : Expr) : TacticM Bool := do
  if isReplicateHead comp then
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.triple_replicate_succ)) then
      return true
  if isListFoldlMHead comp then
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.triple_list_foldlM_cons)) then
      return true
  if isListMapMHead comp then
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.triple_list_mapM_cons)) then
      return true
  return false

/-- Apply a loop invariant rule with an explicitly provided invariant. -/
def runLoopInvExplicit (inv : TSyntax `term) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  match tripleGoalComp? target with
  | none => return false
  | some comp =>
    let comp ← whnfReducible (← instantiateMVars comp)
    if isReplicateHead comp then
      tryEvalTacticSyntax (← `(tactic|
        refine OracleComp.ProgramLogic.triple_replicate (I := $inv) ?_ ?_ ?_))
    else if isListFoldlMHead comp then
      tryEvalTacticSyntax (← `(tactic|
        refine OracleComp.ProgramLogic.triple_list_foldlM (I := $inv) ?_ ?_ ?_))
    else if isListMapMHead comp then
      tryEvalTacticSyntax (← `(tactic|
        refine OracleComp.ProgramLogic.triple_list_mapM (I := $inv) ?_ ?_ ?_))
    else
      return false

/-- Find the local hypotheses that work as explicit bind cuts. -/
def findHoareCutHintCandidates : TacticM (Array Name) :=
  withVCGenLocalHintTiming <| withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some comp := tripleGoalComp? target | return #[]
    let comp ← whnfReducible (← instantiateMVars comp)
    unless isBindExpr comp do return #[]
    let mut found : Array Name := #[]
    for localDecl in ← getLCtx do
      unless localDecl.isImplementationDetail do
        let name := localDecl.userName
        if isUsableBinderName name then
          let type ← instantiateMVars localDecl.type
          unless type.isSort do
            let saved ← saveState
            let ok ← runHoareStepRuleUsing (mkIdent name)
            saved.restore
            if ok then
              found := found.push name
    return found

/-- Find the unique local hypothesis that works as an explicit bind cut.
Returns `none` if there are 0 or ≥ 2 viable candidates. -/
def findUniqueHoareCutHint? : TacticM (Option Name) := do
  let found ← findHoareCutHintCandidates
  return found.toList.head? >>= fun first =>
    if found.size = 1 then some first else none

/-- Find the local hypotheses that work as explicit loop invariants. -/
def findLoopInvHintCandidates : TacticM (Array Name) :=
  withVCGenLocalHintTiming <| withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some comp := tripleGoalComp? target | return #[]
    let comp ← whnfReducible (← instantiateMVars comp)
    unless isReplicateHead comp || isListFoldlMHead comp || isListMapMHead comp do
      return #[]
    let mut found : Array Name := #[]
    for localDecl in ← getLCtx do
      unless localDecl.isImplementationDetail do
        let name := localDecl.userName
        if isUsableBinderName name then
          let type ← instantiateMVars localDecl.type
          unless type.isSort do
            let saved ← saveState
            let ok ← runLoopInvExplicit (mkIdent name)
            saved.restore
            if ok then
              found := found.push name
    return found

/-- Find the unique local hypothesis that works as an explicit loop invariant.
Returns `none` if there are 0 or ≥ 2 viable candidates. -/
def findUniqueLoopInvHint? : TacticM (Option Name) := do
  let found ← findLoopInvHintCandidates
  return found.toList.head? >>= fun first =>
    if found.size = 1 then some first else none

private def potentialLocalHintNames : TacticM (Array Name) := withMainContext do
  let mut names : Array Name := #[]
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let name := localDecl.userName
      if isUsableBinderName name then
        let type ← instantiateMVars localDecl.type
        unless type.isSort do
          names := names.push name
  return names

private def unaryGoalKindAndComp? (target : Expr) : Option (VCSpecKind × Expr) :=
  match tripleGoalComp? target with
  | some comp => some (.unaryTriple, comp)
  | none =>
      match wpGoalComp? target with
      | some comp => some (.unaryWP, comp)
      | none => none

private def takeCandidatePrefix (entries : Array VCSpecEntry) : Array VCSpecEntry :=
  (entries.toList.take 8).toArray

private def registeredVCGenRuleCandidateTiers : TacticM (Array (Array VCSpecEntry)) := do
  let target ← instantiateMVars (← getMainTarget)
  let some (kind, comp) := unaryGoalKindAndComp? target | return #[]
  let goalPattern := classifyUnaryCompPattern comp
  let direct :=
    (← getRegisteredUnaryVCSpecEntries comp).filter (·.kind == kind)
  let fallbackAll :=
    (← getVCSpecEntriesOfKind kind).filter fun entry =>
      !(direct.any fun directEntry => directEntry.theoremName! == entry.theoremName!)
  let fallbackPreferred := fallbackAll.filter (·.spec.compPattern == goalPattern)
  let fallbackFallback := fallbackAll.filter (·.spec.compPattern != goalPattern)
  let mut tiers : Array (Array VCSpecEntry) := #[]
  for tier in #[direct, fallbackPreferred, fallbackFallback] do
    let tier := takeCandidatePrefix tier
    unless tier.isEmpty do
      tiers := tiers.push tier
  return tiers

/-- Find the registered unary `@[vcspec]` entries whose bounded application
makes progress on the current goal. Prefers direct discrimination-tree hits on
the goal's `comp`, falling back to kind-matched entries filtered by structural
compatibility. -/
def findRegisteredVCGenRuleCandidates : TacticM (Array VCSpecEntry) := do
  withVCGenRegisteredTiming do
    for tier in ← registeredVCGenRuleCandidateTiers do
      let mut found : Array VCSpecEntry := #[]
      for entry in tier do
        let saved ← saveState
        let ok ← runUnaryVCSpecRule entry
        saved.restore
        if ok then
          found := found.push entry
      unless found.isEmpty do
        return found
    return #[]

/-- Find the first registered unary `@[vcspec]` entry whose bounded
application makes progress. -/
def findRegisteredVCGenRule? : TacticM (Option VCSpecEntry) := do
  withVCGenRegisteredTiming do
    for tier in ← registeredVCGenRuleCandidateTiers do
      for entry in tier do
        let saved ← saveState
        let ok ← runUnaryVCSpecRule entry
        saved.restore
        if ok then
          return some entry
    return none

/-- Try registered `@[vcspec]` rules against a raw `wp` goal.

This is intentionally direct-hit only: raw `wp` stepping is on the hot path, so
we use the discrimination tree and avoid same-kind fallback scans. -/
private def runRawWpVCSpecBackward : TacticM Bool := do
  withVCGenRegisteredTiming do
    let target ← instantiateMVars (← getMainTarget)
    let comp? :=
      match rawWPGoalParts? target with
      | some (_, comp, _) => some comp
      | none => wpGoalComp? target
    let some comp := comp? | return false
    let comp ← instantiateMVars comp
    let goalPattern := classifyUnaryCompPattern comp
    let entries ← getRegisteredUnaryVCSpecEntriesNoWhnf comp
    let entries :=
      takeCandidatePrefix <|
        entries.filter (fun entry =>
          entry.kind == .unaryWP && entry.spec.compPattern == goalPattern) ++
          entries.filter (fun entry => entry.kind == .unaryTriple &&
            entry.spec.compPattern == goalPattern)
    for entry in entries do
      if ← runUnaryVCSpecRule entry then
        return true
    return false

/-- Report the unsupported goal shape and available alternatives when unary stepping fails. -/
def throwVCGenStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match tripleGoalComp? target with
  | none =>
      if hasProbGoal target then
        if isProbEqGoal target then
          throwError
            "vcstep: found a `Pr[ ...] = Pr[ ...]` goal but no swap or congruence rule applied.\n\
            Goal:{indentExpr target}\n\
            Try `vcstep rw`, `vcstep rw under 1`, `vcstep rw congr`, \
            `vcstep rw congr'`, `vcstep?`, or manual rewriting with \
            `probEvent_bind_bind_swap`."
        else
          throwError
            "vcstep: found a probability goal but could not lower it to a supported\n\
            `Triple` or raw `wp` shape.\n\
            Goal:{indentExpr target}\n\
            Supported direct lowerings include `Pr[ ...] = 1`, `Pr[ ...] = Pr[ ...]`,\n\
            and lower bounds such as `r ≤ Pr[ ...]` / `Pr[ ...] ≥ r`.\n\
            Try `rw [probEvent_eq_wp_propInd]`, `vcstep?`, or manual rewriting."
      else if let some comp := wpGoalComp? target then
        let comp ← whnfReducible (← instantiateMVars comp)
        let theoremMsg ← do
          let tiers ← registeredVCGenRuleCandidateTiers
          let thms := tiers.foldl (init := #[]) fun acc tier =>
            acc ++ tier.map (·.theoremName!)
          pure <| if thms.isEmpty then "" else
            s!"\nRegistered `@[vcspec]` candidates: {formatCandidateNames thms}"
        throwError
          "vcstep: currently in raw `wp` continuation mode, but no matching rule applied to:\n\
          {indentExpr comp}\n\
          Try `vcstep?`, `vcstep`, or manual rewriting.{theoremMsg}"
      else
        throwError
          "vcstep: expected a `Triple`, raw `wp`, or probability goal; got:{indentExpr target}"
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      let cutMsg ←
        if isBindExpr comp then
          let cuts ← potentialLocalHintNames
          pure <| if cuts.isEmpty then "" else
            s!"\nPotential local cut candidates: {formatCandidateNames cuts}"
        else
          pure ""
      let invMsg ←
        if isReplicateHead comp || isListFoldlMHead comp || isListMapMHead comp then
          let invs ← potentialLocalHintNames
          pure <| if invs.isEmpty then "" else
            s!"\nPotential local invariant candidates: {formatCandidateNames invs}"
        else
          pure ""
      let theoremMsg ← do
        let tiers ← registeredVCGenRuleCandidateTiers
        let thms := tiers.foldl (init := #[]) fun acc tier =>
          acc ++ tier.map (·.theoremName!)
        pure <| if thms.isEmpty then "" else
          s!"\nRegistered `@[vcspec]` candidates: {formatCandidateNames thms}"
      throwError
        "vcstep: found a `Triple` goal, but no matching rule applied to:{indentExpr comp}\n\
        Try `vcstep`, or manually unfolding the remaining arithmetic side conditions.\
        {cutMsg}{invMsg}{theoremMsg}"

/-- Try to close or rewrite a `Pr[ ...] = Pr[ ...]` goal by swapping adjacent independent binds.
Handles 0–2 layers of tsum peeling. -/
inductive ProbEqAction where
  | swap
  | congr
  | congrNoSupport
  | rewrite
  | rewriteUnder (depth : Nat)

private def normalizeProbEqGoal : TacticM Unit := do
  discard <| tryEvalTacticSyntax (← `(tactic|
    simp only [map_eq_bind_pure_comp, bind_assoc]))

/-- Normalize a probability equality and try swapping adjacent independent binds. -/
def runProbEqSwap : TacticM Bool := do
  normalizeProbEqGoal
  tryEvalTacticSyntax (← `(tactic| (
    try simp only [bind_assoc]
    first
      | (rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
         exact probEvent_bind_bind_swap _ _ _ _)
      | (rw [show Pr[ _ | _ >>= fun a => _ >>= fun b => _] =
              Pr[ _ | _ >>= fun b => _ >>= fun a => _] from
            probEvent_bind_bind_swap _ _ _ _])
      | (conv in (Pr[ _ | _]) =>
          rw [show Pr[ _ | _ >>= fun a => _ >>= fun b => _] =
                Pr[ _ | _ >>= fun b => _ >>= fun a => _] from
              probEvent_bind_bind_swap _ _ _ _])
      | (rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
         refine tsum_congr fun _ => ?_
         congr 1
         try simp only [monad_norm]
         first
           | exact probEvent_bind_bind_swap _ _ _ _
           | (rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
              exact probEvent_bind_bind_swap _ _ _ _))
      | (rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
         refine tsum_congr fun _ => ?_
         congr 1
         rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
         refine tsum_congr fun _ => ?_
         congr 1
         try simp only [monad_norm]
         first
           | exact probEvent_bind_bind_swap _ _ _ _
           | (rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
              exact probEvent_bind_bind_swap _ _ _ _)))))

/-- Apply probability bind congruence without support hypotheses and introduce named values. -/
def runProbEqCongrNoSupportWithNames (names : Array Name) : TacticM Bool := do
  normalizeProbEqGoal
  if ← tryEvalTacticSyntax (← `(tactic| apply probOutput_bind_congr')) then
    discard <| introMainGoalNames names
    return true
  if ← tryEvalTacticSyntax (← `(tactic| apply probEvent_bind_congr')) then
    discard <| introMainGoalNames names
    return true
  return false

/-- Apply probability bind congruence using fresh names without support hypotheses. -/
def runProbEqCongrNoSupport : TacticM Bool := do
  let names ← getProbCongrNames false
  runProbEqCongrNoSupportWithNames names

/-- Try to decompose a `Pr[ ... | mx >>= f₁] = Pr[ ... | mx >>= f₂]` goal by congruence,
then auto-intro the bound variable and support hypothesis. -/
def runProbEqCongrWithNames (names : Array Name) : TacticM Bool := do
  normalizeProbEqGoal
  if ← tryEvalTacticSyntax (← `(tactic| apply probOutput_bind_congr)) then
    discard <| introMainGoalNames names
    return true
  if ← tryEvalTacticSyntax (← `(tactic| apply probEvent_bind_congr)) then
    discard <| introMainGoalNames names
    return true
  return false

/-- Try support-sensitive probability congruence, then its unconditional variant. -/
def runProbEqCongr : TacticM Bool := do
  let names ← getProbCongrNames true
  if ← runProbEqCongrWithNames names then
    return true
  runProbEqCongrNoSupport

private def chunkNameArray
    (names : Array Name) (width : Nat) : Option (Array (Array Name)) := Id.run do
  if width = 0 || names.isEmpty then
    return none
  if names.size % width != 0 then
    return none
  let mut chunks : Array (Array Name) := #[]
  let mut i := 0
  while i < names.size do
    chunks := chunks.push (names.extract i (i + width))
    i := i + width
  return some chunks

/-- Apply successive congruence steps, grouping names by whether support hypotheses are
introduced. -/
def runProbEqCongrChainWithNames
    (supportSensitive : Bool) (names : Array Name) : TacticM Bool := do
  let width := if supportSensitive then 2 else 1
  let some chunks := chunkNameArray names width | return false
  let saved ← saveState
  for chunk in chunks do
    let ok ←
      if supportSensitive then
        runProbEqCongrWithNames chunk
      else
        runProbEqCongrNoSupportWithNames chunk
    if !ok then
      saved.restore
      return false
  return true

/-- Build a theorem that swaps adjacent binds under `depth` shared prefixes. -/
partial def mkProbSwapUnderProof (depth : Nat) : TacticM (TSyntax `term) := do
  match depth with
  | 0 => `(term| probEvent_bind_bind_swap _ _ _ _)
  | depth + 1 =>
      let inner ← mkProbSwapUnderProof depth
      `(term| probEvent_bind_congr fun _ _ => $inner)

/-- Try to rewrite one top-level bind-swap without closing the goal. -/
def runProbEqRewrite : TacticM Bool := do
  normalizeProbEqGoal
  tryEvalTacticSyntax (← `(tactic| (
    first
      | (simp only [← probEvent_eq_eq_probOutput]
         rw [probEvent_bind_bind_swap]
         try simp only [probEvent_eq_eq_probOutput])
      | rw [probEvent_bind_bind_swap])))

/-- Try to rewrite one bind-swap under `depth` shared prefixes on either side. -/
def runProbEqRewriteUnder (depth : Nat) : TacticM Bool := do
  normalizeProbEqGoal
  let proof ← mkProbSwapUnderProof depth
  tryEvalTacticSyntax (← `(tactic| (
    first
      | (simp only [← probEvent_eq_eq_probOutput]
         first
           | (conv_lhs => rw [show _ from $proof])
           | (conv_rhs => rw [show _ from $proof])
         try simp only [probEvent_eq_eq_probOutput])
      | first
          | (conv_lhs => rw [show _ from $proof])
          | (conv_rhs => rw [show _ from $proof]))))

/-- Execute a probability-equality planner action. -/
def runProbEqAction : ProbEqAction → TacticM Bool
  | .swap => runProbEqSwap
  | .congr => runProbEqCongr
  | .congrNoSupport => runProbEqCongrNoSupport
  | .rewrite => runProbEqRewrite
  | .rewriteUnder depth =>
      if depth = 0 then
        runProbEqRewrite
      else
        runProbEqRewriteUnder depth

private def renderProbEqAction : ProbEqAction → TacticM String
  | .swap => pure "vcstep"
  | .congr => do
      let names ← getProbCongrNames true
      pure s!"vcstep rw congr{renderAsClause names}"
  | .congrNoSupport => do
      let names ← getProbCongrNames false
      pure s!"vcstep rw congr'{renderAsClause names}"
  | .rewrite => pure "vcstep rw"
  | .rewriteUnder depth => pure s!"vcstep rw under {depth}"

private def renderProbEqPlan (actions : List ProbEqAction) : TacticM String := do
  let parts ← actions.mapM renderProbEqAction
  match parts with
  | [] => pure "vcstep"
  | [part] => pure part
  | _ => pure s!"({String.intercalate "; " parts})"

/-- Try a small backtracking-free sequence of probability-equality steps. -/
def tryProbEqActions (steps : List ProbEqAction) : TacticM Bool := do
  let saved ← saveState
  for step in steps do
    if (← getGoals).isEmpty then
      return true
    if !(← runProbEqAction step) then
      saved.restore
      return false
  return true

private def chooseBestProbEqPlan? (plans : List (List ProbEqAction)) :
    TacticM (Option (List ProbEqAction × PreviewResult)) := do
  withVCGenProbPlannerTiming do
    let mut best? : Option (List ProbEqAction × PreviewResult) := none
    for plan in plans do
      let preview ← previewActionWithGoals (tryProbEqActions plan)
      if preview.ok then
        if preview.goalCount = 0 then
          return some (plan, preview)
        match best? with
        | none => best? := some (plan, preview)
        | some (_, bestPreview) =>
            if preview.goalCount < bestPreview.goalCount then
              best? := some (plan, preview)
    return best?

private def mkRewriteChain (depth : Nat) : List ProbEqAction :=
  ((List.range depth).reverse.map fun idx => ProbEqAction.rewriteUnder (idx + 1)) ++
    [ProbEqAction.rewrite]

private def probEqCongrPlans (maxDepth : Nat) : List (List ProbEqAction) :=
  let layers := (List.range maxDepth).map fun idx =>
    let depth := idx + 1
    [List.replicate depth ProbEqAction.congr,
      List.replicate depth ProbEqAction.congrNoSupport]
  layers.foldr List.append []

private def probEqRewritePlans (maxDepth : Nat) : List (List ProbEqAction) :=
  let layers := ((List.range (maxDepth + 1)).reverse.map fun depth =>
    let chain := mkRewriteChain depth
    [chain ++ [ProbEqAction.congr], chain ++ [ProbEqAction.congrNoSupport], chain])
  layers.foldr List.append []

/-- Candidate sequences of swapping, rewriting, and congruence for probability equalities. -/
def probEqActionPlans : List (List ProbEqAction) :=
  [ [.swap]
  , [.congr]
  , [.congrNoSupport]
  , [.rewrite, .congr]
  , [.rewrite, .congrNoSupport]
  , [.congr, .swap]
  , [.congrNoSupport, .swap]
  , [.rewriteUnder 1, .rewrite, .congr]
  , [.rewriteUnder 1, .rewrite, .congrNoSupport]
  , [.rewriteUnder 1, .rewrite]
  , [.rewriteUnder 2, .rewriteUnder 1, .rewrite, .congr]
  , [.rewriteUnder 2, .rewriteUnder 1, .rewrite, .congrNoSupport]
  , [.rewriteUnder 2, .rewriteUnder 1, .rewrite]
  ]

private def probEqPlannerActionPlans : List (List ProbEqAction) :=
  probEqRewritePlans 4 ++ probEqCongrPlans 3 ++
    [ [.congr]
    , [.congrNoSupport]
    , [.congr, .swap]
    , [.congrNoSupport, .swap]
    , [.swap]
    ]

private def probExprComp? (expr : Expr) : Option Expr := do
  let app ←
    match findAppWithHead? ``probOutput expr with
    | some app => some app
    | none => findAppWithHead? ``probEvent expr
  let args ← trailingArgs? app 2
  let #[comp, _] := args | none
  some comp

private partial def topBindDepth (expr : Expr) : Nat :=
  let expr := expr.consumeMData
  if isBindExpr expr then
    let args := expr.getAppArgs
    if h : 0 < args.size then
      let k := args[args.size - 1]
      match k.consumeMData with
      | .lam _ _ body _ => topBindDepth body + 1
      | _ => 1
    else
      1
  else
    0

private def probEqBindDepth? (target : Expr) : Option Nat := do
  let target := target.consumeMData
  guard <| target.isAppOfArity ``Eq 3
  let lhsComp ← probExprComp? (target.getArg! 1)
  let rhsComp ← probExprComp? (target.getArg! 2)
  some (Nat.min (topBindDepth lhsComp) (topBindDepth rhsComp))

private def probEqPlannerActionPlansForDepth (bindDepth : Nat) : List (List ProbEqAction) :=
  let maxRewriteDepth := Nat.min 4 (bindDepth - 2)
  let maxCongrDepth := Nat.min 3 bindDepth
  probEqRewritePlans maxRewriteDepth ++ probEqCongrPlans maxCongrDepth ++
    [ [.congr]
    , [.congrNoSupport]
    , [.congr, .swap]
    , [.congrNoSupport, .swap]
    , [.swap]
    ]

private def probEqPlannerActionPlansForGoal : TacticM (List (List ProbEqAction)) := do
  let target ← instantiateMVars (← getMainTarget)
  match probEqBindDepth? target with
  | some depth => return probEqPlannerActionPlansForDepth depth
  | none => return probEqPlannerActionPlans

/-- Preview candidate probability-equality plans and execute the best successful candidate. -/
def tryProbEqPlans (plans : List (List ProbEqAction)) : TacticM Bool := do
  match ← chooseBestProbEqPlan? plans with
  | none => return false
  | some (plan, _) => tryProbEqActions plan

/-- Explicit probability-equality normalization.

This runs the deeper planner-backed bind-rewrite/congruence search used by `vcstep?`, but only
when the user asks for it. Plain `vcstep` keeps the smaller default plan set. -/
def runProbEqNormalize : TacticM Bool := do
  for plan in ← probEqPlannerActionPlansForGoal do
    let preview ← previewActionWithGoals (tryProbEqActions plan)
    if preview.ok && preview.goalCount = 0 then
      return (← tryProbEqActions plan)
  return false

/-- Try to handle a `Pr[ ...] = Pr[ ...]` equality goal by swap, congr, or swap+congr.
Also tries a fallback bridge from exact `probOutput` equalities into relational VCGen. -/
def runProbOutputEqRelBridge : TacticM Bool := do
  let saved ← saveState
  let tryBridge (symmFirst : Bool) : TacticM Bool := do
    match ← observing? do
      if symmFirst then
        evalTactic (← `(tactic| symm))
      evalTactic (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.probOutput_eq_of_relTriple_eqRel))
    with
    | some _ => return true
    | none => return false
  if ← tryBridge false then
    return true
  saved.restore
  if ← tryBridge true then
    return true
  saved.restore
  return false

/-- Try to handle a `Pr[ ...] = Pr[ ...]` equality goal by swap, congr, or swap+congr. -/
def tryProbEqGoal : TacticM Bool := do
  if ← tryProbEqPlans probEqActionPlans then
    return true
  runProbOutputEqRelBridge

/-- Explain why a bind-swap rewrite at the requested prefix depth failed. -/
def throwVCGenStepRwError (depth : Nat) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if depth = 0 then
    throwError
      "vcstep rw: expected a `Pr[ ...] = Pr[ ...]` goal where one top-level\n\
      bind-swap rewrite applies.\n\
      Goal:{indentExpr target}"
  else
    throwError
      "vcstep rw under {depth}: expected a `Pr[ ...] = Pr[ ...]` goal where one\n\
      bind-swap rewrite applies under {depth} shared bind prefix(es).\n\
      Goal:{indentExpr target}"

/-- Explain a failed combined bind-swap and congruence step. -/
def throwVCGenStepRwCongrError (supportSensitive : Bool) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if supportSensitive then
    throwError
      "vcstep rw congr: expected a `Pr[ ...] = Pr[ ...]` goal with a shared outer\n\
      bind, leaving the bound variable and a support hypothesis.\n\
      Goal:{indentExpr target}"
  else
    throwError
      "vcstep rw congr': expected a `Pr[ ...] = Pr[ ...]` goal with a shared outer\n\
      bind, leaving only the bound variable.\n\
      Goal:{indentExpr target}"

/-- Explain why the bounded probability-equality normalization search failed. -/
def throwVCGenStepRwNormalizeError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  throwError
    "vcstep rw normalize: expected a `Pr[ ...] = Pr[ ...]` goal where the bounded\n\
    probability-equality planner can close the goal by bind-swap and congruence steps.\n\
    Goal:{indentExpr target}"

/-- Try to lower a probability goal into a `Triple`, `wp`, or probability-equality goal. -/
def tryLowerProbGoal : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let isProbEventGoal := (findAppWithHead? ``probEvent target).isSome
  let isProbOutputGoal := (findAppWithHead? ``probOutput target).isSome
  unless isProbEventGoal || isProbOutputGoal do return false
  if isProbEqGoal target then
    if ← tryProbEqGoal then return true
  if isProbEventGoal then
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [← OracleComp.ProgramLogic.triple_propInd_iff_probEvent_eq_one];
        simp only [OracleComp.ProgramLogic.propInd_true])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [eq_comm (a := 1),
            ← OracleComp.ProgramLogic.triple_propInd_iff_probEvent_eq_one];
        simp only [OracleComp.ProgramLogic.propInd_true])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [← OracleComp.ProgramLogic.triple_propInd_iff_le_probEvent])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [ge_iff_le, ← OracleComp.ProgramLogic.triple_propInd_iff_le_probEvent])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [OracleComp.ProgramLogic.probEvent_eq_wp_propInd])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        simp only [OracleComp.ProgramLogic.probEvent_eq_wp_propInd])) then
      return true
  if isProbOutputGoal then
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [OracleComp.ProgramLogic.probOutput_eq_one_iff_triple])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [eq_comm, OracleComp.ProgramLogic.probOutput_eq_one_iff_triple])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [OracleComp.ProgramLogic.le_probOutput_iff_triple_indicator])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [ge_iff_le, OracleComp.ProgramLogic.le_probOutput_iff_triple_indicator])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        rw [OracleComp.ProgramLogic.probOutput_eq_wp_indicator])) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        simp only [OracleComp.ProgramLogic.probOutput_eq_wp_indicator])) then
      return true
  return false

/-- Continue structural stepping on a raw `wp` goal after probability lowering or explicit
`wp`-level work. This stays deliberately smaller than the `Triple` path. -/
def tryRawWpStructuralStep : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let comp? :=
    match rawWPGoalParts? target with
    | some (_, comp, _) => some comp
    | none => wpGoalComp? target
  let some comp := comp? | return false
  let comp ← instantiateMVars comp
  let isLowerBoundGoal := (rawWPGoalParts? target).isSome
  if isLowerBoundGoal then
    if ← runRawWpVCSpecBackward then
      return true
  if ← runWpStepRules then
    return true
  unless isLowerBoundGoal do
    if ← runRawWpVCSpecBackward then
      return true
  if ← tryMatchDecomp comp then
    return true
  return false

/-- Try to synthesize a support-based intermediate postcondition for a bind step.
When the computation is `oa >>= f` and no explicit spec is available, tries applying
`triple_bind` with an inferred cut and closing the spec subgoal via `triple_support`,
which unifies the cut to `fun x => 𝟙⟦x ∈ support oa⟧`. -/
def trySupportCutBind (comp : Expr) : TacticM Bool := do
  if !isBindExpr comp then return false
  match ← observing? do
    evalTactic (← `(tactic| apply OracleComp.ProgramLogic.triple_bind))
    unless ← tryEvalTacticSyntax (← `(tactic|
      classical exact OracleComp.ProgramLogic.triple_support _)) do
      throwError "" with
  | some _ => return true
  | none => return false

end Unary
end TacticInternals
end OracleComp.ProgramLogic
