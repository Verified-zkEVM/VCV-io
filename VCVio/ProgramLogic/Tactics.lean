/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean.Elab.Tactic
import VCVio.ProgramLogic.Notation

/-!
# VCGen-Style Tactics for Probabilistic Program Logic

This file provides the canonical step-through tactic surface for game-hopping proofs,
inspired by EasyCrypt's `proc`, `wp`, `rnd`, `skip`, `swap`, and `seq`.

`VCVio/ProgramLogic/Notation.lean` keeps the notation layer, convenience predicates, and a
small set of coarse compatibility macros. For new proofs, import this file and treat the
tactics below as the primary proof mode.

## Main tactics

### Unary WP
- `wp_step`: Apply exactly one WP rule (`wp_bind`, `wp_pure`, etc.)
- `hoare_step`: Apply one quantitative Hoare/VCGen step on a `Triple` goal
- `wp_seq`: Repeat `wp_step` through several layers
- `hoare_seq`: Repeat `hoare_step` through several layers
- `game_wp` (enhanced): Exhaustively apply WP rules

### Relational (pRHL)
- `rel_step`: Decompose one `>>=` on each side (like EasyCrypt's `seq`/`wp`)
- `rel_seq`: Repeat `rel_step` through several bind layers
- `rel_rnd`: Couple random oracle queries or uniform sampling
- `rel_skip`: Both sides are identical or both pure
- `rel_pure`: Close a goal where both sides are `pure`
- `rel_cond`: Decompose a synchronized conditional (like EasyCrypt's `if`/`cond`)
- `rel_conseq`: Weaken/strengthen the postcondition (like EasyCrypt's `conseq`)
- `rel_inline`: Unfold a definition and retry
- `rel_sim`: Apply relational simulation rule

### Proof mode entry / exit
- `by_equiv`: Transform a `GameEquiv` or `evalDist` equality into a `RelTriple`
- `rel_dist`: Transform a `RelTriple` goal into an `evalDist` equality (reverse of `by_equiv`)
- `game_trans`: Introduce an intermediate game for transitivity
- `by_dist`: Transform an advantage bound into a TV distance / relational goal
- `by_upto bad`: Enter an identical-until-bad TV-distance proof
- `by_hoare`: Transform a probability goal into a quantitative WP goal

### Bind reordering and congruence
- `prob_swap`: Swap two independent sampling operations in a `Pr[...]` goal (closes goal)
- `prob_swap_rw`: Rewrite variant of `prob_swap` for use inside larger proofs
- `prob_congr`: Pointwise congruence under a shared outer bind
-/

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

private def whnfReducible (e : Expr) : MetaM Expr :=
  withReducible <| whnf e

private def headConstName? (e : Expr) : Option Name :=
  e.consumeMData.getAppFn.constName?

private def trailingArgs? (e : Expr) (n : Nat) : Option (Array Expr) :=
  let args := e.consumeMData.getAppArgs
  if _h : n ≤ args.size then
    some <| args.extract (args.size - n) args.size
  else
    none

private partial def findAppWithHead? (head : Name) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if e.getAppFn.isConstOf head then
    some e
  else
    match e with
    | .app f a => findAppWithHead? head f <|> findAppWithHead? head a
    | .lam _ t b _ => findAppWithHead? head t <|> findAppWithHead? head b
    | .forallE _ t b _ => findAppWithHead? head t <|> findAppWithHead? head b
    | .letE _ t v b _ => findAppWithHead? head t <|> findAppWithHead? head v <|> findAppWithHead? head b
    | .mdata _ b => findAppWithHead? head b
    | .proj _ _ b => findAppWithHead? head b
    | _ => none

private def relTripleGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.Relational.RelTriple target
  let args ← trailingArgs? app 3
  some (args[0]!, args[1]!, args[2]!)

private def wpGoalComp? (target : Expr) : Option Expr := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.wp target
  let args ← trailingArgs? app 2
  some args[0]!

private def tripleGoalComp? (target : Expr) : Option Expr := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.Triple target
  let args ← trailingArgs? app 3
  some args[1]!

private def isSimulateQAction (e : Expr) : Bool :=
  (findAppWithHead? ``simulateQ e).isSome

private def hasStateTRunLike (e : Expr) : Bool :=
  (findAppWithHead? ``StateT.run e).isSome || (findAppWithHead? ``StateT.run' e).isSome

private def hasSimulateQRunLike (e : Expr) : Bool :=
  isSimulateQAction e && hasStateTRunLike e

private def isEqRelPost (e : Expr) : Bool :=
  (findAppWithHead? ``OracleComp.ProgramLogic.Relational.EqRel e).isSome

private def isBindExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Bind.bind

private def isPureExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Pure.pure

private def isIfExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``ite || e.consumeMData.getAppFn.isConstOf ``dite

private def isMapExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Functor.map

private def isGameEquivGoal (target : Expr) : Bool :=
  target.consumeMData.getAppFn.isConstOf ``OracleComp.ProgramLogic.GameEquiv

private def tryEvalTacticSyntax (stx : Syntax) : TacticM Bool := do
  let some _ ← observing? (evalTactic stx) | return false
  return true

private def runWpStepRules : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_bind])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_pure])) <||>
    tryEvalTacticSyntax (← `(tactic| simp only [OracleComp.ProgramLogic.wp_pure])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_query])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_ite])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_uniformSample])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_map])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_simulateQ_eq])) <||>
    tryEvalTacticSyntax (← `(tactic| rw [OracleComp.ProgramLogic.wp_liftComp]))

private def runRelStepRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_bind
      (R := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_)) <||>
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_bind ?_ ?_))

private def runRelStepRuleUsing (R : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_bind (R := $R) ?_ ?_))

private def runRelRndRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic| exact OracleComp.ProgramLogic.Relational.relTriple_query _)) <||>
    tryEvalTacticSyntax (← `(tactic| exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) <||>
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.Relational.relTriple_query_bij <;> [skip])) <||>
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij <;> [skip; skip])) <||>
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_evalDist_eq <;> [skip]))

private def runRelRndRuleUsing (f : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_query_bij _ (f := $f) <;> [skip])) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij (f := $f) <;> [skip; skip]))

private def runRelRndRuleWithContextBijection : TacticM Bool := withMainContext do
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if let some app := findAppWithHead? ``Function.Bijective type then
        if let some args := trailingArgs? app 1 then
          let fStx ← PrettyPrinter.delab args[0]!
          if ← runRelRndRuleUsing fStx then
            return true
  return false

private def throwWpStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match wpGoalComp? target with
  | none =>
      throwError "wp_step: expected a goal containing `wp`; got:{indentExpr target}"
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      throwError
        "wp_step: found a `wp` goal, but none of the current single-step rules apply to:{indentExpr comp}\n\
        Current rules handle bind, pure, query, `if`, uniform sampling, `map`, `simulateQ`, and `liftComp`."

private def runHoareStepRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  match tripleGoalComp? target with
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      if isBindExpr comp then
        if ← tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.triple_bind)) then
          return true
      match ← (observing? do
        evalTactic (← `(tactic| unfold OracleComp.ProgramLogic.Triple))
        evalTactic (← `(tactic| change _ ≤ OracleComp.ProgramLogic.wp _ _))
        unless ← runWpStepRules do
          throwError "hoare_step: no matching wp rule after unfolding `Triple`") with
      | some _ => return true
      | none => return false
  | none => return false

private def throwHoareStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match tripleGoalComp? target with
  | none =>
      throwError "hoare_step: expected a quantitative `Triple` goal; got:{indentExpr target}"
  | some comp =>
      let comp ← whnfReducible (← instantiateMVars comp)
      throwError
        "hoare_step: found a `Triple` goal, but no single structural rule applied to:{indentExpr comp}\n\
        Try `by_hoare`, `wp_step`, or manually unfolding the remaining arithmetic side conditions."

private def throwRelStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if isGameEquivGoal target then
    throwError "rel_step: the goal is a `GameEquiv`; use `by_equiv` first to enter relational proof mode."
  match relTripleGoalParts? target with
  | none =>
      throwError "rel_step: expected a `RelTriple` goal; got:{indentExpr target}"
  | some (oa, ob, _) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      if !isBindExpr oa || !isBindExpr ob then
        throwError
          "rel_step: expected both sides of the `RelTriple` to start with `>>=`.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Try `rel_rnd`, `rel_skip`, `rel_pure`, `rel_cond`, or `rel_dist` instead."
      throwError "rel_step: failed to apply `relTriple_bind` to the current goal."

private def throwRelRndError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if isGameEquivGoal target then
    throwError "rel_rnd: the goal is a `GameEquiv`; use `by_equiv` first to enter relational proof mode."
  match relTripleGoalParts? target with
  | none =>
      throwError "rel_rnd: expected a `RelTriple` goal; got:{indentExpr target}"
  | some (oa, ob, _) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      if isBindExpr oa || isBindExpr ob then
        throwError
          "rel_rnd: this goal still has bind structure.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Use `rel_step` first, then apply `rel_rnd` to the sampling/query subgoal."
      if isPureExpr oa && isPureExpr ob then
        throwError "rel_rnd: both sides are `pure`; use `rel_pure` or `rel_skip` instead."
      if oa == ob then
        throwError "rel_rnd: both sides are syntactically identical but no random-step rule matched; try `rel_skip`."
      throwError
        "rel_rnd: expected a single random-step / query-style `RelTriple`, but no coupling rule matched.\n\
        Left side:{indentExpr oa}\n\
        Right side:{indentExpr ob}"

private def runByUptoRule (bad : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_bad
      (bad := $bad)))

private def runRelSimRule : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | some (oa, ob, R) =>
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) then
        return false
      if isEqRelPost R then
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'))
      else
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run))
  | none => return false

private def throwByUptoError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  throwError
    "by_upto: expected a TV-distance goal for two `simulateQ ... run'` computations bounded by\n\
    the probability of a bad event on the left simulation; got:{indentExpr target}"

private def throwRelSimError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if isGameEquivGoal target then
    throwError "rel_sim: the goal is a `GameEquiv`; use `by_equiv` first to enter relational proof mode."
  match relTripleGoalParts? target with
  | none =>
      throwError "rel_sim: expected a `RelTriple` goal; got:{indentExpr target}"
  | some (oa, ob, R) =>
      let oa := oa.consumeMData
      let ob := ob.consumeMData
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) then
        throwError
          "rel_sim: expected a relational goal about `(simulateQ ...).run ...` or \
          `(simulateQ ...).run' ...`.\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}"
      if isEqRelPost R then
        throwError
          "rel_sim: recognized an output-only `simulateQ` goal, but \
          `relTriple_simulateQ_run'` did not apply.\n\
          Expected an `EqRel` postcondition together with the usual per-query simulation and \
          initial-invariant obligations."
      throwError
        "rel_sim: recognized a state-threading `simulateQ` goal, but \
        `relTriple_simulateQ_run` did not apply.\n\
        Expected a postcondition of the form \
        `fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2`, together with the usual simulation and \
        initial-invariant obligations."

/-! ## Unary WP tactics -/

/-- `wp_step` applies exactly one WP decomposition rule and stops.
This gives step-by-step control, unlike the exhaustive `game_wp`. -/
elab "wp_step" : tactic => do
  if ← runWpStepRules then
    return
  throwWpStepError

/-- `hoare_step` applies one quantitative program-logic step to a `Triple` goal.

It first tries the structural bind rule, and otherwise unfolds the triple into a
`pre ≤ wp ...` obligation and delegates to `wp_step`. -/
elab "hoare_step" : tactic => do
  if ← runHoareStepRule then
    return
  throwHoareStepError

/-- `wp_seq n` repeatedly applies `wp_step` `n` times. -/
syntax "wp_seq" num : tactic

elab_rules : tactic
  | `(tactic| wp_seq $n:num) => do
      let k := n.getNat
      if k = 0 then
        throwError "wp_seq: expected a positive number of steps."
      for _ in [:k] do
        if ← runWpStepRules then
          pure ()
        else
          throwWpStepError

/-- `hoare_seq n` repeatedly applies `hoare_step` `n` times. -/
syntax "hoare_seq" num : tactic

elab_rules : tactic
  | `(tactic| hoare_seq $n:num) => do
      let k := n.getNat
      if k = 0 then
        throwError "hoare_seq: expected a positive number of steps."
      for _ in [:k] do
        if ← runHoareStepRule then
          pure ()
        else
          throwHoareStepError

/-! ## Relational step-through tactics (EasyCrypt-inspired) -/

/-- `rel_pure` closes a `RelTriple` goal where both sides are `pure`.

Tries:
1. `relTriple_pure_pure` with the relation provable by assumption or `rfl`
2. `relTriple_refl` if both sides are syntactically the same `pure` value -/
macro "rel_pure" : tactic =>
  `(tactic|
    first
      | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
      | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption)
      | exact OracleComp.ProgramLogic.Relational.relTriple_refl _)

/-- `rel_step` decomposes one `>>=` on each side of a `RelTriple` goal.

Given a goal `RelTriple (oa >>= fa) (ob >>= fb) S`, applies `relTriple_bind`
to produce two subgoals:
1. `RelTriple oa ob R` — the intermediate coupling
2. `∀ a b, R a b → RelTriple (fa a) (fb b) S` — the continuation

When both sides produce the same type, defaults to `R := EqRel _` (equality).
When the types differ, `R` is left as a metavariable for Lean to infer.
Use `rel_step using R` to specify a non-equality intermediate relation explicitly. -/
syntax "rel_step" ("using" term)? : tactic

elab_rules : tactic
  | `(tactic| rel_step) => do
      if ← runRelStepRule then
        return
      throwRelStepError
  | `(tactic| rel_step using $R) => do
      if ← runRelStepRuleUsing R then
        return
      throwRelStepError

/-- `rel_rnd` couples random oracle queries or uniform sampling on both sides.

Tries the following rules in order:
1. `relTriple_query` — identity coupling for same oracle queries
2. `relTriple_refl` — reflexivity (same computation)
3. `relTriple_query_bij` / `relTriple_uniformSample_bij` using a local `Function.Bijective f`
4. `relTriple_query_bij` / `relTriple_uniformSample_bij` leaving bijection subgoals
5. `relTriple_eqRel_of_evalDist_eq` — equal distributions

Use `rel_rnd using f` to specify the bijection explicitly. -/
syntax "rel_rnd" ("using" term)? : tactic

elab_rules : tactic
  | `(tactic| rel_rnd) => do
      if ← tryEvalTacticSyntax (← `(tactic| exact OracleComp.ProgramLogic.Relational.relTriple_query _)) then
        return
      if ← tryEvalTacticSyntax (← `(tactic| exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) then
        return
      if ← runRelRndRuleWithContextBijection then
        return
      if ← runRelRndRule then
        return
      throwRelRndError
  | `(tactic| rel_rnd using $f) => do
      if ← runRelRndRuleUsing f then
        return
      throwRelRndError

/-- `rel_seq n` repeatedly applies `rel_step` `n` times.

`rel_seq n using R` uses `rel_step using R` on the first layer, then ordinary
`rel_step` for the remaining `n - 1` layers. This is useful when the interesting cut
relation only appears deeper in a bind chain. -/
syntax "rel_seq" num ("using" term)? : tactic

elab_rules : tactic
  | `(tactic| rel_seq $n:num) => do
      let k := n.getNat
      if k = 0 then
        throwError "rel_seq: expected a positive number of steps."
      for _ in [:k] do
        if ← runRelStepRule then
          pure ()
        else
          throwRelStepError
  | `(tactic| rel_seq $n:num using $R) => do
      let k := n.getNat
      if k = 0 then
        throwError "rel_seq: expected a positive number of steps."
      if ← runRelStepRuleUsing R then
        pure ()
      else
        throwRelStepError
      for _ in [:k - 1] do
        if ← runRelStepRule then
          pure ()
        else
          throwRelStepError

/-- `rel_skip` closes a `RelTriple` goal where both sides are identical or both pure.

Tries:
1. `relTriple_refl` — both sides are the same
2. `relTriple_eqRel_of_eq rfl` — both sides are definitionally equal
3. `relTriple_eqRel_of_evalDist_eq` — evaluation distributions are equal -/
macro "rel_skip" : tactic =>
  `(tactic|
    first
      | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
      | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
      | (apply OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_evalDist_eq; rfl)
      | (apply OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_evalDist_eq; skip))

/-- `rel_cond` decomposes a `RelTriple` goal where both sides branch on the same condition.

Given a goal `RelTriple (if c then a₁ else a₂) (if c then b₁ else b₂) R`,
applies `relTriple_if` to produce two subgoals:
1. `c → RelTriple a₁ b₁ R`
2. `¬c → RelTriple a₂ b₂ R`

The tactic also tries `simp only [game_rule]` first to expose hidden `if` expressions. -/
macro "rel_cond" : tactic =>
  `(tactic|
    first
      | (apply OracleComp.ProgramLogic.Relational.relTriple_if <;> [intro _; intro _])
      | (simp only [game_rule]
         apply OracleComp.ProgramLogic.Relational.relTriple_if <;> [intro _; intro _]))

/-- `rel_conseq` weakens or strengthens the postcondition of a `RelTriple` goal.

Given a goal `RelTriple oa ob R'`, applies `relTriple_post_mono` to produce:
1. `RelTriple oa ob ?R` — the triple with a (possibly easier) postcondition
2. `∀ x y, ?R x y → R' x y` — the implication between postconditions

Use `rel_conseq with R` to specify the intermediate postcondition explicitly. -/
syntax "rel_conseq" ("with" term)? : tactic

macro_rules
  | `(tactic| rel_conseq) =>
    `(tactic|
      apply OracleComp.ProgramLogic.Relational.relTriple_post_mono)
  | `(tactic| rel_conseq with $R) =>
    `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_post_mono (R := $R) ?_ ?_)

/-- `rel_inline` unfolds definitions and then tries to close or simplify the relational goal.
Use `rel_inline foo bar` to unfold specific definitions, or just `rel_inline` to simplify. -/
macro "rel_inline" ids:ident* : tactic =>
  if ids.size > 0 then
    `(tactic|
      (unfold $ids*
       try simp only [game_rule]
       try rel_skip))
  else
    `(tactic|
      (simp only [game_rule]
       try rel_skip))

/-- `rel_sim` applies the relational `simulateQ` rule with a state invariant.

Given a goal about simulated computations, applies `relTriple_simulateQ_run`
or `relTriple_simulateQ_run'`. -/
elab "rel_sim" : tactic => do
  if ← runRelSimRule then
    return
  throwRelSimError

/-! ## Proof mode entry tactics -/

/-- `by_equiv` transforms a `GameEquiv g₁ g₂` goal into `RelTriple g₁ g₂ (EqRel α)`.
Also works for `evalDist g₁ = evalDist g₂` goals.
Always targets `RelTriple` (coupling-based), never `RelTriple'` (eRHL-based),
so that step-through tactics (`rel_step`, `rel_rnd`, etc.) work on the resulting goal. -/
macro "by_equiv" : tactic =>
  `(tactic|
    first
      | apply OracleComp.ProgramLogic.GameEquiv.of_relTriple
      | (change OracleComp.ProgramLogic.Relational.RelTriple _ _ _)
      | (apply OracleComp.ProgramLogic.Relational.evalDist_eq_of_relTriple_eqRel))

/-- `rel_dist` reduces a `RelTriple oa ob (EqRel α)` goal to `evalDist oa = evalDist ob`.

This is the reverse direction of `by_equiv`: while `by_equiv` enters relational mode from a
distributional equality, `rel_dist` exits relational mode back to distributional reasoning.

Useful when both sides are equal in distribution but not syntactically identical, and the
equality is easier to prove at the `evalDist` level than via stepwise coupling. -/
macro "rel_dist" : tactic =>
  `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_evalDist_eq)

/-- `game_trans` introduces an intermediate game for transitivity of `GameEquiv`.

Given a goal `g₁ ≡ₚ g₃`, `game_trans g₂` produces two subgoals:
1. `g₁ ≡ₚ g₂`
2. `g₂ ≡ₚ g₃`

This is the fundamental tactic for multi-step game-hopping chains. -/
syntax "game_trans" term : tactic

macro_rules
  | `(tactic| game_trans $g) =>
    `(tactic|
      refine OracleComp.ProgramLogic.GameEquiv.trans (g₂ := $g) ?_ ?_)

/-- `by_dist` transforms a TV distance or advantage bound goal into a subgoal
suitable for relational or coupling reasoning. -/
syntax "by_dist" (term)? : tactic

macro_rules
  | `(tactic| by_dist) =>
    `(tactic|
      apply OracleComp.ProgramLogic.AdvBound.of_tvDist)
  | `(tactic| by_dist $eps) =>
    `(tactic|
      (apply OracleComp.ProgramLogic.AdvBound.of_tvDist (ε₂ := $eps)))

/-- `by_upto bad` applies the "identical until bad" TV-distance theorem for `simulateQ`.
It leaves the standard four subgoals: initial non-bad state, agreement off bad,
and bad-state monotonicity for each implementation. -/
syntax "by_upto" term : tactic

elab_rules : tactic
  | `(tactic| by_upto $bad) => do
      if ← runByUptoRule bad then
        return
      throwByUptoError

/-- `by_hoare` transforms a probability goal into a quantitative WP goal. -/
macro "by_hoare" : tactic =>
  `(tactic|
    first
      | rw [OracleComp.ProgramLogic.probEvent_eq_wp_indicator]
      | rw [OracleComp.ProgramLogic.probOutput_eq_wp_indicator])

/-! ## Bind reordering tactic -/

/-- `prob_swap` swaps two independent sampling operations inside a `Pr[...]` goal.

This automates the extremely common pattern:
```
rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
refine tsum_congr fun x => ?_
congr 1
simpa [bind_assoc] using (probEvent_bind_bind_swap mx my f q)
```

Usage: `prob_swap` tries to find and swap adjacent independent binds.

Currently a best-effort macro; for complex nested cases, manual application of
`probEvent_bind_bind_swap` may still be needed. -/
macro "prob_swap" : tactic =>
  `(tactic| (
    try simp only [bind_assoc]
    first
      | (rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
         exact probEvent_bind_bind_swap _ _ _ _)
      | (rw [show Pr[_ | _ >>= fun a => _ >>= fun b => _] =
              Pr[_ | _ >>= fun b => _ >>= fun a => _] from
            probEvent_bind_bind_swap _ _ _ _])
      | (conv in (Pr[_ | _]) =>
          rw [show Pr[_ | _ >>= fun a => _ >>= fun b => _] =
                Pr[_ | _ >>= fun b => _ >>= fun a => _] from
              probEvent_bind_bind_swap _ _ _ _])
      | (rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
         refine tsum_congr fun _ => ?_
         congr 1
         try simp only [bind_assoc]
         first
           | exact probEvent_bind_bind_swap _ _ _ _
           | (rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
              exact probEvent_bind_bind_swap _ _ _ _))))

/-- `prob_swap_at n` repeatedly applies `prob_swap` up to `n` times. -/
macro "prob_swap_at" n:num : tactic =>
  `(tactic| (iterate $n prob_swap))

/-- `prob_swap_rw` rewrites one bind-swap and continues (does NOT close the goal).

Unlike `prob_swap` which proves an equality goal, `prob_swap_rw` performs a rewrite
and leaves the modified goal for further work. Useful when the swap is one step in a
larger proof.

Handles both `probOutput` (`Pr[= x | ...]`) and `probEvent` (`Pr[p | ...]`) goals. -/
macro "prob_swap_rw" : tactic =>
  `(tactic| (
    first
      | (simp only [← probEvent_eq_eq_probOutput]
         rw [probEvent_bind_bind_swap]
         try simp only [probEvent_eq_eq_probOutput])
      | rw [probEvent_bind_bind_swap]))

/-! ## Bind congruence tactics -/

/-- `prob_congr` reduces a `Pr[... | mx >>= f₁] = Pr[... | mx >>= f₂]` goal to a
pointwise equality of the continuations.

Applies `probOutput_bind_congr` or `probEvent_bind_congr`, producing a subgoal
`∀ x ∈ support mx, Pr[... | f₁ x] = Pr[... | f₂ x]`.

Use `prob_congr'` for the stronger variant without the support restriction. -/
macro "prob_congr" : tactic =>
  `(tactic|
    first
      | (apply probOutput_bind_congr)
      | (apply probEvent_bind_congr))

/-- `prob_congr'` is like `prob_congr` but produces `∀ x, ...` without a support restriction. -/
macro "prob_congr'" : tactic =>
  `(tactic|
    first
      | (apply probOutput_bind_congr')
      | (apply probEvent_bind_congr'))

/-! ## Enhanced exhaustive tactics -/

/-- Enhanced `game_rel` with more rules and better backtracking. -/
macro "game_rel'" : tactic =>
  `(tactic| (
    repeat (first
      | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
      | (refine OracleComp.ProgramLogic.Relational.relTriple_bind ?_ ?_
         <;> [skip; intro _ _ _])
      | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
      | (apply OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_evalDist_eq; rfl)
      | exact OracleComp.ProgramLogic.Relational.relTriple_query _
      | (apply OracleComp.ProgramLogic.Relational.relTriple_query_bij; skip)
      | (apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij; skip; skip)
      | (apply OracleComp.ProgramLogic.Relational.relTriple_map; skip)
      | (apply OracleComp.ProgramLogic.Relational.relTriple_if <;> [intro _; intro _]))
    all_goals try simp [game_rule]))

end OracleComp.ProgramLogic
