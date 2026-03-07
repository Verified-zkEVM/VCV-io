/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Notation

/-!
# VCGen-Style Tactics for Probabilistic Program Logic

This file provides step-through tactics for game-hopping proofs, inspired by
EasyCrypt's `proc`, `wp`, `rnd`, `skip`, `swap`, and `seq`.

## Main tactics

### Unary WP
- `wp_step`: Apply exactly one WP rule (`wp_bind`, `wp_pure`, etc.)
- `game_wp` (enhanced): Exhaustively apply WP rules

### Relational (pRHL)
- `rel_step`: Decompose one `>>=` on each side (like EasyCrypt's `seq`/`wp`)
- `rel_rnd`: Couple random oracle queries or uniform sampling
- `rel_skip`: Both sides are identical or both pure
- `rel_pure`: Close a goal where both sides are `pure`
- `rel_cond`: Decompose a synchronized conditional (like EasyCrypt's `if`/`cond`)
- `rel_conseq`: Weaken/strengthen the postcondition (like EasyCrypt's `conseq`)
- `rel_inline`: Unfold a definition and retry
- `rel_sim`: Apply relational simulation rule

### Proof mode entry
- `by_equiv`: Transform a `GameEquiv` or `evalDist` equality into a `RelTriple`
- `game_trans`: Introduce an intermediate game for transitivity
- `by_dist`: Transform an advantage bound into a TV distance / relational goal
- `by_hoare`: Transform a probability goal into a quantitative WP goal

### Bind reordering
- `prob_swap`: Swap two independent sampling operations in a `Pr[...]` goal
-/

/-! ## Unary WP tactics -/

/-- `wp_step` applies exactly one WP decomposition rule and stops.
This gives step-by-step control, unlike the exhaustive `game_wp`. -/
macro "wp_step" : tactic =>
  `(tactic| first
    | rw [OracleComp.ProgramLogic.wp_bind]
    | rw [OracleComp.ProgramLogic.wp_pure]
    | simp only [OracleComp.ProgramLogic.wp_pure]
    | rw [OracleComp.ProgramLogic.wp_query]
    | rw [OracleComp.ProgramLogic.wp_ite]
    | rw [OracleComp.ProgramLogic.wp_uniformSample]
    | rw [OracleComp.ProgramLogic.wp_map]
    | rw [OracleComp.ProgramLogic.wp_simulateQ_eq]
    | rw [OracleComp.ProgramLogic.wp_liftComp])

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

macro_rules
  | `(tactic| rel_step) =>
    `(tactic|
      first
        | refine OracleComp.ProgramLogic.Relational.relTriple_bind
            (R := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_
        | refine OracleComp.ProgramLogic.Relational.relTriple_bind ?_ ?_)
  | `(tactic| rel_step using $R) =>
    `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind (R := $R) ?_ ?_)

/-- `rel_rnd` couples random oracle queries or uniform sampling on both sides.

Tries the following rules in order:
1. `relTriple_query` — identity coupling for same oracle queries
2. `relTriple_refl` — reflexivity (same computation)
3. `relTriple_query_bij` — bijection coupling for oracle queries
4. `relTriple_uniformSample_bij` — bijection coupling for uniform sampling
5. `relTriple_eqRel_of_evalDist_eq` — equal distributions

Use `rel_rnd using f` to specify the bijection explicitly. -/
syntax "rel_rnd" ("using" term)? : tactic

macro_rules
  | `(tactic| rel_rnd) =>
    `(tactic|
      first
        | exact OracleComp.ProgramLogic.Relational.relTriple_query _
        | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
        | (apply OracleComp.ProgramLogic.Relational.relTriple_query_bij
           <;> [skip])
        | (apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij
           <;> [skip; skip])
        | (apply OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_evalDist_eq
           <;> [skip]))
  | `(tactic| rel_rnd using $f) =>
    `(tactic|
      first
        | (apply OracleComp.ProgramLogic.Relational.relTriple_query_bij _ (f := $f)
           <;> [skip])
        | (apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij (f := $f)
           <;> [skip; skip]))

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
macro "rel_sim" : tactic =>
  `(tactic|
    first
      | (apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'
         <;> [skip; skip; skip; skip])
      | (apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run
         <;> [skip; skip; skip; skip]))

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
    simp only [bind_assoc]
    first
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
         simp only [bind_assoc]
         exact probEvent_bind_bind_swap _ _ _ _)))

/-- `prob_swap_at n` repeatedly applies `prob_swap` up to `n` times. -/
macro "prob_swap_at" n:num : tactic =>
  `(tactic| (iterate $n prob_swap))

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
