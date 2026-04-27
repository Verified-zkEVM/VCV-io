/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Experimental.UnifiedLSpec

/-!
# Phase 1: backward-rule application for `@[lspec_spike]` (spike)

**Status: experimental spike.** Imported by `VCVio.lean` because CI
checks that every library file is reachable from its umbrella file, but
not wired into the production `vcstep` / `rvcstep` tactics.

This file is Phase 1 of the migration plan tracked in issue #351.
It builds the smallest piece of machinery on top of
`UnifiedLSpec.lean` that lets a goal in `⊑`-form be **closed** (or
reduced to subgoals) by an entry returned from `lookup`:

* `bridgeToLeForm`: instantiate an `LSpecEntry`'s proof with fresh
  metavars and bridge `Triple → ⊑ wp`.  `RelTriple` is a `def` and
  unfolds definitionally, so it needs no explicit rewrite.

* `tryApply`: feed the bridged proof into `Meta.apply` against a goal
  metavariable.  Returns `none` if the entry does not apply, otherwise
  the list of remaining subgoals (typically `[]` for our demo lemmas).

* `tryApplyMatching`: glue together `lookup` and `tryApply`: take a
  goal in `⊑`-form, classify it (unary or relational), look up
  matching entries from the unified registry, and apply the first one
  that succeeds.  Mirrors how `vcstep`/`rvcstep` would consume the new
  registry side-by-side with the legacy `@[vcspec]` chain.

## Scope of Phase 1

What this layer covers:

* Lemmas whose `pre`, `post`, and `epost` are abstract (forall-bound),
  e.g. `triple_pure : Triple (post x) (pure x) post`.  Specialisation
  happens through ordinary unification inside `Meta.apply`.

* Goals whose `post` and `epost` slots match a registered lemma after
  beta/eta reduction (Lean's `isDefEq` handles those routinely).

What it intentionally does **not** cover:

* Consequence weakening when the lemma's `post` or `epost` is
  *concrete* but the goal's is different.  Loom2's
  `mkSpecBackwardProof` (`Loom/Tactic/Spec.lean:143-258`) handles this
  by abstracting `post`/`epost` to fresh mvars and chaining
  `WP.wp_consequence_rel` / `WP.wp_econs_rel`; doing the same here is
  the natural extension once Phase 2 (side-by-side mode in
  `vcstep`/`rvcstep`) needs it.

* Excess-state args (e.g. `Pred = σ → Prop`).  Our quantitative
  carriers are flat (`ℝ≥0∞`, `Prob`), so no state binders are
  required for the spike.

* Full `BackwardRule` caching.  The production entry point below caches
  lookup results by normalized target expression, but still rebuilds the
  bridged proof at application time so each attempt gets fresh
  metavariables.

The goal of Phase 1 is to demonstrate end-to-end usefulness of the
unified registry, not to ship a production tactic.  See
`UnifiedLSpecBackwardDemo.lean` for the worked example.
-/

open Lean Elab Meta
open Lean.Elab.Tactic.Do.SpecAttr (SpecProof)

namespace OracleComp.ProgramLogic.Experimental

/-! ## Bridging to `⊑`-form -/

/--
If `(prf, type)` represents a proof of `Std.Do'.Triple pre x post epost`,
return the `⊑`-form `prf' : pre ⊑ wp x post epost` and its type.
Otherwise return the input unchanged.

This mirrors Loom2's `Loom.Tactic.SpecAttr.tripleToWpProof?` (see
`loom2/Loom/Tactic/Attr.lean:52-66`).  We need to manually reorder
the type-class arguments because `Std.Do'.Triple` and
`Std.Do'.Triple.iff` quantify them in different positions:

* `Triple` order:    `m Pred EPred α Monad AL EAL WP pre x post epost`
* `Triple.iff` order: `m Pred EPred Monad AL EAL WP α x pre post epost`

(`Triple.iff` is defined inside `namespace Triple` in
`loom2/Loom/Triple/Basic.lean:47-49`, after a `variable` declaration
that fixes `m Pred EPred`.  The `α` migrates to a section-local
implicit and ends up after the instances.)
-/
private def bridgeTriple? (prf type : Expr) : MetaM (Expr × Expr) := do
  let type ← whnfR type
  if type.isAppOfArity ``Std.Do'.Triple 12 then
    let .const _ lvls := type.getAppFn
      | return (prf, type)
    let args := type.getAppArgs
    let tripleIff := mkAppN (mkConst ``Std.Do'.Triple.iff lvls)
      #[ args[0]!  -- m
       , args[1]!  -- Pred
       , args[2]!  -- EPred
       , args[4]!  -- Monad
       , args[5]!  -- Assertion Pred
       , args[6]!  -- Assertion EPred
       , args[7]!  -- WP
       , args[3]!  -- α
       , args[9]!  -- x
       , args[8]!  -- pre
       , args[10]! -- post
       , args[11]! -- epost
       ]
    let prf' ← mkAppM ``Iff.mp #[tripleIff, prf]
    let type' ← instantiateMVars (← inferType prf')
    return (prf', type')
  else
    return (prf, type)

/--
Instantiate an `LSpecEntry`'s proof and (if needed) bridge to
`pre ⊑ wp …` form.

For unary entries whose lemma is stated as `Triple …`, this calls
`Triple.iff.mp` so the resulting proof has type `pre ⊑ wp x post epost`.
For relational entries whose lemma is already in `pre ⊑ rwp …` form
(e.g. `rwp_pure`), no rewriting is needed; `RelTriple` itself is a
`def` and unfolds definitionally during `Meta.apply`'s `isDefEq`.

Returns `(proof, type, postMVars)` where `postMVars` is the array of
metavariables introduced for the lemma's universally quantified
parameters (currently unused by the apply path; kept so that future
versions can post-filter on `WP`/`RelWP` instance metavariables).
-/
def bridgeToLeForm (entry : LSpecEntry) :
    MetaM (Expr × Expr × Array Expr) := do
  let (xs, _bs, prf, type) ← entry.proof.instantiate
  let (prf', type') ← bridgeTriple? prf type
  return (prf', type', xs)

/-! ## Applying an entry to a goal -/

/--
For lemmas whose `Pred` is universe-polymorphic (e.g.
`rwp_pure : post a b ⊑ rwp (pure a) (pure b) post epost₁ epost₂`),
`Lean.Order.PartialOrder.rel` cannot reduce to `≤` until `Pred` is
fixed.  But the goal `0 ≤ rwp …` uses raw `≤`, so `Meta.apply` reaches
a dead end (it cannot unify `rel ?Pred …` with `≤ ENNReal …` without
already knowing `?Pred = ENNReal`).

We unblock this by inspecting the goal: if the goal head is `≤` at
some concrete `Pred`, we eagerly unify the bridged proof's `Pred`
slot with that type before handing off to `Meta.apply`.

This mirrors what Loom2's `BackwardRule.apply` does indirectly via
`Sym.Pattern.unify?` (which carries the lattice type as a pattern
key and unifies it eagerly).
-/
private def fixPredFromGoal? (prfTy goalTy : Expr) : MetaM Unit := do
  -- Bridged proof type: `Lean.Order.PartialOrder.rel (Pred := ?P) ?pre ?rhs`
  let prfTy ← whnfR prfTy
  let goalTy ← whnfR goalTy
  unless prfTy.isAppOfArity ``Lean.Order.PartialOrder.rel 4 do return
  -- Goal: `LE.le (α := P) ?pre ?rhs` (P is the ambient type of the precondition)
  unless goalTy.isAppOfArity ``LE.le 4 do return
  let prfPred  := prfTy.getArg! 0
  let goalPred := goalTy.getArg! 0
  -- Best-effort: if either side is still a metavariable, unify; ignore failure.
  _ ← isDefEq prfPred goalPred

/--
Try to apply `entry` to the goal `mvarId`, which is expected to be in
`⊑`-form (`pre ⊑ wp …` or `pre ⊑ rwp …`, equivalently `≤` in our
quantitative carriers).

Returns `some subgoals` on success, `none` if the entry does not
unify or `Meta.apply` raises an exception.  No subgoals reasonably
remain for `triple_pure` and `rwp_pure` against fully-concrete goals,
which is what the demo file checks.
-/
def tryApply (mvarId : MVarId) (entry : LSpecEntry) :
    MetaM (Option (List MVarId)) := do
  let (prf, ty, _xs) ← bridgeToLeForm entry
  let goalTy ← instantiateMVars (← mvarId.getType)
  fixPredFromGoal? ty goalTy
  try
    let subgoals ← mvarId.apply prf
    return some subgoals
  catch _ =>
    return none

/-- Debug variant of `tryApply` that surfaces the `Meta.apply` error
when it fires.  Useful while iterating on the spike. -/
def tryApplyDebug (mvarId : MVarId) (entry : LSpecEntry) :
    MetaM (Except String (List MVarId)) := do
  let (prf, ty, _xs) ← bridgeToLeForm entry
  let goalTy ← instantiateMVars (← mvarId.getType)
  fixPredFromGoal? ty goalTy
  try
    let subgoals ← mvarId.apply prf
    return .ok subgoals
  catch ex =>
    let msg ← ex.toMessageData.toString
    return .error msg

/--
End-to-end backward chaining: classify the goal, look up matching
entries from the unified registry, and apply the first one that
succeeds.  Returns the chosen entry plus any remaining subgoals.

This is the single function that a future `vcstep`-style tactic would
call once per step.  It is intentionally side-effect-free with respect
to the legacy `@[vcspec]` registries; Phase 2 of the migration plan
(issue #351) will wire it in side-by-side.
-/
def tryApplyMatching (mvarId : MVarId) :
    MetaM (Option (LSpecEntry × List MVarId)) := do
  let target ← instantiateMVars (← mvarId.getType)
  let candidates ← lookup target
  for entry in candidates do
    match ← tryApply mvarId entry with
    | none           => continue
    | some subgoals  => return some (entry, subgoals)
  return none

initialize lspecBackwardLookupCache : IO.Ref (Std.HashMap Expr (Array LSpecEntry)) ←
  IO.mkRef {}

private def backwardLookupKey (target : Expr) : MetaM Expr := do
  let target ← instantiateMVars target
  whnfR target

/-- Cached lookup for the production side-by-side backward path.

The cached value is the set of registry entries selected for a normalized target.
`tryApply` is intentionally rerun with fresh metavariables for each goal. -/
def lookupCached (target : Expr) : MetaM (Array LSpecEntry) := do
  let key ← backwardLookupKey target
  let cache ← lspecBackwardLookupCache.get
  match cache[key]? with
  | some candidates => return candidates
  | none =>
      let candidates ← lookup key
      lspecBackwardLookupCache.modify fun cache => cache.insert key candidates
      return candidates

/-- Cached end-to-end backward chaining used by production tactics. -/
def tryApplyMatchingCached (mvarId : MVarId) :
    MetaM (Option (LSpecEntry × List MVarId)) := do
  let target ← instantiateMVars (← mvarId.getType)
  let candidates ← lookupCached target
  for entry in candidates do
    match ← tryApply mvarId entry with
    | none           => continue
    | some subgoals  => return some (entry, subgoals)
  return none

end OracleComp.ProgramLogic.Experimental
