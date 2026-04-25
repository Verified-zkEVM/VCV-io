/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Experimental.UnifiedLSpec
import VCVio.ProgramLogic.Tactics.Experimental.UnifiedLSpecBackward
import VCVio.ProgramLogic.Tactics.Experimental.UnifiedLSpecDemo

/-!
# Phase 1: backward-rule demo for `@[lspec_spike]` (spike)

**Status: experimental spike.** Imported by `VCVio.lean` because CI
checks that every library file is reachable from its umbrella file, but
not wired into the production `vcstep` / `rvcstep` tactics.

This file demonstrates that `tryApplyMatching` from
`UnifiedLSpecBackward.lean` can actually **close** a goal end-to-end,
using only the unified `@[lspec_spike]` registry populated in
`UnifiedLSpecDemo.lean`.

The two probes reuse the synthetic goal *types* defined in the
registration demo (`unaryProbe`, `relProbe`).  Each test:

1. Creates a fresh metavariable whose target is the probe's type.
2. Calls `tryApplyMatching`, which classifies the goal, queries the
   unified registry, and applies the first matching entry.
3. Reports which entry fired and how many subgoals remain.

For both `triple_pure` and `rwp_pure`, the lemma instantiates and
closes the goal directly: zero remaining subgoals.

Combined with `UnifiedLSpecDemo.lean`, this confirms the Route A
hypothesis: a single attribute, a single registry, kind-tagged
lookup, and uniform backward chaining are sufficient to handle both
unary and relational program-logic specs.
-/

open Lean Meta Elab Term
open OracleComp.ProgramLogic.Experimental

namespace OracleComp.ProgramLogic.Experimental.BackwardDemo

/-! ## Helper -/

/--
Allocate a synthetic goal whose target is the type of `probe`, then
report what `tryApplyMatching` does to it.
-/
private def runProbe (label : String) (probe : Name) : MetaM Unit := do
  let ty ← inferType (mkConst probe)
  IO.println s!"{label} goal type:  {← Meta.ppExpr ty}"
  let goal ← mkFreshExprSyntheticOpaqueMVar ty
  match ← tryApplyMatching goal.mvarId! with
  | none =>
      IO.println s!"  → tryApplyMatching: no entry applied"
  | some (entry, subgoals) =>
      let nm : Name := match entry.proof with
        | .global n => n
        | _ => `«local»
      IO.println s!"  → tryApplyMatching applied: {nm}"
      IO.println s!"      remaining subgoals: {subgoals.length}"
      for sg in subgoals do
        let sgTy ← instantiateMVars (← sg.getType)
        IO.println s!"        - {← Meta.ppExpr sgTy}"

/-! ## Demo -/

def demoBackward : MetaM Unit := do
  IO.println "── Phase 1: backward-rule application demo ──"
  runProbe "unary"      ``OracleComp.ProgramLogic.Experimental.Demo.unaryProbe
  runProbe "relational" ``OracleComp.ProgramLogic.Experimental.Demo.relProbe

run_meta demoBackward

/-! ## Expected output

```
── Phase 1: backward-rule application demo ──
unary goal type:  0 ≤ Std.Do'.wp (pure 7) (fun x ↦ 0) epost⟨⟩
  → tryApplyMatching applied: OracleComp.ProgramLogic.triple_pure
      remaining subgoals: 0
relational goal type:  0 ≤ Std.Do'.rwp (pure 1) Demo.relRightAlias (fun x x_1 ↦ 0) epost⟨⟩ epost⟨⟩
  → tryApplyMatching applied: Std.Do'.RelWP.rwp_pure
      remaining subgoals: 0
```

Both probes are closed by the single registered lemma of the matching
kind, with no remaining subgoals.  Concretely:

* `triple_pure : Triple (post x) (pure x) post` is bridged to
  `(post x) ⊑ wp (pure x) post ⊥` by `Triple.iff.mp`, then unified
  against `0 ≤ wp (pure 7) (fun _ => 0) ⊥`.  Unification fixes
  `x := 7`, `post := fun _ => 0`, and the LHS β-reduces to `0`.

* `rwp_pure : post a b ⊑ rwp (pure a) (pure b) post epost₁ epost₂`
  needs no bridging (already in `⊑`-form).  Unification sees through
  `relRightAlias`, fixes `a := 1`, `b := 2`, `post := fun _ _ => 0`,
  and the LHS β-reduces to `0`.

This is the smallest end-to-end proof that the unified `@[lspec_spike]`
registry can support a backward-chaining tactic with no per-kind
plumbing on the application side.
-/

end OracleComp.ProgramLogic.Experimental.BackwardDemo
