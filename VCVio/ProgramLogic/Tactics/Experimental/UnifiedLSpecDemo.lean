/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Experimental.UnifiedLSpec

/-!
# Unified `@[lspec_spike]` Attribute (spike, demo)

**Status: experimental spike.** Imported by `VCVio.lean` because CI
checks that every library file is reachable from its umbrella file, but
not wired into the production `vcstep` / `rvcstep` tactics.

This file demonstrates Route A from the relational-tactic-alignment
investigation: a *single* attribute, indexed by program head, that
covers both unary (`Triple`/`pre ⊑ wp …`) and relational
(`RelTriple`/`pre ⊑ rwp …`) lemmas end-to-end.

## What the spike establishes

1. **Auto-bridging at registration.** Both `Triple → ⊑ wp` (via
   `Std.Do'.Triple.iff`) and `RelTriple → ⊑ rwp` (definitionally,
   since `RelTriple` is a `def`) are handled in the attribute's `add`
   handler, so the stored proof is uniformly in `⊑`-form. This is
   the same normalization Loom2's `@[lspec]` does for the unary
   side.

2. **Single registry, kind-tagged entries.** One `Sym.DiscrTree`
   keyed on the head of the *program* slot. Unary entries use the
   head of `c`; relational entries use the head of the *left*
   program `x`, with the head of the *right* program `y` cached as a
   secondary filter. This is implemented by `selectLSpecKey` in the
   companion file.

3. **Uniform lookup.** `lookup` takes a target in `⊑`-form, classifies
   it as unary or relational by the rhs head (`Std.Do'.wp` vs
   `Std.Do'.rwp`), and returns matching entries with the right
   secondary filter applied.

## What the spike confirms

* The lookup tree is shared but does *not* cross-contaminate: a unary
  goal returns only `LSpecKind.unary` entries, and vice versa. The
  registry is checked at runtime via `reportRegistry` and the two
  `demoLookup*` functions below.

* Pre-existing lemmas (`triple_pure` on the unary side, `rwp_pure`
  on the relational side) are accepted by the new attribute without
  any rewriting of the lemma statements. That is the main
  ergonomic claim: lemma authors keep writing `Triple` /
  `RelTriple`, and the unified registry handles the bridging.

## What the spike does *not* do

* Build backward rules. That is straightforward once the proof is in
  `⊑`-form (see `Loom.Tactic.Spec.tryMkBackwardRuleFromSpec`).
* Implement match/let/lattice splitting, caching, or
  OracleComp-specific pre-passes. Those layers would sit *above* the
  unified kernel exactly as they do today.
* Replace the current `@[vcspec]` / `@[wpStep]` registrations.
  Migration would happen in a follow-up PR.
-/

open Lean Elab Meta
open OracleComp.ProgramLogic.Experimental

attribute [lspec_spike] OracleComp.ProgramLogic.triple_pure
attribute [lspec_spike] Std.Do'.RelWP.rwp_pure

namespace OracleComp.ProgramLogic.Experimental.Demo

/-! ## Reporting -/

def reportRegistry : MetaM Unit := do
  let registry := lspecRegistry.getState (← getEnv)
  IO.println s!"unified-lspec-spike: {registry.all.size} registered entries"
  for entry in registry.all do
    let proofName : Name :=
      match entry.proof with
      | .global n => n
      | _ => `«local»
    let kindStr : String :=
      match entry.kind with
      | .unary => "unary"
      | .relational rh => s!"relational(rightHead = {rh})"
    IO.println s!"  • {proofName}  [{kindStr}]  prio={entry.priority}"

run_meta reportRegistry

/-! ## Lookup demo

We elaborate two synthetic goal terms (one unary, one relational)
and confirm that `lookup` returns exactly the registered entries.

The goal terms are stated against the oracle spec `unifSpec`, with
`ProbComp = OracleComp unifSpec`, so all the carrier instances
(`Std.Do'.WP (ProbComp _) ℝ≥0∞ EPost.nil` and the relational
counterpart) are visible from `Loom/Quantitative.lean`.
-/

open Lean Meta Elab Term

/-- Bench: the *type* of this term is the unary `⊑`-form goal we want
to look up against. -/
def unaryProbe : (0 : ENNReal) ≤
    Std.Do'.wp (pure 7 : ProbComp ℕ) (fun _ => (0 : ENNReal))
      Std.Do'.EPost.nil.mk := by
  exact zero_le _

/-- Reducible alias used to ensure relational right-head filtering sees
through definitionally equal wrappers. -/
abbrev relRightAlias : ProbComp ℕ := pure 2

/-- Bench: the *type* of this term is the relational `⊑`-form goal we
want to look up against.

The right program intentionally uses `relRightAlias`, so lookup must
normalize the right-hand side before applying the secondary right-head
filter. -/
def relProbe : (0 : ENNReal) ≤
    Std.Do'.rwp (pure 1 : ProbComp ℕ) relRightAlias
      (fun _ _ => (0 : ENNReal)) Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk := by
  exact zero_le _

def demoLookups : MetaM Unit := do
  let unaryTy ← inferType (mkConst ``unaryProbe)
  let unaryHits ← lookup unaryTy
  IO.println s!"unary goal type:  {← Meta.ppExpr unaryTy}"
  IO.println s!"  → unary lookup hits: {unaryHits.size}"
  for entry in unaryHits do
    let nm : Name := match entry.proof with
      | .global n => n
      | _ => `«local»
    IO.println s!"      {nm}"
  let relTy ← inferType (mkConst ``relProbe)
  let relHits ← lookup relTy
  IO.println s!"relational goal type:  {← Meta.ppExpr relTy}"
  IO.println s!"  → relational lookup hits: {relHits.size}"
  for entry in relHits do
    let nm : Name := match entry.proof with
      | .global n => n
      | _ => `«local»
    IO.println s!"      {nm}"

run_meta demoLookups

/-! ## Expected output

When this file is built, the two `run_meta` blocks above should print
something like:

```
unified-lspec-spike: 2 registered entries
  • OracleComp.ProgramLogic.triple_pure  [unary]  prio=1000
  • Std.Do'.RelWP.rwp_pure  [relational(rightHead = Pure.pure)]  prio=1000
unary goal type:  0 ≤ Std.Do'.wp (pure 7) (fun x ↦ 0) epost⟨⟩
  → unary lookup hits: 1
      OracleComp.ProgramLogic.triple_pure
relational goal type:  0 ≤ Std.Do'.rwp (pure 1) relRightAlias (fun x x_1 ↦ 0) epost⟨⟩ epost⟨⟩
  → relational lookup hits: 1
      Std.Do'.RelWP.rwp_pure
```

The two key claims of the spike are confirmed:

1. **Unified registration auto-bridges both shapes.** The unary
   `triple_pure` entered the registry from a `Triple` lemma, and
   the relational `rwp_pure` entered from a `pre ⊑ rwp …` lemma.
   No lemma rewriting required.

2. **Single registry, kind-tagged lookup is correct.** The DiscrTree
   is shared (both entries share program head `Pure.pure`), but
   each goal recovers exactly the matching-kind entries:

   * The unary `≤ Std.Do'.wp` goal returns only `triple_pure`.
   * The relational `≤ Std.Do'.rwp` goal returns only `rwp_pure`, even
     when the right program is wrapped in a reducible alias.

The code in `UnifiedLSpec.lean` is ~190 lines including comments;
real migration to this kernel would replace `@[vcspec]` and friends
in `Tactics/Common/Registry.lean`. -/

end OracleComp.ProgramLogic.Experimental.Demo
