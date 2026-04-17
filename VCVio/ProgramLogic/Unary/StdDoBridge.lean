/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Std.Tactic.Do
import VCVio.ProgramLogic.Unary.HoareTriple
import VCVio.OracleComp.Coercions.SubSpec

/-!
# `Std.Do` / `mvcgen` bridge for `OracleComp`

This module provides a proposition-level bridge on top of the quantitative WP in
`ProgramLogic.Unary.HoareTriple`, with a `Std.Do.WPMonad` instance for `.pure` post-shape.
The bridge is scoped to almost-sure correctness (`= 1`).
-/

open ENNReal
open Std.Do

universe u

namespace OracleComp.ProgramLogic.StdDo

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β : Type}

/-- Proposition-level bridge from quantitative WP (`= 1` threshold). -/
noncomputable def wpProp (oa : OracleComp spec α) (post : α → Prop) : Prop := by
  classical
  exact OracleComp.ProgramLogic.wp (spec := spec) oa (fun x => if post x then 1 else 0) = 1

/-- Proposition-style triple alias used by the `Std.Do` bridge. -/
def tripleProp (pre : Prop) (oa : OracleComp spec α) (post : α → Prop) : Prop :=
  pre → wpProp (spec := spec) oa post

/-- Adequacy bridge between `wpProp` and event probability `= 1`. -/
theorem wpProp_iff_probEvent_eq_one (oa : OracleComp spec α) (p : α → Prop) :
    wpProp (spec := spec) oa p ↔ Pr[ p | oa] = 1 := by
  classical
  let _ : DecidablePred p := Classical.decPred p
  constructor <;> intro h
  · simpa [wpProp, OracleComp.ProgramLogic.probEvent_eq_wp_indicator (spec := spec) oa p] using h
  · simpa [wpProp, OracleComp.ProgramLogic.probEvent_eq_wp_indicator (spec := spec) oa p] using h

/-- Support-based characterization of almost-sure postconditions for `OracleComp`. -/
theorem wpProp_iff_forall_support (oa : OracleComp spec α) (p : α → Prop) :
    wpProp (spec := spec) oa p ↔ ∀ x ∈ support oa, p x := by
  rw [wpProp_iff_probEvent_eq_one]
  constructor
  · intro h
    exact (probEvent_eq_one_iff (mx := oa) (p := p)).1 h |>.2
  · intro h
    exact probEvent_eq_one (mx := oa) (p := p)
      ⟨HasEvalPMF.probFailure_eq_zero oa, h⟩

/-- `wpProp` rule for `pure`. -/
theorem wpProp_pure (x : α) (p : α → Prop) :
    wpProp (spec := spec) (pure x : OracleComp spec α) p ↔ p x := by
  simp [wpProp_iff_forall_support]

/-- `wpProp` rule for bind. -/
theorem wpProp_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) (p : β → Prop) :
    wpProp (spec := spec) (oa >>= ob) p ↔ wpProp oa (fun a => wpProp (ob a) p) := by
  rw [wpProp_iff_forall_support, wpProp_iff_forall_support]
  constructor
  · intro h a ha
    rw [wpProp_iff_forall_support (spec := spec) (oa := ob a) (p := p)]
    intro b hb
    exact h b ((mem_support_bind_iff oa ob b).2 ⟨a, ha, hb⟩)
  · intro h b hb
    rcases (mem_support_bind_iff oa ob b).1 hb with ⟨a, ha, hb'⟩
    exact ((wpProp_iff_forall_support (spec := spec) (oa := ob a) (p := p)).1 (h a ha)) b hb'

private theorem wpProp_and (oa : OracleComp spec α) (p q : α → Prop) :
    wpProp (spec := spec) oa (fun a => p a ∧ q a) ↔
      wpProp oa p ∧ wpProp oa q := by
  rw [wpProp_iff_forall_support, wpProp_iff_forall_support, wpProp_iff_forall_support]
  constructor
  · intro h
    exact ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩
  · intro h x hx
    exact ⟨h.1 x hx, h.2 x hx⟩

/-- `Std.Do` `WP` instance for `OracleComp`, scoped to almost-sure correctness. -/
noncomputable instance instWPOracleComp : Std.Do.WP (OracleComp spec) .pure where
  wp oa :=
    { trans := fun Q => ⌜wpProp (spec := spec) oa (fun a => (Q.1 a).down)⌝
      conjunctiveRaw := by
        intro Q₁ Q₂
        apply SPred.pure_congr
        simp [wpProp_and] }

/-- `Std.Do` `WPMonad` instance for `OracleComp` under `wpProp`. -/
noncomputable instance instWPMonadOracleComp : Std.Do.WPMonad (OracleComp spec) .pure where
  toLawfulMonad := inferInstance
  toWP := instWPOracleComp (spec := spec)
  wp_pure a := by
    ext Q
    change wpProp (spec := spec) (pure a) (fun a => (Q.1 a).down) ↔ (Q.1 a).down
    exact wpProp_pure a _
  wp_bind x f := by
    ext Q
    change wpProp (spec := spec) (x >>= f) (fun b => (Q.1 b).down) ↔
      wpProp x (fun a => wpProp (f a) (fun b => (Q.1 b).down))
    exact wpProp_bind x f _

namespace Spec

/-- Query specification for `mspec`/`mvcgen` in the `.pure` `Std.Do` view. -/
@[spec] theorem query (t : spec.Domain) {Q : Std.Do.PostCond (spec.Range t) .pure} :
    Std.Do.Triple (OracleComp.query t : OracleComp spec (spec.Range t))
      (⌜wpProp (spec := spec) (OracleComp.query t) (fun a => (Q.1 a).down)⌝)
      Q := by
  simp [Std.Do.Triple, Std.Do.WP.wp, PredTrans.apply]

/-- Bind-chain specification shape for `mspec`/`mvcgen` in OracleComp do-blocks. -/
@[spec] theorem query_bind (t : spec.Domain) {f : spec.Range t → OracleComp spec α}
    {Q : Std.Do.PostCond α .pure} :
    Std.Do.Triple ((OracleComp.query t : OracleComp spec (spec.Range t)) >>= f)
      (⌜wpProp (spec := spec)
        ((OracleComp.query t : OracleComp spec (spec.Range t)) >>= f) (fun a => (Q.1 a).down)⌝)
      Q := by
  simp [Std.Do.Triple, Std.Do.WP.wp, PredTrans.apply]

/-- Explicit-head spec for the `MonadLift OracleQuery OracleComp`-form of `query`.

When `query t` appears inside a `do` block, Lean's elaborator inserts a single
`MonadLift.monadLift _ (OracleQuery.query t)` (no `MonadLiftT` wrapper). The
ascription form `(OracleComp.query t : OracleComp spec _)` instead elaborates
to `liftM (instMonadLiftTOfMonadLift _ _) (OracleQuery.query t)`. The two are
definitionally equal but syntactically distinct, and
`Lean.Elab.Tactic.Do.Spec.findSpec` matches keys syntactically against a
`DiscrTree`. This lemma re-states the content of `Spec.query` with the
explicit `MonadLift.monadLift` head so `mvcgen` finds a match in `do`-block
contexts. The two should be unified once core `mvcgen` normalizes
`liftM`/`MonadLiftT` chains in its discrimination-tree key construction
(upstream issue). -/
@[spec] theorem monadLift_query (t : spec.Domain)
    {Q : Std.Do.PostCond (spec.Range t) .pure} :
    Std.Do.Triple
      (MonadLift.monadLift (OracleQuery.query t) : OracleComp spec (spec.Range t))
      (⌜wpProp (spec := spec) (OracleComp.query t) (fun a => (Q.1 a).down)⌝)
      Q := Spec.query t

/-!
## Architectural note: `mvcgen` for stateful handlers over `OracleComp`

Stateful handlers like `cachingOracle` (`StateT`) and `loggingOracle`
(`WriterT`) are defined as `QueryImpl spec (T (OracleComp spec))` for some
state-tracking transformer `T`. `mvcgen` walks their bodies cleanly thanks
to:

1. The low-priority `MonadLift (OracleComp spec) (OracleComp superSpec)`
   instance in `Coercions/SubSpec.lean`. By being lower priority than Lean's
   built-in reflexive `MonadLiftT.refl`, the self-lift case
   (`spec = superSpec`) is solved by `MonadLiftT.refl` rather than this
   parametric instance, and `monadLift mx : OracleComp spec α` reduces to
   `id mx = mx` definitionally. This is what
   `Std.Do.Spec.UnfoldLift.monadLift_refl` (a `rfl`-based lemma) needs in
   order to peel off the spurious self-lifts the parametric instance would
   otherwise leave behind around every nested oracle query. By being lower
   priority than the built-in `MonadLift (OracleQuery superSpec) (OracleComp
   superSpec)`, single-query lifts also resolve via the standard "lift query
   then embed" path and avoid spurious walks through `liftComp`.

2. The `Spec.monadLift_query` lemma below, which provides a
   `DiscrTree`-friendly `@[spec]` keyed by the explicit
   `MonadLift.monadLift _ (OracleQuery.query t)` head that `do`-block
   elaboration produces. The plain `Spec.query` above keys on a different
   syntactic head and doesn't fire inside `do` blocks.

The first is now structural in VCVio with no special override needed. The
second is a workaround for a discrimination-tree-key normalisation gap in
upstream `mvcgen` and can be removed once
`Lean.Elab.Tactic.Do.Spec.findSpec` and `Lean.Elab.Tactic.Do.Attr.mkSpecTheorem`
canonicalise `liftM`/`MonadLiftT` chains.
-/

end Spec

end OracleComp.ProgramLogic.StdDo
