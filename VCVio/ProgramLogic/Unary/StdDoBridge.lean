/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Std.Tactic.Do
import VCVio.ProgramLogic.Unary.HoareTriple
import VCVio.ProgramLogic.Unary.WriterTBridge

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
variable [IsUniformSpec spec]
variable {α β : Type}

open Classical in
/-- Proposition-level bridge from quantitative WP (`= 1` threshold). -/
noncomputable def wpProp (oa : OracleComp spec α) (post : α → Prop) : Prop :=
  wp oa (fun x => if post x then 1 else 0) = 1

/-- Proposition-style triple alias used by the `Std.Do` bridge. -/
def tripleProp (pre : Prop) (oa : OracleComp spec α) (post : α → Prop) : Prop :=
  pre → wpProp (spec := spec) oa post

/-- Adequacy bridge between `wpProp` and event probability `= 1`. -/
theorem wpProp_iff_probEvent_eq_one (oa : OracleComp spec α) (p : α → Prop) :
    wpProp (spec := spec) oa p ↔ Pr[ p | oa] = 1 := by
  classical
  simp [wpProp, OracleComp.ProgramLogic.probEvent_eq_wp_indicator (spec := spec) oa p]

/-- Support-based characterization of almost-sure postconditions for `OracleComp`. -/
theorem wpProp_iff_forall_support (oa : OracleComp spec α) (p : α → Prop) :
    wpProp (spec := spec) oa p ↔ ∀ x ∈ support oa, p x := by
  simp [wpProp_iff_probEvent_eq_one]

/-- `wpProp` rule for `pure`. -/
theorem wpProp_pure (x : α) (p : α → Prop) :
    wpProp (spec := spec) (pure x : OracleComp spec α) p ↔ p x := by
  simp [wpProp_iff_forall_support]

/-- `wpProp` rule for bind. -/
theorem wpProp_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) (p : β → Prop) :
    wpProp (spec := spec) (oa >>= ob) p ↔ wpProp oa (fun a => wpProp (ob a) p) := by
  grind [wpProp_iff_forall_support]

private theorem wpProp_and (oa : OracleComp spec α) (p q : α → Prop) :
    wpProp (spec := spec) oa (fun a => p a ∧ q a) ↔
      wpProp oa p ∧ wpProp oa q := by
  grind [wpProp_iff_forall_support]

/-- `Std.Do` `WP` instance for `OracleComp`, scoped to almost-sure correctness. -/
noncomputable instance instWPOracleComp : Std.Do.WP (OracleComp spec) .pure where
  wp oa :=
    { trans := fun Q => ⌜wpProp (spec := spec) oa (fun a => (Q.1 a).down)⌝
      conjunctiveRaw := fun Q₁ Q₂ => SPred.pure_congr (by simp [wpProp_and]) }

/-- `Std.Do` `WPMonad` instance for `OracleComp` under `wpProp`. -/
noncomputable instance instWPMonadOracleComp : Std.Do.WPMonad (OracleComp spec) .pure where
  toLawfulMonad := inferInstance
  toWP := instWPOracleComp (spec := spec)
  wp_pure a := by
    ext Q
    exact wpProp_pure a _
  wp_bind x f := by
    ext Q
    exact wpProp_bind x f _

/-! ## Support-based bridge for stateful transformers over `OracleComp`

The two lemmas below reduce `Std.Do.Triple` for `StateT σ (OracleComp spec)` and
`WriterT ω (OracleComp spec)` to support-based statements about the underlying
`OracleComp` distribution. They are the canonical "escape hatch" used whenever a
handler proof needs to leave `mvcgen` (e.g. to perform a structural induction on
`OracleComp`) without abandoning the `Std.Do` proof mode entirely. -/

section StatefulBridges

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [IsUniformSpec spec]

/-- Support characterization of `Std.Do.Triple` on `StateT σ (OracleComp spec)`.

A triple `⦃P⦄ mx ⦃Q⦄` holds iff every outcome `(a, s')` in the support of
`mx.run s` satisfies the postcondition `Q.1 a s'`, whenever the starting state
`s` satisfies the precondition `P`. -/
theorem triple_stateT_iff_forall_support {σ α : Type}
    (mx : StateT σ (OracleComp spec) α)
    (P : Std.Do.Assertion (.arg σ .pure)) (Q : Std.Do.PostCond α (.arg σ .pure)) :
    Std.Do.Triple mx P Q ↔
      ∀ s : σ, (P s).down →
        ∀ a s', (a, s') ∈ support (mx.run s) → (Q.1 a s').down := by
  rw [Std.Do.Triple.iff]
  simp only [SPred.entails_1]
  refine forall_congr' (fun s => imp_congr_right (fun _hP => ?_))
  change wpProp (spec := spec) (mx.run s) (fun p => (Q.1 p.1 p.2).down) ↔ _
  rw [wpProp_iff_forall_support, Prod.forall]

/-- Support characterization of `Std.Do.Triple` on `WriterT ω (OracleComp spec)`.

A triple `⦃P⦄ mx ⦃Q⦄` over the writer log holds iff every outcome `(a, w)` in
the support of `mx.run` satisfies `Q.1 a (s ++ w)` for every starting log `s`
satisfying `P`. The starting log `s` threads through the WP interpretation
itself, not through `mx`: `WriterT.run mx` always begins from `∅` and produces
pairs `(a, w)`, and the WP transformer defined in
`VCVio.ProgramLogic.Unary.WriterTBridge` then prepends `s` via `s ++ _` before
applying the postcondition. This is why `s` appears only in `Q.1 a (s ++ w)`
on the right-hand side. -/
theorem triple_writerT_iff_forall_support {ω α : Type}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (mx : WriterT ω (OracleComp spec) α)
    (P : Std.Do.Assertion (.arg ω .pure)) (Q : Std.Do.PostCond α (.arg ω .pure)) :
    Std.Do.Triple mx P Q ↔
      ∀ s : ω, (P s).down →
        ∀ a w, (a, w) ∈ support mx.run → (Q.1 a (s ++ w)).down := by
  rw [Std.Do.Triple.iff]
  simp only [SPred.entails_1]
  refine forall_congr' (fun s => imp_congr_right (fun _hP => ?_))
  change wpProp (spec := spec) mx.run
      (fun p => (Q.1 p.1 (s ++ p.2)).down) ↔ _
  rw [wpProp_iff_forall_support, Prod.forall]

/-- `Monoid`-variant of `triple_writerT_iff_forall_support`.

For `WriterT ω (OracleComp spec)` where the log `ω` is a (multiplicative)
monoid, a triple `⦃P⦄ mx ⦃Q⦄` holds iff every outcome `(a, w)` in the support
of `mx.run` satisfies `Q.1 a (s * w)` for every starting log `s` satisfying
`P`. As in the `Append`-based variant, the starting log `s` threads through
the WP interpretation (`s * _`), not through `mx`. This is the dual of the
`Append`-based characterization and is what `countingOracle` / `costOracle`
proofs use (where `QueryCount ι = ι → ℕ` has a `Monoid` instance but no
`Append`). -/
theorem triple_writerT_iff_forall_support_monoid {ω α : Type} [Monoid ω]
    (mx : WriterT ω (OracleComp spec) α)
    (P : Std.Do.Assertion (.arg ω .pure)) (Q : Std.Do.PostCond α (.arg ω .pure)) :
    Std.Do.Triple mx P Q ↔
      ∀ s : ω, (P s).down →
        ∀ a w, (a, w) ∈ support mx.run → (Q.1 a (s * w)).down := by
  rw [Std.Do.Triple.iff]
  simp only [SPred.entails_1]
  refine forall_congr' (fun s => imp_congr_right (fun _hP => ?_))
  change wpProp (spec := spec) mx.run
      (fun p => (Q.1 p.1 (s * p.2)).down) ↔ _
  rw [wpProp_iff_forall_support, Prod.forall]

end StatefulBridges

namespace Spec

/-- Query specification for `mspec`/`mvcgen` in the `.pure` `Std.Do` view.

The bare `query` here resolves to `HasQuery.query (m := OracleComp spec)`, which
unfolds to `liftM (OracleSpec.query t)`. -/
@[spec] theorem query (t : spec.Domain) {Q : Std.Do.PostCond (spec.Range t) .pure} :
    Std.Do.Triple (HasQuery.query t : OracleComp spec (spec.Range t))
      (⌜wpProp (spec := spec) (HasQuery.query t) (fun a => (Q.1 a).down)⌝)
      Q := .rfl

/-- Bind-chain specification shape for `mspec`/`mvcgen` in OracleComp do-blocks. -/
@[spec] theorem query_bind (t : spec.Domain) {f : spec.Range t → OracleComp spec α}
    {Q : Std.Do.PostCond α .pure} :
    Std.Do.Triple ((HasQuery.query t : OracleComp spec (spec.Range t)) >>= f)
      (⌜wpProp (spec := spec)
        ((HasQuery.query t : OracleComp spec (spec.Range t)) >>= f) (fun a => (Q.1 a).down)⌝)
      Q := .rfl

/-- Explicit-head spec for the `MonadLift OracleQuery OracleComp`-form of `query`.

When `query t` appears inside a `do` block via `MonadLift`, Lean's elaborator
inserts a single `MonadLift.monadLift _ (OracleSpec.query t)` (no `MonadLiftT`
wrapper). The `HasQuery.query` form (the bare `query` after the ergonomic
cutover) instead elaborates via `MonadLiftT`. The two are definitionally
equal but syntactically distinct, and
`Lean.Elab.Tactic.Do.Spec.findSpec` matches keys syntactically against a
`DiscrTree`. This lemma re-states the content of `Spec.query` with the
explicit `MonadLift.monadLift` head so `mvcgen` finds a match in `do`-block
contexts. -/
@[spec] theorem monadLift_query (t : spec.Domain)
    {Q : Std.Do.PostCond (spec.Range t) .pure} :
    Std.Do.Triple
      (MonadLift.monadLift (OracleSpec.query t) : OracleComp spec (spec.Range t))
      (⌜wpProp (spec := spec) (HasQuery.query t) (fun a => (Q.1 a).down)⌝)
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
   `MonadLift.monadLift _ (OracleSpec.query t)` head that `do`-block
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
