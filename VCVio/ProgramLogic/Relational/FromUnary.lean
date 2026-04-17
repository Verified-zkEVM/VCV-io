/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Unary.StdDoBridge
import VCVio.ProgramLogic.Relational.Basic

/-!
# Lifting unary `Std.Do` triples to relational couplings

Two `OracleComp` computations that are independently correct (each satisfying a unary
`Std.Do.Triple`) can always be paired via the product coupling, since every
`OracleComp` distribution sums to probability `1` (`HasEvalPMF`).

This file provides the "unary → relational" bridge:

* `relTriple_prod_of_wpProp` — two unary `wpProp` witnesses give a relational triple on
  the product postcondition.
* `relTriple_prod_of_triple` — same statement, phrased directly in terms of
  `Std.Do.Triple`.
* `relTriple_prod` — a slightly stronger variant taking `support`-style postconditions.

These lemmas let proofs established against the stateful `Std.Do`/`mvcgen` proof mode
be composed into relational arguments (e.g. game-hopping reductions) without redoing
the underlying analysis.
-/

open ENNReal OracleSpec OracleComp
open Std.Do

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β : Type}

/-- Core lift: two `support`-style unary postconditions combine into a relational
coupling. The product coupling `evalDist oa ⊗ evalDist ob` witnesses the conjunction,
using `HasEvalPMF` to ensure neither side has failure mass. -/
theorem relTriple_prod
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {P : α → Prop} {Q : β → Prop}
    (hP : ∀ a ∈ support oa, P a)
    (hQ : ∀ b ∈ support ob, Q b) :
    RelTriple oa ob (fun a b => P a ∧ Q b) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost]
  have hp : (evalDist oa).toPMF none = 0 := by
    change Pr[⊥ | oa] = 0; exact probFailure_eq_zero (mx := oa)
  have hq : (evalDist ob).toPMF none = 0 := by
    change Pr[⊥ | ob] = 0; exact probFailure_eq_zero (mx := ob)
  refine ⟨_root_.SPMF.Coupling.prod hp hq, ?_⟩
  intro z hz
  rcases (mem_support_bind_iff (evalDist oa)
    (fun a => evalDist ob >>= fun b => (pure (a, b) : SPMF (α × β))) z).1 hz with
    ⟨a, ha, hz'⟩
  have ha_supp : a ∈ support oa :=
    (mem_support_iff (mx := oa) (x := a)).2
      (by simpa [probOutput_def] using (mem_support_iff (mx := evalDist oa) (x := a)).1 ha)
  rcases (mem_support_bind_iff (evalDist ob)
    (fun b => (pure (a, b) : SPMF (α × β))) z).1 hz' with ⟨b, hb, hz''⟩
  have hb_supp : b ∈ support ob :=
    (mem_support_iff (mx := ob) (x := b)).2
      (by simpa [probOutput_def] using (mem_support_iff (mx := evalDist ob) (x := b)).1 hb)
  have : z = (a, b) := by
    simpa [support_pure, Set.mem_singleton_iff] using hz''
  subst this
  exact ⟨hP a ha_supp, hQ b hb_supp⟩

/-- `wpProp`-phrased version of the product lift. -/
theorem relTriple_prod_of_wpProp
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {P : α → Prop} {Q : β → Prop}
    (hP : OracleComp.ProgramLogic.StdDo.wpProp (spec := spec₁) oa P)
    (hQ : OracleComp.ProgramLogic.StdDo.wpProp (spec := spec₂) ob Q) :
    RelTriple oa ob (fun a b => P a ∧ Q b) :=
  relTriple_prod
    ((OracleComp.ProgramLogic.StdDo.wpProp_iff_forall_support
      (spec := spec₁) oa P).1 hP)
    ((OracleComp.ProgramLogic.StdDo.wpProp_iff_forall_support
      (spec := spec₂) ob Q).1 hQ)

/-- `Std.Do.Triple`-phrased version of the product lift. Two independent `Std.Do`
triples with pure precondition `True` combine into a `RelTriple` over the product
postcondition. -/
theorem relTriple_prod_of_triple
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {P : α → Prop} {Q : β → Prop}
    (hP : Std.Do.Triple (m := OracleComp spec₁) (ps := .pure) oa
      (⌜True⌝) (⇓a => ⌜P a⌝))
    (hQ : Std.Do.Triple (m := OracleComp spec₂) (ps := .pure) ob
      (⌜True⌝) (⇓b => ⌜Q b⌝)) :
    RelTriple oa ob (fun a b => P a ∧ Q b) := by
  have hP' : OracleComp.ProgramLogic.StdDo.wpProp (spec := spec₁) oa P := by
    have := hP trivial
    simpa [Std.Do.WP.wp, PredTrans.apply,
      OracleComp.ProgramLogic.StdDo.instWPOracleComp] using this
  have hQ' : OracleComp.ProgramLogic.StdDo.wpProp (spec := spec₂) ob Q := by
    have := hQ trivial
    simpa [Std.Do.WP.wp, PredTrans.apply,
      OracleComp.ProgramLogic.StdDo.instWPOracleComp] using this
  exact relTriple_prod_of_wpProp hP' hQ'

/-- Relational triples are monotone in the postcondition, so a product coupling can be
weakened to any relation implied by the conjunction of independent postconditions. -/
theorem relTriple_of_triple_of_imp
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {P : α → Prop} {Q : β → Prop} {R : RelPost α β}
    (hP : Std.Do.Triple (m := OracleComp spec₁) (ps := .pure) oa
      (⌜True⌝) (⇓a => ⌜P a⌝))
    (hQ : Std.Do.Triple (m := OracleComp spec₂) (ps := .pure) ob
      (⌜True⌝) (⇓b => ⌜Q b⌝))
    (hImp : ∀ a b, P a → Q b → R a b) :
    RelTriple oa ob R :=
  relTriple_post_mono
    (relTriple_prod_of_triple hP hQ)
    (fun _ _ ⟨hp, hq⟩ => hImp _ _ hp hq)

/-! ## Smoke tests -/

/-- Smoke test: two independent pure computations compose into a product relational
triple, without touching any coupling machinery by hand. -/
private example (x : α) (y : β) :
    RelTriple
      (pure x : OracleComp spec₁ α)
      (pure y : OracleComp spec₂ β)
      (fun a b => a = x ∧ b = y) :=
  relTriple_prod_of_wpProp
    (P := fun a => a = x)
    (Q := fun b => b = y)
    ((OracleComp.ProgramLogic.StdDo.wpProp_pure (spec := spec₁) x _).2 rfl)
    ((OracleComp.ProgramLogic.StdDo.wpProp_pure (spec := spec₂) y _).2 rfl)

/-- Smoke test: using `relTriple_of_triple_of_imp` to project a product coupling onto
any logically weaker relation. -/
private example (x : α) :
    RelTriple
      (pure x : OracleComp spec₁ α)
      (pure x : OracleComp spec₁ α)
      (EqRel α) :=
  relTriple_of_triple_of_imp (P := fun a => a = x) (Q := fun a => a = x)
    (by
      unfold Std.Do.Triple
      intro _
      exact (OracleComp.ProgramLogic.StdDo.wpProp_pure (spec := spec₁) x _).2 rfl)
    (by
      unfold Std.Do.Triple
      intro _
      exact (OracleComp.ProgramLogic.StdDo.wpProp_pure (spec := spec₁) x _).2 rfl)
    (fun _ _ hP hQ => by dsimp [EqRel]; rw [hP, hQ])

end OracleComp.ProgramLogic.Relational
