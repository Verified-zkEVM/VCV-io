/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.RelationalAlgebra
import ToMathlib.ProbabilityTheory.Coupling
import VCVio.EvalDist.Defs.Instances
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist

/-!
# Relational program-logic baseline

This file defines `RelTriple` via the generic two-monad algebra interface
`MAlgRelOrdered`, instantiated for `OracleComp` using coupling semantics.

`HasCoupling` and coupling lemmas remain as semantic bridge lemmas.
-/

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
variable {α β γ δ : Type}

/-- Relational postconditions over two output spaces. -/
abbrev RelPost (α : Type) (β : Type) := α → β → Prop

/-- Equality relation helper for same-type outputs. -/
def EqRel (α : Type) : RelPost α α := fun x y => x = y

/-- Coupling-based semantic relational WP for `OracleComp`. -/
def CouplingPost (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  ∃ c : _root_.SPMF.Coupling (evalDist oa) (evalDist ob),
    ∀ z ∈ support c.1, R z.1 z.2

/-- Relational algebra instance for `OracleComp`, based on coupling semantics. -/
noncomputable instance instMAlgRelOrdered :
    MAlgRelOrdered (OracleComp spec₁) (OracleComp spec₂) Prop where
  rwp oa ob R := CouplingPost oa ob R
  rwp_pure a b R := by
    apply propext
    constructor
    · intro h
      rcases h with ⟨c, hc⟩
      have hcPure : _root_.SubPMF.IsCoupling c.1 (pure a) (pure b) := by
        simpa [evalDist_pure] using c.2
      have hcEq : c.1 = (pure (a, b) : SPMF (_ × _)) :=
        (_root_.SubPMF.IsCoupling.pure_iff).1 hcPure
      have hmem : (a, b) ∈ support c.1 := by
        simp [hcEq, support_pure]
      exact hc (a, b) hmem
    · intro hR
      refine ⟨⟨(pure (a, b) : SPMF (_ × _)), ?_⟩, ?_⟩
      · have hcPure : _root_.SubPMF.IsCoupling (pure (a, b) : SPMF (_ × _)) (pure a) (pure b) :=
          (_root_.SubPMF.IsCoupling.pure_iff).2 rfl
        simpa [evalDist_pure] using hcPure
      · intro z hz
        have hzEq : z = (a, b) := by
          simpa [support_pure, Set.mem_singleton_iff] using hz
        simpa [hzEq] using hR
  rwp_mono hpost := by
    intro h
    rcases h with ⟨c, hc⟩
    exact ⟨c, fun z hz => hpost z.1 z.2 (hc z hz)⟩
  rwp_bind_le {α β γ δ} oa ob fa fb post := by
    intro hxy
    rcases hxy with ⟨c, hcCut⟩
    classical
    let d : α → β → SPMF (γ × δ) := fun a b =>
      if hcut : CouplingPost (fa a) (fb b) post then (Classical.choose hcut).1 else failure
    have hd :
        ∀ a b, c.1.1 (some (a, b)) ≠ 0 →
          _root_.SPMF.IsCoupling (d a b) (evalDist (fa a)) (evalDist (fb b)) := by
      intro a b hmass
      have hsupp : (a, b) ∈ support c.1 :=
        (mem_support_iff c.1 (a, b)).2 (by
          simpa [SPMF.apply_eq_toPMF_some] using hmass)
      have hcut : CouplingPost (fa a) (fb b) post := hcCut (a, b) hsupp
      have hCouple : _root_.SPMF.IsCoupling (Classical.choose hcut).1 (evalDist (fa a))
          (evalDist (fb b)) := (Classical.choose hcut).2
      simpa [d, hcut] using hCouple
    have hbind :
        _root_.SPMF.IsCoupling
          (c.1 >>= fun p => d p.1 p.2)
          (evalDist oa >>= fun a => evalDist (fa a))
          (evalDist ob >>= fun b => evalDist (fb b)) :=
      _root_.SPMF.IsCoupling.bind c d hd
    refine ⟨⟨c.1 >>= fun p => d p.1 p.2, ?_⟩, ?_⟩
    · simpa [evalDist_bind] using hbind
    · intro z hz
      rcases (mem_support_bind_iff c.1 (fun p => d p.1 p.2) z).1 hz with
        ⟨ab, hab, hz'⟩
      have hcut : CouplingPost (fa ab.1) (fb ab.2) post := hcCut ab hab
      have hz'' : z ∈ support (Classical.choose hcut).1 := by
        simpa [d, hcut] using hz'
      exact (Classical.choose_spec hcut) z hz''

/-- Relational weakest precondition induced by `MAlgRelOrdered` for `OracleComp`. -/
abbrev RelWP (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  MAlgRelOrdered.RelWP (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop) oa ob R

/-- Relational Hoare-style triple with implicit precondition `True`. -/
abbrev RelTriple (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  MAlgRelOrdered.Triple
    (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop)
    True oa ob R

@[simp] lemma relTriple_iff_relWP {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} :
    RelTriple oa ob R ↔ RelWP oa ob R := by
  constructor
  · intro h
    exact h trivial
  · intro h _
    exact h

@[simp] lemma relWP_iff_couplingPost {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} :
    RelWP oa ob R ↔ CouplingPost oa ob R := Iff.rfl

/-- Existence of an `SPMF` coupling witness between two computations. -/
def HasCoupling (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) : Prop :=
  Nonempty (_root_.SPMF.Coupling (evalDist oa) (evalDist ob))

/-- Any relational triple yields a coupling witness. -/
lemma hasCoupling_of_relTriple {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} (h : RelTriple oa ob R) : HasCoupling oa ob := by
  rcases (relTriple_iff_relWP (oa := oa) (ob := ob) (R := R)).1 h with ⟨c, _⟩
  exact ⟨c⟩

/-- Reflexivity rule for relational triples on equality. -/
lemma relTriple_refl (oa : OracleComp spec₁ α) :
    RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa oa (EqRel α) := by
  apply (relTriple_iff_relWP (oa := oa) (ob := oa) (R := EqRel α)).2
  refine ⟨_root_.SPMF.Coupling.refl (evalDist oa), ?_⟩
  intro z hz
  rcases (mem_support_bind_iff
    (evalDist oa) (fun a => (pure (a, a) : SPMF (α × α))) z).1 hz with ⟨a, _, hz'⟩
  have hzEq : z = (a, a) := by
    simpa [support_pure, Set.mem_singleton_iff] using hz'
  simp [EqRel, hzEq]

/-- Postcondition monotonicity for relational triples. -/
lemma relTriple_post_mono {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R R' : RelPost α β}
    (h : RelTriple oa ob R)
    (hpost : ∀ ⦃x y⦄, R x y → R' x y) :
    RelTriple oa ob R' := by
  rcases (relTriple_iff_relWP (oa := oa) (ob := ob) (R := R)).1 h with ⟨c, hc⟩
  apply (relTriple_iff_relWP (oa := oa) (ob := ob) (R := R')).2
  exact ⟨c, fun z hz => hpost (hc z hz)⟩

/-- Bind composition rule for relational triples. -/
lemma relTriple_bind
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {R : RelPost α β} {S : RelPost γ δ}
    (hxy : RelTriple oa ob R)
    (hfg : ∀ a b, R a b → RelTriple (fa a) (fb b) S) :
    RelTriple (oa >>= fa) (ob >>= fb) S := by
  unfold RelTriple at hxy ⊢
  refine MAlgRelOrdered.triple_bind
    (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop)
    (x := oa) (y := ob) (f := fa) (g := fb) (cut := R) (post := S)
    hxy ?_
  intro a b hR
  exact (hfg a b hR) trivial

end OracleComp.ProgramLogic.Relational
