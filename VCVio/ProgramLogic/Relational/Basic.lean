/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.RelationalAlgebra
import ToMathlib.ProbabilityTheory.Coupling
import VCVio.EvalDist.Defs.Instances
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.Monad.Map
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

/-- Pure values on both sides: `R a b` implies the coupling. -/
lemma relTriple_pure_pure {a : α} {b : β} {R : RelPost α β} (h : R a b) :
    RelTriple (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) R := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost]
  refine ⟨⟨pure (a, b), ?_⟩, fun z hz => ?_⟩
  · simpa [evalDist_pure] using _root_.SubPMF.IsCoupling.pure_iff.mpr rfl
  · have : z = (a, b) := by simpa [support_pure] using hz
    subst this; exact h

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

/-- Equality of programs gives an equality-relation relational triple. -/
lemma relTriple_eqRel_of_eq {oa ob : OracleComp spec₁ α}
    (h : oa = ob) : RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa ob (EqRel α) := by
  subst h
  exact relTriple_refl (spec₁ := spec₁) (oa := oa)

/-- Equality of evaluation distributions gives an equality-relation relational triple. -/
lemma relTriple_eqRel_of_evalDist_eq {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : evalDist oa = evalDist ob) :
    RelTriple oa ob (EqRel α) := by
  apply (relTriple_iff_relWP (oa := oa) (ob := ob) (R := EqRel α)).2
  let cdiag := _root_.SPMF.Coupling.refl (evalDist oa)
  refine ⟨⟨cdiag.1, ?_⟩, ?_⟩
  · constructor
    · exact cdiag.2.map_fst
    · simpa [h] using cdiag.2.map_snd
  · intro z hz
    rcases (mem_support_bind_iff
      (evalDist oa) (fun a => (pure (a, a) : SPMF (α × α))) z).1 hz with ⟨a, _, hz'⟩
    have hzEq : z = (a, a) := by
      simpa [support_pure, Set.mem_singleton_iff] using hz'
    simp [EqRel, hzEq]

/-- If two computations have equal output distributions, any reflexive postcondition holds. -/
lemma relTriple_of_evalDist_eq
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    {R : RelPost α α}
    (h : evalDist oa = evalDist ob)
    (hR : ∀ x, R x x) :
    RelTriple oa ob R := by
  refine relTriple_post_mono
    (h := relTriple_eqRel_of_evalDist_eq (oa := oa) (ob := ob) h) ?_
  intro x y hxy
  dsimp [EqRel] at hxy
  cases hxy
  exact hR x

/-- Pointwise output-probability equality gives an equality-relation relational triple. -/
lemma relTriple_eqRel_of_probOutput_eq {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : ∀ x : α, Pr[= x | oa] = Pr[= x | ob]) :
    RelTriple oa ob (EqRel α) :=
  relTriple_eqRel_of_evalDist_eq (spec₁ := spec₁) (spec₂ := spec₂) (oa := oa) (ob := ob)
    (evalDist_ext h)

/-- Equality-relation relational triples imply equality of point output probabilities. -/
lemma probOutput_eq_of_relTriple_eqRel {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : RelTriple oa ob (EqRel α)) (x : α) :
    Pr[= x | oa] = Pr[= x | ob] := by
  rcases (relTriple_iff_relWP (oa := oa) (ob := ob) (R := EqRel α)).1 h with ⟨c, hc⟩
  have hfst :
      Pr[= x | Prod.fst <$> c.1] = Pr[= x | oa] := by
    simpa [probOutput_def] using congrArg (fun p : SPMF α => p x) c.2.map_fst
  have hsnd :
      Pr[= x | Prod.snd <$> c.1] = Pr[= x | ob] := by
    simpa [probOutput_def] using congrArg (fun p : SPMF α => p x) c.2.map_snd
  have hmap_fst :
      Pr[= x | Prod.fst <$> c.1] = Pr[(fun z : α × α => z.1 = x) | c.1] := by
    calc
      Pr[= x | Prod.fst <$> c.1]
          = Pr[(fun a : α => a = x) | Prod.fst <$> c.1] := by
              simp
      _ = Pr[(fun z : α × α => z.1 = x) | c.1] := by
            simpa [Function.comp] using
              (probEvent_map (mx := c.1) (f := Prod.fst) (q := fun a : α => a = x))
  have hmap_snd :
      Pr[(fun z : α × α => z.2 = x) | c.1] = Pr[= x | Prod.snd <$> c.1] := by
    calc
      Pr[(fun z : α × α => z.2 = x) | c.1]
          = Pr[(fun a : α => a = x) | Prod.snd <$> c.1] := by
              simpa [Function.comp] using
                (probEvent_map (mx := c.1) (f := Prod.snd) (q := fun a : α => a = x)).symm
      _ = Pr[= x | Prod.snd <$> c.1] := by
            simp
  have hevent :
      Pr[(fun z : α × α => z.1 = x) | c.1] = Pr[(fun z : α × α => z.2 = x) | c.1] := by
    refine probEvent_ext (mx := c.1) ?_
    intro z hz
    have hzEq : z.1 = z.2 := hc z hz
    constructor <;> intro hx <;> simpa [hzEq] using hx
  calc
    Pr[= x | oa] = Pr[= x | Prod.fst <$> c.1] := hfst.symm
    _ = Pr[(fun z : α × α => z.1 = x) | c.1] := hmap_fst
    _ = Pr[(fun z : α × α => z.2 = x) | c.1] := hevent
    _ = Pr[= x | Prod.snd <$> c.1] := hmap_snd
    _ = Pr[= x | ob] := hsnd

/-- Equality-relation relational triples imply equality of evaluation distributions. -/
lemma evalDist_eq_of_relTriple_eqRel {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : RelTriple oa ob (EqRel α)) :
    evalDist oa = evalDist ob :=
  evalDist_ext (fun x => probOutput_eq_of_relTriple_eqRel (spec₁ := spec₁) (spec₂ := spec₂) h x)

/-- Bool-specialized bridge from relational triples to game success equality. -/
lemma probOutput_true_eq_of_relTriple_eqRel
    {oa : OracleComp spec₁ Bool} {ob : OracleComp spec₂ Bool}
    (h : RelTriple oa ob (EqRel Bool)) :
    Pr[= true | oa] = Pr[= true | ob] :=
  probOutput_eq_of_relTriple_eqRel (spec₁ := spec₁) (spec₂ := spec₂) h true

/-! ## Oracle query coupling rules (pRHL level) -/

/-- Same-type identity coupling: querying the same oracle on both sides yields equal outputs. -/
lemma relTriple_query (t : spec₁.Domain) :
    RelTriple
      (spec₁ := spec₁) (spec₂ := spec₁)
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (EqRel (spec₁.Range t)) := by
  simpa using
    (relTriple_refl (spec₁ := spec₁)
      (oa := (liftM (query t) : OracleComp spec₁ (spec₁.Range t))))

/-- Bijection coupling (the "rnd" rule from EasyCrypt):
querying the same oracle on both sides, related by a bijection `f`. -/
lemma relTriple_query_bij (t : spec₁.Domain)
    {f : spec₁.Range t → spec₁.Range t}
    (hf : Function.Bijective f) :
    RelTriple
      (spec₁ := spec₁) (spec₂ := spec₁)
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (fun a b => f a = b) := by
  apply (relTriple_iff_relWP
    (oa := (liftM (query t) : OracleComp spec₁ (spec₁.Range t)))
    (ob := (liftM (query t) : OracleComp spec₁ (spec₁.Range t)))
    (R := fun a b => f a = b)).2
  refine ⟨⟨evalDist (liftM (query t) : OracleComp spec₁ (spec₁.Range t)) >>= fun a =>
      pure (a, f a), ?_⟩, ?_⟩
  · constructor
    · simp
    · simp only [map_bind, map_pure, evalDist_query]
      show f <$> (liftM (PMF.uniformOfFintype (spec₁.Range t)) : SPMF _) =
        (liftM (PMF.uniformOfFintype (spec₁.Range t)) : SPMF _)
      rw [show f <$> (liftM (PMF.uniformOfFintype (spec₁.Range t)) : SPMF _) =
        (liftM (f <$> PMF.uniformOfFintype (spec₁.Range t)) : SPMF _) from by simp]
      congr 1
      exact PMF.uniformOfFintype_map_of_bijective f hf
  · intro z hz
    rcases (mem_support_bind_iff
      (evalDist (liftM (query t) : OracleComp spec₁ (spec₁.Range t)))
      (fun a => (pure (a, f a) : SPMF ((spec₁.Range t) × (spec₁.Range t)))) z).1 hz with
      ⟨a, _, hz'⟩
    have hzEq : z = (a, f a) := by
      simpa [support_pure, Set.mem_singleton_iff] using hz'
    simp [hzEq]

lemma relTriple_map {R : RelPost γ δ}
    {f : α → γ} {g : β → δ}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (h : RelTriple oa ob (fun a b => R (f a) (g b))) :
    RelTriple (f <$> oa) (g <$> ob) R := by
  have h1 : RelWP oa ob (fun a b => R (f a) (g b)) ≤ RelWP oa (g <$> ob) (fun a d => R (f a) d) :=
    MAlgRelOrdered.relWP_map_right g oa ob _
  have h2 : RelWP oa (g <$> ob) (fun a d => R (f a) d) ≤ RelWP (f <$> oa) (g <$> ob) R :=
    MAlgRelOrdered.relWP_map_left f oa (g <$> ob) _
  exact le_trans h (le_trans h1 h2)

private lemma list_eq_of_forall₂_eqRel {xs ys : List α}
    (hxy : List.Forall₂ (EqRel α) xs ys) : xs = ys := by
  induction hxy with
  | nil =>
      rfl
  | @cons a b xs ys hab htl ih =>
      dsimp [EqRel] at hab ⊢
      cases hab
      simpa using congrArg (List.cons a) ih

/-- Lift a one-step coupling through bounded iteration. -/
lemma relTriple_replicate
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} (n : ℕ)
    (hstep : RelTriple oa ob R) :
    RelTriple (oa.replicate n) (ob.replicate n) (List.Forall₂ R) := by
  induction n with
  | zero =>
      rw [OracleComp.replicate_zero, OracleComp.replicate_zero]
      exact relTriple_pure_pure (R := List.Forall₂ R) (a := []) (b := []) List.Forall₂.nil
  | succ n ih =>
      rw [OracleComp.replicate_succ_bind, OracleComp.replicate_succ_bind]
      refine relTriple_bind hstep ?_
      intro a b hab
      refine relTriple_bind ih ?_
      intro xs ys hxy
      exact relTriple_pure_pure (List.Forall₂.cons hab hxy)

/-- Equality coupling version of `relTriple_replicate`. -/
lemma relTriple_replicate_eqRel
    {oa ob : OracleComp spec₁ α} (n : ℕ)
    (hstep : RelTriple oa ob (EqRel α)) :
    RelTriple (oa.replicate n) (ob.replicate n) (EqRel (List α)) := by
  refine relTriple_post_mono
    (h := relTriple_replicate (n := n) (R := EqRel α) hstep) ?_
  intro xs ys hxy
  exact list_eq_of_forall₂_eqRel hxy

/-- Lift pointwise relational reasoning through finite list traversals. -/
lemma relTriple_list_mapM
    {xs : List α} {ys : List β}
    {f : α → OracleComp spec₁ γ} {g : β → OracleComp spec₂ δ}
    {Rin : α → β → Prop} {Rout : γ → δ → Prop}
    (hxy : List.Forall₂ Rin xs ys)
    (hfg : ∀ a b, Rin a b → RelTriple (f a) (g b) Rout) :
    RelTriple (xs.mapM f) (ys.mapM g) (List.Forall₂ Rout) := by
  induction hxy with
  | nil =>
      rw [List.mapM_nil, List.mapM_nil]
      exact relTriple_pure_pure (R := List.Forall₂ Rout) (a := []) (b := []) List.Forall₂.nil
  | @cons a b xs ys hab htl ih =>
      rw [List.mapM_cons, List.mapM_cons]
      refine relTriple_bind (hfg a b hab) ?_
      intro x y hxy
      refine relTriple_bind ih ?_
      intro xs' ys' hxs
      exact relTriple_pure_pure (List.Forall₂.cons hxy hxs)

/-- Same-input equality-coupling specialization of `relTriple_list_mapM`. -/
lemma relTriple_list_mapM_eqRel
    {xs : List α}
    {f : α → OracleComp spec₁ β} {g : α → OracleComp spec₂ β}
    (hfg : ∀ a, RelTriple (f a) (g a) (EqRel β)) :
    RelTriple (xs.mapM f) (xs.mapM g) (EqRel (List β)) := by
  refine relTriple_post_mono
    (h := relTriple_list_mapM
      (Rin := EqRel α) (Rout := EqRel β)
      (hxy := by
        induction xs with
        | nil => exact List.Forall₂.nil
        | cons a xs ih => exact List.Forall₂.cons rfl ih)
      (hfg := by
        intro a b hab
        dsimp [EqRel] at hab
        cases hab
        simpa using hfg a)) ?_
  intro xs ys hxy
  exact list_eq_of_forall₂_eqRel hxy

/-- Loop-invariant rule for bounded left folds over related input lists. -/
lemma relTriple_list_foldlM
    {σ₁ σ₂ : Type}
    {xs : List α} {ys : List β}
    {f : σ₁ → α → OracleComp spec₁ σ₁}
    {g : σ₂ → β → OracleComp spec₂ σ₂}
    {Rin : α → β → Prop} {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hxy : List.Forall₂ Rin xs ys)
    (hfg : ∀ a b, Rin a b → ∀ t₁ t₂, S t₁ t₂ → RelTriple (f t₁ a) (g t₂ b) S) :
    RelTriple (xs.foldlM f s₁) (ys.foldlM g s₂) S := by
  induction hxy generalizing s₁ s₂ with
  | nil =>
      rw [List.foldlM_nil, List.foldlM_nil]
      exact relTriple_pure_pure (R := S) (a := s₁) (b := s₂) hs
  | @cons a b xs ys hab htl ih =>
      rw [List.foldlM_cons, List.foldlM_cons]
      refine relTriple_bind (hfg a b hab s₁ s₂ hs) ?_
      intro t₁ t₂ ht
      exact ih ht

/-- Same-input specialization of `relTriple_list_foldlM`. -/
lemma relTriple_list_foldlM_same
    {σ₁ σ₂ : Type}
    {xs : List α}
    {f : σ₁ → α → OracleComp spec₁ σ₁}
    {g : σ₂ → α → OracleComp spec₂ σ₂}
    {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hfg : ∀ a t₁ t₂, S t₁ t₂ → RelTriple (f t₁ a) (g t₂ a) S) :
    RelTriple (xs.foldlM f s₁) (xs.foldlM g s₂) S := by
  refine relTriple_list_foldlM
    (Rin := EqRel α) (hs := hs)
    (hxy := by simp [EqRel]) ?_
  intro a b hab t₁ t₂ ht
  dsimp [EqRel] at hab
  cases hab
  simpa using hfg a t₁ t₂ ht

/-! ## Synchronized branching rule -/

/-- Synchronized conditional: if both sides branch on the same condition, the
relational triple holds if it holds on both branches. -/
lemma relTriple_if {c : Prop} [Decidable c]
    {oa₁ oa₂ : OracleComp spec₁ α} {ob₁ ob₂ : OracleComp spec₂ β}
    {R : RelPost α β}
    (htrue : c → RelTriple oa₁ ob₁ R)
    (hfalse : ¬c → RelTriple oa₂ ob₂ R) :
    RelTriple (if c then oa₁ else oa₂) (if c then ob₁ else ob₂) R := by
  split_ifs with h
  · exact htrue h
  · exact hfalse h

/-- Pure-left rule: the left side is a pure value, applied via bind decomposition. -/
lemma relTriple_pure_left {a : α} {ob : OracleComp spec₂ β}
    {R : RelPost α β}
    (h : RelTriple (pure a : OracleComp spec₁ α) ob
      (fun x y => x = a ∧ R x y))  :
    RelTriple (pure a : OracleComp spec₁ α) ob R :=
  relTriple_post_mono h (fun _ _ ⟨_, hr⟩ => hr)

/-- Pure-right rule: the right side is a pure value, applied via bind decomposition. -/
lemma relTriple_pure_right {oa : OracleComp spec₁ α} {b : β}
    {R : RelPost α β}
    (h : RelTriple oa (pure b : OracleComp spec₂ β)
      (fun x y => y = b ∧ R x y)) :
    RelTriple oa (pure b : OracleComp spec₂ β) R :=
  relTriple_post_mono h (fun _ _ ⟨_, hr⟩ => hr)

section Sampling

variable [SampleableType α]

/-- Relational coupling for uniform sampling via bijection.
Given a bijection `f : α → α` such that `R x (f x)` for all `x`,
the two uniform samples are related by `R`. -/
lemma relTriple_uniformSample_bij
    {f : α → α} (hf : Function.Bijective f) (R : RelPost α α)
    (hR : ∀ x, R x (f x)) :
    RelTriple ($ᵗ α) ($ᵗ α) R := by
  apply (relTriple_iff_relWP
    (oa := ($ᵗ α : ProbComp α))
    (ob := ($ᵗ α : ProbComp α))
    (R := R)).2
  refine ⟨⟨evalDist ($ᵗ α : ProbComp α) >>= fun a =>
      pure (a, f a), ?_⟩, ?_⟩
  · constructor
    · simp
    · simp only [map_bind, map_pure]
      calc
        (do
            let a ← evalDist ($ᵗ α : ProbComp α)
            pure (f a)) = f <$> evalDist ($ᵗ α : ProbComp α) := by
              rfl
        _ = evalDist (f <$> ($ᵗ α : ProbComp α)) := by
          exact (evalDist_map ($ᵗ α : ProbComp α) f).symm
        _ = evalDist ($ᵗ α : ProbComp α) := by
          apply evalDist_ext
          intro x
          obtain ⟨x', rfl⟩ := hf.surjective x
          rw [probOutput_map_injective ($ᵗ α) hf.injective x']
          simpa [uniformSample] using
            SampleableType.probOutput_selectElem_eq (β := α) x' (f x')
  · intro z hz
    rcases (mem_support_bind_iff
      (evalDist ($ᵗ α : ProbComp α))
      (fun a => (pure (a, f a) : SPMF (α × α))) z).1 hz with
      ⟨a, _, hz'⟩
    have hzEq : z = (a, f a) := by
      simpa [support_pure, Set.mem_singleton_iff] using hz'
    simpa [hzEq] using hR a

/-- Identity coupling for uniform sampling. -/
lemma relTriple_uniformSample_refl :
    RelTriple ($ᵗ α) ($ᵗ α) (EqRel α) :=
  relTriple_uniformSample_bij Function.bijective_id (EqRel α) fun _ => rfl

end Sampling

end OracleComp.ProgramLogic.Relational
