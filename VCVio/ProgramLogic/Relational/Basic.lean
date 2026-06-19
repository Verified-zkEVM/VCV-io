/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.RelationalAlgebra
import ToMathlib.ProbabilityTheory.Coupling
import VCVio.EvalDist.Defs.Instances
import VCVio.EvalDist.Defs.NeverFails
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Monad.Map
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.EvalDist
import VCVio.ProgramLogic.Unary.HoarePropTriple

/-!
# Relational program-logic baseline

This file defines `RelTriple` via the generic two-monad algebra interface
`MAlgRelOrdered`, instantiated for `OracleComp` using coupling semantics.

`HasCoupling` and coupling lemmas remain as semantic bridge lemmas.
-/

universe u v w x

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type v}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [IsUniformSpec spec₁] [IsUniformSpec spec₂]
variable {α β γ δ : Type}

/-- Relational postconditions over two output spaces. -/
abbrev RelPost (α : Sort w) (β : Sort x) := α → β → Prop

/-- Equality relation helper for same-type outputs. -/
def EqRel (α : Sort w) : RelPost α α := Eq

/-- Coupling-based semantic relational WP for `OracleComp`. -/
def CouplingPost (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) : Prop :=
  ∃ c : _root_.SPMF.Coupling (𝒟[oa]) (𝒟[ob]),
    ∀ z ∈ support c.1, R z.1 z.2

/-- Relational algebra instance for `OracleComp`, based on coupling semantics. -/
noncomputable instance instMAlgRelOrdered :
    MAlgRelOrdered (OracleComp spec₁) (OracleComp spec₂) Prop where
  rwp := CouplingPost
  rwp_pure a b R := by
    apply propext
    constructor
    · rintro ⟨c, hc⟩
      have hcEq : c.1 = (pure (a, b) : SPMF (_ × _)) :=
        _root_.SPMF.IsCoupling.pure_iff.1 (by simpa [evalDist_pure] using c.2)
      exact hc (a, b) (by simp [hcEq, support_pure])
    · intro hR
      refine ⟨⟨(pure (a, b) : SPMF (_ × _)), ?_⟩, fun z hz => ?_⟩
      · simpa [evalDist_pure] using _root_.SPMF.IsCoupling.pure_iff.2 rfl
      · obtain rfl : z = (a, b) := by simpa [support_pure] using hz
        exact hR
  rwp_mono hpost := fun ⟨c, hc⟩ => ⟨c, fun z hz => hpost z.1 z.2 (hc z hz)⟩
  rwp_bind_le {α β γ δ} oa ob fa fb post := by
    rintro ⟨c, hcCut⟩
    classical
    let d : α → β → SPMF (γ × δ) := fun a b =>
      if hcut : CouplingPost (fa a) (fb b) post then (Classical.choose hcut).1 else failure
    have hd : ∀ a b, c.1.1 (some (a, b)) ≠ 0 →
        _root_.SPMF.IsCoupling (d a b) (𝒟[fa a]) (𝒟[fb b]) := fun a b hmass => by
      have hcut : CouplingPost (fa a) (fb b) post := hcCut (a, b)
        ((mem_support_iff c.1 (a, b)).2 (by simpa [SPMF.apply_eq_toPMF_some] using hmass))
      simpa [d, hcut] using (Classical.choose hcut).2
    refine ⟨⟨c.1 >>= fun p => d p.1 p.2, ?_⟩, fun z hz => ?_⟩
    · simpa [evalDist_bind] using _root_.SPMF.IsCoupling.bind c d hd
    · rcases (mem_support_bind_iff c.1 (fun p => d p.1 p.2) z).1 hz with ⟨ab, hab, hz'⟩
      have hcut : CouplingPost (fa ab.1) (fb ab.2) post := hcCut ab hab
      exact Classical.choose_spec hcut z (by simpa [d, hcut] using hz')

/-- Anchoring instance for the qualitative `Prop`-valued relational logic on `OracleComp`.

When one of the two computations is `pure`, the relational coupling logic collapses to the
unary support-based logic of the other side. This is the relational analogue of the
*Dirac coupling* identity `c (a, b) = (evalDist y) b` whenever `c` couples `pure a` with `y`.

Together with the unary `Prop` algebra in `VCVio/ProgramLogic/Unary/HoarePropTriple.lean`,
this lets `wpExc` / `rwpExc`-style honest exception combinators (in
`ToMathlib/Control/Monad/RelationalAlgebraAnchored.lean`) be derived uniformly. -/
instance instAnchored : MAlgRelOrdered.Anchored (OracleComp spec₁) (OracleComp spec₂) Prop where
  rwp_pure_left {α β} a y post := by
    refine propext ⟨fun ⟨c, hc⟩ => ?_, fun hwp => ?_⟩
    · rw [OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support]
      intro b hb
      have hcPure : _root_.SPMF.IsCoupling c.1 (pure a) (𝒟[y]) := by
        simpa [evalDist_pure] using c.2
      have hmass : c.1 (a, b) ≠ 0 := by
        rw [hcPure.apply_pure_left_eq b]
        exact (mem_support_iff_evalDist_apply_ne_zero y b).1 hb
      exact hc (a, b) ((mem_support_iff c.1 (a, b)).2 hmass)
    · rw [OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support] at hwp
      refine ⟨⟨((a, ·) : β → α × β) <$> 𝒟[y], ?_⟩, ?_⟩
      · simpa [evalDist_pure] using
          _root_.SPMF.IsCoupling.dirac_left a (probFailure_eq_zero (mx := y))
      · intro z hz
        rw [support_map] at hz
        obtain ⟨b, hb, rfl⟩ := hz
        exact hwp b ((mem_support_iff_evalDist_apply_ne_zero y b).2 hb)
  rwp_pure_right {α β} x b post := by
    refine propext ⟨fun ⟨c, hc⟩ => ?_, fun hwp => ?_⟩
    · rw [OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support]
      intro a ha
      have hcPure : _root_.SPMF.IsCoupling c.1 (𝒟[x]) (pure b) := by
        simpa [evalDist_pure] using c.2
      have hmass : c.1 (a, b) ≠ 0 := by
        rw [hcPure.apply_pure_right_eq a]
        exact (mem_support_iff_evalDist_apply_ne_zero x a).1 ha
      exact hc (a, b) ((mem_support_iff c.1 (a, b)).2 hmass)
    · rw [OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support] at hwp
      refine ⟨⟨((·, b) : α → α × β) <$> 𝒟[x], ?_⟩, ?_⟩
      · simpa [evalDist_pure] using
          _root_.SPMF.IsCoupling.dirac_right b (probFailure_eq_zero (mx := x))
      · intro z hz
        rw [support_map] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        exact hwp a ((mem_support_iff_evalDist_apply_ne_zero x a).2 ha)

/-- Relational weakest precondition induced by `MAlgRelOrdered` for `OracleComp`. -/
abbrev RelWP (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) : Prop :=
  MAlgRelOrdered.RelWP (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop) oa ob R

/-- Relational Hoare-style triple with implicit precondition `True`. -/
abbrev RelTriple (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) : Prop :=
  MAlgRelOrdered.Triple (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop) True oa ob R

@[simp] lemma relTriple_iff_relWP {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} :
    RelTriple oa ob R ↔ RelWP oa ob R :=
  ⟨fun h => h trivial, fun h _ => h⟩

@[simp] lemma relWP_iff_couplingPost {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} :
    RelWP oa ob R ↔ CouplingPost oa ob R := Iff.rfl

/-- Existence of an `SPMF` coupling witness between two computations. -/
def HasCoupling (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) : Prop :=
  Nonempty (_root_.SPMF.Coupling (𝒟[oa]) (𝒟[ob]))

/-- Any relational triple yields a coupling witness. -/
lemma hasCoupling_of_relTriple {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} (h : RelTriple oa ob R) : HasCoupling oa ob :=
  ⟨(relTriple_iff_relWP.1 h).choose⟩

/-- Pure values on both sides: `R a b` implies the coupling. -/
lemma relTriple_pure_pure {a : α} {b : β} {R : RelPost α β} (h : R a b) :
    RelTriple (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) R := by
  refine relTriple_iff_relWP.2 ⟨⟨pure (a, b), ?_⟩, fun z hz => ?_⟩
  · simpa [evalDist_pure] using _root_.SPMF.IsCoupling.pure_iff.mpr rfl
  · obtain rfl : z = (a, b) := by simpa [support_pure] using hz
    exact h

/-- Reflexivity rule for relational triples on equality. -/
lemma relTriple_refl (oa : OracleComp spec₁ α) :
    RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa oa (EqRel α) := by
  refine relTriple_iff_relWP.2 ⟨_root_.SPMF.Coupling.refl (𝒟[oa]), fun z hz => ?_⟩
  obtain ⟨a, -, rfl⟩ : ∃ a ∈ support (𝒟[oa]), (a, a) = z := by
    simpa [_root_.SPMF.Coupling.refl, support_pure] using hz
  rfl

/-- Postcondition monotonicity for relational triples. -/
lemma relTriple_post_mono {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R R' : RelPost α β}
    (h : RelTriple oa ob R) (hpost : ∀ ⦃x y⦄, R x y → R' x y) :
    RelTriple oa ob R' :=
  relTriple_iff_relWP.2 ((relTriple_iff_relWP.1 h).imp fun _ hc z hz => hpost (hc z hz))

/-- The trivial product coupling always exists for `OracleComp`, so any pair of computations
satisfies the constantly-true postcondition.

The witness is the product coupling `evalDist oa ⊗ evalDist ob`, which is well-defined because
`OracleComp` computations have no failure mass. This discharges any `RelTriple` goal whose
postcondition is structurally `fun _ _ => True` and is the foundation of the trivial-leaf
closer in `tryCloseRelGoalImmediate`. -/
lemma relTriple_true (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) :
    RelTriple oa ob (fun _ _ => True) :=
  relTriple_iff_relWP.2
    ⟨_root_.SPMF.Coupling.prod (probFailure_eq_zero (mx := oa)) (probFailure_eq_zero (mx := ob)),
      fun _ _ => trivial⟩

/-- Any postcondition that is unconditionally true gives a valid relational triple,
via the product coupling. Useful as a closing rule for vacuous postconditions. -/
lemma relTriple_post_const {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β}
    (h : ∀ a b, R a b) :
    RelTriple oa ob R :=
  relTriple_post_mono (relTriple_true oa ob) (fun _ _ _ => h _ _)

/-- Symmetry for relational triples, swapping the two computations and the postcondition. -/
lemma relTriple_symm {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β}
    (h : RelTriple oa ob R) :
    RelTriple ob oa (fun b a => R a b) := by
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨⟨Prod.swap <$> c.1, ?_, ?_⟩, fun z hz => ?_⟩
  · simpa [Functor.map_map] using c.2.map_snd
  · simpa [Functor.map_map] using c.2.map_fst
  · obtain ⟨z', hz', rfl⟩ := support_map _ c.1 ▸ hz
    exact hc z' hz'

/-- Transport a relational triple across equality of the left output distribution. -/
lemma relTriple_of_evalDist_eq_left
    {ι₃ : Type w} {spec₃ : OracleSpec ι₃} [IsUniformSpec spec₃]
    {oa : OracleComp spec₁ α} {oa' : OracleComp spec₂ α}
    {ob : OracleComp spec₃ β} {R : RelPost α β}
    (heq : 𝒟[oa] = 𝒟[oa']) (h : RelTriple oa' ob R) :
    RelTriple oa ob R := by
  rcases relTriple_iff_relWP.1 h with ⟨c, hc⟩
  exact relTriple_iff_relWP.2 ⟨⟨c.1, by simpa [heq] using c.2.map_fst, c.2.map_snd⟩, hc⟩

/-- Transport a relational triple across equality of the right output distribution. -/
lemma relTriple_of_evalDist_eq_right
    {ι₃ : Type w} {spec₃ : OracleSpec ι₃} [IsUniformSpec spec₃]
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {ob' : OracleComp spec₃ β} {R : RelPost α β}
    (heq : 𝒟[ob] = 𝒟[ob']) (h : RelTriple oa ob R) :
    RelTriple oa ob' R := by
  rcases relTriple_iff_relWP.1 h with ⟨c, hc⟩
  exact relTriple_iff_relWP.2 ⟨⟨c.1, c.2.map_fst, by simpa [heq] using c.2.map_snd⟩, hc⟩

/-- Bind composition rule for relational triples. -/
lemma relTriple_bind
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {fa : α → OracleComp spec₁ γ}
    {fb : β → OracleComp spec₂ δ} {R : RelPost α β} {S : RelPost γ δ}
    (hxy : RelTriple oa ob R) (hfg : ∀ a b, R a b → RelTriple (fa a) (fb b) S) :
    RelTriple (oa >>= fa) (ob >>= fb) S :=
  MAlgRelOrdered.triple_bind hxy fun a b hR => hfg a b hR trivial

/-- Equality of programs gives an equality-relation relational triple. -/
lemma relTriple_eqRel_of_eq {oa ob : OracleComp spec₁ α}
    (h : oa = ob) : RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa ob (EqRel α) :=
  h ▸ relTriple_refl oa

/-- Equality of evaluation distributions gives an equality-relation relational triple. -/
lemma relTriple_eqRel_of_evalDist_eq {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : 𝒟[oa] = 𝒟[ob]) :
    RelTriple oa ob (EqRel α) :=
  relTriple_of_evalDist_eq_right h (relTriple_refl oa)

/-- If two computations have equal output distributions, any reflexive postcondition holds. -/
lemma relTriple_of_evalDist_eq
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} {R : RelPost α α}
    (h : 𝒟[oa] = 𝒟[ob]) (hR : ∀ x, R x x) :
    RelTriple oa ob R :=
  relTriple_post_mono (relTriple_eqRel_of_evalDist_eq h) fun x _ hxy => hxy ▸ hR x

/-- Pointwise output-probability equality gives an equality-relation relational triple. -/
lemma relTriple_eqRel_of_probOutput_eq {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : ∀ x : α, Pr[= x | oa] = Pr[= x | ob]) :
    RelTriple oa ob (EqRel α) :=
  relTriple_eqRel_of_evalDist_eq (evalDist_ext h)

/-- Swapping two adjacent independent binds preserves the output distribution. -/
lemma relTriple_bind_bind_swap_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₁ β}
    {f : α → β → OracleComp spec₁ γ} :
    RelTriple
      (oa >>= fun a => ob >>= fun b => f a b)
      (ob >>= fun b => oa >>= fun a => f a b)
      (EqRel γ) :=
  relTriple_eqRel_of_probOutput_eq (probOutput_bind_bind_swap oa ob f)

/-- Equality-relation relational triples imply equality of point output probabilities. -/
lemma probOutput_eq_of_relTriple_eqRel {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : RelTriple oa ob (EqRel α)) (x : α) : Pr[= x | oa] = Pr[= x | ob] := by
  rcases (relTriple_iff_relWP (oa := oa) (ob := ob) (R := EqRel α)).1 h with ⟨c, hc⟩
  have hfst : Pr[= x | Prod.fst <$> c.1] = Pr[= x | oa] := by grind [c.2.map_fst]
  have hsnd : Pr[= x | Prod.snd <$> c.1] = Pr[= x | ob] := by grind [c.2.map_snd]
  have hevent : Pr[ (fun z : α × α => z.1 = x) | c.1] = Pr[ (fun z : α × α => z.2 = x) | c.1] :=
    probEvent_ext fun z hz => by rw [hc z hz]
  grind

/-- Equality-relation relational triples imply equality of evaluation distributions. -/
lemma evalDist_eq_of_relTriple_eqRel {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : RelTriple oa ob (EqRel α)) :
    𝒟[oa] = 𝒟[ob] :=
  evalDist_ext (probOutput_eq_of_relTriple_eqRel h)

/-- Transitivity through an intermediate computation related to the left side by `EqRel`. -/
lemma relTriple_trans_eqRel_left
    {ι₃ : Type w} {spec₃ : OracleSpec ι₃} [IsUniformSpec spec₃]
    {oa : OracleComp spec₁ α} {mid : OracleComp spec₂ α}
    {ob : OracleComp spec₃ β} {R : RelPost α β}
    (hleft : RelTriple oa mid (EqRel α)) (hright : RelTriple mid ob R) :
    RelTriple oa ob R :=
  relTriple_of_evalDist_eq_left (evalDist_eq_of_relTriple_eqRel hleft) hright

/-- Transitivity through an intermediate computation related to the right side by `EqRel`. -/
lemma relTriple_trans_eqRel_right
    {ι₃ : Type w} {spec₃ : OracleSpec ι₃} [IsUniformSpec spec₃]
    {oa : OracleComp spec₁ α} {mid : OracleComp spec₂ β}
    {ob : OracleComp spec₃ β} {R : RelPost α β}
    (hleft : RelTriple oa mid R) (hright : RelTriple mid ob (EqRel β)) :
    RelTriple oa ob R :=
  relTriple_of_evalDist_eq_right (evalDist_eq_of_relTriple_eqRel hright) hleft

/-- Transitivity of equality-relation relational triples through an intermediate computation. -/
lemma relTriple_trans_eqRel
    {ι₃ : Type w} {spec₃ : OracleSpec ι₃} [IsUniformSpec spec₃]
    {oa : OracleComp spec₁ α} {mid : OracleComp spec₂ α} {ob : OracleComp spec₃ α}
    (hleft : RelTriple oa mid (EqRel α)) (hright : RelTriple mid ob (EqRel α)) :
    RelTriple oa ob (EqRel α) :=
  relTriple_trans_eqRel_left hleft hright

/-- Bool-specialized bridge from relational triples to game success equality. -/
lemma probOutput_true_eq_of_relTriple_eqRel
    {oa : OracleComp spec₁ Bool} {ob : OracleComp spec₂ Bool} (h : RelTriple oa ob (EqRel Bool)) :
    Pr[= true | oa] = Pr[= true | ob] :=
  probOutput_eq_of_relTriple_eqRel h true

/-! ## Oracle query coupling rules (pRHL level) -/

/-- Same-type identity coupling: querying the same oracle on both sides yields equal outputs. -/
lemma relTriple_query (t : spec₁.Domain) :
    RelTriple
      (spec₁ := spec₁) (spec₂ := spec₁)
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (EqRel (spec₁.Range t)) :=
  relTriple_refl (liftM (query t) : OracleComp spec₁ (spec₁.Range t))

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
  refine relTriple_iff_relWP.2
    ⟨⟨𝒟[(liftM (query t) : OracleComp spec₁ (spec₁.Range t))] >>= fun a => pure (a, f a),
      by simp, ?_⟩, fun z hz => ?_⟩
  · simp only [map_bind, map_pure, evalDist_query]
    change f <$> (liftM (PMF.uniformOfFintype (spec₁.Range t)) : SPMF _) = _
    rw [← liftM_map]
    exact congrArg liftM (PMF.uniformOfFintype_map_of_bijective f hf)
  · obtain ⟨a, -, rfl⟩ := by simpa [support_pure] using hz
    rfl

/-- Bind rule specialized to two equal oracle queries coupled by a bijection.

The continuation is stated over the left sample only, with the right sample
already rewritten to `f a`. This is the stable continuation shape used by
the relational tactic for unary bijection hints. -/
lemma relTriple_bind_query_bij (t : spec₁.Domain)
    {f : spec₁.Range t → spec₁.Range t} {fa : spec₁.Range t → OracleComp spec₁ γ}
    {fb : spec₁.Range t → OracleComp spec₁ δ} {S : RelPost γ δ}
    (hfg : ∀ a, RelTriple (fa a) (fb (f a)) S)
    (hf : Function.Bijective f) :
    RelTriple
      ((liftM (query t) : OracleComp spec₁ (spec₁.Range t)) >>= fa)
      ((liftM (query t) : OracleComp spec₁ (spec₁.Range t)) >>= fb)
      S :=
  relTriple_bind (R := fun a b => b = f a)
    (relTriple_post_mono (relTriple_query_bij t hf) fun _ _ h => h.symm)
    fun a b hb => by simpa [hb] using hfg a

/-- Mapping both sides of a relational triple by `f` and `g` transports the
postcondition along `f` and `g`. -/
lemma relTriple_map {R : RelPost γ δ} {f : α → γ} {g : β → δ}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (h : RelTriple oa ob (fun a b => R (f a) (g b))) :
    RelTriple (f <$> oa) (g <$> ob) R :=
  h.trans ((MAlgRelOrdered.relWP_map_right g oa ob _).trans
    (MAlgRelOrdered.relWP_map_left f oa (g <$> ob) _))

/-- If a relational triple holds for `fun a b => f a = g b`, then mapping by `f` and `g`
produces equal distributions. Generalizes `evalDist_eq_of_relTriple_eqRel`. -/
lemma evalDist_map_eq_of_relTriple {σ : Type} {f : α → σ} {g : β → σ} {oa : OracleComp spec₁ α}
    {ob : OracleComp spec₂ β} (h : RelTriple oa ob (fun a b => f a = g b)) :
    𝒟[f <$> oa] = 𝒟[g <$> ob] :=
  evalDist_eq_of_relTriple_eqRel (relTriple_map h)

private lemma list_eq_of_forall₂_eqRel {xs ys : List α}
    (hxy : List.Forall₂ (EqRel α) xs ys) : xs = ys := by
  rwa [EqRel, List.forall₂_eq_eq_eq] at hxy

/-- Lift a one-step coupling through bounded iteration. -/
lemma relTriple_replicate
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} (n : ℕ)
    (hstep : RelTriple oa ob R) :
    RelTriple (oa.replicate n) (ob.replicate n) (List.Forall₂ R) := by
  induction n with
  | zero =>
    simp only [OracleComp.replicate_zero]
    exact relTriple_pure_pure List.Forall₂.nil
  | succ n ih =>
    simp only [OracleComp.replicate_succ_bind]
    exact relTriple_bind hstep fun a b hab =>
      relTriple_bind ih fun xs ys hxy => relTriple_pure_pure (List.Forall₂.cons hab hxy)

/-- Equality coupling version of `relTriple_replicate`. -/
lemma relTriple_replicate_eqRel
    {oa ob : OracleComp spec₁ α} (n : ℕ)
    (hstep : RelTriple oa ob (EqRel α)) :
    RelTriple (oa.replicate n) (ob.replicate n) (EqRel (List α)) :=
  relTriple_post_mono
    (h := relTriple_replicate (n := n) (R := EqRel α) hstep)
    fun _ _ => list_eq_of_forall₂_eqRel

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
    simp only [List.mapM_nil]
    exact relTriple_pure_pure (R := List.Forall₂ Rout) (a := []) (b := []) List.Forall₂.nil
  | @cons a b xs ys hab htl ih =>
    simp only [List.mapM_cons]
    exact relTriple_bind (hfg a b hab) fun x y hxy =>
      relTriple_bind ih fun xs' ys' hxs => relTriple_pure_pure (List.Forall₂.cons hxy hxs)

/-- Same-input equality-coupling specialization of `relTriple_list_mapM`. -/
lemma relTriple_list_mapM_eqRel
    {xs : List α}
    {f : α → OracleComp spec₁ β} {g : α → OracleComp spec₂ β}
    (hfg : ∀ a, RelTriple (f a) (g a) (EqRel β)) :
    RelTriple (xs.mapM f) (xs.mapM g) (EqRel (List β)) :=
  relTriple_post_mono
    (h := relTriple_list_mapM (Rin := EqRel α) (Rout := EqRel β)
      (hxy := by rw [EqRel, List.forall₂_eq_eq_eq])
      (hfg := by rintro a _ rfl; simpa using hfg a))
    fun _ _ => list_eq_of_forall₂_eqRel

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
    exact relTriple_bind (hfg a b hab s₁ s₂ hs) fun t₁ t₂ ht => ih ht

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
      (fun x y => x = a ∧ R x y)) :
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
  refine relTriple_iff_relWP.2
    ⟨⟨𝒟[($ᵗ α : ProbComp α)] >>= fun a => pure (a, f a), by simp, ?_⟩, fun z hz => ?_⟩
  · simp only [map_bind, map_pure]
    change f <$> 𝒟[($ᵗ α : ProbComp α)] = _
    rw [← evalDist_map]
    refine evalDist_ext fun x => ?_
    obtain ⟨x', rfl⟩ := hf.surjective x
    rw [probOutput_map_injective ($ᵗ α) hf.injective x']
    simpa [uniformSample] using SampleableType.probOutput_selectElem_eq (β := α) x' (f x')
  · obtain ⟨a, -, rfl⟩ := by simpa [support_pure] using hz
    simpa using hR a

/-- Bind rule specialized to two uniform samples coupled by a bijection.

The continuation is stated over the left sample only, with the right sample
already rewritten to `f a`. This avoids exposing an auxiliary equality witness
to proof scripts after `rvcstep using f`. -/
lemma relTriple_bind_uniformSample_bij
    {f : α → α}
    {fa : α → ProbComp γ} {fb : α → ProbComp δ}
    {S : RelPost γ δ}
    (hfg : ∀ a, RelTriple (fa a) (fb (f a)) S)
    (hf : Function.Bijective f) :
    RelTriple (($ᵗ α : ProbComp α) >>= fa) (($ᵗ α : ProbComp α) >>= fb) S := by
  refine relTriple_bind (R := fun a b => b = f a) ?_ ?_
  · exact relTriple_uniformSample_bij hf _ (fun _ => rfl)
  · intro a b hb
    simpa [hb] using hfg a

/-- Identity coupling for uniform sampling. -/
lemma relTriple_uniformSample_refl :
    RelTriple ($ᵗ α) ($ᵗ α) (EqRel α) :=
  relTriple_uniformSample_bij Function.bijective_id (EqRel α) fun _ => rfl

end Sampling

end OracleComp.ProgramLogic.Relational
