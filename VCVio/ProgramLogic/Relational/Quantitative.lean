/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Relational.QuantitativeDefs
import VCVio.EvalDist.TVDist
import VCVio.ProgramLogic.Unary.HoareTriple
import ToMathlib.ProbabilityTheory.OptimalCoupling

/-!
# Quantitative Relational Program Logic (eRHL)

This file develops the main theorem layer for the eRHL-style quantitative relational
logic for `OracleComp`, building on the core interfaces in
`VCVio.ProgramLogic.Relational.QuantitativeDefs`.

The core idea (from Avanzini-Barthe-Gregoire-Davoli, POPL 2025) is to make pre/postconditions
`ℝ≥0∞`-valued instead of `Prop`-valued. This subsumes both pRHL (exact coupling, via indicator
postconditions) and apRHL (ε-approximate coupling, via threshold preconditions).

## Main results in this file

- coupling-mass lemmas and support facts
- introduction, consequence, and bind rules for eRHL
- bridges to exact and approximate couplings
- total-variation characterizations via `EqRel`

## Design

```
                eRHL (ℝ≥0∞-valued pre/post)
               /          |           \
              /           |            \
pRHL (exact)    apRHL (ε-approx)   stat-distance
indicator R      1-ε, indicator R    1, indicator(=)
```
-/

open ENNReal OracleSpec OracleComp

universe u v

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic.Relational

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
variable [IsUniformSpec spec₁] [IsUniformSpec spec₂]
variable {α β γ δ : Type}

/-! ## Helpers for coupling mass -/

private lemma coupling_probFailure_eq_zero
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (c : SPMF.Coupling (𝒟[oa]) (𝒟[ob])) :
    Pr[⊥ | c.1] = 0 := by
  have h1 : Pr[⊥ | Prod.fst <$> c.1] = Pr[⊥ | c.1] :=
    probFailure_map (f := Prod.fst) (mx := c.1)
  rw [c.2.map_fst] at h1
  rw [← h1]
  exact probFailure_eq_zero (mx := oa)

private lemma coupling_tsum_probOutput_eq_one
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (c : SPMF.Coupling (𝒟[oa]) (𝒟[ob])) :
    ∑' z : α × β, Pr[= z | c.1] = 1 := by
  rw [tsum_probOutput_eq_sub, coupling_probFailure_eq_zero c, tsub_zero]

universe w in
lemma spmf_bind_const_of_no_failure {α' β' : Type w}
    {p : SPMF α'} (hp : Pr[⊥ | p] = 0) (q : SPMF β') :
    (p >>= fun _ => q) = q := by
  apply SPMF.ext; intro y
  change Pr[= y | p >>= fun _ => q] = Pr[= y | q]
  rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub, hp,
    tsub_zero, one_mul]

universe w in
lemma spmf_map_const_of_no_failure {α' β' : Type w}
    {p : SPMF α'} (hp : Pr[⊥ | p] = 0) (b : β') :
    ((fun _ : α' => b) <$> p) = (pure b : SPMF β') :=
  spmf_bind_const_of_no_failure hp (pure b : SPMF β')

universe w in
lemma spmf_bind_bind_const_of_no_failure {α' β' γ' : Type w}
    {p : SPMF α'} (hp : Pr[⊥ | p] = 0) (q : α' → SPMF β')
    (hq : ∀ a, Pr[⊥ | q a] = 0) (r : SPMF γ') :
    (p >>= fun a => q a >>= fun _ => r) = r := by
  calc
    (p >>= fun a => q a >>= fun _ => r)
        = p >>= fun _ => r := bind_congr fun a => spmf_bind_const_of_no_failure (hq a) r
    _ = r := spmf_bind_const_of_no_failure hp r

lemma probFailure_evalDist_eq_zero
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α : Type u} (mx : m α) :
    Pr[⊥ | 𝒟[mx]] = 0 :=
  probFailure_eq_zero (mx := mx)

private lemma nonempty_spmf_coupling
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} :
    Nonempty (SPMF.Coupling (𝒟[oa]) (𝒟[ob])) :=
  ⟨SPMF.Coupling.prod (probFailure_eq_zero (mx := oa)) (probFailure_eq_zero (mx := ob))⟩

namespace PMF

/-- Fiber of a deterministic observation map. -/
private def fiber {α β : Type*} (f : α → β) (b : β) : Set α := {a | f a = b}

/-- Conditional distribution of a PMF along a deterministic observation map.

For an observation value outside the support of `f <$> p`, the choice of
distribution is irrelevant; we use an arbitrary support point of `p`. -/
noncomputable def condOnMap {α β : Type*} (p : PMF α) (f : α → β) (b : β) : PMF α := by
    classical
    exact
      if h : ∃ a ∈ fiber f b, a ∈ p.support then
        p.filter (fiber f b) h
      else
        pure p.support_nonempty.some

lemma condOnMap_apply_of_not_mem_fiber {α β : Type*} (p : PMF α) (f : α → β)
    (b : β) {a : α} (ha : a ∉ fiber f b)
    (hb : ∃ a ∈ fiber f b, a ∈ p.support) :
    condOnMap p f b a = 0 := by
  rw [condOnMap, dif_pos hb]
  exact PMF.filter_apply_eq_zero_of_notMem (p := p) (s := fiber f b) (h := hb) ha

lemma condOnMap_apply_of_mem_support {α β : Type*} (p : PMF α) (f : α → β)
    {a : α} (ha : a ∈ p.support) :
    condOnMap p f (f a) a = p a * ((PMF.map f p) (f a))⁻¹ := by
  classical
  letI : DecidableEq β := Classical.decEq β
  have hb : ∃ x ∈ fiber f (f a), x ∈ p.support := ⟨a, rfl, ha⟩
  rw [condOnMap, dif_pos hb, PMF.filter_apply,
    Set.indicator_of_mem (show a ∈ fiber f (f a) from rfl)]
  simp only [PMF.map_apply, Set.indicator_apply, fiber, Set.mem_setOf_eq, eq_comm]

lemma map_bind_condOnMap {α β : Type*} (p : PMF α) (f : α → β) :
    (PMF.map f p).bind (condOnMap p f) = p := by
  classical
  ext a
  rw [PMF.bind_apply]
  by_cases ha : a ∈ p.support
  · have hsingle : ∀ b, b ≠ f a → (PMF.map f p) b * condOnMap p f b a = 0 := by
      intro b hb
      by_cases hbmem : ∃ x ∈ fiber f b, x ∈ p.support
      · rw [condOnMap_apply_of_not_mem_fiber p f b (fun h => hb h.symm) hbmem, mul_zero]
      · rw [show (PMF.map f p) b = 0 by
          rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
          exact fun ⟨x, hx, hfx⟩ => hbmem ⟨x, hfx, hx⟩, zero_mul]
    rw [tsum_eq_single (f a) hsingle, condOnMap_apply_of_mem_support p f ha, mul_comm, mul_assoc,
      ENNReal.inv_mul_cancel
        (by rw [← PMF.mem_support_iff, PMF.mem_support_map_iff]; exact ⟨a, ha, rfl⟩)
        (PMF.apply_ne_top _ _), mul_one]
  · rw [(PMF.apply_eq_zero_iff _ _).2 ha, ENNReal.tsum_eq_zero]
    intro b
    by_cases hbmem : ∃ x ∈ fiber f b, x ∈ p.support
    · rw [show condOnMap p f b a = 0 by
        rw [condOnMap, dif_pos hbmem, PMF.filter_apply_eq_zero_iff]; exact Or.inr ha, mul_zero]
    · rw [show (PMF.map f p) b = 0 by
        rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
        exact fun ⟨x, hx, hfx⟩ => hbmem ⟨x, hfx, hx⟩, zero_mul]

end PMF

namespace PMF

/-- Conditional output kernel induced by a deterministic observation map.

When the observation value is not in the support of `f <$> p`, the fallback
is used. Since the observation has zero mass there, this does not affect the
rebuilt distribution, but it makes pointwise continuation equalities easier
to state. -/
noncomputable def mapKernelWithFallback {α β γ : Type*}
    (p : PMF α) (f : α → β) (out : α → γ) (fallback : β → γ) (b : β) : PMF γ := by
    classical
    exact
      if h : ∃ a ∈ fiber f b, a ∈ p.support then
        PMF.map out (p.filter (fiber f b) h)
      else
        pure (fallback b)

lemma map_bind_mapKernelWithFallback {α β γ : Type*}
    (p : PMF α) (f : α → β) (out : α → γ) (fallback : β → γ) :
    (PMF.map f p).bind (mapKernelWithFallback p f out fallback) = PMF.map out p := by
  let K : β → PMF γ := fun b => PMF.map out (condOnMap p f b)
  have hbind :
      (PMF.map f p).bind (mapKernelWithFallback p f out fallback) =
        (PMF.map f p).bind K := by
    refine PMF.bind_congr (PMF.map f p) _ _ ?_
    intro b hb
    obtain ⟨a, ha, hfa⟩ := (PMF.mem_support_map_iff f p b).1 hb
    have hex : ∃ a ∈ fiber f b, a ∈ p.support := ⟨a, hfa, ha⟩
    simp only [K, mapKernelWithFallback, condOnMap, dif_pos hex]
  rw [hbind]
  simp only [K, ← PMF.map_bind, map_bind_condOnMap]

lemma mapKernelWithFallback_eq_pure_of {α β γ : Type*}
    (p : PMF α) (f : α → β) (out : α → γ) (fallback : β → γ)
    (bad : β → Prop)
    (h_eq : ∀ a b, f a = b → ¬ bad b → out a = fallback b)
    (b : β) (hb : ¬ bad b) :
    mapKernelWithFallback p f out fallback b = pure (fallback b) := by
  by_cases hex : ∃ a ∈ fiber f b, a ∈ p.support
  · rw [mapKernelWithFallback, dif_pos hex]
    refine PMF.eq_pure_of_forall_ne_eq_zero _ (fallback b) ?_
    intro y hy
    rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
    rintro ⟨a, ha, rfl⟩
    exact hy (h_eq a b ((PMF.mem_support_filter_iff hex).1 ha).1 hb)
  · rw [mapKernelWithFallback, dif_neg hex]

end PMF

theorem ofReal_tvDist_map_private_right_bad_le
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α β γ : Type u}
    (oa : m α) (ob : m β)
    (pub : α → β) (fa : α → γ) (fb : β → γ) (bad : β → Prop)
    (h_eq : ∀ a b, pub a = b → ¬ bad b → fa a = fb b) :
    ENNReal.ofReal (tvDist (fa <$> oa) (fb <$> ob))
      ≤ ENNReal.ofReal (tvDist (pub <$> oa) ob) + Pr[bad | ob] := by
  let p : PMF α := liftM oa
  let q : PMF β := liftM ob
  let K : β → PMF γ := PMF.mapKernelWithFallback p pub fa fb
  have hstep : ∀ b, ¬ bad b → 𝒟[K b] = 𝒟[(pure (fb b) : PMF γ)] := fun b hb =>
    congrArg evalDist (PMF.mapKernelWithFallback_eq_pure_of p pub fa fb bad h_eq b hb)
  have h :=
    ofReal_tvDist_bind_event_right_le
      (m := PMF) (mx := PMF.map pub p) (my := q)
      (f := K) (g := fun b => (pure (fb b) : PMF γ)) bad hstep
  have hK : (PMF.map pub p).bind K = PMF.map fa p :=
    PMF.map_bind_mapKernelWithFallback p pub fa fb
  have hq : q.bind (fun b => (pure (fb b) : PMF γ)) = PMF.map fb q := by
    simpa [Function.comp_def] using PMF.bind_pure_comp fb q
  have hp_pub : (liftM (pub <$> oa) : PMF β) = PMF.map pub p :=
    MonadHom.mmap_map (F := MonadHom.ofLift _ PMF) (x := oa) (g := pub)
  have hp_fa : (liftM (fa <$> oa) : PMF γ) = PMF.map fa p :=
    MonadHom.mmap_map (F := MonadHom.ofLift _ PMF) (x := oa) (g := fa)
  have hq_fb : (liftM (fb <$> ob) : PMF γ) = PMF.map fb q :=
    MonadHom.mmap_map (F := MonadHom.ofLift _ PMF) (x := ob) (g := fb)
  have hleft :
      tvDist (fa <$> oa) (fb <$> ob) =
        tvDist ((PMF.map pub p).bind K) (q.bind fun b => (pure (fb b) : PMF γ)) := by
    unfold tvDist
    rw [evalDist_def (fa <$> oa),
      evalDist_def (fb <$> ob),
      PMF.evalDist_eq ((PMF.map pub p).bind K),
      PMF.evalDist_eq (q.bind fun b => (pure (fb b) : PMF γ)),
      show (liftM (fa <$> oa) : SPMF γ) = liftM ((liftM (fa <$> oa) : PMF γ)) from rfl,
      show (liftM (fb <$> ob) : SPMF γ) = liftM ((liftM (fb <$> ob) : PMF γ)) from rfl,
      hp_fa, hq_fb, hK, hq]
  have hbase :
      tvDist (pub <$> oa) ob = tvDist (PMF.map pub p) q := by
    unfold tvDist
    rw [evalDist_def (pub <$> oa),
      evalDist_def ob,
      PMF.evalDist_eq (PMF.map pub p),
      PMF.evalDist_eq q,
      show (liftM (pub <$> oa) : SPMF β) = liftM ((liftM (pub <$> oa) : PMF β)) from rfl,
      show (liftM ob : SPMF β) = liftM ((liftM ob : PMF β)) from rfl,
      hp_pub]
  simpa [hleft, hbase] using h

theorem evalDist_bind_ignore
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α β γ : Type u}
    (mx : m α) (noise : α → m β) (f : α → γ) :
    𝒟[mx >>= fun a => noise a >>= fun _ => pure (f a)] =
      𝒟[f <$> mx] := by
  rw [evalDist_bind, evalDist_map]
  congr 1
  funext a
  rw [evalDist_bind, evalDist_pure]
  exact spmf_bind_const_of_no_failure
    (probFailure_of_liftM_PMF (noise a)) (pure (f a) : SPMF γ)

theorem evalDist_bind_const_of_no_failure
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    {α β : Type u}
    (mx : m α) (my : m β) :
    𝒟[mx >>= fun _ => my] = 𝒟[my] := by
  rw [evalDist_bind]
  exact spmf_bind_const_of_no_failure (probFailure_of_liftM_PMF mx) (𝒟[my])

namespace SPMF

lemma bind_liftM {α β : Type u} (p : PMF α) (f : α → PMF β) :
    ((liftM p : SPMF α) >>= fun a => (liftM (f a) : SPMF β)) =
      (liftM (p.bind f) : SPMF β) := by
  rw [← SPMF.toPMF_inj]
  simp [SPMF.toPMF_bind, SPMF.toPMF_liftM, Option.elimM, PMF.monad_bind_eq_bind]

lemma map_const_liftM {α β : Type u} (q : PMF α) (b : β) :
    ((fun _ : α => b) <$> (liftM q : SPMF α)) = (pure b : SPMF β) :=
  spmf_map_const_of_no_failure (probFailure_of_liftM_PMF q) b

end SPMF

/-- Lift a coupling of a deterministic observation of the left computation
into a coupling of the full left computation with the right one. -/
noncomputable def liftLeftMapCoupling
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (f : α → β)
    (c : SPMF.Coupling (𝒟[f <$> oa]) (𝒟[ob])) : SPMF (α × β) :=
  c.1 >>= fun z =>
    (fun a => (a, z.2)) <$>
      (liftM (PMF.condOnMap (MonadHom.ofLift _ PMF oa) f z.1) : SPMF α)

theorem liftLeftMapCoupling_isCoupling
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (f : α → β)
    (c : SPMF.Coupling (𝒟[f <$> oa]) (𝒟[ob])) :
    SPMF.IsCoupling (liftLeftMapCoupling f c) (𝒟[oa]) (𝒟[ob]) := by
  constructor
  · unfold liftLeftMapCoupling
    calc
      Prod.fst <$> (c.1 >>= fun z =>
          (fun a => (a, z.2)) <$>
            (liftM (PMF.condOnMap (MonadHom.ofLift _ PMF oa) f z.1) : SPMF α))
          = c.1 >>= fun z =>
              (liftM (PMF.condOnMap (MonadHom.ofLift _ PMF oa) f z.1) : SPMF α) := by
            simp [map_bind, Functor.map_map]
      _ = (Prod.fst <$> c.1) >>= fun b =>
            (liftM (PMF.condOnMap (MonadHom.ofLift _ PMF oa) f b) : SPMF α) := by
            rw [bind_map_left]
      _ = 𝒟[f <$> oa] >>= fun b =>
            (liftM (PMF.condOnMap (MonadHom.ofLift _ PMF oa) f b) : SPMF α) := by
            rw [c.2.map_fst]
      _ = 𝒟[oa] := by
            rw [evalDist_def (f <$> oa), evalDist_def oa,
              show (liftM (f <$> oa) : SPMF β) = liftM ((liftM (f <$> oa) : PMF β)) from rfl,
              show (liftM (f <$> oa) : PMF β) = f <$> (liftM oa : PMF α) from
                MonadHom.mmap_map (F := MonadHom.ofLift _ PMF) (x := oa) (g := f)]
            change ((liftM (PMF.map f (MonadHom.ofLift _ PMF oa)) : SPMF β) >>= fun b =>
                (liftM (PMF.condOnMap (MonadHom.ofLift _ PMF oa) f b) : SPMF α)) =
              liftM (MonadHom.ofLift _ PMF oa)
            rw [SPMF.bind_liftM, PMF.map_bind_condOnMap]
  · unfold liftLeftMapCoupling
    calc
      Prod.snd <$> (c.1 >>= fun z =>
          (fun a => (a, z.2)) <$>
            (liftM (PMF.condOnMap (MonadHom.ofLift _ PMF oa) f z.1) : SPMF α))
          = Prod.snd <$> c.1 := by
            simp [map_bind, Functor.map_map, SPMF.map_const_liftM]
      _ = 𝒟[ob] := c.2.map_snd

private lemma Finset_sum_iSup_le_iSup_sum {ι : Type*} {J : ι → Type*}
    [hne : ∀ i, Nonempty (J i)]
    (g : (i : ι) → J i → ℝ≥0∞) (s : Finset ι) :
    ∑ i ∈ s, ⨆ j, g i j ≤ ⨆ (f : ∀ i, J i), ∑ i ∈ s, g i (f i) := by
  letI : DecidableEq ι := Classical.decEq ι
  haveI : Nonempty (∀ i, J i) := ⟨fun i => (hne i).some⟩
  refine Finset.induction_on s (by simp) fun a s ha ih => ?_
  simp_rw [Finset.sum_insert ha]
  calc (⨆ j, g a j) + ∑ i ∈ s, ⨆ j, g i j
      ≤ (⨆ j, g a j) + ⨆ (f : ∀ i, J i), ∑ i ∈ s, g i (f i) :=
        add_le_add le_rfl ih
    _ = ⨆ j, ⨆ (f : ∀ i, J i), (g a j + ∑ i ∈ s, g i (f i)) := by
        rw [ENNReal.iSup_add]; congr 1; ext j; rw [ENNReal.add_iSup]
    _ ≤ ⨆ (f : ∀ i, J i), (g a (f a) + ∑ i ∈ s, g i (f i)) := by
        refine iSup_le fun j => iSup_le fun f => ?_
        refine le_iSup_of_le (Function.update f a j) (le_of_eq ?_)
        rw [Function.update_self]
        exact congrArg _ <| Finset.sum_congr rfl fun i hi => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]

private lemma ENNReal_tsum_iSup_le {ι : Type*} {J : ι → Type*}
    [∀ i, Nonempty (J i)] (g : (i : ι) → J i → ℝ≥0∞) :
    ∑' i, ⨆ j, g i j ≤ ⨆ (f : ∀ i, J i), ∑' i, g i (f i) := by
  letI : DecidableEq ι := Classical.decEq ι
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => le_trans (Finset_sum_iSup_le_iSup_sum g s) ?_
  exact iSup_mono fun f => ENNReal.sum_le_tsum _

/-- Pushing a distribution forward along a packing into its support subtype and then
projecting back to the value recovers the original distribution, provided the packing acts
as the identity on the support. Used to build a coupling on the finite support subtypes and
transport it back. -/
private lemma evalDist_map_val_pack_eq {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec]
    {α : Type} [DecidableEq α] {oa : OracleComp spec α} {S : Type} (val : S → α)
    (pack : α → S) (hpack : ∀ a ∈ finSupport oa, val (pack a) = a) :
    val <$> (pack <$> 𝒟[oa]) = 𝒟[oa] := by
  refine SPMF.ext fun x => ?_
  simp only [Functor.map_map]
  calc
    Pr[= x | (val ∘ pack) <$> 𝒟[oa]]
        = Pr[ fun y : α => val (pack y) = x | 𝒟[oa]] := by
          simpa using probEvent_map (mx := 𝒟[oa]) (f := val ∘ pack) (q := fun y : α => y = x)
    _ = Pr[ fun y : α => y = x | 𝒟[oa]] :=
          probEvent_ext fun y hy => by
            simp [hpack y (mem_finSupport_of_mem_support_evalDist (oa := oa) (x := y) hy)]
    _ = Pr[= x | 𝒟[oa]] := by simp

/-- Pushing a coupling `c` of `𝒟[oa]` and `𝒟[ob]` forward along a pair of maps `f`, `g`
(componentwise) yields a coupling of `f <$> 𝒟[oa]` and `g <$> 𝒟[ob]`. Used to transport a
coupling between the finite support subtypes and the original distributions. -/
private lemma isCoupling_map_pair {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {A B : Type} (f : α → A) (g : β → B) (c : SPMF.Coupling (𝒟[oa]) (𝒟[ob])) :
    SPMF.IsCoupling ((fun z => (f z.1, g z.2)) <$> c.1) (f <$> 𝒟[oa]) (g <$> 𝒟[ob]) := by
  refine ⟨?_, ?_⟩
  · rw [show (Prod.fst <$> ((fun z => (f z.1, g z.2)) <$> c.1) : SPMF A) = f <$> (Prod.fst <$> c.1)
      from by simp [Functor.map_map], c.2.map_fst]
  · rw [show (Prod.snd <$> ((fun z => (f z.1, g z.2)) <$> c.1) : SPMF B) = g <$> (Prod.snd <$> c.1)
      from by simp [Functor.map_map], c.2.map_snd]

/-- The eRHL-based relational triple `RelTriple'` agrees with the coupling-based `CouplingPost`:
for any post-relation `R`, there is a coupling of `𝒟[oa]` and `𝒟[ob]` supported on `R` exactly
when the eRHL judgement holds. -/
theorem relTriple'_iff_couplingPost
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} :
    RelTriple' oa ob R ↔ CouplingPost oa ob R := by
  constructor
  · intro h
    classical
    letI : DecidableEq α := Classical.decEq α
    letI : DecidableEq β := Classical.decEq β
    unfold RelTriple' at h
    by_cases hne : Nonempty (SPMF.Coupling (𝒟[oa]) (𝒟[ob]))
    · let A := {a // a ∈ finSupport oa}
      let B := {b // b ∈ finSupport ob}
      letI : DecidableEq A := Classical.decEq A
      letI : DecidableEq B := Classical.decEq B
      letI : Fintype A := inferInstance
      letI : Fintype B := inferInstance
      have hA_nonempty : (finSupport oa).Nonempty := finSupport_nonempty_of_liftM_PMF oa
      have hB_nonempty : (finSupport ob).Nonempty := finSupport_nonempty_of_liftM_PMF ob
      let a₀ : A := ⟨hA_nonempty.choose, hA_nonempty.choose_spec⟩
      let b₀ : B := ⟨hB_nonempty.choose, hB_nonempty.choose_spec⟩
      let packA : α → A := fun a => if ha : a ∈ finSupport oa then ⟨a, ha⟩ else a₀
      let packB : β → B := fun b => if hb : b ∈ finSupport ob then ⟨b, hb⟩ else b₀
      let packPair : α × β → A × B := fun z => (packA z.1, packB z.2)
      let valPair : A × B → α × β := fun z => (z.1.1, z.2.1)
      let pa : SPMF A := packA <$> 𝒟[oa]
      let pb : SPMF B := packB <$> 𝒟[ob]
      have hvalA : Subtype.val <$> pa = 𝒟[oa] :=
        evalDist_map_val_pack_eq Subtype.val packA fun a ha => by simp [packA, ha]
      have hvalB : Subtype.val <$> pb = 𝒟[ob] :=
        evalDist_map_val_pack_eq Subtype.val packB fun b hb => by simp [packB, hb]
      have hsub_nonempty : Nonempty (SPMF.Coupling pa pb) := by
        rcases hne with ⟨c₀⟩
        exact ⟨⟨packPair <$> c₀.1, isCoupling_map_pair packA packB c₀⟩⟩
      let fSub : Option (A × B) → ℝ≥0∞
        | none => 0
        | some z => RelPost.indicator R z.1.1 z.2.1
      have hfSub : ∀ z, fSub z ≠ ⊤ := by
        rintro (_ | z)
        · simp [fSub]
        · by_cases hR : R z.1.1 z.2.1 <;> simp [fSub, RelPost.indicator, hR]
      obtain ⟨cMaxSub, hMaxSub⟩ := SPMF.exists_max_coupling
        (p := pa) (q := pb) fSub hfSub hsub_nonempty (isCompact_couplings_set pa pb)
      have hsub_obj :
          ∀ c : SPMF.Coupling pa pb,
            (∑' z : Option (A × B), c.1.1 z * fSub z) =
              Pr[ fun z : A × B => R z.1.1 z.2.1 | (c.1 : SPMF (A × B))] := by
        intro c
        rw [probEvent_eq_tsum_ite, tsum_option _ ENNReal.summable]
        simp only [RelPost.indicator, mul_zero, mul_ite, mul_one, tsum_fintype, zero_add, fSub]
        rfl
      have hlift_obj :
          ∀ c : SPMF.Coupling (𝒟[oa]) (𝒟[ob]),
            Pr[ fun z : A × B => R z.1.1 z.2.1 | packPair <$> c.1] =
              Pr[ fun z : α × β => R z.1 z.2 | c.1] := by
        intro c
        rw [probEvent_map]
        refine probEvent_ext fun z hz => ?_
        have hzfst : z.1 ∈ support 𝒟[oa] := by rw [← c.2.map_fst, support_map]; exact ⟨z, hz, rfl⟩
        have hzsnd : z.2 ∈ support 𝒟[ob] := by rw [← c.2.map_snd, support_map]; exact ⟨z, hz, rfl⟩
        simp [packPair, packA, packB,
          mem_finSupport_of_mem_support_evalDist (oa := oa) (x := z.1) hzfst,
          mem_finSupport_of_mem_support_evalDist (oa := ob) (x := z.2) hzsnd]
      have hpush :
          SPMF.IsCoupling (valPair <$> cMaxSub.1) (𝒟[oa]) (𝒟[ob]) := by
        constructor
        · simpa [valPair] using
            (congrArg (fun p : SPMF A => Subtype.val <$> p) cMaxSub.2.map_fst).trans hvalA
        · simpa [valPair] using
            (congrArg (fun p : SPMF B => Subtype.val <$> p) cMaxSub.2.map_snd).trans hvalB
      let cMax : SPMF.Coupling (𝒟[oa]) (𝒟[ob]) := ⟨valPair <$> cMaxSub.1, hpush⟩
      have hpush_obj :
          Pr[ fun z : α × β => R z.1 z.2 | cMax.1] =
            Pr[ fun z : A × B => R z.1.1 z.2.1 | cMaxSub.1] :=
        probEvent_map (mx := cMaxSub.1) (f := valPair) (q := fun z : α × β => R z.1 z.2)
      have hsub_le_max :
          ∀ c : SPMF.Coupling pa pb,
            Pr[ fun z : A × B => R z.1.1 z.2.1 | (c.1 : SPMF (A × B))] ≤
              Pr[ fun z : A × B => R z.1.1 z.2.1 | (cMaxSub.1 : SPMF (A × B))] := by
        intro c
        rw [← hsub_obj c, ← hsub_obj cMaxSub]
        exact (le_iSup (f := fun c' : SPMF.Coupling pa pb =>
          ∑' z : Option (A × B), c'.1.1 z * fSub z) c).trans hMaxSub.le
      have hupper :
          eRelWP oa ob (RelPost.indicator R) ≤
            Pr[ fun z : α × β => R z.1 z.2 | cMax.1] := by
        unfold eRelWP
        refine iSup_le fun c => ?_
        let cLift : SPMF.Coupling pa pb := ⟨packPair <$> c.1, isCoupling_map_pair packA packB c⟩
        calc
          ∑' z, Pr[= z | c.1] * RelPost.indicator R z.1 z.2
              = Pr[ fun z : α × β => R z.1 z.2 | c.1] := by
                  simpa [RelPost.indicator] using
                    indicator_objective_eq_probEvent (mx := c.1) (R := R)
          _ = Pr[ fun z : A × B => R z.1.1 z.2.1 | packPair <$> c.1] :=
                (hlift_obj c).symm
          _ ≤ Pr[ fun z : α × β => R z.1 z.2 | cMax.1] := by
            rw [hpush_obj]; exact hsub_le_max cLift
      exact ⟨cMax, (probEvent_eq_one_iff (mx := cMax.1) (p := fun z : α × β => R z.1 z.2)).1
        (le_antisymm probEvent_le_one (le_trans h hupper)) |>.2⟩
    · haveI : IsEmpty (SPMF.Coupling (𝒟[oa]) (𝒟[ob])) := not_nonempty_iff.mp hne
      simp [eRelWP] at h
  · intro ⟨c, hc⟩
    unfold RelTriple' eRelWP
    refine le_iSup_of_le c <| le_of_eq ?_
    rw [← coupling_tsum_probOutput_eq_one c]
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support c.1
    · simp [RelPost.indicator, hc z hz]
    · simp [probOutput_eq_zero_of_not_mem_support hz]

/-- Bridge: `RelTriple'` agrees with the existing `RelTriple`. -/
theorem relTriple'_iff_relTriple
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} :
    RelTriple' oa ob R ↔ RelTriple oa ob R := by
  rw [relTriple'_iff_couplingPost, relTriple_iff_relWP, relWP_iff_couplingPost]

/-- If a `RelTriple'` holds for `fun a b => f a = g b`, then mapping by `f` and `g`
produces equal distributions. This is the eRHL-level version of
`evalDist_map_eq_of_relTriple`. -/
lemma evalDist_map_eq_of_relTriple' {σ : Type}
    {f : α → σ} {g : β → σ}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (h : RelTriple' oa ob (fun a b => f a = g b)) :
    𝒟[f <$> oa] = 𝒟[g <$> ob] :=
  evalDist_map_eq_of_relTriple (relTriple'_iff_relTriple.mp h)

/-! ## Quantitative relational WP rules -/

/-- Pure rule for quantitative relational WP. -/
theorem eRelWP_pure_le (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    post a b ≤ eRelWP (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) post := by
  unfold eRelWP
  have hc : SPMF.IsCoupling (pure (a, b) : SPMF (α × β))
      (𝒟[(pure a : OracleComp spec₁ α)]) (𝒟[(pure b : OracleComp spec₂ β)]) := by
    simpa only [evalDist_pure] using SPMF.IsCoupling.pure_iff.mpr rfl
  apply le_iSup_of_le ⟨pure (a, b), hc⟩
  have key : ∑' z, Pr[= z | (pure (a, b) : SPMF (α × β))] * post z.1 z.2 = post a b := by
    rw [tsum_eq_single (a, b)]
    · simp [SPMF.probOutput_eq_apply]
    · intro z hz
      have : Pr[= z | (pure (a, b) : SPMF (α × β))] = 0 := by
        rw [SPMF.probOutput_eq_apply]; simp [hz]
      simp [this]
  exact key ▸ le_refl _

/-- Monotonicity/consequence rule for quantitative relational WP. -/
theorem eRelWP_conseq {pre pre' : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {post post' : α → β → ℝ≥0∞}
    (hpre : pre' ≤ pre) (hpost : ∀ a b, post a b ≤ post' a b)
    (h : pre ≤ eRelWP oa ob post) :
    pre' ≤ eRelWP oa ob post' := by
  refine le_trans hpre (le_trans h ?_)
  unfold eRelWP
  refine iSup_le fun c => le_trans
    (ENNReal.tsum_le_tsum fun z : α × β => mul_le_mul' le_rfl (hpost z.1 z.2))
    (le_iSup (f := fun c' : SPMF.Coupling (𝒟[oa]) (𝒟[ob]) =>
      ∑' z : α × β, Pr[= z | c'.1] * post' z.1 z.2) c)

/-- Bind/sequential composition rule for quantitative relational WP. -/
theorem eRelWP_bind_rule
    {pre : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {cut : α → β → ℝ≥0∞} {post : γ → δ → ℝ≥0∞}
    (hxy : pre ≤ eRelWP oa ob cut)
    (hfg : ∀ a b, cut a b ≤ eRelWP (fa a) (fb b) post) :
    pre ≤ eRelWP (oa >>= fa) (ob >>= fb) post := by
  refine le_trans (eRelWP_conseq le_rfl hfg hxy) ?_
  unfold eRelWP
  refine iSup_le fun c => ?_
  have hne : ∀ a b, Nonempty (SPMF.Coupling (𝒟[fa a]) (𝒟[fb b])) :=
    fun a b => nonempty_spmf_coupling
  calc ∑' z, Pr[= z | c.1] *
        (⨆ d : SPMF.Coupling (𝒟[fa z.1]) (𝒟[fb z.2]),
          ∑' w, Pr[= w | d.1] * post w.1 w.2)
      = ∑' z, ⨆ d : SPMF.Coupling (𝒟[fa z.1]) (𝒟[fb z.2]),
          Pr[= z | c.1] * (∑' w, Pr[= w | d.1] * post w.1 w.2) := by
        congr 1; ext z; exact ENNReal.mul_iSup ..
    _ ≤ ⨆ (D : ∀ z : α × β,
            SPMF.Coupling (𝒟[fa z.1]) (𝒟[fb z.2])),
          ∑' z, Pr[= z | c.1] * (∑' w, Pr[= w | (D z).1] * post w.1 w.2) :=
        ENNReal_tsum_iSup_le _
    _ ≤ ⨆ c' : SPMF.Coupling (𝒟[oa >>= fa]) (𝒟[ob >>= fb]),
          ∑' w, Pr[= w | c'.1] * post w.1 w.2 := by
        refine iSup_le fun D => ?_
        let d : α → β → SPMF (γ × δ) := fun a b => (D (a, b)).1
        let c' : SPMF.Coupling (𝒟[oa >>= fa]) (𝒟[ob >>= fb]) :=
          ⟨c.1 >>= fun p => d p.1 p.2, by
            rw [evalDist_bind, evalDist_bind]
            exact SPMF.IsCoupling.bind c d fun a b _ => (D (a, b)).2⟩
        apply le_iSup_of_le c'
        suffices h : ∑' z, Pr[= z | c.1] * (∑' w, Pr[= w | d z.1 z.2] * post w.1 w.2) =
            ∑' w, Pr[= w | c'.1] * post w.1 w.2 from h.le
        have hbind : ∀ w : γ × δ,
            Pr[= w | c'.1] = ∑' z : α × β, Pr[= z | c.1] * Pr[= w | d z.1 z.2] :=
          probOutput_bind_eq_tsum c.1 fun p => d p.1 p.2
        simp_rw [hbind]
        calc ∑' z, Pr[= z | c.1] * (∑' w, Pr[= w | d z.1 z.2] * post w.1 w.2)
            = ∑' z, ∑' w, Pr[= z | c.1] * Pr[= w | d z.1 z.2] * post w.1 w.2 := by
              simp [ENNReal.tsum_mul_left, mul_assoc]
          _ = ∑' w, ∑' z, Pr[= z | c.1] * Pr[= w | d z.1 z.2] * post w.1 w.2 :=
              ENNReal.tsum_comm
          _ = ∑' w, (∑' z, Pr[= z | c.1] * Pr[= w | d z.1 z.2]) * post w.1 w.2 := by
              simp [ENNReal.tsum_mul_right]

/-! ## Indicator-postcondition rules (`RelTriple'`)

These are direct quantitative analogues of the pRHL effect-rule block in
`VCVio.ProgramLogic.Relational.Basic`, expressed as quantitative `eRelWP` lower bounds
via the `relTriple'_iff_relTriple` bridge. They give the eRHL-flavoured statement of
every coupling primitive `OracleComp` already exposes, so downstream proofs can mix exact
indicator rules with the genuinely quantitative bounds below without having to re-derive the
bridge each time.

Each rule is a one-line wrapper of its `RelTriple` cousin. The proofs that the underlying
couplings exist live in `Basic.lean`; this section only repackages them at the `RelTriple'`
level.
-/

/-- `RelTriple'` introduction from a pure-pure pair satisfying the post. -/
theorem relTriple'_pure_pure {a : α} {b : β} {R : RelPost α β} (h : R a b) :
    RelTriple' (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) R :=
  relTriple'_iff_relTriple.mpr (relTriple_pure_pure (spec₁ := spec₁) (spec₂ := spec₂) h)

/-- Reflexivity rule for `RelTriple'` on the diagonal equality relation. -/
theorem relTriple'_refl (oa : OracleComp spec₁ α) :
    RelTriple' (spec₁ := spec₁) (spec₂ := spec₁) oa oa (EqRel α) :=
  relTriple'_iff_relTriple.mpr (relTriple_refl (spec₁ := spec₁) oa)

/-- Postcondition monotonicity for `RelTriple'`. -/
theorem relTriple'_post_mono {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R R' : RelPost α β}
    (h : RelTriple' oa ob R)
    (hpost : ∀ ⦃x y⦄, R x y → R' x y) :
    RelTriple' oa ob R' :=
  relTriple'_iff_relTriple.mpr (relTriple_post_mono (relTriple'_iff_relTriple.mp h) hpost)

/-- Sequential composition rule for `RelTriple'`. -/
theorem relTriple'_bind
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {R : RelPost α β} {S : RelPost γ δ}
    (hxy : RelTriple' oa ob R)
    (hfg : ∀ a b, R a b → RelTriple' (fa a) (fb b) S) :
    RelTriple' (oa >>= fa) (ob >>= fb) S :=
  relTriple'_iff_relTriple.mpr <|
    relTriple_bind (relTriple'_iff_relTriple.mp hxy)
      (fun a b hR => relTriple'_iff_relTriple.mp (hfg a b hR))

/-- Equality of programs lifts to a `RelTriple'` on `EqRel`. -/
theorem relTriple'_eqRel_of_eq {oa ob : OracleComp spec₁ α}
    (h : oa = ob) :
    RelTriple' (spec₁ := spec₁) (spec₂ := spec₁) oa ob (EqRel α) :=
  relTriple'_iff_relTriple.mpr (relTriple_eqRel_of_eq h)

/-- Equality of evaluation distributions lifts to a `RelTriple'` on `EqRel`. -/
theorem relTriple'_eqRel_of_evalDist_eq {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : 𝒟[oa] = 𝒟[ob]) :
    RelTriple' oa ob (EqRel α) :=
  relTriple'_iff_relTriple.mpr (relTriple_eqRel_of_evalDist_eq h)

/-- Pointwise output-probability equality lifts to a `RelTriple'` on `EqRel`. -/
theorem relTriple'_eqRel_of_probOutput_eq {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : ∀ x : α, Pr[= x | oa] = Pr[= x | ob]) :
    RelTriple' oa ob (EqRel α) :=
  relTriple'_iff_relTriple.mpr (relTriple_eqRel_of_probOutput_eq h)

/-! ### Oracle-query coupling rules (eRHL level) -/

/-- Same-type identity coupling for queries: `RelTriple'` analogue of `relTriple_query`. -/
theorem relTriple'_query (t : spec₁.Domain) :
    RelTriple'
      (spec₁ := spec₁) (spec₂ := spec₁)
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (EqRel (spec₁.Range t)) :=
  relTriple'_iff_relTriple.mpr (relTriple_query (spec₁ := spec₁) t)

/-- Bijection coupling for queries (the eRHL "rnd" rule). -/
theorem relTriple'_query_bij (t : spec₁.Domain)
    {f : spec₁.Range t → spec₁.Range t}
    (hf : Function.Bijective f) :
    RelTriple'
      (spec₁ := spec₁) (spec₂ := spec₁)
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (fun a b => f a = b) :=
  relTriple'_iff_relTriple.mpr (relTriple_query_bij (spec₁ := spec₁) t hf)

/-! ### Functorial / structural rules -/

/-- `Functor.map` rule for `RelTriple'`. -/
theorem relTriple'_map {R : RelPost γ δ}
    {f : α → γ} {g : β → δ}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (h : RelTriple' oa ob (fun a b => R (f a) (g b))) :
    RelTriple' (f <$> oa) (g <$> ob) R :=
  relTriple'_iff_relTriple.mpr (relTriple_map (relTriple'_iff_relTriple.mp h))

/-- Synchronized conditional rule for `RelTriple'`. -/
theorem relTriple'_if {c : Prop} [Decidable c]
    {oa₁ oa₂ : OracleComp spec₁ α} {ob₁ ob₂ : OracleComp spec₂ β}
    {R : RelPost α β}
    (htrue : c → RelTriple' oa₁ ob₁ R)
    (hfalse : ¬c → RelTriple' oa₂ ob₂ R) :
    RelTriple' (if c then oa₁ else oa₂) (if c then ob₁ else ob₂) R :=
  relTriple'_iff_relTriple.mpr <|
    relTriple_if
      (fun hc => relTriple'_iff_relTriple.mp (htrue hc))
      (fun hc => relTriple'_iff_relTriple.mp (hfalse hc))

/-- Pure-left rule: lift the strengthened post `(· = a) ∧ R` back to `R`. -/
theorem relTriple'_pure_left {a : α} {ob : OracleComp spec₂ β}
    {R : RelPost α β}
    (h : RelTriple' (pure a : OracleComp spec₁ α) ob (fun x y => x = a ∧ R x y)) :
    RelTriple' (pure a : OracleComp spec₁ α) ob R :=
  relTriple'_iff_relTriple.mpr (relTriple_pure_left (relTriple'_iff_relTriple.mp h))

/-- Pure-right rule: lift the strengthened post `(· = b) ∧ R` back to `R`. -/
theorem relTriple'_pure_right {oa : OracleComp spec₁ α} {b : β}
    {R : RelPost α β}
    (h : RelTriple' oa (pure b : OracleComp spec₂ β) (fun x y => y = b ∧ R x y)) :
    RelTriple' oa (pure b : OracleComp spec₂ β) R :=
  relTriple'_iff_relTriple.mpr (relTriple_pure_right (relTriple'_iff_relTriple.mp h))

/-! ### Iteration / list-traversal rules -/

/-- `RelTriple'` for `OracleComp.replicate`. -/
theorem relTriple'_replicate
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} (n : ℕ)
    (hstep : RelTriple' oa ob R) :
    RelTriple' (oa.replicate n) (ob.replicate n) (List.Forall₂ R) :=
  relTriple'_iff_relTriple.mpr (relTriple_replicate n (relTriple'_iff_relTriple.mp hstep))

/-- Equality-relation specialization of `relTriple'_replicate`. -/
theorem relTriple'_replicate_eqRel
    {oa ob : OracleComp spec₁ α} (n : ℕ)
    (hstep : RelTriple' oa ob (EqRel α)) :
    RelTriple' (oa.replicate n) (ob.replicate n) (EqRel (List α)) :=
  relTriple'_iff_relTriple.mpr (relTriple_replicate_eqRel n (relTriple'_iff_relTriple.mp hstep))

/-- `RelTriple'` for `List.mapM`. -/
theorem relTriple'_list_mapM
    {xs : List α} {ys : List β}
    {f : α → OracleComp spec₁ γ} {g : β → OracleComp spec₂ δ}
    {Rin : α → β → Prop} {Rout : γ → δ → Prop}
    (hxy : List.Forall₂ Rin xs ys)
    (hfg : ∀ a b, Rin a b → RelTriple' (f a) (g b) Rout) :
    RelTriple' (xs.mapM f) (ys.mapM g) (List.Forall₂ Rout) :=
  relTriple'_iff_relTriple.mpr <|
    relTriple_list_mapM hxy
      (fun a b hab => relTriple'_iff_relTriple.mp (hfg a b hab))

/-- Same-input specialization of `relTriple'_list_mapM`. -/
theorem relTriple'_list_mapM_eqRel
    {xs : List α}
    {f : α → OracleComp spec₁ β} {g : α → OracleComp spec₂ β}
    (hfg : ∀ a, RelTriple' (f a) (g a) (EqRel β)) :
    RelTriple' (xs.mapM f) (xs.mapM g) (EqRel (List β)) :=
  relTriple'_iff_relTriple.mpr <|
    relTriple_list_mapM_eqRel (fun a => relTriple'_iff_relTriple.mp (hfg a))

/-- `RelTriple'` for `List.foldlM`. -/
theorem relTriple'_list_foldlM
    {σ₁ σ₂ : Type}
    {xs : List α} {ys : List β}
    {f : σ₁ → α → OracleComp spec₁ σ₁}
    {g : σ₂ → β → OracleComp spec₂ σ₂}
    {Rin : α → β → Prop} {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hxy : List.Forall₂ Rin xs ys)
    (hfg : ∀ a b, Rin a b → ∀ t₁ t₂, S t₁ t₂ → RelTriple' (f t₁ a) (g t₂ b) S) :
    RelTriple' (xs.foldlM f s₁) (ys.foldlM g s₂) S :=
  relTriple'_iff_relTriple.mpr <|
    relTriple_list_foldlM hs hxy
      (fun a b hab t₁ t₂ ht => relTriple'_iff_relTriple.mp (hfg a b hab t₁ t₂ ht))

/-- Same-input specialization of `relTriple'_list_foldlM`. -/
theorem relTriple'_list_foldlM_same
    {σ₁ σ₂ : Type}
    {xs : List α}
    {f : σ₁ → α → OracleComp spec₁ σ₁}
    {g : σ₂ → α → OracleComp spec₂ σ₂}
    {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hfg : ∀ a t₁ t₂, S t₁ t₂ → RelTriple' (f t₁ a) (g t₂ a) S) :
    RelTriple' (xs.foldlM f s₁) (xs.foldlM g s₂) S :=
  relTriple'_iff_relTriple.mpr <|
    relTriple_list_foldlM_same hs
      (fun a t₁ t₂ ht => relTriple'_iff_relTriple.mp (hfg a t₁ t₂ ht))

section Sampling

variable [SampleableType α]

/-- Bijection coupling for uniform sampling at the `RelTriple'` level. -/
theorem relTriple'_uniformSample_bij
    {f : α → α} (hf : Function.Bijective f) (R : RelPost α α)
    (hR : ∀ x, R x (f x)) :
    RelTriple' ($ᵗ α) ($ᵗ α) R :=
  relTriple'_iff_relTriple.mpr (relTriple_uniformSample_bij hf R hR)

/-- Identity coupling for uniform sampling at the `RelTriple'` level. -/
theorem relTriple'_uniformSample_refl :
    RelTriple' ($ᵗ α) ($ᵗ α) (EqRel α) :=
  relTriple'_iff_relTriple.mpr relTriple_uniformSample_refl

end Sampling

/-! ## Helpers for statistical distance / coupling characterization -/

private lemma probOutput_diag_le_min_marginals
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (c : SPMF.Coupling (𝒟[oa]) (𝒟[ob])) (a : α) :
    Pr[= (a, a) | c.1] ≤ min (Pr[= a | 𝒟[oa]]) (Pr[= a | 𝒟[ob]]) := by
  refine le_min ?_ ?_
  · calc
      Pr[= (a, a) | c.1] = Pr[fun z : α × α => z = (a, a) | c.1] :=
        (probEvent_eq_eq_probOutput c.1 (a, a)).symm
      _ ≤ Pr[fun z : α × α => z.1 = a | c.1] :=
        _root_.probEvent_mono fun z _ hz => by
          simp [hz]
      _ = Pr[fun x : α => x = a | Prod.fst <$> c.1] := by
        simpa only [Function.comp_apply] using
          (probEvent_map (mx := c.1) (f := Prod.fst) (q := fun x : α => x = a)).symm
      _ = Pr[= a | Prod.fst <$> c.1] := by
        rw [probEvent_eq_eq_probOutput]
      _ = Pr[= a | 𝒟[oa]] := by
        rw [c.2.map_fst]
  · calc
      Pr[= (a, a) | c.1] = Pr[fun z : α × α => z = (a, a) | c.1] :=
        (probEvent_eq_eq_probOutput c.1 (a, a)).symm
      _ ≤ Pr[fun z : α × α => z.2 = a | c.1] :=
        _root_.probEvent_mono fun z _ hz => by
          simp [hz]
      _ = Pr[fun x : α => x = a | Prod.snd <$> c.1] := by
        simpa only [Function.comp_apply] using
          (probEvent_map (mx := c.1) (f := Prod.snd) (q := fun x : α => x = a)).symm
      _ = Pr[= a | Prod.snd <$> c.1] := by
        rw [probEvent_eq_eq_probOutput]
      _ = Pr[= a | 𝒟[ob]] := by
        rw [c.2.map_snd]

private lemma eRelWP_indicator_eqRel_le
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    eRelWP oa ob (RelPost.indicator (EqRel α)) ≤
      ∑' a, min (Pr[= a | 𝒟[oa]]) (Pr[= a | 𝒟[ob]]) := by
  letI : DecidableEq α := Classical.decEq α
  unfold eRelWP
  refine iSup_le fun c => ?_
  calc ∑' z, Pr[= z | c.1] * RelPost.indicator (EqRel α) z.1 z.2
      = ∑' z : α × α, if z.1 = z.2 then Pr[= z | c.1] else 0 := by
        congr 1; ext ⟨a, b⟩; simp [RelPost.indicator, EqRel]
    _ = ∑' a, Pr[= (a, a) | c.1] := by
        rw [ENNReal.tsum_prod']
        congr 1; ext a
        rw [tsum_eq_single a (fun b hb => if_neg (Ne.symm hb))]
        simp
    _ ≤ ∑' a, min (Pr[= a | 𝒟[oa]]) (Pr[= a | 𝒟[ob]]) :=
        ENNReal.tsum_le_tsum fun a => probOutput_diag_le_min_marginals c a

private lemma min_add_tsub (a b : ℝ≥0∞) : min a b + (a - b) = a := by
  rw [add_comm, tsub_add_min]

private lemma tsum_min_add_etvDist_eq_one
    {p q : PMF (Option α)} (hp : p none = 0) (hq : q none = 0) :
    ∑' a, min (p (some a)) (q (some a)) + p.etvDist q = 1 := by
  set S := ∑' a, min (p (some a)) (q (some a))
  have hsum_p : ∑' a, p (some a) = 1 := by
    simpa [tsum_option _ ENNReal.summable, hp] using p.tsum_coe
  have hsum_q : ∑' a, q (some a) = 1 := by
    simpa [tsum_option _ ENNReal.summable, hq] using q.tsum_coe
  have hS_le : S ≤ 1 := hsum_p ▸ ENNReal.tsum_le_tsum fun a => min_le_left _ _
  have h1 : S + ∑' a, (p (some a) - q (some a)) = 1 := by
    rw [← ENNReal.tsum_add, ← hsum_p]
    exact tsum_congr fun a => min_add_tsub (p (some a)) (q (some a))
  have h2 : S + ∑' a, (q (some a) - p (some a)) = 1 := by
    rw [← ENNReal.tsum_add, ← hsum_q]
    exact tsum_congr fun a => by rw [min_comm]; exact min_add_tsub (q (some a)) (p (some a))
  have hS_ne_top : S ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hS_le
  have htsub1 : ∑' a, (p (some a) - q (some a)) = 1 - S :=
    ENNReal.eq_sub_of_add_eq hS_ne_top (by rwa [add_comm] at h1)
  have htsub2 : ∑' a, (q (some a) - p (some a)) = 1 - S :=
    ENNReal.eq_sub_of_add_eq hS_ne_top (by rwa [add_comm] at h2)
  have habsdiff_sum : ∑' a, ENNReal.absDiff (p (some a)) (q (some a)) = 2 * (1 - S) := by
    simp only [ENNReal.absDiff, ENNReal.tsum_add, htsub1, htsub2, two_mul]
  rw [PMF.etvDist, tsum_option _ ENNReal.summable, hp, hq, ENNReal.absDiff_self, zero_add,
    habsdiff_sum, mul_comm, ENNReal.mul_div_cancel_right two_ne_zero ofNat_ne_top]
  exact add_tsub_cancel_of_le hS_le

private lemma tsum_min_eq_one_sub_etvDist
    {p q : PMF (Option α)} (hp : p none = 0) (hq : q none = 0) :
    ∑' a, min (p (some a)) (q (some a)) = 1 - p.etvDist q :=
  ENNReal.eq_sub_of_add_eq (PMF.etvDist_ne_top p q) (tsum_min_add_etvDist_eq_one hp hq)

private lemma tsum_min_probOutput_eq_one_sub_etvDist
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    ∑' a, min (Pr[= a | 𝒟[oa]]) (Pr[= a | 𝒟[ob]]) =
      1 - (𝒟[oa]).toPMF.etvDist (𝒟[ob]).toPMF := by
  simp_rw [show ∀ a, min (Pr[= a | 𝒟[oa]]) (Pr[= a | 𝒟[ob]]) =
      min ((𝒟[oa]).toPMF (some a)) ((𝒟[ob]).toPMF (some a))
      from fun a => by simp [probOutput_def, SPMF.apply_eq_toPMF_some]]
  exact tsum_min_eq_one_sub_etvDist
    (probFailure_eq_zero (mx := oa))
    (probFailure_eq_zero (mx := ob))

private lemma tsum_min_le_eRelWP
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    ∑' a, min (Pr[= a | 𝒟[oa]]) (Pr[= a | 𝒟[ob]]) ≤
      eRelWP oa ob (RelPost.indicator (EqRel α)) := by
  letI : DecidableEq α := Classical.decEq α
  set pa := 𝒟[oa]; set pb := 𝒟[ob]
  set P := fun a => Pr[= a | pa]; set Q := fun a => Pr[= a | pb]
  set rP := fun a => P a - min (P a) (Q a)
  set rQ := fun a => Q a - min (Q a) (P a)
  set δ := ∑' a, rP a
  have hP_sum : ∑' a, P a = 1 := tsum_probOutput_of_liftM_PMF oa
  have hQ_sum : ∑' a, Q a = 1 := tsum_probOutput_of_liftM_PMF ob
  have hδ_ne_top : δ ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (hP_sum ▸ ENNReal.tsum_le_tsum fun a => tsub_le_self)
  have hδ_eq_rQ : ∑' a, rQ a = δ := by
    have hS_ne_top : (∑' a, min (P a) (Q a)) ≠ ⊤ :=
      ne_top_of_le_ne_top one_ne_top (hP_sum ▸ ENNReal.tsum_le_tsum fun a => min_le_left _ _)
    have h1 : ∑' a, min (P a) (Q a) + δ = 1 := by
      rw [← ENNReal.tsum_add, ← hP_sum]
      exact tsum_congr fun a => add_tsub_cancel_of_le (min_le_left (P a) (Q a))
    have h2 : ∑' a, min (P a) (Q a) + ∑' a, rQ a = 1 := by
      rw [← ENNReal.tsum_add, ← hQ_sum]
      exact tsum_congr fun a =>
        min_comm (P a) (Q a) ▸ add_tsub_cancel_of_le (min_le_left (Q a) (P a))
    exact ((ENNReal.add_right_inj hS_ne_top).mp (h1.trans h2.symm)).symm
  have hmul_δ : ∀ a, rP a * (δ * δ⁻¹) = rP a := by
    intro a
    rcases eq_or_ne δ 0 with hδ0 | hδ0
    · have : rP a = 0 := le_antisymm (hδ0 ▸ ENNReal.le_tsum a) bot_le
      simp [this, hδ0]
    · rw [ENNReal.mul_inv_cancel hδ0 hδ_ne_top, mul_one]
  set cf : Option (α × α) → ℝ≥0∞ := fun
    | none => 0
    | some (a, b) => (if a = b then min (P a) (Q a) else 0) + rP a * rQ b * δ⁻¹
  have hfst_sum : ∀ a, ∑' b, cf (some (a, b)) = P a := by
    intro a
    change ∑' b, ((if a = b then min (P a) (Q a) else 0) + rP a * rQ b * δ⁻¹) = P a
    rw [ENNReal.tsum_add, tsum_eq_single a (fun b hb => if_neg (Ne.symm hb))]
    simp only [ite_true]
    simp_rw [mul_right_comm (rP a) (rQ _) δ⁻¹]
    rw [ENNReal.tsum_mul_left, hδ_eq_rQ, mul_assoc, mul_comm δ⁻¹ δ, hmul_δ]
    exact add_tsub_cancel_of_le (min_le_left _ _)
  have hsnd_sum : ∀ b, ∑' a, cf (some (a, b)) = Q b := by
    intro b
    change ∑' a, ((if a = b then min (P a) (Q a) else 0) + rP a * rQ b * δ⁻¹) = Q b
    rw [ENNReal.tsum_add]
    conv_lhs => arg 1; rw [show
      (fun a => if a = b then min (P a) (Q a) else (0 : ℝ≥0∞)) =
        (fun a => if a = b then min (Q b) (P b) else 0) from by
          ext a
          split <;> simp_all [min_comm]]
    rw [tsum_eq_single b (fun a ha => if_neg ha)]
    simp only [ite_true]
    have htsum_rQ : ∑' a, rP a * rQ b * δ⁻¹ = rQ b := by
      simp_rw [mul_rotate (rP _) (rQ b) δ⁻¹]
      rw [ENNReal.tsum_mul_left]
      rcases eq_or_ne δ 0 with hδ0 | hδ0
      · have hrQ0 : rQ b = 0 :=
          le_antisymm (hδ0 ▸ hδ_eq_rQ ▸ ENNReal.le_tsum b) bot_le
        simp only [hrQ0, zero_mul]
      · rw [mul_assoc, ENNReal.inv_mul_cancel hδ0 hδ_ne_top, mul_one]
    rw [htsum_rQ]
    exact add_tsub_cancel_of_le (min_le_left _ _)
  have hcf_sum : ∑' x, cf x = 1 := by
    rw [tsum_option _ ENNReal.summable, show cf none = 0 from rfl, zero_add,
      ENNReal.tsum_prod', tsum_congr hfst_sum]
    exact hP_sum
  let c_pmf : PMF (Option (α × α)) := ⟨cf, hcf_sum ▸ ENNReal.summable.hasSum⟩
  let c_spmf : SPMF (α × α) := c_pmf
  have hite_tsum : ∀ {β : Type} (P : Prop) [Decidable P] (f : β → ℝ≥0∞),
      ∑' b, (if P then f b else 0) = if P then ∑' b, f b else 0 := by
    intro β P _ f; split <;> simp
  have hcpl_fst : Prod.fst <$> c_spmf = pa := by
    apply SPMF.ext; intro a
    rw [show (Prod.fst <$> c_spmf) a = Pr[= a | Prod.fst <$> c_spmf] from rfl,
      probOutput_map_eq_tsum_ite c_spmf Prod.fst a]
    change ∑' z : α × α, (if a = z.1 then cf (some z) else 0) = P a
    rw [ENNReal.tsum_prod', tsum_congr fun a₁ => hite_tsum (a = a₁) (fun b => cf (some (a₁, b))),
      tsum_eq_single a (fun a' (ha' : a' ≠ a) => if_neg (Ne.symm ha')), if_pos rfl, hfst_sum]
  have hcpl_snd : Prod.snd <$> c_spmf = pb := by
    apply SPMF.ext; intro b
    rw [show (Prod.snd <$> c_spmf) b = Pr[= b | Prod.snd <$> c_spmf] from rfl,
      probOutput_map_eq_tsum_ite c_spmf Prod.snd b]
    change ∑' z : α × α, (if b = z.2 then cf (some z) else 0) = Q b
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm,
      tsum_congr fun b₁ => hite_tsum (b = b₁) (fun a => cf (some (a, b₁))),
      tsum_eq_single b (fun b' (hb' : b' ≠ b) => if_neg (Ne.symm hb')), if_pos rfl, hsnd_sum]
  let c : SPMF.Coupling pa pb := ⟨c_spmf, hcpl_fst, hcpl_snd⟩
  have hobj_eq : ∑' z : α × α, Pr[= z | c.1] * RelPost.indicator (EqRel α) z.1 z.2 =
      ∑' a, cf (some (a, a)) := by
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun a => ?_
    rw [tsum_eq_single a fun b hb => ?_]
    · simp only [RelPost.indicator, EqRel, ite_true, mul_one, SPMF.probOutput_eq_apply]; rfl
    · simp [RelPost.indicator, EqRel, Ne.symm hb]
  calc ∑' a, min (P a) (Q a)
      ≤ ∑' a, cf (some (a, a)) := ENNReal.tsum_le_tsum fun a => by simp [cf]
    _ = ∑' z : α × α, Pr[= z | c.1] * RelPost.indicator (EqRel α) z.1 z.2 :=
        hobj_eq.symm
    _ ≤ eRelWP oa ob (RelPost.indicator (EqRel α)) :=
        le_iSup (fun c' : SPMF.Coupling pa pb =>
          ∑' z, Pr[= z | c'.1] * RelPost.indicator (EqRel α) z.1 z.2) c

/-! ## Statistical distance via eRHL -/

/-- Statistical distance as a complement of eRHL value with equality indicator.
Uses `SPMF.tvDist` directly to handle cross-spec comparison. -/
theorem spmf_tvDist_eq_one_sub_eRelWP_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} :
    SPMF.tvDist (𝒟[oa]) (𝒟[ob]) =
      (1 - eRelWP oa ob (RelPost.indicator (EqRel α))).toReal := by
  set p := (𝒟[oa]).toPMF
  set q := (𝒟[ob]).toPMF
  have htmin := tsum_min_probOutput_eq_one_sub_etvDist (oa := oa) (ob := ob)
  have hle : eRelWP oa ob (RelPost.indicator (EqRel α)) ≤ 1 - p.etvDist q :=
    htmin ▸ eRelWP_indicator_eqRel_le
  have hge : 1 - p.etvDist q ≤ eRelWP oa ob (RelPost.indicator (EqRel α)) :=
    htmin ▸ tsum_min_le_eRelWP
  have heq : eRelWP oa ob (RelPost.indicator (EqRel α)) =
      1 - (𝒟[oa]).toPMF.etvDist (𝒟[ob]).toPMF := le_antisymm hle hge
  simp only [heq, SPMF.tvDist, PMF.tvDist,
    ENNReal.sub_sub_cancel one_ne_top (PMF.etvDist_le_one _ _)]

/-- Same-spec version using the `tvDist` notation. -/
theorem tvDist_eq_one_sub_eRelWP_eqRel
    {oa ob : OracleComp spec₁ α} :
    tvDist oa ob = (1 - eRelWP (spec₂ := spec₁) oa ob
      (RelPost.indicator (EqRel α))).toReal := by
  simpa [tvDist] using
    (spmf_tvDist_eq_one_sub_eRelWP_eqRel
      (spec₁ := spec₁) (spec₂ := spec₁) (oa := oa) (ob := ob))

/-- A TV-distance bound induces an approximate equality coupling. -/
theorem approxRelTriple_eqRel_of_ofReal_tvDist_le
    {oa ob : OracleComp spec₁ α} {ε : ℝ≥0∞}
    (h : ENNReal.ofReal (tvDist oa ob) ≤ ε) :
    ApproxRelTriple ε oa ob (EqRel α) := by
  unfold ApproxRelTriple
  rw [tvDist_eq_one_sub_eRelWP_eqRel] at h
  set w := eRelWP (spec₂ := spec₁) oa ob (RelPost.indicator (EqRel α)) with hw
  have hsub_ne_top : 1 - w ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top tsub_le_self
  have hsub_le : 1 - w ≤ ε := by
    simpa [hw, ENNReal.ofReal_toReal hsub_ne_top] using h
  rw [tsub_le_iff_right] at hsub_le ⊢
  simpa [add_comm, add_left_comm, add_assoc] using hsub_le

/-- Game equivalence from pRHL equality coupling. -/
theorem gameEquiv_of_relTriple'_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : RelTriple' oa ob (EqRel α)) :
    𝒟[oa] = 𝒟[ob] :=
  evalDist_eq_of_relTriple_eqRel (relTriple'_iff_relTriple.mp h)

/-! ## Relational algebra instance -/

/-- Pure values characterize the quantitative relational weakest precondition. -/
theorem eRelWP_pure (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    eRelWP (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) post = post a b := by
  apply le_antisymm
  · unfold eRelWP
    refine iSup_le fun c => ?_
    have hcEq : c.1 = (pure (a, b) : SPMF (α × β)) := by
      apply SPMF.IsCoupling.pure_iff.mp
      simpa only [evalDist_pure] using c.2
    rw [hcEq, tsum_eq_single (a, b)]
    · simp [SPMF.probOutput_eq_apply]
    · intro z hz
      simp [SPMF.probOutput_eq_apply, hz]
  · exact eRelWP_pure_le (spec₁ := spec₁) (spec₂ := spec₂) a b post

/-- Quantitative relational weakest precondition is monotone in the postcondition. -/
theorem eRelWP_mono {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {post post' : α → β → ℝ≥0∞}
    (hpost : ∀ a b, post a b ≤ post' a b) :
    eRelWP oa ob post ≤ eRelWP oa ob post' :=
  eRelWP_conseq (spec₁ := spec₁) (spec₂ := spec₂)
    (pre := eRelWP oa ob post) (pre' := eRelWP oa ob post)
    (oa := oa) (ob := ob) (post := post) (post' := post')
    le_rfl hpost le_rfl

/-- Quantitative relational weakest preconditions compose through bind. -/
theorem eRelWP_bind_le
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (fa : α → OracleComp spec₁ γ) (fb : β → OracleComp spec₂ δ)
    (post : γ → δ → ℝ≥0∞) :
    eRelWP oa ob (fun a b => eRelWP (fa a) (fb b) post) ≤
      eRelWP (oa >>= fa) (ob >>= fb) post :=
  eRelWP_bind_rule (spec₁ := spec₁) (spec₂ := spec₂)
    (pre := eRelWP oa ob (fun a b => eRelWP (fa a) (fb b) post))
    (oa := oa) (ob := ob) (fa := fa) (fb := fb)
    (cut := fun a b => eRelWP (fa a) (fb b) post)
    (post := post) le_rfl (fun _ _ => le_rfl)

/-- Quantitative relational algebra instance for `OracleComp`, based on `eRelWP`. -/
noncomputable instance instMAlgRelOrdered_eRelWP :
    MAlgRelOrdered (OracleComp spec₁) (OracleComp spec₂) ℝ≥0∞ where
  rwp := fun oa ob post => eRelWP oa ob post
  rwp_pure := fun a b post => eRelWP_pure (spec₁ := spec₁) (spec₂ := spec₂) a b post
  rwp_mono := fun hpost => eRelWP_mono (spec₁ := spec₁) (spec₂ := spec₂) hpost
  rwp_bind_le := fun oa ob fa fb post =>
    eRelWP_bind_le (spec₁ := spec₁) (spec₂ := spec₂) oa ob fa fb post

/-- Anchoring instance for the quantitative `ℝ≥0∞`-valued relational logic on `OracleComp`.

When one of the two computations is `pure`, the supremum over couplings collapses to the
single Dirac coupling (existence: `IsCoupling.dirac_left`; uniqueness on the supports follows
from `IsCoupling.apply_pure_left_eq`), and the relational expectation reduces to the unary
expectation `wp y (post a)` (resp. `wp x (fun a => post a b)`). This is the genuinely
quantitative analogue of the qualitative `Anchored Prop` instance in
`VCVio/ProgramLogic/Relational/Basic.lean`. -/
noncomputable instance instAnchored_eRelWP :
    MAlgRelOrdered.Anchored (OracleComp spec₁) (OracleComp spec₂) ℝ≥0∞ where
  rwp_pure_left {α β} a y post := by
    change eRelWP (pure a : OracleComp spec₁ α) y post =
      wp y (post a)
    rw [wp_eq_tsum]
    apply le_antisymm
    · refine iSup_le fun c => ?_
      have hcPure : SPMF.IsCoupling c.1 (pure a) (𝒟[y]) := by
        simpa [evalDist_pure] using c.2
      exact (hcPure.tsum_pure_left post).le
    · have hnf : (𝒟[y]).toPMF none = 0 := probFailure_eq_zero (mx := y)
      have hcPure : SPMF.IsCoupling (((a, ·) : β → α × β) <$> 𝒟[y]) (pure a) (𝒟[y]) :=
        SPMF.IsCoupling.dirac_left a hnf
      have hCoupling : SPMF.IsCoupling (((a, ·) : β → α × β) <$> 𝒟[y])
          (𝒟[(pure a : OracleComp spec₁ α)]) (𝒟[y]) := by
        simpa [evalDist_pure] using hcPure
      let c : SPMF.Coupling (𝒟[(pure a : OracleComp spec₁ α)]) (𝒟[y]) :=
        ⟨((a, ·) : β → α × β) <$> 𝒟[y], hCoupling⟩
      exact le_iSup_of_le c (hcPure.tsum_pure_left post).ge
  rwp_pure_right {α β} x b post := by
    change eRelWP x (pure b : OracleComp spec₂ β) post =
      wp x (fun a => post a b)
    rw [wp_eq_tsum]
    apply le_antisymm
    · refine iSup_le fun c => ?_
      have hcPure : SPMF.IsCoupling c.1 (𝒟[x]) (pure b) := by
        simpa [evalDist_pure] using c.2
      exact (hcPure.tsum_pure_right post).le
    · have hnf : (𝒟[x]).toPMF none = 0 := probFailure_eq_zero (mx := x)
      have hcPure : SPMF.IsCoupling (((·, b) : α → α × β) <$> 𝒟[x]) (𝒟[x]) (pure b) :=
        SPMF.IsCoupling.dirac_right b hnf
      have hCoupling : SPMF.IsCoupling (((·, b) : α → α × β) <$> 𝒟[x])
          (𝒟[x]) (𝒟[(pure b : OracleComp spec₂ β)]) := by
        simpa [evalDist_pure] using hcPure
      let c : SPMF.Coupling (𝒟[x]) (𝒟[(pure b : OracleComp spec₂ β)]) :=
        ⟨((·, b) : α → α × β) <$> 𝒟[x], hCoupling⟩
      exact le_iSup_of_le c (hcPure.tsum_pure_right post).ge

noncomputable example :
    MAlgRelOrdered (OptionT (OracleComp spec₁)) (OracleComp spec₂) ℝ≥0∞ :=
  inferInstance

noncomputable example {ε : Type} :
    MAlgRelOrdered (ExceptT ε (OracleComp spec₁)) (OracleComp spec₂) ℝ≥0∞ :=
  inferInstance

noncomputable example {σ : Type} :
    MAlgRelOrdered (StateT σ (OracleComp spec₁)) (OracleComp spec₂) (σ → ℝ≥0∞) :=
  inferInstance

/-! ## Specialisations of the generic asynchronous and structural rules

The following examples confirm that the generic rules in
`ToMathlib/Control/Monad/RelationalAlgebra.lean` (asynchronous one-sided
binds and structural pure rules) automatically apply to `eRelWP`. They are
the quantitative counterparts of SSProve's `apply_left` / `apply_right` /
`if_rule` style rules.
-/

example {α β γ : Type}
    (oa : OracleComp spec₁ α) (fa : α → OracleComp spec₁ γ)
    (ob : OracleComp spec₂ β) (post : γ → β → ℝ≥0∞) :
    eRelWP oa ob (fun a b => eRelWP (fa a) (pure b : OracleComp spec₂ β) post)
      ≤ eRelWP (oa >>= fa) ob post :=
  MAlgRelOrdered.relWP_bind_left_le oa fa ob post

example {α β δ : Type}
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (fb : β → OracleComp spec₂ δ)
    (post : α → δ → ℝ≥0∞) :
    eRelWP oa ob (fun a b => eRelWP (pure a : OracleComp spec₁ α) (fb b) post)
      ≤ eRelWP oa (ob >>= fb) post :=
  MAlgRelOrdered.relWP_bind_right_le oa ob fb post

example {α β : Type}
    (b : Bool) (oa oa' : OracleComp spec₁ α) (ob ob' : OracleComp spec₂ β)
    (pre : ℝ≥0∞) (post : α → β → ℝ≥0∞)
    (h_t : b = true → MAlgRelOrdered.Triple pre oa ob post)
    (h_f : b = false → MAlgRelOrdered.Triple pre oa' ob' post) :
    MAlgRelOrdered.Triple pre
        (if b then oa else oa') (if b then ob else ob') post :=
  MAlgRelOrdered.triple_ite b h_t h_f

/-! ## Quantitative effect-specific rules (eRHL primitives)

These are the genuinely quantitative companions of the indicator wrappers above: they
expose witness-based lower bounds for `eRelWP` on the basic `OracleComp` effect operations
(uniform sampling and oracle queries under a bijection). Together with the existing closed
form `eRelWP_pure` and the core `eRelWP_pure_le / _conseq / _bind_rule`, they are sufficient to
discharge most apRHL-style goals without descending to the underlying coupling supremum.
-/

/-- A witness coupling provides a lower bound on the eRHL weakest precondition.

This is the basic primitive used by every closed-form / lower-bound rule below, and is the
right tool whenever a proof can exhibit a specific coupling. -/
theorem le_eRelWP_of_isCoupling
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (post : α → β → ℝ≥0∞)
    (c : SPMF (α × β)) (hc : SPMF.IsCoupling c (𝒟[oa]) (𝒟[ob])) :
    (∑' z, Pr[= z | c] * post z.1 z.2) ≤ eRelWP oa ob post :=
  le_iSup (f := fun c' : SPMF.Coupling (𝒟[oa]) (𝒟[ob]) =>
    ∑' z, Pr[= z | c'.1] * post z.1 z.2) ⟨c, hc⟩

@[deprecated (since := "2026-06-25")]
alias eRelWP_ge_of_isCoupling := le_eRelWP_of_isCoupling

/-- A witness coupling whose score dominates the precondition discharges a
quantitative relational WP lower-bound obligation. -/
theorem eRelWP_of_isCoupling
    {pre : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (post : α → β → ℝ≥0∞)
    (c : SPMF (α × β)) (hc : SPMF.IsCoupling c (𝒟[oa]) (𝒟[ob]))
    (hpre : pre ≤ ∑' z, Pr[= z | c] * post z.1 z.2) :
    pre ≤ eRelWP oa ob post :=
  hpre.trans (le_eRelWP_of_isCoupling post c hc)

/-- Reindex the score of the bijection coupling `base >>= fun a => pure (a, f a)` as a
sum over `a`, collapsing the second component. Shared by the uniform-sampling and
oracle-query lower bounds below. -/
private lemma tsum_probOutput_bind_pure_pair {α' : Type*}
    (base : SPMF α') (f : α' → α') (post : α' → α' → ℝ≥0∞) :
    (∑' z : α' × α', Pr[= z | (base >>= fun a => pure (a, f a))] * post z.1 z.2)
      = ∑' a : α', Pr[= a | base] * post a (f a) :=
  calc ∑' z : α' × α', Pr[= z | (base >>= fun a => pure (a, f a))] * post z.1 z.2
      = ∑' z : α' × α', (∑' a : α', Pr[= a | base] *
          Pr[= z | (pure (a, f a) : SPMF (α' × α'))]) * post z.1 z.2 := by
        simp_rw [probOutput_bind_eq_tsum base fun a => pure (a, f a)]
    _ = ∑' a : α', ∑' z : α' × α', Pr[= a | base] *
          Pr[= z | (pure (a, f a) : SPMF (α' × α'))] * post z.1 z.2 := by
        rw [ENNReal.tsum_comm]; exact tsum_congr fun a => by rw [ENNReal.tsum_mul_right]
    _ = ∑' a : α', Pr[= a | base] * post a (f a) :=
      tsum_congr fun a => by
        rw [tsum_eq_single (a, f a) fun z hz => by simp [SPMF.probOutput_eq_apply, hz],
          show Pr[= (a, f a) | (pure (a, f a) : SPMF (α' × α'))] = 1 by
            simp [SPMF.probOutput_eq_apply], mul_one]

/-! ### Uniform sampling under a bijection -/

section Sampling

variable [SampleableType α]

/-- Quantitative lower bound for two uniform samples coupled by a bijection.

The bijection coupling `(fun x => (x, f x)) <$> $ᵗ α` realises the sum on the left as a
score, providing the sharpest "syntactic" lower bound on the coupling supremum. -/
theorem eRelWP_uniformSample_bij_ge
    {f : α → α} (hf : Function.Bijective f) (post : α → α → ℝ≥0∞) :
    (∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)] * post a (f a))
      ≤ eRelWP ($ᵗ α : ProbComp α) ($ᵗ α : ProbComp α) post := by
  set c : SPMF (α × α) := 𝒟[($ᵗ α : ProbComp α)] >>= fun a => pure (a, f a)
  have hc : SPMF.IsCoupling c (𝒟[($ᵗ α : ProbComp α)])
      (𝒟[($ᵗ α : ProbComp α)]) := by
    constructor
    · simp [c]
    · simp only [c, map_bind, map_pure]
      calc
        (do
            let a ← 𝒟[($ᵗ α : ProbComp α)]
            pure (f a)) = f <$> 𝒟[($ᵗ α : ProbComp α)] := rfl
        _ = 𝒟[f <$> ($ᵗ α : ProbComp α)] :=
          (evalDist_map ($ᵗ α : ProbComp α) f).symm
        _ = 𝒟[($ᵗ α : ProbComp α)] := by
          apply evalDist_ext
          intro x
          obtain ⟨x', rfl⟩ := hf.surjective x
          rw [probOutput_map_injective ($ᵗ α) hf.injective x']
          simpa [uniformSample] using
            SampleableType.probOutput_selectElem_eq (β := α) x' (f x')
  calc ∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)] * post a (f a)
      = ∑' z : α × α, Pr[= z | c] * post z.1 z.2 :=
        (tsum_probOutput_bind_pure_pair (𝒟[($ᵗ α : ProbComp α)]) f post).symm
    _ ≤ eRelWP ($ᵗ α : ProbComp α) ($ᵗ α : ProbComp α) post :=
        le_eRelWP_of_isCoupling post c hc

/-- Any precondition below the bijection average discharges the quantitative
relational WP lower-bound for two uniform samples. -/
theorem eRelWP_uniformSample_bij
    {f : α → α} (hf : Function.Bijective f) (post : α → α → ℝ≥0∞)
    {pre : ℝ≥0∞}
    (hpre : pre ≤ ∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)] * post a (f a)) :
    pre ≤ eRelWP ($ᵗ α : ProbComp α) ($ᵗ α : ProbComp α) post :=
  hpre.trans (eRelWP_uniformSample_bij_ge hf post)

end Sampling

/-! ### Oracle queries under a bijection -/

/-- Quantitative lower bound for two oracle queries coupled by a bijection on the range.
This is the eRHL counterpart of `relTriple_query_bij`. -/
theorem eRelWP_query_bij_ge (t : spec₁.Domain)
    {f : spec₁.Range t → spec₁.Range t}
    (hf : Function.Bijective f)
    (post : spec₁.Range t → spec₁.Range t → ℝ≥0∞) :
    (∑' a : spec₁.Range t,
        Pr[= a | (liftM (query t) : OracleComp spec₁ (spec₁.Range t))] * post a (f a))
      ≤ eRelWP (spec₁ := spec₁) (spec₂ := spec₁)
          (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
          (liftM (query t) : OracleComp spec₁ (spec₁.Range t)) post := by
  set oq : OracleComp spec₁ (spec₁.Range t) := liftM (query t)
  set c : SPMF (spec₁.Range t × spec₁.Range t) := 𝒟[oq] >>= fun a => pure (a, f a)
  have hc : SPMF.IsCoupling c (𝒟[oq]) (𝒟[oq]) := by
    constructor
    · simp [c]
    · simp only [c, map_bind, map_pure, oq, evalDist_query]
      change f <$> (liftM (PMF.uniformOfFintype (spec₁.Range t)) : SPMF _) =
        (liftM (PMF.uniformOfFintype (spec₁.Range t)) : SPMF _)
      rw [show f <$> (liftM (PMF.uniformOfFintype (spec₁.Range t)) : SPMF _) =
        (liftM (f <$> PMF.uniformOfFintype (spec₁.Range t)) : SPMF _) from by simp]
      congr 1
      exact PMF.uniformOfFintype_map_of_bijective f hf
  calc ∑' a : spec₁.Range t, Pr[= a | oq] * post a (f a)
      = ∑' z : spec₁.Range t × spec₁.Range t, Pr[= z | c] * post z.1 z.2 :=
        (tsum_probOutput_bind_pure_pair (𝒟[oq]) f post).symm
    _ ≤ eRelWP (spec₁ := spec₁) (spec₂ := spec₁) oq oq post :=
        le_eRelWP_of_isCoupling post c hc

/-- Triple form of `eRelWP_query_bij_ge`. -/
theorem eRelWP_query_bij (t : spec₁.Domain)
    {f : spec₁.Range t → spec₁.Range t}
    (hf : Function.Bijective f)
    (post : spec₁.Range t → spec₁.Range t → ℝ≥0∞)
    {pre : ℝ≥0∞}
    (hpre : pre ≤ ∑' a : spec₁.Range t,
        Pr[= a | (liftM (query t) : OracleComp spec₁ (spec₁.Range t))] * post a (f a)) :
    pre ≤ eRelWP (spec₁ := spec₁) (spec₂ := spec₁)
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t)) post :=
  hpre.trans (eRelWP_query_bij_ge t hf post)

/-! ## Demonstration examples for the indicator wrappers and quantitative primitives

Small examples illustrating how the `RelTriple'` wrappers and the closed-form / lower-bound
`eRelWP` rules combine in practice.
-/

/-- Querying the same oracle on both sides, then mapping by a function, yields a `RelTriple'`
on the equality of the mapped outputs. Uses `relTriple'_query` followed by
`relTriple'_post_mono`. -/
example (t : spec₁.Domain) (g : spec₁.Range t → α) :
    RelTriple' (spec₁ := spec₁) (spec₂ := spec₁)
      (g <$> (liftM (query t) : OracleComp spec₁ (spec₁.Range t)))
      (g <$> (liftM (query t) : OracleComp spec₁ (spec₁.Range t)))
      (EqRel α) :=
  relTriple'_map (R := EqRel α)
    (relTriple'_post_mono (relTriple'_query t)
      (fun _ _ h => congrArg g h))

/-- Quantitative bound via `eRelWP_uniformSample_bij`: any precondition below the
bijection-shifted average is realised by the bijection coupling. -/
example [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) (post : α → α → ℝ≥0∞) :
    (∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)] * post a (f a))
      ≤ eRelWP ($ᵗ α : ProbComp α) ($ᵗ α : ProbComp α) post :=
  eRelWP_uniformSample_bij hf post le_rfl

end OracleComp.ProgramLogic.Relational
