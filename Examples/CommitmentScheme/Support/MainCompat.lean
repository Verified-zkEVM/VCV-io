/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import VCVio.OracleComp.EvalDist
import VCVio.EvalDist.TVDist
import VCVio.ProgramLogic.Notation
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.ProgramLogic.Unary.SimulateQ

/-!
# Commitment Scheme local compatibility shims

This file contains proof-local adapters against `main` APIs.

## TODO: upstream candidates

The following declarations are not commitment-scheme-specific and should
eventually move to VCVio core:
- `tvDist_bind_left_le` → `VCVio/EvalDist/TVDist.lean`
- `map_run_simulateQ_eq_of_query_map_eq'` → `VCVio/ProgramLogic/Relational/`
- `run'_simulateQ_eq_of_query_map_eq'` → `VCVio/ProgramLogic/Relational/`
- `tvDist_simulateQ_le_probEvent_bad_dist` → `VCVio/ProgramLogic/Relational/`
-/

open OracleSpec OracleComp

universe u v w

open ENNReal in
private lemma pmf_etvDist_bind_left_le {α : Type u} {β : Type u}
    (p : PMF α) (f g : α → PMF β) :
    (p.bind f).etvDist (p.bind g) ≤ ∑' a, (f a).etvDist (g a) * p a := by
  have hrhs :
      (∑' a, (f a).etvDist (g a) * p a) =
        (∑' a, (∑' b, ENNReal.absDiff ((f a) b) ((g a) b)) * p a) / 2 := by
    calc
      ∑' a, (f a).etvDist (g a) * p a
          = ∑' a, ((∑' b, ENNReal.absDiff ((f a) b) ((g a) b)) / 2) * p a := by
              refine tsum_congr fun a => ?_
              rw [PMF.etvDist]
      _ = ∑' a, ((∑' b, ENNReal.absDiff ((f a) b) ((g a) b)) * p a) * (2 : ENNReal)⁻¹ := by
              refine tsum_congr fun a => ?_
              rw [div_eq_mul_inv]
              ac_rfl
      _ = (∑' a, (∑' b, ENNReal.absDiff ((f a) b) ((g a) b)) * p a) * (2 : ENNReal)⁻¹ := by
              rw [ENNReal.tsum_mul_right]
      _ = (∑' a, (∑' b, ENNReal.absDiff ((f a) b) ((g a) b)) * p a) / 2 := by
              rw [div_eq_mul_inv]
  rw [PMF.etvDist, hrhs]
  simpa [div_eq_mul_inv] using mul_le_mul_right' (a := (2 : ENNReal)⁻¹) (show
    ∑' y, ENNReal.absDiff (∑' x, p x * (f x) y) (∑' x, p x * (g x) y)
      ≤ ∑' x, (∑' y, ENNReal.absDiff ((f x) y) ((g x) y)) * p x from by
        calc
          ∑' y, ENNReal.absDiff (∑' x, p x * (f x) y) (∑' x, p x * (g x) y)
              ≤ ∑' y, ∑' x, ENNReal.absDiff (p x * (f x) y) (p x * (g x) y) :=
                ENNReal.tsum_le_tsum fun y => ENNReal.absDiff_tsum_le _ _
          _ ≤ ∑' y, ∑' x, ENNReal.absDiff ((f x) y) ((g x) y) * p x :=
                ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun x => by
                  simpa [mul_comm, mul_left_comm, mul_assoc] using
                    (ENNReal.absDiff_mul_right_le ((f x) y) ((g x) y) (p x))
          _ = ∑' x, ∑' y, ENNReal.absDiff ((f x) y) ((g x) y) * p x := ENNReal.tsum_comm
          _ = ∑' x, (∑' y, ENNReal.absDiff ((f x) y) ((g x) y)) * p x := by
                congr 1
                ext x
                rw [ENNReal.tsum_mul_right])

open ENNReal in
private lemma pmf_tvDist_bind_left_le
    {α : Type u} {β : Type u}
    (p : PMF α) (f g : α → PMF β) :
    PMF.tvDist (p.bind f) (p.bind g) ≤ ∑' a, (p a).toReal * PMF.tvDist (f a) (g a) := by
  simp only [PMF.tvDist]
  refine le_trans (ENNReal.toReal_mono ?_ (pmf_etvDist_bind_left_le p f g)) ?_
  · refine ne_top_of_le_ne_top one_ne_top ?_
    calc
      ∑' a, (f a).etvDist (g a) * p a ≤ ∑' a, 1 * p a :=
        ENNReal.tsum_le_tsum fun a => by
          exact mul_le_mul' (PMF.etvDist_le_one _ _) le_rfl
      _ = 1 * ∑' a, p a := by rw [ENNReal.tsum_mul_left]
      _ = 1 := by simp [p.tsum_coe]
  · refine le_of_eq ?_
    calc
      ((∑' a, (f a).etvDist (g a) * p a)).toReal
          = ∑' a, ((f a).etvDist (g a) * p a).toReal := by
              rw [ENNReal.tsum_toReal_eq]
              intro a
              exact ENNReal.mul_ne_top (PMF.etvDist_ne_top _ _) (PMF.apply_ne_top _ _)
      _ = ∑' a, (p a).toReal * PMF.tvDist (f a) (g a) := by
              refine tsum_congr fun a => ?_
              rw [ENNReal.toReal_mul, PMF.tvDist]
              ac_rfl

open ENNReal in
private lemma spmf_tvDist_bind_left_le_liftM
    {α : Type u} {β : Type u}
    (p : PMF α) (f g : α → PMF β) :
    SPMF.tvDist
        ((liftM p : SPMF α) >>= fun a => liftM (f a))
        ((liftM p : SPMF α) >>= fun a => liftM (g a)) ≤
      ∑' a, (p a).toReal * SPMF.tvDist (liftM (f a)) (liftM (g a)) := by
  simpa [SPMF.tvDist, SPMF.toPMF_bind, SPMF.toPMF_liftM, Option.elimM, PMF.monad_bind_eq_bind]
    using pmf_tvDist_bind_left_le p (fun a => PMF.map Option.some (f a))
      (fun a => PMF.map Option.some (g a))

open ENNReal in
lemma tvDist_bind_left_le
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [HasEvalPMF m]
    {α : Type u} {β : Type u}
    (mx : m α) (f g : α → m β) :
    tvDist (mx >>= f) (mx >>= g) ≤ ∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a) := by
  rw [tvDist, evalDist_bind, evalDist_bind]
  simp_rw [HasEvalPMF.evalDist_of_hasEvalPMF_def]
  calc
    SPMF.tvDist
        ((liftM (HasEvalPMF.toPMF mx) : SPMF α) >>= fun a => liftM (HasEvalPMF.toPMF (f a)))
        ((liftM (HasEvalPMF.toPMF mx) : SPMF α) >>= fun a => liftM (HasEvalPMF.toPMF (g a)))
      ≤ ∑' a, (HasEvalPMF.toPMF mx a).toReal *
          SPMF.tvDist (liftM (HasEvalPMF.toPMF (f a))) (liftM (HasEvalPMF.toPMF (g a))) := by
            exact spmf_tvDist_bind_left_le_liftM (HasEvalPMF.toPMF mx)
              (fun a => HasEvalPMF.toPMF (f a))
              (fun a => HasEvalPMF.toPMF (g a))
    _ = ∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a) := by
          refine tsum_congr fun a => ?_
          simp [probOutput_def, tvDist, HasEvalPMF.evalDist_of_hasEvalPMF_def]

namespace OracleComp.ProgramLogic.Relational

variable {α : Type _}

private lemma probOutput_simulateQ_run_eq_zero_of_bad
    {σ : Type} {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (h_mono : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (h_bad : bad s₀)
    (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl oa).run s₀] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    rw [simulateQ_pure]
    show Pr[= (x, s) | (pure a : StateT σ (OracleComp spec) α).run s₀] = 0
    simp [Prod.ext_iff]
    rintro rfl rfl
    exact hs h_bad
  | query_bind t oa ih =>
    simp [StateT.run_bind]
    intro u s' h_mem
    rw [← probOutput_eq_zero_iff]
    exact ih u s' (h_mono t s₀ h_bad (u, s') h_mem)

theorem map_run_simulateQ_eq_of_query_map_eq'
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =
      (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      calc
        ((impl₁ t).run s >>= fun x =>
            Prod.map id proj <$> (simulateQ impl₁ (oa x.1)).run x.2)
            =
            ((impl₁ t).run s >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run (proj x.2)) := by
                  refine bind_congr fun x => ?_
                  simpa using ih x.1 x.2
        _ =
            ((Prod.map id proj <$> (impl₁ t).run s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  exact
                    (bind_map_left (m := OracleComp spec') (Prod.map id proj)
                      ((impl₁ t).run s)
                      (fun y => (simulateQ impl₂ (oa y.1)).run y.2)).symm
        _ =
            ((impl₂ t).run (proj s) >>= fun x =>
              (simulateQ impl₂ (oa x.1)).run x.2) := by
                  rw [hproj t s]

theorem run'_simulateQ_eq_of_query_map_eq'
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    (simulateQ impl₁ oa).run' s = (simulateQ impl₂ oa).run' (proj s) := by
  have hrun := map_run_simulateQ_eq_of_query_map_eq' impl₁ impl₂ proj hproj oa s
  have hmap := congrArg (fun p => Prod.fst <$> p) hrun
  simpa [StateT.run'] using hmap

private lemma probOutput_simulateQ_run_eq_of_not_bad_dist
    {σ : Type} {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl₁ oa).run s₀] =
      Pr[= (x, s) | (simulateQ impl₂ oa).run s₀] := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ (pure a) s₀ h_bad x s hs,
        probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ (pure a) s₀ h_bad x s hs]
    · rfl
  | query_bind t oa ih =>
    by_cases h_bad : bad s₀
    · rw [probOutput_simulateQ_run_eq_zero_of_bad impl₁ bad h_mono₁ _ s₀ h_bad x s hs,
        probOutput_simulateQ_run_eq_zero_of_bad impl₂ bad h_mono₂ _ s₀ h_bad x s hs]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      have step1 : ∀ (p : spec.Range t × σ),
          Pr[= p | (impl₁ t).run s₀] *
            Pr[= (x, s) | (simulateQ impl₁ (oa p.1)).run p.2] =
          Pr[= p | (impl₁ t).run s₀] *
            Pr[= (x, s) | (simulateQ impl₂ (oa p.1)).run p.2] := by
        intro ⟨u, s'⟩; congr 1; exact ih u s'
      rw [show (∑' p, Pr[= p | (impl₁ t).run s₀] *
          Pr[= (x, s) | (simulateQ impl₁ (oa p.1)).run p.2]) =
          (∑' p, Pr[= p | (impl₁ t).run s₀] *
          Pr[= (x, s) | (simulateQ impl₂ (oa p.1)).run p.2]) from
        tsum_congr step1]
      exact tsum_congr (fun p => by rw [h_agree_dist t s₀ h_bad p])

private lemma probOutput_simulateQ_run_eq_zero_of_bad_unused
    {σ : Type} {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (h_mono : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) (h_bad : bad s₀)
    (x : α) (s : σ) (hs : ¬bad s) :
    Pr[= (x, s) | (simulateQ impl₁ oa).run s₀] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure a =>
    rw [simulateQ_pure]
    show Pr[= (x, s) | (pure a : StateT σ (OracleComp spec) α).run s₀] = 0
    simp [Prod.ext_iff]
    rintro rfl rfl
    exact hs h_bad
  | query_bind t oa ih =>
    simp [StateT.run_bind]
    intro u s' h_mem
    rw [← probOutput_eq_zero_iff]
    exact ih u s' (h_mono t s₀ h_bad (u, s') h_mem)

private lemma probEvent_not_bad_eq_dist
    {σ : Type} {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[fun x => ¬bad x.2 | (simulateQ impl₁ oa).run s₀] =
    Pr[fun x => ¬bad x.2 | (simulateQ impl₂ oa).run s₀] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr (fun ⟨a, s⟩ => ?_)
  split_ifs with h
  · rfl
  · exact probOutput_simulateQ_run_eq_of_not_bad_dist impl₁ impl₂ bad h_agree_dist h_mono₁ h_mono₂
      oa s₀ a s h

private lemma probEvent_bad_eq_dist
    {σ : Type} {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2)
    (oa : OracleComp spec α) (s₀ : σ) :
    Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀] =
    Pr[bad ∘ Prod.snd | (simulateQ impl₂ oa).run s₀] := by
  have h1 := probEvent_compl ((simulateQ impl₁ oa).run s₀) (bad ∘ Prod.snd)
  have h2 := probEvent_compl ((simulateQ impl₂ oa).run s₀) (bad ∘ Prod.snd)
  simp only [NeverFail.probFailure_eq_zero, tsub_zero] at h1 h2
  have h_not_bad := probEvent_not_bad_eq_dist impl₁ impl₂ bad h_agree_dist h_mono₁ h_mono₂ oa s₀
  have h_not_bad' : Pr[fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₁ oa).run s₀] =
      Pr[fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₂ oa).run s₀] :=
    h_not_bad
  have hne : Pr[fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₁ oa).run s₀] ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) probEvent_le_one
  calc Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀]
      = 1 - Pr[fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₁ oa).run s₀] := by
        rw [← h1]; exact (ENNReal.add_sub_cancel_right hne).symm
    _ = 1 - Pr[fun x => ¬(bad ∘ Prod.snd) x | (simulateQ impl₂ oa).run s₀] := by
        rw [h_not_bad']
    _ = Pr[bad ∘ Prod.snd | (simulateQ impl₂ oa).run s₀] := by
        rw [← h2]; exact ENNReal.add_sub_cancel_right
          (ne_top_of_le_ne_top (by simp) probEvent_le_one)

theorem tvDist_simulateQ_le_probEvent_bad_dist
    {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited] {σ : Type}
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (oa : OracleComp spec α) (s₀ : σ)
    (h_init : ¬bad s₀)
    (h_agree_dist : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      ∀ p, Pr[= p | (impl₁ t).run s] = Pr[= p | (impl₂ t).run s])
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2) :
    tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal := by
  classical
  let sim₁ := (simulateQ impl₁ oa).run s₀
  let sim₂ := (simulateQ impl₂ oa).run s₀
  have h_eq : ∀ (x : α) (s : σ), ¬bad s →
      Pr[= (x, s) | sim₁] = Pr[= (x, s) | sim₂] :=
    fun x s hs => probOutput_simulateQ_run_eq_of_not_bad_dist impl₁ impl₂ bad h_agree_dist
      h_mono₁ h_mono₂ oa s₀ x s hs
  have h_bad_eq : Pr[bad ∘ Prod.snd | sim₁] = Pr[bad ∘ Prod.snd | sim₂] :=
    probEvent_bad_eq_dist impl₁ impl₂ bad h_agree_dist h_mono₁ h_mono₂ oa s₀
  have h_tv_joint : tvDist sim₁ sim₂ ≤ Pr[bad ∘ Prod.snd | sim₁].toReal :=
    tvDist_le_probEvent_of_probOutput_eq_of_not (mx := sim₁) (my := sim₂) (bad ∘ Prod.snd)
      (fun xs hxs => by
        rcases xs with ⟨x, s⟩
        simpa using h_eq x s hxs)
      h_bad_eq
  have h_map :
      tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤ tvDist sim₁ sim₂ := by
    simpa [sim₁, sim₂, StateT.run'] using
      (tvDist_map_le (m := OracleComp spec) (α := α × σ) (β := α) Prod.fst sim₁ sim₂)
  exact le_trans h_map h_tv_joint

end OracleComp.ProgramLogic.Relational
