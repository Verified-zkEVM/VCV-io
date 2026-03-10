/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.Control.Monad.Algebra
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Quantitative Hoare triples for `OracleComp`

The construction is based on a Loom-style ordered monad algebra (`MAlgOrdered`) instantiated
for `OracleComp spec` with carrier `ℝ≥0∞`.
-/

open ENNReal

universe u

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β σ : Type}

/-! ## API contract

- This unary quantitative interface is instantiated for `OracleComp spec`.
- Probability/evaluation assumptions are `[spec.Fintype]` and `[spec.Inhabited]`.
- The quantitative codomain is fixed to `ℝ≥0∞`.
-/

/-- Expectation-style algebra for oracle computations returning `ℝ≥0∞`. -/
noncomputable def μ (oa : OracleComp spec ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, Pr[= x | oa] * x

private lemma μ_bind_eq_tsum {α : Type}
    (oa : OracleComp spec α) (ob : α → OracleComp spec ℝ≥0∞) :
    μ (oa >>= ob) = ∑' x, Pr[= x | oa] * μ (ob x) := by
  unfold μ
  calc
    (∑' y, Pr[= y | oa >>= ob] * y)
        = (∑' y, (∑' x, Pr[= x | oa] * Pr[= y | ob x]) * y) := by
            refine tsum_congr ?_
            intro y
            rw [probOutput_bind_eq_tsum]
    _ = (∑' y, ∑' x, (Pr[= x | oa] * Pr[= y | ob x]) * y) := by
          refine tsum_congr ?_
          intro y
          rw [ENNReal.tsum_mul_right]
    _ = ∑' x, ∑' y, (Pr[= x | oa] * Pr[= y | ob x]) * y := by
          rw [ENNReal.tsum_comm]
    _ = ∑' x, Pr[= x | oa] * ∑' y, Pr[= y | ob x] * y := by
          refine tsum_congr ?_
          intro x
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr ?_
          intro y
          rw [mul_assoc]
    _ = ∑' x, Pr[= x | oa] * μ (ob x) := by
          rfl

noncomputable instance instMAlgOrdered :
    MAlgOrdered (OracleComp spec) ℝ≥0∞ where
  μ := μ (spec := spec)
  μ_pure x := by
    classical
    simp [μ, probOutput_pure]
  μ_bind_mono f g hfg x := by
    rw [μ_bind_eq_tsum (oa := x) (ob := f), μ_bind_eq_tsum (oa := x) (ob := g)]
    refine ENNReal.tsum_le_tsum ?_
    intro a
    simpa [mul_comm] using (mul_le_mul_right (hfg a) (Pr[= a | x]))

/-- Quantitative weakest precondition for `OracleComp`. -/
noncomputable abbrev wp (oa : OracleComp spec α) (post : α → ℝ≥0∞) : ℝ≥0∞ :=
  MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa post

/-- Quantitative Hoare-style triple for `OracleComp`. -/
noncomputable abbrev Triple (pre : ℝ≥0∞) (oa : OracleComp spec α) (post : α → ℝ≥0∞) : Prop :=
  MAlgOrdered.Triple (m := OracleComp spec) (l := ℝ≥0∞) pre oa post

@[simp, game_rule] theorem wp_pure (x : α) (post : α → ℝ≥0∞) :
    wp (spec := spec) (pure x) post = post x := by
  simp [wp, MAlgOrdered.wp_pure]

@[simp, game_rule] theorem wp_ite (c : Prop) [Decidable c]
    (oa ob : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (spec := spec) (if c then oa else ob) post =
      if c then wp oa post else wp ob post := by
  split_ifs <;> rfl

@[simp, game_rule] theorem wp_dite (c : Prop) [Decidable c]
    (oa : c → OracleComp spec α) (ob : ¬c → OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (spec := spec) (dite c oa ob) post =
      dite c (fun h => wp (oa h) post) (fun h => wp (ob h) post) := by
  split_ifs <;> rfl

@[game_rule] theorem wp_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (post : β → ℝ≥0∞) :
    wp (spec := spec) (oa >>= ob) post =
      wp oa (fun x => wp (ob x) post) := by
  simpa [wp] using
    (MAlgOrdered.wp_bind (m := OracleComp spec) (l := ℝ≥0∞) oa ob post)

@[game_rule] theorem wp_replicate_zero (oa : OracleComp spec α) (post : List α → ℝ≥0∞) :
    wp (spec := spec) (oa.replicate 0) post = post [] := by
  simp [OracleComp.replicate_zero]

@[game_rule] theorem wp_replicate_succ
    (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp (spec := spec) (oa.replicate (n + 1)) post =
      wp oa (fun x => wp (oa.replicate n) (fun xs => post (x :: xs))) := by
  rw [OracleComp.replicate_succ_bind, wp_bind]
  congr 1
  funext x
  rw [wp_bind]
  simp

@[game_rule] theorem wp_list_mapM_nil
    (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp (spec := spec) (([] : List α).mapM f) post = post [] := by
  simp

@[game_rule] theorem wp_list_mapM_cons
    (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp (spec := spec) ((x :: xs).mapM f) post =
      wp (f x) (fun y => wp (xs.mapM f) (fun ys => post (y :: ys))) := by
  rw [List.mapM_cons, wp_bind]
  congr 1
  funext y
  rw [wp_bind]
  simp

@[game_rule] theorem wp_list_foldlM_nil
    (f : σ → α → OracleComp spec σ) (init : σ) (post : σ → ℝ≥0∞) :
    wp (spec := spec) (([] : List α).foldlM f init) post = post init := by
  simp

@[game_rule] theorem wp_list_foldlM_cons
    (x : α) (xs : List α) (f : σ → α → OracleComp spec σ)
    (init : σ) (post : σ → ℝ≥0∞) :
    wp (spec := spec) ((x :: xs).foldlM f init) post =
      wp (f init x) (fun s => wp (xs.foldlM f s) post) := by
  rw [List.foldlM_cons, wp_bind]

theorem wp_mono (oa : OracleComp spec α) {post post' : α → ℝ≥0∞}
    (hpost : ∀ x, post x ≤ post' x) :
    wp (spec := spec) oa post ≤ wp oa post' := by
  simpa [wp] using
    (MAlgOrdered.wp_mono (m := OracleComp spec) (l := ℝ≥0∞) oa hpost)

@[game_rule] theorem wp_map
    (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp (f <$> oa) post = wp oa (post ∘ f) := by
  show wp (oa >>= fun a => pure (f a)) post = wp oa (post ∘ f)
  rw [wp_bind]
  congr 1
  funext a
  simp [Function.comp]

/-- General unfolding: `wp` as weighted sum over output probabilities. -/
theorem wp_eq_tsum (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp oa post = ∑' x, Pr[= x | oa] * post x := by
  show μ (oa >>= fun a => pure (post a)) = _
  rw [μ_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  have : μ (pure (post x) : OracleComp spec ℝ≥0∞) = post x := by
    classical
    simp [μ, probOutput_pure]
  rw [this]

@[simp] theorem wp_const (oa : OracleComp spec α) (c : ℝ≥0∞) :
    wp oa (fun _ => c) = c := by
  rw [wp_eq_tsum, ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

@[game_rule] theorem wp_add (oa : OracleComp spec α) (f g : α → ℝ≥0∞) :
    wp oa (fun x => f x + g x) = wp oa f + wp oa g := by
  simp only [wp_eq_tsum, mul_add, ENNReal.tsum_add]

@[game_rule] theorem wp_mul_const (oa : OracleComp spec α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    wp oa (fun x => c * f x) = c * wp oa f := by
  simp only [wp_eq_tsum]; simp_rw [mul_left_comm]; exact ENNReal.tsum_mul_left

theorem wp_const_mul (oa : OracleComp spec α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    wp oa (fun x => f x * c) = wp oa f * c := by
  simp_rw [mul_comm _ c]; rw [wp_mul_const, mul_comm]

theorem triple_conseq {pre pre' : ℝ≥0∞} {oa : OracleComp spec α}
    {post post' : α → ℝ≥0∞}
    (hpre : pre' ≤ pre) (hpost : ∀ x, post x ≤ post' x) :
    Triple (spec := spec) pre oa post → Triple pre' oa post' := by
  simpa [Triple, wp] using
    (MAlgOrdered.triple_conseq (m := OracleComp spec) (l := ℝ≥0∞) hpre hpost)

theorem triple_bind {pre : ℝ≥0∞} {oa : OracleComp spec α}
    {cut : α → ℝ≥0∞} {ob : α → OracleComp spec β} {post : β → ℝ≥0∞}
    (hoa : Triple (spec := spec) pre oa cut)
    (hob : ∀ x, Triple (cut x) (ob x) post) :
    Triple pre (oa >>= ob) post := by
  simpa [Triple, wp] using
    (MAlgOrdered.triple_bind (m := OracleComp spec) (l := ℝ≥0∞) hoa hob)

theorem triple_bind_wp {pre : ℝ≥0∞} {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {post : β → ℝ≥0∞}
    (h : Triple (spec := spec) pre oa (fun x => wp (ob x) post)) :
    Triple pre (oa >>= ob) post := by
  show pre ≤ wp (oa >>= ob) post
  rw [wp_bind]; exact h

theorem triple_pure (x : α) (post : α → ℝ≥0∞) :
    Triple (spec := spec) (post x) (pure x) post := by
  simp [Triple, MAlgOrdered.Triple]

/-- A quantitative triple with precondition `0` is always true. -/
theorem triple_zero (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Triple (spec := spec) 0 oa post := by
  simp [Triple, MAlgOrdered.Triple]

theorem triple_ite {c : Prop} [Decidable c] {pre : ℝ≥0∞}
    {oa ob : OracleComp spec α} {post : α → ℝ≥0∞}
    (ht : c → Triple (spec := spec) pre oa post)
    (hf : ¬c → Triple pre ob post) :
    Triple pre (if c then oa else ob) post := by
  split_ifs with h
  · exact ht h
  · exact hf h

theorem triple_dite {c : Prop} [Decidable c] {pre : ℝ≥0∞}
    {oa : c → OracleComp spec α} {ob : ¬c → OracleComp spec α} {post : α → ℝ≥0∞}
    (ht : ∀ h : c, Triple (spec := spec) pre (oa h) post)
    (hf : ∀ h : ¬c, Triple pre (ob h) post) :
    Triple pre (dite c oa ob) post := by
  split_ifs with h
  · exact ht h
  · exact hf h

/-- `probEvent` as a WP of an indicator postcondition. -/
lemma probEvent_eq_wp_indicator (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] :
    Pr[p | oa] = wp oa (fun x => if p x then 1 else 0) := by
  rw [probEvent_eq_tsum_ite, wp, MAlgOrdered.wp]
  change (∑' x : α, if p x then Pr[= x | oa] else 0) =
    μ ((oa >>= fun a => pure (if p a then 1 else 0)) : OracleComp spec ℝ≥0∞)
  rw [μ_bind_eq_tsum]
  refine tsum_congr ?_
  intro x
  have hμ :
      μ (pure (if p x then 1 else 0) : OracleComp spec ℝ≥0∞) = (if p x then 1 else 0) := by
    simpa using
      (MAlgOrdered.μ_pure (m := OracleComp spec) (l := ℝ≥0∞) (x := if p x then 1 else 0))
  rw [hμ]
  split_ifs <;> simp

/-- `probOutput` as a WP of a singleton-indicator postcondition. -/
lemma probOutput_eq_wp_indicator (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Pr[= x | oa] = wp oa (fun y => if y = x then 1 else 0) := by
  simpa [probEvent_eq_eq_probOutput] using
    (probEvent_eq_wp_indicator (oa := oa) (p := fun y => y = x))

/-- `liftM` query form of `wp_query`. -/
theorem wp_liftM_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp (spec := spec) (liftM (query t) : OracleComp spec (spec.Range t)) post =
      ∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u := by
  rw [wp, MAlgOrdered.wp]
  calc
    μ (do let a ← liftM (query t); pure (post a))
        = ∑' u : spec.Range t,
            Pr[= u | (liftM (query t) : OracleComp spec (spec.Range t))] *
              μ (pure (post u) : OracleComp spec ℝ≥0∞) := by
            simpa using
              (μ_bind_eq_tsum
                (oa := (liftM (query t) : OracleComp spec (spec.Range t)))
                (ob := fun a => pure (post a)))
    _ = ∑' u : spec.Range t,
          (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u := by
            refine tsum_congr ?_
            intro u
            have hμ :
                μ (pure (post u) : OracleComp spec ℝ≥0∞) = post u := by
              let _ : DecidableEq ℝ≥0∞ := Classical.decEq ℝ≥0∞
              simp [μ, probOutput_pure]
            have hprob :
                Pr[= u | (liftM (query t) : OracleComp spec (spec.Range t))] =
                  (1 / Fintype.card (spec.Range t) : ℝ≥0∞) := by
              exact (probOutput_query_eq_div (spec := spec) t u)
            rw [hμ]
            simp [hprob]

/-- Quantitative WP rule for a uniform oracle query. -/
@[game_rule] theorem wp_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp (spec := spec) (query t : OracleComp spec (spec.Range t)) post =
      ∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u := by
  simpa using wp_liftM_query (spec := spec) t post

section Sampling

variable [SampleableType α]

@[game_rule] theorem wp_uniformSample (post : α → ℝ≥0∞) :
    wp ($ᵗ α) post = ∑' x, Pr[= x | ($ᵗ α : ProbComp α)] * post x := by
  rw [wp, MAlgOrdered.wp]
  calc
    μ (do let a ← $ᵗ α; pure (post a))
        = ∑' x, Pr[= x | ($ᵗ α : ProbComp α)] * μ (pure (post x) : ProbComp ℝ≥0∞) := by
          simpa using
            (μ_bind_eq_tsum (oa := ($ᵗ α : ProbComp α)) (ob := fun a => pure (post a)))
    _ = ∑' x, Pr[= x | ($ᵗ α : ProbComp α)] * post x := by
          refine tsum_congr ?_
          intro x
          have hμ : μ (pure (post x) : ProbComp ℝ≥0∞) = post x := by
            let _ : DecidableEq ℝ≥0∞ := Classical.decEq ℝ≥0∞
            simp [μ, probOutput_pure]
          rw [hμ]

end Sampling

/-- Indicator-event probability as an exact quantitative triple. -/
theorem triple_probEvent_indicator (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Triple (spec := spec) (Pr[p | oa]) oa (fun x => if p x then 1 else 0) := by
  unfold Triple MAlgOrdered.Triple
  simp [probEvent_eq_wp_indicator]

/-- Singleton-output probability as an exact quantitative triple. -/
theorem triple_probOutput_indicator (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Triple (spec := spec) (Pr[= x | oa]) oa (fun y => if y = x then 1 else 0) := by
  unfold Triple MAlgOrdered.Triple
  simp [probOutput_eq_wp_indicator]

/-- The support event of an `OracleComp` occurs almost surely. -/
@[simp] theorem probEvent_mem_support (oa : OracleComp spec α) :
    Pr[fun x => x ∈ support oa | oa] = 1 := by
  rw [probEvent_eq_one_iff]
  constructor
  · simp
  · intro x hx
    exact hx

/-- Exact probability-1 events are exact quantitative triples. -/
theorem triple_probEvent_eq_one (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] (h : Pr[p | oa] = 1) :
    Triple (spec := spec) 1 oa (fun x => if p x then 1 else 0) := by
  simpa [h] using triple_probEvent_indicator (oa := oa) p

/-- Exact probability-1 singleton outputs are exact quantitative triples. -/
theorem triple_probOutput_eq_one (oa : OracleComp spec α) [DecidableEq α]
    (x : α) (h : Pr[= x | oa] = 1) :
    Triple (spec := spec) 1 oa (fun y => if y = x then 1 else 0) := by
  simpa [h] using triple_probOutput_indicator (oa := oa) x

/-- Support membership is a useful default cut function for support-sensitive bind proofs. -/
theorem triple_support (oa : OracleComp spec α) [DecidablePred fun x => x ∈ support oa] :
    Triple (spec := spec) 1 oa (fun x => if x ∈ support oa then 1 else 0) := by
  simpa using
    triple_probEvent_eq_one (oa := oa) (p := fun x => x ∈ support oa)
      (h := probEvent_mem_support (oa := oa))

/-! ## Congruence under evalDist equality -/

lemma probOutput_congr_evalDist {oa ob : OracleComp spec α}
    (h : evalDist oa = evalDist ob) (x : α) :
    Pr[= x | oa] = Pr[= x | ob] := by
  show evalDist oa x = evalDist ob x
  rw [h]

lemma μ_congr_evalDist {oa ob : OracleComp spec ℝ≥0∞}
    (h : evalDist oa = evalDist ob) :
    μ oa = μ ob := by
  unfold μ
  exact tsum_congr fun x => by rw [probOutput_congr_evalDist h]

lemma wp_congr_evalDist {oa ob : OracleComp spec α}
    (h : evalDist oa = evalDist ob) (post : α → ℝ≥0∞) :
    wp oa post = wp ob post := by
  show μ (oa >>= fun a => pure (post a)) = μ (ob >>= fun a => pure (post a))
  exact μ_congr_evalDist (by simp [h])

lemma μ_cross_congr_evalDist {ι' : Type*} {spec' : OracleSpec ι'}
    [spec'.Fintype] [spec'.Inhabited]
    {oa : OracleComp spec' ℝ≥0∞} {ob : OracleComp spec ℝ≥0∞}
    (h : evalDist oa = evalDist ob) :
    @μ _ spec' _ _ oa = μ ob := by
  simp only [μ]
  exact tsum_congr fun x => by
    show evalDist oa x * x = evalDist ob x * x
    rw [h]

end OracleComp.ProgramLogic
