/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Instances

/-!
# Evaluation Distributions of Computations with `Bind`

File for lemmas about `evalDist` and `support` involving the monadic `pure` and `bind`.
-/

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

open ENNReal

section pure

@[simp, grind =] lemma support_pure [HasEvalSet m] (x : α) :
    support (pure x : m α) = {x} := by aesop (rule_sets := [UnfoldEvalDist])

lemma mem_support_pure_iff [HasEvalSet m] (x y : α) :
    x ∈ support (pure y : m α) ↔ x = y := by grind
lemma mem_support_pure_iff' [HasEvalSet m] (x y : α) :
    x ∈ support (pure y : m α) ↔ y = x := by aesop

@[simp, grind =] lemma finSupport_pure [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    (x : α) : finSupport (pure x : m α) = {x} := by aesop

lemma mem_finSupport_pure_iff [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    (x y : α) : x ∈ finSupport (pure y : m α) ↔ x = y := by grind
lemma mem_finSupport_pure_iff' [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    (x y : α) : x ∈ finSupport (pure y : m α) ↔ y = x := by aesop

@[simp] lemma evalDist_pure [HasEvalSPMF m] {α : Type u} (x : α) :
    evalDist (pure x : m α) = pure x := by simp [evalDist]

@[simp] lemma evalDist_comp_pure [HasEvalSPMF m] :
    evalDist ∘ (pure : α → m α) = pure := by aesop

@[simp] lemma evalDist_comp_pure' [HasEvalSPMF m] (f : α → β) :
    evalDist ∘ (pure : β → m β) ∘ f = pure ∘ f := by aesop

@[simp, grind =] lemma probOutput_pure [HasEvalSPMF m] [DecidableEq α] (x y : α) :
    Pr[= x | (pure y : m α)] = if x = y then 1 else 0 := by aesop (rule_sets := [UnfoldEvalDist])

@[simp, grind =] lemma probOutput_pure_self [HasEvalSPMF m] (x : α) :
    Pr[= x | (pure x : m α)] = 1 := by aesop (rule_sets := [UnfoldEvalDist])

@[simp, grind =] lemma probFailure_pure [HasEvalSPMF m] (x : α) :
    Pr[⊥ | (pure x : m α)] = 0 := by aesop (rule_sets := [UnfoldEvalDist])

/-- Fallback when we don't have decidable equality. -/
lemma probOutput_pure_eq_indicator [HasEvalSPMF m] (x y : α) :
    Pr[= x | (pure y : m α)] = Set.indicator {y} (Function.const α 1) x := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp] lemma probEvent_pure [HasEvalSPMF m] (x : α) (p : α → Prop) [DecidablePred p] :
    Pr[p | (pure x : m α)] = if p x then 1 else 0 := by
  aesop (rule_sets := [UnfoldEvalDist])

/-- Fallback when we don't have decidable equality. -/
lemma probEvent_pure_eq_indicator [HasEvalSPMF m] (x : α) (p : α → Prop) :
    Pr[p | (pure x : m α)] = Set.indicator {x | p x} (Function.const α 1) x := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp]
lemma tsum_probOutput_pure [HasEvalSPMF m] (x : α) :
    ∑' y : α, Pr[= y | (pure x : m α)] = 1 := by
  have : DecidableEq α := Classical.decEq α; simp

@[simp]
lemma tsum_probOutput_pure' [HasEvalSPMF m] (x : α) :
    ∑' y : α, Pr[= x | (pure y : m α)] = 1 := by
  have : DecidableEq α := Classical.decEq α; simp

@[simp]
lemma sum_probOutput_pure [Fintype α] [HasEvalSPMF m] (x : α) :
    ∑ y : α, Pr[= y | (pure x : m α)] = 1 := by
  have : DecidableEq α := Classical.decEq α; simp

@[simp]
lemma sum_probOutput_pure' [Fintype α] [HasEvalSPMF m] (x : α) :
    ∑ y : α, Pr[= x | (pure y : m α)] = 1 := by
  have : DecidableEq α := Classical.decEq α; simp

end pure

section bind

@[simp, grind =] lemma support_bind [HasEvalSet m] (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) := by
  aesop (rule_sets := [UnfoldEvalDist])

@[grind =]
lemma mem_support_bind_iff [HasEvalSet m] (mx : m α) (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp

-- dt: do we need global assumptions about `decidable_eq` for the `finSupport` definition?
@[simp, grind =] lemma finSupport_bind [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    [DecidableEq β] (mx : m α) (my : α → m β) : finSupport (mx >>= my) =
      Finset.biUnion (finSupport mx) fun x => finSupport (my x) := by aesop

@[grind =]
lemma mem_finSupport_bind_iff [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    [DecidableEq β] (mx : m α) (my : α → m β) (y : β) : y ∈ finSupport (mx >>= my) ↔
      ∃ x ∈ finSupport mx, y ∈ finSupport (my x) := by aesop

@[simp, grind =] lemma evalDist_bind [HasEvalSPMF m] (mx : m α) (my : α → m β) :
    evalDist (mx >>= my) = evalDist mx >>= fun x => evalDist (my x) :=
  MonadHom.toFun_bind' _ mx my

@[grind =]
lemma probOutput_bind_eq_tsum [HasEvalSPMF m] (mx : m α) (my : α → m β) (y : β) :
    Pr[= y | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[= y | my x] := by
  simp [probOutput_def]

@[grind =]
lemma probEvent_bind_eq_tsum [HasEvalSPMF m] (mx : m α) (my : α → m β) (q : β → Prop) :
    Pr[q | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[q | my x] := by
  simp [probEvent_eq_tsum_indicator, probOutput_bind_eq_tsum,
    Set.indicator, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => by split_ifs <;> simp

lemma probFailure_bind_eq_tsum [HasEvalSPMF m] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑' x : α, Pr[= x | mx] * Pr[⊥ | my x] := by
  rw [probFailure_eq_sub_tsum]
  conv =>
    left
    right
    congr
    ext
    rw [probOutput_bind_eq_tsum]

  simp only [probFailure_eq_sub_tsum]

  sorry

@[simp]
lemma probFailure_bind_eq_zero_iff [HasEvalSPMF m] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = 0 ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, Pr[⊥ | my x] = 0 := by
  simp [probFailure_bind_eq_tsum]
  grind

/-- Version of `probOutput_bind_eq_tsum` that sums only over the subtype given by the support
of the first computation. This can be useful to avoid looking at edge cases that can't actually
happen in practice after the first computation. A common example is if the first computation
does some error handling to avoids returning malformed outputs. -/
lemma probOutput_bind_eq_tsum_subtype [HasEvalSPMF m] (mx : m α) (my : α → m β) (y : β) :
    Pr[= y | mx >>= my] = ∑' x : support mx, Pr[= x | mx] * Pr[= y | my x] := by
  rw [tsum_subtype _ (fun x ↦ Pr[= x | mx] * Pr[= y | my x]), probOutput_bind_eq_tsum]
  refine tsum_congr (fun x ↦ ?_)
  by_cases hx : x ∈ support mx <;> aesop

lemma probEvent_bind_eq_tsum_subtype [HasEvalSPMF m] (mx : m α) (my : α → m β) (q : β → Prop) :
    Pr[q | mx >>= my] = ∑' x : support mx, Pr[= x | mx] * Pr[q | my x] := by
  rw [tsum_subtype _ (fun x ↦ Pr[= x | mx] * Pr[q | my x]), probEvent_bind_eq_tsum]
  refine tsum_congr (fun x ↦ ?_)
  by_cases hx : x ∈ support mx <;> aesop

lemma probOutput_bind_eq_sum_finSupport [HasEvalSPMF m] [HasEvalFinset m]
    (mx : m α) (my : α → m β) [DecidableEq α] (y : β) :
    Pr[= y | mx >>= my] = ∑ x ∈ finSupport mx, Pr[= x | mx] * Pr[= y | my x] :=
  (probOutput_bind_eq_tsum mx my y).trans (tsum_eq_sum' <| by sorry)

lemma probEvent_bind_eq_sum_finSupport [HasEvalSPMF m] [HasEvalFinset m]
    (mx : m α) (my : α → m β) [DecidableEq α] (q : β → Prop) :
    Pr[q | mx >>= my] = ∑ x ∈ finSupport mx, Pr[= x | mx] * Pr[q | my x] :=
  (probEvent_bind_eq_tsum mx my q).trans (tsum_eq_sum' <| by sorry)

lemma probOutput_bind_of_const [HasEvalSPMF m] (mx : m α) (my : α → m β)
    (y : β) (r : ℝ≥0∞) (h : ∀ x, Pr[= y | my x] = r) :
    Pr[= y | mx >>= my] = (1 - Pr[⊥ | mx]) * r := by
  simp [probOutput_bind_eq_tsum, h, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]

lemma probFailure_bind_of_const [Nonempty α] [HasEvalSPMF m]
    (mx : m α) (my : α → m β) (r : ℝ≥0∞) (h : ∀ x, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + r - Pr[⊥ | mx] * r := by
  have : r ≠ ⊤ := λ hr ↦ probFailure_ne_top ((h (Classical.arbitrary α)).trans hr)
  simp [probFailure_bind_eq_tsum, h, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]
  rw [ENNReal.sub_mul λ _ _ ↦ this, one_mul]
  refine symm (AddLECancellable.add_tsub_assoc_of_le ?_ ?_ _)
  · refine ENNReal.addLECancellable_iff_ne.2 (ENNReal.mul_ne_top probFailure_ne_top this)
  · by_cases hr : r = 0
    · simp only [hr, mul_zero, le_refl]
    refine mul_le_of_le_div (le_of_le_of_eq probFailure_le_one ?_)
    refine symm (ENNReal.div_self hr this)

lemma probFailure_bind_eq_sub_mul [HasEvalSPMF m]
    (mx : m α) (my : α → m β) (r : ℝ≥0∞) (h : ∀ x, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = 1 - (1 - Pr[⊥ | mx]) * (1 - r) := by
  rw [probFailure_bind_eq_tsum]
  rw [← tsum_probOutput_eq_sub]
  rw [← ENNReal.tsum_mul_right]

  sorry
  -- have hl : ∀ x, [=x|mx] * [⊥|my x] ≤ [=x|mx] :=
  --   λ x ↦ le_of_le_of_eq (mul_le_mul' le_rfl probFailure_le_one) (mul_one _)
  -- calc [⊥ | mx] + ∑' x, [= x | mx] * [⊥ | my x]
  --   _ = 1 - (∑' x, [= x | mx]) + (∑' x, [= x | mx] * [⊥ | my x]) := by
  --     rw [probFailure_eq_sub_tsum]
  --   _ = 1 - (∑' x, [= x | mx] - ∑' x, [= x | mx] * [⊥ | my x]) := by
  --     exact Eq.symm (AddLECancellable.tsub_tsub_assoc
  --       (by simp) tsum_probOutput_le_one (ENNReal.tsum_le_tsum hl))
  --   _ = 1 - ∑' x, ([= x | mx] - [= x | mx] * [⊥ | my x]) := by
  --     refine congr_arg (1 - ·) (ENNReal.eq_sub_of_add_eq ?_ ?_).symm
  --     · refine ne_top_of_le_ne_top one_ne_top ?_
  --       refine le_trans ?_ (@tsum_probOutput_le_one _ _ _ _ mx)
  --       refine ENNReal.tsum_le_tsum λ x ↦ ?_
  --       exact hl x
  --     rw [← ENNReal.tsum_add]
  --     refine tsum_congr λ x ↦ tsub_add_cancel_of_le (hl x)
  --   _ = 1 - ∑' x : α, [= x | mx] * (1 - r) := by
  --     refine congr_arg (1 - ·) (tsum_congr λ x ↦ ?_)
  --     rw [ENNReal.mul_sub (λ _ _ ↦ probOutput_ne_top), mul_one, ← h x]

lemma probFailure_bind_le_of_forall [HasEvalSPMF m] {mx : m α}
    {s : ℝ≥0∞} (h' : Pr[⊥ | mx] = s) (my : α → m β) {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, Pr[⊥ | my x] ≤ r) :
    Pr[⊥ | mx >>= my] ≤ s + (1 - s) * r := by
  sorry

/-- Version of `probFailure_bind_le_of_forall` with the `1 - s` factor ommited for convenience. -/
lemma probFailure_bind_le_of_forall' [HasEvalSPMF m] {mx : m α}
    {s : ℝ≥0∞} (h' : Pr[⊥ | mx] = s) (my : α → m β) {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, Pr[⊥ | my x] ≤ r) : Pr[⊥ | mx >>= my] ≤ s + r := by
  sorry

/-- Version of `probFailure_bind_le_of_forall` when `mx` never fails. -/
lemma probFailure_bind_le_of_le_of_probFailure_eq_zero [HasEvalSPMF m] {mx : m α}
    (h' : Pr[⊥ | mx] = 0) {my : α → m β} {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, Pr[⊥ | my x] ≤ r) : Pr[⊥ | mx >>= my] ≤ r := by
  sorry

lemma probFailure_bind_of_probFailure_eq_zero [HasEvalSPMF m] {mx : m α}
    (h' : Pr[⊥ | mx] = 0) {my : α → m β} :
    Pr[⊥ | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[⊥ | my x] := by
  sorry

end bind


-- section bind

-- variable (oa : OracleComp spec α) (ob : α → OracleComp spec β)

-- end bind

-- section mul_le_probEvent_bind

-- lemma mul_le_probEvent_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--     {p : α → Prop} {q : β → Prop} {r r' : ℝ≥0∞}
--     (h : r ≤ [p | oa]) (h' : ∀ x ∈ oa.support, p x → r' ≤ [q | ob x]) :
--     r * r' ≤ [q | oa >>= ob] := by
--   rw [probEvent_bind_eq_tsum]
--   refine (mul_le_mul_right' h r').trans ?_
--   rw [probEvent_eq_tsum_indicator, ← ENNReal.tsum_mul_right]
--   refine ENNReal.tsum_le_tsum fun x => ?_
--   rw [← Set.indicator_mul_const]
--   by_cases hx : x ∈ oa.support
--   · refine Set.indicator_apply_le' (fun h => ?_) (fun _ => zero_le')
--     exact (ENNReal.mul_le_mul_left (probOutput_ne_zero _ _ hx) probOutput_ne_top).mpr (h' x hx h)
--   · simp [probOutput_eq_zero _ _ hx]

-- end mul_le_probEvent_bind

-- section bind_const

-- variable (oa : OracleComp spec α) (ob : OracleComp spec β)

-- -- lemma probFailure_bind_const :
-- --   [⊥ | do oa; ob] = [⊥ | oa] + [⊥ | ob] - [⊥ | oa] * [⊥ | ob]


-- end bind_const

-- lemma probFailure_bind_congr (mx : OracleComp spec α)
--     {my : α → OracleComp spec β} {oc : α → OracleComp spec γ}
--     (h : ∀ x ∈ mx.support, [⊥ | my x] = [⊥ | oc x]) : [⊥ | mx >>= my] = [⊥ | mx >>= oc] := by
--   sorry

-- lemma probFailure_bind_congr' (mx : OracleComp spec α)
--     {my : α → OracleComp spec β} {oc : α → OracleComp spec γ}
--     (h : ∀ x, [⊥ | my x] = [⊥ | oc x]) : [⊥ | mx >>= my] = [⊥ | mx >>= oc] := by
--   sorry

-- lemma probOutput_bind_congr {mx : OracleComp spec α} {ob₁ ob₂ : α → OracleComp spec β} {y : β}
--     (h : ∀ x ∈ mx.support, [= y | ob₁ x] = [= y | ob₂ x]) :
--     [= y | mx >>= ob₁] = [= y | mx >>= ob₂] := by
--   sorry

-- lemma probOutput_bind_congr' (mx : OracleComp spec α) {ob₁ ob₂ : α → OracleComp spec β} (y : β)
--     (h : ∀ x, [= y | ob₁ x] = [= y | ob₂ x]) :
--     [= y | mx >>= ob₁] = [= y | mx >>= ob₂] := by
--   sorry

-- lemma probOutput_bind_mono {mx : OracleComp spec α}
--     {my : α → OracleComp spec β} {oc : α → OracleComp spec γ} {y : β} {z : γ}
--     (h : ∀ x ∈ mx.support, [= y | my x] ≤ [= z | oc x]) :
--     [= y | mx >>= my] ≤ [= z | mx >>= oc] := by
--   sorry

-- lemma probOutput_bind_congr_div_const {mx : OracleComp spec α}
--     {ob₁ ob₂ : α → OracleComp spec β} {y : β} {r : ℝ≥0∞}
--     (h : ∀ x ∈ mx.support, [= y | ob₁ x] = [= y | ob₂ x] / r) :
--     [= y | mx >>= ob₁] = [= y | mx >>= ob₂] / r := by
--   sorry

-- lemma probOutput_bind_congr_eq_add {γ₁ γ₂ : Type u}
--     {mx : OracleComp spec α} {my : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ mx.support, [= y | my x] = [= z₁ | oc₁ x] + [= z₂ | oc₂ x]) :
--     [= y | mx >>= my] = [= z₁ | mx >>= oc₁] + [= z₂ | mx >>= oc₂] := by
--   simp [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
--   refine tsum_congr fun x => ?_
--   by_cases hx : x ∈ mx.support
--   · simp [h x hx, left_distrib]
--   · simp [probOutput_eq_zero _ _ hx]

-- lemma probOutput_bind_congr_le_add {γ₁ γ₂ : Type u}
--     {mx : OracleComp spec α} {my : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ mx.support, [= y | my x] ≤ [= z₁ | oc₁ x] + [= z₂ | oc₂ x]) :
--     [= y | mx >>= my] ≤ [= z₁ | mx >>= oc₁] + [= z₂ | mx >>= oc₂] := by
--   sorry

-- lemma probOutput_bind_congr_add_le {γ₁ γ₂ : Type u}
--     {mx : OracleComp spec α} {my : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ mx.support, [= z₁ | oc₁ x] + [= z₂ | oc₂ x] ≤ [= y | my x]) :
--     [= z₁ | mx >>= oc₁] + [= z₂ | mx >>= oc₂] ≤ [= y | mx >>= my] := by
--   sorry

-- lemma probOutput_bind_congr_le_sub {γ₁ γ₂ : Type u}
--     {mx : OracleComp spec α} {my : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ mx.support, [= y | my x] ≤ [= z₁ | oc₁ x] - [= z₂ | oc₂ x]) :
--     [= y | mx >>= my] ≤ [= z₁ | mx >>= oc₁] - [= z₂ | mx >>= oc₂] := by
--   sorry

-- lemma probOutput_bind_congr_sub_le {γ₁ γ₂ : Type u}
--     {mx : OracleComp spec α} {my : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ mx.support, [= z₁ | oc₁ x] - [= z₂ | oc₂ x] ≤ [= y | my x]) :
--     [= z₁ | mx >>= oc₁] - [= z₂ | mx >>= oc₂] ≤ [= y | mx >>= my] := by
--   sorry
