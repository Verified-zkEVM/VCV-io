/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Basic

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

@[simp, grind =]
lemma evalDist_pure [HasEvalSPMF m] {α : Type u} (x : α) :
    evalDist (pure x : m α) = pure x := by simp [evalDist]

@[simp]
lemma evalDist_comp_pure [HasEvalSPMF m] :
    evalDist ∘ (pure : α → m α) = pure := by aesop

@[simp]
lemma evalDist_comp_pure' [HasEvalSPMF m] (f : α → β) :
    evalDist ∘ (pure : β → m β) ∘ f = pure ∘ f := by grind

@[simp, grind =]
lemma probOutput_pure [HasEvalSPMF m] [DecidableEq α] (x y : α) :
    Pr[= x | (pure y : m α)] = if x = y then 1 else 0 := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp, grind =]
lemma probOutput_pure_self [HasEvalSPMF m] (x : α) :
    Pr[= x | (pure x : m α)] = 1 := by
  aesop (rule_sets := [UnfoldEvalDist])

/-- Fallback when we don't have decidable equality. -/
@[grind =]
lemma probOutput_pure_eq_indicator [HasEvalSPMF m] (x y : α) :
    Pr[= x | (pure y : m α)] = Set.indicator {y} (Function.const α 1) x := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp, grind =]
lemma probEvent_pure [HasEvalSPMF m] (x : α) (p : α → Prop) [DecidablePred p] :
    Pr[p | (pure x : m α)] = if p x then 1 else 0 := by
  aesop (rule_sets := [UnfoldEvalDist])

/-- Fallback when we don't have decidable equality. -/
@[grind =]
lemma probEvent_pure_eq_indicator [HasEvalSPMF m] (x : α) (p : α → Prop) :
    Pr[p | (pure x : m α)] = Set.indicator {x | p x} (Function.const α 1) x := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp, grind =]
lemma probFailure_pure [HasEvalSPMF m] (x : α) :
    Pr[⊥ | (pure x : m α)] = 0 := by aesop (rule_sets := [UnfoldEvalDist])

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

@[simp, grind =]
lemma support_bind [HasEvalSet m] (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) := by
  aesop (rule_sets := [UnfoldEvalDist])

@[grind =]
lemma mem_support_bind_iff [HasEvalSet m] (mx : m α) (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp

-- dt: do we need global assumptions about `decidable_eq` for the `finSupport` definition?
@[simp, grind =]
lemma finSupport_bind [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    [DecidableEq β] (mx : m α) (my : α → m β) : finSupport (mx >>= my) =
      Finset.biUnion (finSupport mx) fun x => finSupport (my x) := by aesop

@[grind =]
lemma mem_finSupport_bind_iff [HasEvalSet m] [HasEvalFinset m] [DecidableEq α]
    [DecidableEq β] (mx : m α) (my : α → m β) (y : β) : y ∈ finSupport (mx >>= my) ↔
      ∃ x ∈ finSupport mx, y ∈ finSupport (my x) := by aesop

@[simp, grind =]
lemma evalDist_bind [HasEvalSPMF m] (mx : m α) (my : α → m β) :
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

@[grind =]
lemma probFailure_bind_eq_add_tsum [HasEvalSPMF m] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑' x : α, Pr[= x | mx] * Pr[⊥ | my x] := by
  simp [probFailure_def, Option.elimM, tsum_option, probOutput_def,
    SPMF.apply_eq_toPMF_some]

@[simp]
lemma probFailure_bind_eq_zero_iff [HasEvalSPMF m] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = 0 ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, Pr[⊥ | my x] = 0 := by
  simp [probFailure_bind_eq_add_tsum]
  grind

-- lemma probFailure_bind_eq_zero [HasEvalSPMF m] {mx : m α} {my : α → m β}

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
  (probOutput_bind_eq_tsum mx my y).trans (tsum_eq_sum' <| by simp)

lemma probEvent_bind_eq_sum_finSupport [HasEvalSPMF m] [HasEvalFinset m]
    (mx : m α) (my : α → m β) [DecidableEq α] (q : β → Prop) :
    Pr[q | mx >>= my] = ∑ x ∈ finSupport mx, Pr[= x | mx] * Pr[q | my x] :=
  (probEvent_bind_eq_tsum mx my q).trans (tsum_eq_sum' <| by simp)

section const

@[simp]
lemma support_bind_const [HasEvalSet m] (mx : m α) (my : m β) :
    support (mx >>= fun _ => my) = {y ∈ support my | (support mx).Nonempty} := by
  grind [= Set.Nonempty]

@[simp]
lemma finSupport_bind_const [HasEvalSet m] [HasEvalFinset m]
    [DecidableEq β] [DecidableEq α] (mx : m α) (my : m β) :
    finSupport (mx >>= fun _ => my) = if (finSupport mx).Nonempty then finSupport my else ∅ := by
  aesop

lemma probOutput_bind_of_const [HasEvalSPMF m] (mx : m α)
    {my : α → m β} {y : β} {r : ℝ≥0∞} (h : ∀ x ∈ support mx, Pr[= y | my x] = r) :
    Pr[= y | mx >>= my] = (1 - Pr[⊥ | mx]) * r := by
  rw [probOutput_bind_eq_tsum, ← tsum_probOutput_eq_sub, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · aesop
  · aesop

@[simp, grind =_]
lemma probOutput_bind_const [HasEvalSPMF m] (mx : m α) (my : m β) (y : β) :
    Pr[= y | mx >>= fun _ => my] = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by
  rw [probOutput_bind_of_const mx fun _ _ => rfl]

lemma probEvent_bind_of_const [HasEvalSPMF m] (mx : m α)
    {my : α → m β} {p : β → Prop} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[p | my x] = r) :
    Pr[p | mx >>= my] = (1 - Pr[⊥ | mx]) * r := by
  rw [probEvent_bind_eq_tsum, ← tsum_probOutput_eq_sub, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · aesop
  · aesop

@[simp, grind =_]
lemma probEvent_bind_const [HasEvalSPMF m] (mx : m α) (my : m β) (p : β → Prop) :
    Pr[p | mx >>= fun _ => my] = (1 - Pr[⊥ | mx]) * Pr[p | my] := by
  rw [probEvent_bind_of_const mx fun _ _ => rfl]

lemma probFailure_bind_of_const' [HasEvalSPMF m]
    (mx : m α) {my : α → m β} {r : ℝ≥0∞} (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + r - Pr[⊥ | mx] * r := by
  -- have hr : r ≤ 1
  rw [probFailure_bind_eq_add_tsum]

  sorry

-- TODO: `h` should only require `∀ x ∈ support mx`.
lemma probFailure_bind_of_const [Nonempty α] [HasEvalSPMF m]
    (mx : m α) {my : α → m β} {r : ℝ≥0∞} (h : ∀ x, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + r - Pr[⊥ | mx] * r := by
  have : r ≠ ⊤ := λ hr ↦ probFailure_ne_top ((h (Classical.arbitrary α)).trans hr)
  simp [probFailure_bind_eq_add_tsum, h, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]
  rw [ENNReal.sub_mul λ _ _ ↦ this, one_mul]
  refine symm (AddLECancellable.add_tsub_assoc_of_le ?_ ?_ _)
  · refine ENNReal.addLECancellable_iff_ne.2 (ENNReal.mul_ne_top probFailure_ne_top this)
  · by_cases hr : r = 0
    · simp only [hr, mul_zero, le_refl]
    refine mul_le_of_le_div (le_of_le_of_eq probFailure_le_one ?_)
    refine symm (ENNReal.div_self hr this)

@[simp, grind =_]
lemma probFailure_bind_const [Nonempty α] [HasEvalSPMF m] (mx : m α) (my : m β) :
    Pr[⊥ | mx >>= fun _ => my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by
  rw [probFailure_bind_of_const mx fun _ => rfl]

/-- Write the probability of `mx >>= my` failing given that `my` has constant failure chance over
the possible outputs in `support mx` as a fixed expression without any sums. -/
lemma probFailure_bind_eq_sub_mul' [Nonempty α] [HasEvalSPMF m]
    (mx : m α) (my : α → m β) (r : ℝ≥0∞) (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = 1 - (1 - Pr[⊥ | mx]) * (1 - r) := by
  by_cases hmx : ∃ x, x ∈ (support mx)
  · have hr : r ≤ 1 := by
      obtain ⟨x, hx⟩ := hmx
      specialize h x hx
      aesop
    rw [← ENNReal.toReal_eq_toReal_iff']
    · rw [probFailure_bind_eq_add_tsum]

      sorry

    simp

    simp
  · rw [probFailure_eq_one]
    rw [probFailure_eq_one]
    simp
    aesop
    aesop

-- TODO: this is a really gross way to prove this.
-- Should be a better way to move to real
lemma probFailure_bind_eq_sub_mul [Nonempty α] [HasEvalSPMF m]
    (mx : m α) (my : α → m β) (r : ℝ≥0∞) (h : ∀ x, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = 1 - (1 - Pr[⊥ | mx]) * (1 - r) := by
  have hr : r ≤ 1 := by
    specialize h (Classical.arbitrary α)
    rw [← h]
    aesop
  rw [probFailure_bind_of_const mx h]

  rw [← ENNReal.toReal_eq_toReal_iff']

  · rw [ENNReal.toReal_sub_of_le]
    rw [ENNReal.toReal_add]
    rw [ENNReal.toReal_sub_of_le]
    rw [ENNReal.toReal_mul]
    simp only [toReal_one, toReal_mul, probFailure_le_one, ne_eq, one_ne_top, not_false_eq_true,
      toReal_sub_of_le]
    rw [ENNReal.toReal_sub_of_le]
    simp
    set x := Pr[⊥ | mx].toReal
    set v := r.toReal

    ring
    · simp [hr]
    simp
    apply mul_le_one'
    simp
    simp
    simp
    simp
    aesop
    refine le_add_left ?_
    by_cases hr : r = 0
    simp [hr]
    refine ENNReal.mul_le_of_le_div ?_
    rw [ENNReal.div_self]
    aesop
    aesop
    aesop
    aesop
  · aesop
  · simp


end const

lemma probFailure_bind_le_of_forall [HasEvalSPMF m] {mx : m α}
    {s : ℝ≥0∞} (h' : Pr[⊥ | mx] ≤ s) (my : α → m β) {r : ℝ≥0∞}
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

section bind_const

variable (mx : m α) (my : m β)



end bind_const

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
