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

lemma evalDist_bind_of_support_eq_empty [HasEvalSPMF m] (mx : m α) (my : α → m β)
    (h : support mx = ∅) : evalDist (mx >>= my) = failure := by
  simp [SPMF.ext_iff, ← probOutput_def, h]

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

@[grind =]
lemma probFailure_bind_eq_add_tsum_support [HasEvalSPMF m] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * Pr[⊥ | my x] := by
  rw [probFailure_bind_eq_add_tsum]
  congr 1
  rw [tsum_subtype (support mx) (fun x => Pr[= x | mx] * Pr[⊥ | my x])]
  refine tsum_congr fun x => ?_
  unfold Set.indicator
  aesop

@[simp, grind =]
lemma probFailure_bind_eq_zero_iff [HasEvalSPMF m] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = 0 ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, Pr[⊥ | my x] = 0 := by
  simp [probFailure_bind_eq_add_tsum]
  grind

/-- Version of `probOutput_bind_eq_tsum` that sums only over the subtype given by the support
of the first computation. This can be useful to avoid looking at edge cases that can't actually
happen in practice after the first computation. A common example is if the first computation
does some error handling to avoids returning malformed outputs. -/
lemma probOutput_bind_eq_tsum_subtype [HasEvalSPMF m] (mx : m α) (my : α → m β) (y : β) :
    Pr[= y | mx >>= my] = ∑' x : support mx, Pr[= x | mx] * Pr[= y | my x] := by
  rw [tsum_subtype _ (fun x => Pr[= x | mx] * Pr[= y | my x]), probOutput_bind_eq_tsum]
  refine tsum_congr (fun x => ?_)
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
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    aesop
  · aesop

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

/-- Write the probability of `mx >>= my` failing given that `my` has constant failure chance over
the possible outputs in `support mx` as a fixed expression without any sums. -/
lemma probFailure_bind_of_const [HasEvalSPMF m]
    {mx : m α} {my : α → m β} {r : ℝ≥0∞} (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + r * (1 - Pr[⊥ | mx]) := by
  calc Pr[⊥ | mx >>= my]
    _ = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * Pr[⊥ | my x] := by grind
    _ = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * r := by grind
    _ = Pr[⊥ | mx] + r * (1 - Pr[⊥ | mx]) := by
      rw [ENNReal.tsum_mul_right, mul_comm, tsum_support_probOutput_eq_sub]

lemma probFailure_bind_of_const' [HasEvalSPMF m]
    {mx : m α} {my : α → m β} {r : ℝ≥0∞} (hr : r ≠ ⊤) (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + r - Pr[⊥ | mx] * r := by
  rw [probFailure_bind_of_const h, ENNReal.mul_sub, AddLECancellable.add_tsub_assoc_of_le,
    mul_comm Pr[⊥ | mx] r, mul_one] <;> simp [hr, ENNReal.mul_eq_top]

@[simp, grind =_]
lemma probFailure_bind_const [HasEvalSPMF m] (mx : m α) (my : m β) :
    Pr[⊥ | mx >>= fun _ => my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by
  rw [probFailure_bind_of_const' (by simp) fun _ _ => rfl]

lemma probFailure_bind_eq_sub_mul [HasEvalSPMF m]
    (mx : m α) (my : α → m β) (r : ℝ≥0∞) (hr : r ≠ ⊤) (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = 1 - (1 - Pr[⊥ | mx]) * (1 - r) := by
  by_cases h' : (support mx).Nonempty
  · obtain ⟨x, hx⟩ := h'
    have : Pr[⊥ | my x] = r := h x hx
    have hr : r ≠ ⊤ := by aesop
    rw [probFailure_bind_of_const' hr h, ENNReal.one_sub_one_sub_mul_one_sub (by simp)]
    aesop
  · rw [Set.nonempty_iff_ne_empty, not_not] at h'
    have := evalDist_bind_of_support_eq_empty mx my h'
    have hmx : Pr[⊥ | mx] = 1 := by aesop
    rw [probFailure_def, this]
    simp [hmx]

end const

section mono

lemma probFailure_bind_le_add_of_forall [HasEvalSPMF m] {mx : m α}
    {my : α → m β} {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, Pr[⊥ | my x] ≤ r) :
    Pr[⊥ | mx >>= my] ≤ Pr[⊥ | mx] + (1 - Pr[⊥ | mx]) * r := by
  calc Pr[⊥ | mx >>= my]
    _ = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * Pr[⊥ | my x] := by
      rw [probFailure_bind_eq_add_tsum_support]
    _ ≤ Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * r := by
      refine add_le_add le_rfl ?_
      exact ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (hr x.1 x.2)
    _ ≤ Pr[⊥ | mx] + (1 - Pr[⊥ | mx]) * r := by simp [ENNReal.tsum_mul_right]

/-- Version of `probFailure_bind_le_of_forall` with that allows a manual `Pr[⊥ | mx]` value. -/
lemma probFailure_bind_le_of_forall' [HasEvalSPMF m] {mx : m α}
    {s : ℝ≥0∞} (h' : Pr[⊥ | mx] = s) (my : α → m β) {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, Pr[⊥ | my x] ≤ r) : Pr[⊥ | mx >>= my] ≤ s + r := by
  rw [probFailure_bind_eq_add_tsum_support]
  refine add_le_add (le_of_eq h') ?_
  calc ∑' x : support mx, Pr[= x | mx] * Pr[⊥ | my x]
    _ ≤ ∑' x : support mx, Pr[= x | mx] * r :=
        ENNReal.tsum_le_tsum fun ⟨x, hx⟩ => mul_le_mul' le_rfl (hr x hx)
    _ = (1 - Pr[⊥ | mx]) * r := by rw [ENNReal.tsum_mul_right, tsum_support_probOutput_eq_sub]
    _ = (1 - s) * r := by rw [h']
    _ ≤ 1 * r := mul_le_mul' tsub_le_self le_rfl
    _ = r := one_mul r

/-- Version of `probFailure_bind_le_of_forall` when `mx` never fails. -/
lemma probFailure_bind_le_of_forall [HasEvalSPMF m] {mx : m α}
    (h' : Pr[⊥ | mx] = 0) {my : α → m β} {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, Pr[⊥ | my x] ≤ r) : Pr[⊥ | mx >>= my] ≤ r := by
  refine (probFailure_bind_le_add_of_forall hr).trans (by simp [h'])

end mono

lemma probFailure_bind_of_probFailure_eq_zero [HasEvalSPMF m] {mx : m α}
    (h' : Pr[⊥ | mx] = 0) {my : α → m β} :
    Pr[⊥ | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[⊥ | my x] := by
  rw [probFailure_bind_eq_add_tsum, h', zero_add]

end bind


section congr_mono

variable [HasEvalSPMF m]

lemma mul_le_probEvent_bind {mx : m α} {my : α → m β}
    {p : α → Prop} {q : β → Prop} {r r' : ℝ≥0∞}
    (h : r ≤ Pr[p | mx]) (h' : ∀ x ∈ support mx, p x → r' ≤ Pr[q | my x]) :
    r * r' ≤ Pr[q | mx >>= my] := by
  have := Classical.decPred p
  rw [probEvent_bind_eq_tsum]
  calc r * r'
    _ ≤ Pr[p | mx] * r' := (mul_le_mul_left h) r'
    _ = (∑' x, if p x then Pr[= x | mx] else 0) * r' := by rw [probEvent_eq_tsum_ite]
    _ = ∑' x, (if p x then Pr[= x | mx] else 0) * r' := ENNReal.tsum_mul_right.symm
    _ ≤ ∑' x, Pr[= x | mx] * Pr[q | my x] := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        split_ifs with hp
        · by_cases hx : x ∈ support mx
          · exact mul_le_mul' le_rfl (h' x hx hp)
          · simp [probOutput_eq_zero_of_not_mem_support hx]
        · simp [zero_mul]

lemma probFailure_bind_congr (mx : m α)
    {my : α → m β} {oc : α → m γ}
    (h : ∀ x ∈ support mx, Pr[⊥ | my x] = Pr[⊥ | oc x]) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx >>= oc] := by
  simp only [probFailure_bind_eq_add_tsum]
  congr 1
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probFailure_bind_congr' (mx : m α)
    {my : α → m β} {oc : α → m γ}
    (h : ∀ x, Pr[⊥ | my x] = Pr[⊥ | oc x]) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx >>= oc] :=
  probFailure_bind_congr mx fun x _ => h x

lemma probOutput_bind_congr {mx : m α} {ob₁ ob₂ : α → m β} {y : β}
    (h : ∀ x ∈ support mx, Pr[= y | ob₁ x] = Pr[= y | ob₂ x]) :
    Pr[= y | mx >>= ob₁] = Pr[= y | mx >>= ob₂] := by
  simp only [probOutput_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probOutput_bind_congr' (mx : m α) {ob₁ ob₂ : α → m β} (y : β)
    (h : ∀ x, Pr[= y | ob₁ x] = Pr[= y | ob₂ x]) :
    Pr[= y | mx >>= ob₁] = Pr[= y | mx >>= ob₂] :=
  probOutput_bind_congr fun x _ => h x

lemma probOutput_bind_mono {mx : m α}
    {my : α → m β} {oc : α → m γ} {y : β} {z : γ}
    (h : ∀ x ∈ support mx, Pr[= y | my x] ≤ Pr[= z | oc x]) :
    Pr[= y | mx >>= my] ≤ Pr[= z | mx >>= oc] := by
  simp only [probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · exact mul_le_mul' le_rfl (h x hx)
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probEvent_bind_congr {mx : m α} {ob₁ ob₂ : α → m β} {q : β → Prop}
    (h : ∀ x ∈ support mx, Pr[q | ob₁ x] = Pr[q | ob₂ x]) :
    Pr[q | mx >>= ob₁] = Pr[q | mx >>= ob₂] := by
  simp only [probEvent_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probEvent_bind_congr' (mx : m α) {ob₁ ob₂ : α → m β} (q : β → Prop)
    (h : ∀ x, Pr[q | ob₁ x] = Pr[q | ob₂ x]) :
    Pr[q | mx >>= ob₁] = Pr[q | mx >>= ob₂] :=
  probEvent_bind_congr fun x _ => h x

lemma probEvent_bind_mono {mx : m α} {my oc : α → m β} {q : β → Prop}
    (h : ∀ x ∈ support mx, Pr[q | my x] ≤ Pr[q | oc x]) :
    Pr[q | mx >>= my] ≤ Pr[q | mx >>= oc] := by
  simp only [probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · exact mul_le_mul' le_rfl (h x hx)
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probOutput_bind_congr_div_const {mx : m α}
    {ob₁ ob₂ : α → m β} {y : β} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[= y | ob₁ x] = Pr[= y | ob₂ x] / r) :
    Pr[= y | mx >>= ob₁] = Pr[= y | mx >>= ob₂] / r := by
  simp only [probOutput_bind_eq_tsum, div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx, div_eq_mul_inv, mul_assoc]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probOutput_bind_congr_eq_add {γ₁ γ₂ : Type u}
    {mx : m α} {my : α → m β}
      {oc₁ : α → m γ₁} {oc₂ : α → m γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ support mx, Pr[= y | my x] = Pr[= z₁ | oc₁ x] + Pr[= z₂ | oc₂ x]) :
    Pr[= y | mx >>= my] = Pr[= z₁ | mx >>= oc₁] + Pr[= z₂ | mx >>= oc₂] := by
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx, left_distrib]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probOutput_bind_congr_le_add {γ₁ γ₂ : Type u}
    {mx : m α} {my : α → m β}
      {oc₁ : α → m γ₁} {oc₂ : α → m γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ support mx, Pr[= y | my x] ≤ Pr[= z₁ | oc₁ x] + Pr[= z₂ | oc₂ x]) :
    Pr[= y | mx >>= my] ≤ Pr[= z₁ | mx >>= oc₁] + Pr[= z₂ | mx >>= oc₂] := by
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · calc Pr[= x | mx] * Pr[= y | my x]
      _ ≤ Pr[= x | mx] * (Pr[= z₁ | oc₁ x] + Pr[= z₂ | oc₂ x]) := mul_le_mul' le_rfl (h x hx)
      _ = Pr[= x | mx] * Pr[= z₁ | oc₁ x] + Pr[= x | mx] * Pr[= z₂ | oc₂ x] := left_distrib ..
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probOutput_bind_congr_add_le {γ₁ γ₂ : Type u}
    {mx : m α} {my : α → m β}
      {oc₁ : α → m γ₁} {oc₂ : α → m γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ support mx, Pr[= z₁ | oc₁ x] + Pr[= z₂ | oc₂ x] ≤ Pr[= y | my x]) :
    Pr[= z₁ | mx >>= oc₁] + Pr[= z₂ | mx >>= oc₂] ≤ Pr[= y | mx >>= my] := by
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · calc Pr[= x | mx] * Pr[= z₁ | oc₁ x] + Pr[= x | mx] * Pr[= z₂ | oc₂ x]
      _ = Pr[= x | mx] * (Pr[= z₁ | oc₁ x] + Pr[= z₂ | oc₂ x]) := (left_distrib ..).symm
      _ ≤ Pr[= x | mx] * Pr[= y | my x] := mul_le_mul' le_rfl (h x hx)
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probOutput_bind_congr_le_sub {γ₁ γ₂ : Type u}
    {mx : m α} {my : α → m β}
      {oc₁ : α → m γ₁} {oc₂ : α → m γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ support mx, Pr[= y | my x] ≤ Pr[= z₁ | oc₁ x] - Pr[= z₂ | oc₂ x])
    (h' : ∀ x ∈ support mx, Pr[= z₂ | oc₂ x] ≤ Pr[= z₁ | oc₁ x]) :
    Pr[= y | mx >>= my] ≤ Pr[= z₁ | mx >>= oc₁] - Pr[= z₂ | mx >>= oc₂] := by
  have hadd : Pr[= y | mx >>= my] + Pr[= z₂ | mx >>= oc₂] ≤ Pr[= z₁ | mx >>= oc₁] := by
    simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ support mx
    · rw [← left_distrib]
      exact mul_le_mul' le_rfl
        ((add_le_add (h x hx) le_rfl).trans_eq (tsub_add_cancel_of_le (h' x hx)))
    · simp [probOutput_eq_zero_of_not_mem_support hx]
  exact (ENNReal.cancel_of_ne probOutput_ne_top).le_tsub_of_add_le_right hadd

lemma probOutput_bind_congr_sub_le {γ₁ γ₂ : Type u}
    {mx : m α} {my : α → m β}
      {oc₁ : α → m γ₁} {oc₂ : α → m γ₂}
    {y : β} {z₁ : γ₁} {z₂ : γ₂}
    (h : ∀ x ∈ support mx, Pr[= z₁ | oc₁ x] - Pr[= z₂ | oc₂ x] ≤ Pr[= y | my x]) :
    Pr[= z₁ | mx >>= oc₁] - Pr[= z₂ | mx >>= oc₂] ≤ Pr[= y | mx >>= my] := by
  simp only [probOutput_bind_eq_tsum]
  rw [tsub_le_iff_right, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [← left_distrib]
    exact mul_le_mul' le_rfl (tsub_le_iff_right.mp (h x hx))
  · simp [probOutput_eq_zero_of_not_mem_support hx]

/-- Union bound for bind: if `Pr[¬p | mx] ≤ ε₁` and `Pr[¬q | my x] ≤ ε₂` for all `x` satisfying
`p`, then `Pr[¬q | mx >>= my] ≤ ε₁ + ε₂`. Useful for sequential composition of error bounds. -/
lemma probEvent_bind_le_add {mx : m α} {my : α → m β}
    {p : α → Prop} {q : β → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : Pr[fun x => ¬p x | mx] ≤ ε₁)
    (h₂ : ∀ x ∈ support mx, p x → Pr[fun y => ¬q y | my x] ≤ ε₂) :
    Pr[fun y => ¬q y | mx >>= my] ≤ ε₁ + ε₂ := by
  have := Classical.decPred p; have := Classical.decPred q
  rw [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[fun y => ¬q y | my x]
      = ∑' x, Pr[= x | mx] * Pr[fun y => ¬q y | my x] := rfl
    _ ≤ ∑' x, (Pr[= x | mx] * if p x then ε₂ else 1) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · by_cases hp : p x
          · simp only [if_pos hp]; exact mul_le_mul' le_rfl (h₂ x hx hp)
          · simp only [if_neg hp]; exact mul_le_mul' le_rfl probEvent_le_one
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = ∑' x, (if p x then Pr[= x | mx] * ε₂ else Pr[= x | mx]) := by
        refine tsum_congr fun x => ?_; split_ifs <;> ring
    _ ≤ ∑' x, (Pr[= x | mx] * ε₂ + (if ¬p x then Pr[= x | mx] else 0)) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        split_ifs <;> simp
    _ = (∑' x, Pr[= x | mx]) * ε₂ + Pr[fun x => ¬p x | mx] := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, probEvent_eq_tsum_ite]
    _ ≤ 1 * ε₂ + ε₁ := by
        exact add_le_add (mul_le_mul' tsum_probOutput_le_one le_rfl) h₁
    _ = ε₁ + ε₂ := by ring

/-- `probEvent` version of `probEvent_bind_mono` with additive error bound. -/
lemma probEvent_bind_congr_le_add {mx : m α} {my oc : α → m β}
    {q : β → Prop} {ε : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[q | my x] ≤ Pr[q | oc x] + ε) :
    Pr[q | mx >>= my] ≤ Pr[q | mx >>= oc] + ε := by
  simp only [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * ε) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · calc Pr[= x | mx] * Pr[q | my x]
            _ ≤ Pr[= x | mx] * (Pr[q | oc x] + ε) := mul_le_mul' le_rfl (h x hx)
            _ = Pr[= x | mx] * Pr[q | oc x] + Pr[= x | mx] * ε := left_distrib ..
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx] * Pr[q | oc x]) + ∑' x, Pr[= x | mx] * ε := ENNReal.tsum_add
    _ = (∑' x, Pr[= x | mx] * Pr[q | oc x]) + (∑' x, Pr[= x | mx]) * ε := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[q | oc x]) + ε := by
        exact add_le_add le_rfl (mul_le_of_le_one_left (zero_le _) tsum_probOutput_le_one)

end congr_mono

section swap_compl

variable [HasEvalSPMF m]

/-- Swapping two independent random draws preserves probability of any event. -/
lemma probEvent_bind_bind_swap [LawfulMonad m]
    {β γ : Type u}
    (mx : m α) (my : m β) (f : α → β → m γ) (q : γ → Prop) :
    Pr[q | mx >>= fun a => my >>= fun b => f a b] =
      Pr[q | my >>= fun b => mx >>= fun a => f a b] := by
  classical
  calc
    Pr[q | mx >>= fun a => my >>= fun b => f a b]
        = ∑' a : α, Pr[= a | mx] * Pr[q | my >>= fun b => f a b] := by
          simp [probEvent_bind_eq_tsum]
    _ = ∑' a : α, Pr[= a | mx] * ∑' b : β, Pr[= b | my] * Pr[q | f a b] := by
          refine tsum_congr fun a => ?_
          simp [probEvent_bind_eq_tsum]
    _ = ∑' a : α, ∑' b : β, Pr[= a | mx] * Pr[= b | my] * Pr[q | f a b] := by
          refine tsum_congr fun a => ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (ENNReal.tsum_mul_left (a := Pr[= a | mx])
              (f := fun b => Pr[= b | my] * Pr[q | f a b])).symm
    _ = ∑' b : β, ∑' a : α, Pr[= a | mx] * Pr[= b | my] * Pr[q | f a b] := by
          simpa using (ENNReal.tsum_comm (f := fun a b =>
            Pr[= a | mx] * Pr[= b | my] * Pr[q | f a b]))
    _ = ∑' b : β, Pr[= b | my] * ∑' a : α, Pr[= a | mx] * Pr[q | f a b] := by
          refine tsum_congr fun b => ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (ENNReal.tsum_mul_left (a := Pr[= b | my])
              (f := fun a => Pr[= a | mx] * Pr[q | f a b]))
    _ = Pr[q | my >>= fun b => mx >>= fun a => f a b] := by
          simp [probEvent_bind_eq_tsum]

/-- If `Pr[p | mx] ≥ 1 - ε` and `mx` never fails, then `Pr[¬p | mx] ≤ ε`. -/
lemma probEvent_compl_le_of_ge
    {mx : m α} {p : α → Prop} {ε : ℝ≥0∞}
    (hfail : Pr[⊥ | mx] = 0)
    (h : Pr[p | mx] ≥ 1 - ε) :
    Pr[fun x => ¬p x | mx] ≤ ε := by
  by_cases hε : (1 : ℝ≥0∞) ≤ ε
  · exact le_trans probEvent_le_one hε
  · have hε' : ε ≤ 1 := le_of_not_ge hε
    have hsum : Pr[p | mx] + Pr[fun x => ¬p x | mx] = 1 := by
      simpa [hfail] using probEvent_compl mx p
    have hne : Pr[p | mx] ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt probEvent_le_one (by simp))
    have hnot : Pr[fun x => ¬p x | mx] = 1 - Pr[p | mx] := by
      have hsum' : Pr[fun x => ¬p x | mx] + Pr[p | mx] = 1 := by
        simpa [add_comm] using hsum
      have := ENNReal.eq_sub_of_add_eq (hc := hne) hsum'
      simpa using this
    rw [hnot]
    exact le_trans (tsub_le_tsub_left h _)
      (by simp [ENNReal.sub_sub_cancel ENNReal.one_ne_top hε'])

/-- If `Pr[¬p | mx] ≤ ε` and `mx` never fails, then `Pr[p | mx] ≥ 1 - ε`. -/
lemma probEvent_ge_of_compl_le
    {mx : m α} {p : α → Prop} {ε : ℝ≥0∞}
    (hfail : Pr[⊥ | mx] = 0)
    (h : Pr[fun x => ¬p x | mx] ≤ ε) :
    Pr[p | mx] ≥ 1 - ε := by
  have hsum : Pr[p | mx] + Pr[fun x => ¬p x | mx] = 1 := by
    simpa [hfail] using probEvent_compl mx p
  have hne : Pr[fun x => ¬p x | mx] ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt probEvent_le_one (by simp))
  have hgood : Pr[p | mx] = 1 - Pr[fun x => ¬p x | mx] := by
    have := ENNReal.eq_sub_of_add_eq (hc := hne) hsum
    simpa using this
  rw [hgood]
  exact tsub_le_tsub_left h _

end swap_compl
