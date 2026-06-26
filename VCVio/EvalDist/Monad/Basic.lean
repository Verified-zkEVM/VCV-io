/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.EvalDist.Defs.Basic
import ToMathlib.Data.ENNReal.Gauss

/-!
# Evaluation Distributions of Computations with `Bind`

File for lemmas about `evalDist` and `support` involving the monadic `pure` and `bind`.
-/

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

open ENNReal

/- The monad/functor laws are confluent (terminating) rewrites. Tagging them for `grind` lets it
normalize a computation's structure (`mx >>= pure = mx`, `pure a >>= f = f a`, reassociation,
`f <$> pure a = pure (f a)`) *before* it falls into `probOutput`/`tsum` expansion — turning what
would otherwise be a `grind` explosion on a structured-computation equality into a quick solve. (The
analogous `bind_pure_comp`/`map_eq_bind` laws are deliberately omitted: their function argument sits
under a binder that `grind`'s pattern compiler cannot index.) -/
attribute [grind =] bind_pure pure_bind bind_assoc map_pure

/-! ## Probabilities of `pure` -/

section pure

@[simp, grind =] lemma support_pure [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] (x : α) :
    support (pure x : m α) = {x} := monadLift_pure x

lemma mem_support_pure_iff [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] (x y : α) :
    x ∈ support (pure y : m α) ↔ x = y := by grind
lemma mem_support_pure_iff' [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] (x y : α) :
    x ∈ support (pure y : m α) ↔ y = x := by aesop

@[simp, grind =]
lemma finSupport_pure [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]
    [DecidableEq α] (x : α) : finSupport (pure x : m α) = {x} := by aesop

lemma mem_finSupport_pure_iff [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]
    [DecidableEq α] (x y : α) : x ∈ finSupport (pure y : m α) ↔ x = y := by grind
lemma mem_finSupport_pure_iff' [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]
    [DecidableEq α] (x y : α) : x ∈ finSupport (pure y : m α) ↔ y = x := by aesop

@[simp, grind =, game_rule]
lemma evalDist_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] {α : Type u} (x : α) :
    𝒟[(pure x : m α)] = pure x := by simp [evalDist]

@[simp]
lemma evalDist_comp_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    evalDist ∘ (pure : α → m α) = pure := by aesop

@[simp]
lemma evalDist_comp_pure' [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (f : α → β) :
    evalDist ∘ (pure : β → m β) ∘ f = pure ∘ f := by grind

@[simp, grind =, game_rule]
lemma probOutput_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [DecidableEq α] (x y : α) :
    Pr[= x | (pure y : m α)] = if x = y then 1 else 0 := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp, grind =]
lemma probOutput_pure_self [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    Pr[= x | (pure x : m α)] = 1 := by
  aesop (rule_sets := [UnfoldEvalDist])

/-- Fallback when we don't have decidable equality. -/
@[grind =]
lemma probOutput_pure_eq_indicator [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x y : α) :
    Pr[= x | (pure y : m α)] = Set.indicator {y} (Function.const α 1) x := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp, grind =]
lemma probEvent_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) (p : α → Prop)
    [DecidablePred p] :
    Pr[ p | (pure x : m α)] = if p x then 1 else 0 := by
  aesop (rule_sets := [UnfoldEvalDist])

/-- Fallback when we don't have decidable equality. -/
@[grind =]
lemma probEvent_pure_eq_indicator [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α)
    (p : α → Prop) :
    Pr[ p | (pure x : m α)] = Set.indicator {x | p x} (Function.const α 1) x := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp, grind =]
lemma probFailure_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    Pr[⊥ | (pure x : m α)] = 0 := by aesop (rule_sets := [UnfoldEvalDist])

@[simp]
lemma tsum_probOutput_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    ∑' y : α, Pr[= y | (pure x : m α)] = 1 := by
  have : DecidableEq α := Classical.decEq α; simp

@[simp]
lemma tsum_probOutput_pure' [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    ∑' y : α, Pr[= x | (pure y : m α)] = 1 := by
  have : DecidableEq α := Classical.decEq α; simp

@[simp]
lemma sum_probOutput_pure [Fintype α] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    ∑ y : α, Pr[= y | (pure x : m α)] = 1 := by
  have : DecidableEq α := Classical.decEq α; simp

@[simp]
lemma sum_probOutput_pure' [Fintype α] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    ∑ y : α, Pr[= x | (pure y : m α)] = 1 := by
  have : DecidableEq α := Classical.decEq α; simp

end pure

/-! ## Probabilities of `bind` -/

section bind

@[simp, grind =]
lemma support_bind [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) :=
  monadLift_bind mx my

@[grind =]
lemma mem_support_bind_iff [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] (mx : m α)
    (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp

@[simp, grind =]
lemma finSupport_bind [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] (mx : m α) (my : α → m β) : finSupport (mx >>= my) =
      Finset.biUnion (finSupport mx) fun x => finSupport (my x) := by aesop

@[grind =]
lemma mem_finSupport_bind_iff [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] (mx : m α) (my : α → m β) (y : β) : y ∈ finSupport (mx >>= my) ↔
      ∃ x ∈ finSupport mx, y ∈ finSupport (my x) := by aesop

@[simp, grind =, game_rule]
lemma evalDist_bind [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α) (my : α → m β) :
    𝒟[mx >>= my] = 𝒟[mx] >>= fun x => 𝒟[my x] :=
  monadLift_bind mx my

lemma evalDist_bind_of_support_eq_empty [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) (my : α → m β)
    (h : support mx = ∅) : 𝒟[mx >>= my] = failure := by
  simp [SPMF.ext_iff, ← probOutput_def, h]

@[grind =, game_rule]
lemma probOutput_bind_eq_tsum [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α)
    (my : α → m β) (y : β) :
    Pr[= y | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[= y | my x] := by
  simp [probOutput_def]

@[grind =]
lemma probEvent_bind_eq_tsum [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α)
    (my : α → m β) (q : β → Prop) :
    Pr[ q | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[ q | my x] := by
  simp only [probEvent_eq_tsum_indicator, Set.indicator, Set.mem_setOf_eq, probOutput_bind_eq_tsum,
    ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => by split_ifs <;> simp

@[grind =]
lemma probFailure_bind_eq_add_tsum [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α)
    (my : α → m β) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑' x : α, Pr[= x | mx] * Pr[⊥ | my x] := by
  simp [probFailure_def, Option.elimM, tsum_option, probOutput_def,
    SPMF.apply_eq_toPMF_some]

@[grind =]
lemma probFailure_bind_eq_add_tsum_support [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * Pr[⊥ | my x] := by
  rw [probFailure_bind_eq_add_tsum]
  congr 1
  rw [tsum_subtype (support mx) fun x => Pr[= x | mx] * Pr[⊥ | my x]]
  refine tsum_congr fun x => ?_
  aesop (add simp Set.indicator)

-- `grind`-safe in isolation: this support-quantifier characterization saturates `grind` only in
-- combination with the `probEvent_eq_one_iff` family (kept `simp`-only). See `probability.md`.
@[simp, grind =]
lemma probFailure_bind_eq_zero_iff [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = 0 ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, Pr[⊥ | my x] = 0 := by
  simp [probFailure_bind_eq_add_tsum, or_iff_not_imp_left]

/-- Version of `probOutput_bind_eq_tsum` that sums only over the subtype given by the support
of the first computation. This can be useful to avoid looking at edge cases that can't actually
happen in practice after the first computation. A common example is if the first computation
does some error handling to avoids returning malformed outputs. -/
lemma probOutput_bind_eq_tsum_subtype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) (my : α → m β) (y : β) :
    Pr[= y | mx >>= my] = ∑' x : support mx, Pr[= x | mx] * Pr[= y | my x] := by
  rw [tsum_subtype _ (fun x => Pr[= x | mx] * Pr[= y | my x]), probOutput_bind_eq_tsum]
  refine tsum_congr (fun x => ?_)
  by_cases hx : x ∈ support mx <;> aesop

lemma probEvent_bind_eq_tsum_subtype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] (mx : m α) (my : α → m β) (q : β → Prop) :
    Pr[ q | mx >>= my] = ∑' x : support mx, Pr[= x | mx] * Pr[ q | my x] := by
  rw [tsum_subtype _ (fun x ↦ Pr[= x | mx] * Pr[ q | my x]), probEvent_bind_eq_tsum]
  refine tsum_congr (fun x ↦ ?_)
  by_cases hx : x ∈ support mx <;> aesop

/-- If `Pr[q | my x] ≤ ε` for every `x` in the support of `mx`, then the bound also
holds for the bind. -/
lemma probEvent_bind_le_of_forall_le [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {my : α → m β} {q : β → Prop} {ε : ENNReal}
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ ε) :
    Pr[ q | mx >>= my] ≤ ε := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' x : α, Pr[= x | mx] * Pr[ q | my x]
      ≤ ∑' x : α, Pr[= x | mx] * ε := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact mul_le_mul' le_rfl (h x hx)
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x : α, Pr[= x | mx]) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = ε := one_mul _

lemma probOutput_bind_eq_sum_finSupport [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] [HasEvalFinset m]
    (mx : m α) (my : α → m β) [DecidableEq α] (y : β) :
    Pr[= y | mx >>= my] = ∑ x ∈ finSupport mx, Pr[= x | mx] * Pr[= y | my x] :=
  (probOutput_bind_eq_tsum mx my y).trans (tsum_eq_sum' <| by simp)

lemma probEvent_bind_eq_sum_finSupport [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] [HasEvalFinset m]
    (mx : m α) (my : α → m β) [DecidableEq α] (q : β → Prop) :
    Pr[ q | mx >>= my] = ∑ x ∈ finSupport mx, Pr[= x | mx] * Pr[ q | my x] :=
  (probEvent_bind_eq_tsum mx my q).trans (tsum_eq_sum' <| by simp)

section const

section support

variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

@[simp]
lemma support_bind_const (mx : m α) (my : m β) :
    support (mx >>= fun _ => my) = {y ∈ support my | (support mx).Nonempty} := by
  grind [= Set.Nonempty]

@[simp]
lemma finSupport_bind_const [HasEvalFinset m]
    [DecidableEq β] [DecidableEq α] (mx : m α) (my : m β) :
    finSupport (mx >>= fun _ => my) = if (finSupport mx).Nonempty then finSupport my else ∅ := by
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    aesop
  · aesop

end support

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [EvalDistCompatible m]

lemma probOutput_bind_of_const (mx : m α)
    {my : α → m β} {y : β} {r : ℝ≥0∞} (h : ∀ x ∈ support mx, Pr[= y | my x] = r) :
    Pr[= y | mx >>= my] = (1 - Pr[⊥ | mx]) * r := by
  rw [probOutput_bind_eq_tsum, ← tsum_probOutput_eq_sub, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · aesop
  · aesop

@[simp, grind =_]
lemma probOutput_bind_const (mx : m α) (my : m β) (y : β) :
    Pr[= y | mx >>= fun _ => my] = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by
  rw [probOutput_bind_of_const mx fun _ _ => rfl]

lemma probEvent_bind_of_const (mx : m α)
    {my : α → m β} {p : β → Prop} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[ p | my x] = r) :
    Pr[ p | mx >>= my] = (1 - Pr[⊥ | mx]) * r := by
  rw [probEvent_bind_eq_tsum, ← tsum_probOutput_eq_sub, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · aesop
  · aesop

@[simp, grind =_]
lemma probEvent_bind_const (mx : m α) (my : m β) (p : β → Prop) :
    Pr[ p | mx >>= fun _ => my] = (1 - Pr[⊥ | mx]) * Pr[ p | my] := by
  rw [probEvent_bind_of_const mx fun _ _ => rfl]

/-- Write the probability of `mx >>= my` failing given that `my` has constant failure chance over
the possible outputs in `support mx` as a fixed expression without any sums. -/
lemma probFailure_bind_of_const
    {mx : m α} {my : α → m β} {r : ℝ≥0∞} (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + r * (1 - Pr[⊥ | mx]) := by
  calc Pr[⊥ | mx >>= my]
    _ = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * Pr[⊥ | my x] := by grind
    _ = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * r := by grind
    _ = Pr[⊥ | mx] + r * (1 - Pr[⊥ | mx]) := by
      rw [ENNReal.tsum_mul_right, mul_comm, tsum_support_probOutput_eq_sub]

lemma probFailure_bind_of_const'
    {mx : m α} {my : α → m β} {r : ℝ≥0∞} (hr : r ≠ ⊤) (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + r - Pr[⊥ | mx] * r := by
  rw [probFailure_bind_of_const h, ENNReal.mul_sub, AddLECancellable.add_tsub_assoc_of_le,
    mul_comm Pr[⊥ | mx] r, mul_one] <;> simp [hr, ENNReal.mul_eq_top]

@[simp, grind =_]
lemma probFailure_bind_const (mx : m α) (my : m β) :
    Pr[⊥ | mx >>= fun _ => my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by
  rw [probFailure_bind_of_const' (by simp) fun _ _ => rfl]

lemma probFailure_bind_eq_sub_mul
    (mx : m α) (my : α → m β) (r : ℝ≥0∞) (hr : r ≠ ⊤) (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = 1 - (1 - Pr[⊥ | mx]) * (1 - r) := by
  rcases (support mx).eq_empty_or_nonempty with h' | ⟨x, hx⟩
  · rw [probFailure_bind_of_const' hr h, probFailure_eq_one h']
    simp [ENNReal.add_sub_cancel_right hr]
  · rw [probFailure_bind_of_const' hr h,
      ENNReal.one_sub_one_sub_mul_one_sub (by simp) (h x hx ▸ probFailure_le_one)]

end const

section mono

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [EvalDistCompatible m]

lemma probFailure_bind_le_add_of_forall {mx : m α}
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
lemma probFailure_bind_le_of_forall' {mx : m α}
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
lemma probFailure_bind_le_of_forall {mx : m α}
    (h' : Pr[⊥ | mx] = 0) {my : α → m β} {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, Pr[⊥ | my x] ≤ r) : Pr[⊥ | mx >>= my] ≤ r := by
  refine (probFailure_bind_le_add_of_forall hr).trans (by simp [h'])

end mono

lemma probFailure_bind_of_probFailure_eq_zero [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    {mx : m α} (h' : Pr[⊥ | mx] = 0) {my : α → m β} :
    Pr[⊥ | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[⊥ | my x] := by
  rw [probFailure_bind_eq_add_tsum, h', zero_add]

end bind

section forall_support

variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

@[simp] lemma allOutputsSatisfy_pure (p : α → Prop) (x : α) :
    allOutputsSatisfy p (pure x : m α) ↔ p x := by
  simp [allOutputsSatisfy]

@[simp] lemma someOutputSatisfies_pure (p : α → Prop) (x : α) :
    someOutputSatisfies p (pure x : m α) ↔ p x := by
  simp [someOutputSatisfies]

@[simp] lemma allOutputsSatisfy_bind
    (mx : m α) (my : α → m β) (p : β → Prop) :
    allOutputsSatisfy p (mx >>= my) ↔
      allOutputsSatisfy (fun a => allOutputsSatisfy p (my a)) mx := by
  simp only [allOutputsSatisfy, support_bind]
  aesop

@[simp] lemma someOutputSatisfies_bind
    (mx : m α) (my : α → m β) (p : β → Prop) :
    someOutputSatisfies p (mx >>= my) ↔
      someOutputSatisfies (fun a => someOutputSatisfies p (my a)) mx := by
  simp only [someOutputSatisfies, support_bind]
  aesop

end forall_support

/-! ## Congruence and monotonicity for `bind` -/

section congr_mono

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [EvalDistCompatible m]

lemma mul_le_probEvent_bind {mx : m α} {my : α → m β}
    {p : α → Prop} {q : β → Prop} {r r' : ℝ≥0∞}
    (h : r ≤ Pr[ p | mx]) (h' : ∀ x ∈ support mx, p x → r' ≤ Pr[ q | my x]) :
    r * r' ≤ Pr[ q | mx >>= my] := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc r * r'
    _ ≤ Pr[ p | mx] * r' := by gcongr
    _ = ∑' x, (if p x then Pr[= x | mx] else 0) * r' := by
        rw [probEvent_eq_tsum_ite, ENNReal.tsum_mul_right]
    _ ≤ ∑' x, Pr[= x | mx] * Pr[ q | my x] := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · split_ifs with hp
          · exact mul_le_mul' le_rfl (h' x hx hp)
          · simp
        · simp [probOutput_eq_zero_of_not_mem_support hx]

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
    (h : ∀ x ∈ support mx, Pr[ q | ob₁ x] = Pr[ q | ob₂ x]) :
    Pr[ q | mx >>= ob₁] = Pr[ q | mx >>= ob₂] := by
  simp only [probEvent_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probEvent_bind_congr' (mx : m α) {ob₁ ob₂ : α → m β} (q : β → Prop)
    (h : ∀ x, Pr[ q | ob₁ x] = Pr[ q | ob₂ x]) :
    Pr[ q | mx >>= ob₁] = Pr[ q | mx >>= ob₂] :=
  probEvent_bind_congr fun x _ => h x

lemma evalDist_bind_congr {mx : m α} {ob₁ ob₂ : α → m β}
    (h : ∀ x ∈ support mx, 𝒟[ob₁ x] = 𝒟[ob₂ x]) :
    𝒟[mx >>= ob₁] = 𝒟[mx >>= ob₂] :=
  evalDist_ext fun y => probOutput_bind_congr fun x hx => evalDist_ext_iff.mp (h x hx) y

lemma evalDist_bind_congr' (mx : m α) {ob₁ ob₂ : α → m β}
    (h : ∀ x, 𝒟[ob₁ x] = 𝒟[ob₂ x]) :
    𝒟[mx >>= ob₁] = 𝒟[mx >>= ob₂] :=
  evalDist_bind_congr fun x _ => h x

lemma probEvent_bind_mono {mx : m α} {my oc : α → m β} {q : β → Prop}
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ Pr[ q | oc x]) :
    Pr[ q | mx >>= my] ≤ Pr[ q | mx >>= oc] := by
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

lemma probEvent_bind_congr_div_const {mx : m α}
    {ob₁ ob₂ : α → m β} {q : β → Prop} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[ q | ob₁ x] = Pr[ q | ob₂ x] / r) :
    Pr[ q | mx >>= ob₁] = Pr[ q | mx >>= ob₂] / r := by
  simp only [probEvent_bind_eq_tsum, div_eq_mul_inv]
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

lemma probEvent_bind_congr_eq_add {γ₁ γ₂ : Type u}
    {mx : m α} {my : α → m β}
      {oc₁ : α → m γ₁} {oc₂ : α → m γ₂}
    {q : β → Prop} {q₁ : γ₁ → Prop} {q₂ : γ₂ → Prop}
    (h : ∀ x ∈ support mx, Pr[ q | my x] = Pr[ q₁ | oc₁ x] + Pr[ q₂ | oc₂ x]) :
    Pr[ q | mx >>= my] = Pr[ q₁ | mx >>= oc₁] + Pr[ q₂ | mx >>= oc₂] := by
  simp only [probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
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

lemma probEvent_bind_congr_add_le {γ₁ γ₂ : Type u}
    {mx : m α} {my : α → m β}
      {oc₁ : α → m γ₁} {oc₂ : α → m γ₂}
    {q : β → Prop} {q₁ : γ₁ → Prop} {q₂ : γ₂ → Prop}
    (h : ∀ x ∈ support mx, Pr[ q₁ | oc₁ x] + Pr[ q₂ | oc₂ x] ≤ Pr[ q | my x]) :
    Pr[ q₁ | mx >>= oc₁] + Pr[ q₂ | mx >>= oc₂] ≤ Pr[ q | mx >>= my] := by
  simp only [probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · calc Pr[= x | mx] * Pr[ q₁ | oc₁ x] + Pr[= x | mx] * Pr[ q₂ | oc₂ x]
      _ = Pr[= x | mx] * (Pr[ q₁ | oc₁ x] + Pr[ q₂ | oc₂ x]) := (left_distrib ..).symm
      _ ≤ Pr[= x | mx] * Pr[ q | my x] := mul_le_mul' le_rfl (h x hx)
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

lemma probEvent_bind_congr_le_sub {γ₁ γ₂ : Type u}
    {mx : m α} {my : α → m β}
      {oc₁ : α → m γ₁} {oc₂ : α → m γ₂}
    {q : β → Prop} {q₁ : γ₁ → Prop} {q₂ : γ₂ → Prop}
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ Pr[ q₁ | oc₁ x] - Pr[ q₂ | oc₂ x])
    (h' : ∀ x ∈ support mx, Pr[ q₂ | oc₂ x] ≤ Pr[ q₁ | oc₁ x]) :
    Pr[ q | mx >>= my] ≤ Pr[ q₁ | mx >>= oc₁] - Pr[ q₂ | mx >>= oc₂] := by
  have hadd : Pr[ q | mx >>= my] + Pr[ q₂ | mx >>= oc₂] ≤ Pr[ q₁ | mx >>= oc₁] := by
    simp only [probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ support mx
    · rw [← left_distrib]
      exact mul_le_mul' le_rfl
        ((add_le_add (h x hx) le_rfl).trans_eq (tsub_add_cancel_of_le (h' x hx)))
    · simp [probOutput_eq_zero_of_not_mem_support hx]
  exact (ENNReal.cancel_of_ne probEvent_ne_top).le_tsub_of_add_le_right hadd

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

lemma probEvent_bind_congr_sub_le {γ₁ γ₂ : Type u}
    {mx : m α} {my : α → m β}
      {oc₁ : α → m γ₁} {oc₂ : α → m γ₂}
    {q : β → Prop} {q₁ : γ₁ → Prop} {q₂ : γ₂ → Prop}
    (h : ∀ x ∈ support mx, Pr[ q₁ | oc₁ x] - Pr[ q₂ | oc₂ x] ≤ Pr[ q | my x]) :
    Pr[ q₁ | mx >>= oc₁] - Pr[ q₂ | mx >>= oc₂] ≤ Pr[ q | mx >>= my] := by
  simp only [probEvent_bind_eq_tsum]
  rw [tsub_le_iff_right, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [← left_distrib]
    exact mul_le_mul' le_rfl (tsub_le_iff_right.mp (h x hx))
  · simp [probOutput_eq_zero_of_not_mem_support hx]

/-- Union bound for bind: if `Pr[ ¬p | mx] ≤ ε₁` and `Pr[ ¬q | my x] ≤ ε₂` for all `x` satisfying
`p`, then `Pr[ ¬q | mx >>= my] ≤ ε₁ + ε₂`. Useful for sequential composition of error bounds. -/
lemma probEvent_bind_le_add {mx : m α} {my : α → m β}
    {p : α → Prop} {q : β → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : Pr[ fun x => ¬p x | mx] ≤ ε₁)
    (h₂ : ∀ x ∈ support mx, p x → Pr[ fun y => ¬q y | my x] ≤ ε₂) :
    Pr[ fun y => ¬q y | mx >>= my] ≤ ε₁ + ε₂ := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[ fun y => ¬q y | my x]
      ≤ ∑' x, (Pr[= x | mx] * ε₂ + if ¬p x then Pr[= x | mx] else 0) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · by_cases hp : p x
          · rw [if_neg (not_not_intro hp), add_zero]
            exact mul_le_mul' le_rfl (h₂ x hx hp)
          · rw [if_pos hp]
            exact (mul_le_of_le_one_right zero_le probEvent_le_one).trans le_add_self
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx]) * ε₂ + Pr[ fun x => ¬p x | mx] := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, probEvent_eq_tsum_ite]
    _ ≤ 1 * ε₂ + ε₁ := add_le_add (mul_le_mul' tsum_probOutput_le_one le_rfl) h₁
    _ = ε₁ + ε₂ := by ring

/-- `probEvent` version of `probEvent_bind_mono` with additive error bound. -/
lemma probEvent_bind_congr_le_add {mx : m α} {my oc : α → m β}
    {q : β → Prop} {ε : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ Pr[ q | oc x] + ε) :
    Pr[ q | mx >>= my] ≤ Pr[ q | mx >>= oc] + ε := by
  simp only [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[ q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[ q | oc x] + Pr[= x | mx] * ε) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact (mul_le_mul' le_rfl (h x hx)).trans_eq (left_distrib ..)
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[ q | oc x]) + ε := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        gcongr
        exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

end congr_mono

/-! ## Swapping independent draws -/

section swap_compl

variable [MonadLiftT m SPMF]

/-- Swapping two independent random draws preserves the output distribution: although
`mx >>= fun a => my >>= fun b => f a b` and `my >>= fun b => mx >>= fun a => f a b` need not be
equal as `m`-computations when `m` is non-commutative, the two draws are independent, so their
output distributions agree. The `probEvent`/`probOutput` forms (`probEvent_bind_bind_swap`,
`probOutput_bind_bind_swap`) are corollaries. -/
lemma evalDist_bind_bind_swap [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : m β) (f : α → β → m γ) :
    𝒟[mx >>= fun a => my >>= fun b => f a b] =
      𝒟[my >>= fun b => mx >>= fun a => f a b] := by
  refine evalDist_ext fun x => ?_
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => mul_left_comm _ _ _

/-- Swapping two independent random draws preserves probability of any event. Corollary of
`evalDist_bind_bind_swap`. -/
lemma probEvent_bind_bind_swap [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : m β) (f : α → β → m γ) (q : γ → Prop) :
    Pr[ q | mx >>= fun a => my >>= fun b => f a b] =
      Pr[ q | my >>= fun b => mx >>= fun a => f a b] := by
  rw [probEvent_def, probEvent_def, evalDist_bind_bind_swap]

/-- Swapping two independent random draws preserves the probability of any fixed output. Corollary
of `evalDist_bind_bind_swap`. -/
lemma probOutput_bind_bind_swap [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : m β) (f : α → β → m γ) (z : γ) :
    Pr[= z | mx >>= fun a => my >>= fun b => f a b] =
      Pr[= z | my >>= fun b => mx >>= fun a => f a b] := by
  rw [probOutput_def, probOutput_def, evalDist_bind_bind_swap]

/-! ## Complement bounds -/

omit [Monad m] in
/-- If `1 - ε ≤ Pr[ p | mx]` and `mx` never fails, then `Pr[ ¬p | mx] ≤ ε`. -/
lemma probEvent_compl_le_of_one_sub_le
    {mx : m α} {p : α → Prop} {ε : ℝ≥0∞}
    (hfail : Pr[⊥ | mx] = 0)
    (h : 1 - ε ≤ Pr[ p | mx]) :
    Pr[ fun x => ¬p x | mx] ≤ ε := by
  have hsum : Pr[ fun x => ¬p x | mx] + Pr[ p | mx] = 1 := by
    simpa [hfail, add_comm] using probEvent_compl mx p
  rwa [ENNReal.eq_sub_of_add_eq probEvent_ne_top hsum, tsub_le_iff_tsub_le]

@[deprecated (since := "2026-06-25")]
alias probEvent_compl_le_of_ge := probEvent_compl_le_of_one_sub_le

omit [Monad m] in
/-- If `Pr[ ¬p | mx] ≤ ε` and `mx` never fails, then `1 - ε ≤ Pr[ p | mx]`. -/
lemma probEvent_one_sub_le_of_compl_le
    {mx : m α} {p : α → Prop} {ε : ℝ≥0∞}
    (hfail : Pr[⊥ | mx] = 0)
    (h : Pr[ fun x => ¬p x | mx] ≤ ε) :
    1 - ε ≤ Pr[ p | mx] := by
  have hsum : Pr[ p | mx] + Pr[ fun x => ¬p x | mx] = 1 := by
    simpa [hfail] using probEvent_compl mx p
  rw [ENNReal.eq_sub_of_add_eq probEvent_ne_top hsum]
  exact tsub_le_tsub_left h _

@[deprecated (since := "2026-06-25")]
alias probEvent_ge_of_compl_le := probEvent_one_sub_le_of_compl_le

end swap_compl

/-! ## Union bounds -/

section union_bound

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

omit [Monad m] [LawfulMonadLiftT m SPMF] in
/-- Union bound for finset-indexed events: the probability that *some* event in `s` holds
is at most the sum of the individual event probabilities. -/
lemma probEvent_exists_finset_le_sum
    {ι : Type*} (s : Finset ι) (mx : m α) (E : ι → α → Prop) :
    Pr[ (fun x => ∃ i ∈ s, E i x) | mx] ≤ Finset.sum s (fun i => Pr[ E i | mx]) := by
  classical
  refine Finset.induction_on s (by simp) fun a s ha ih => ?_
  rw [Finset.sum_insert ha, show (fun x => ∃ i ∈ insert a s, E i x)
      = (fun x => E a x ∨ ∃ i ∈ s, E i x) by simp]
  refine (probEvent_or_le mx (E a) _).trans ?_
  gcongr

end union_bound
