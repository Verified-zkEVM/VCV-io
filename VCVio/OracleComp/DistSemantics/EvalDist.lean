/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Traversal
import VCVio.OracleComp.SimSemantics.SimulateQ
import Mathlib.Probability.Distributions.Uniform
import ToMathlib.General

/-!
# Denotational Semantics for Output Distributions

This file gives definitions for the output distribution or computations with uniform oracles.
Given a computation `oa : OracleComp spec α` we define a distribution `evalDist oa : PMF α`
expressing the probability of getting an output `x : α` if the oracles in `spec` were to
respond uniformly to all queries.

We also define functions `probOutput oa x` and `probEvent oa p` for the probabilities of a
specific output of of a specific predicate holding on the output respectively.
We introduce notation `[= x | oa]` and `[p | oa]` for these defintions as well.
λ α ↦ (α → β)
The behavior of more complex oracles should first be implemented using `OracleComp.simulate`
before applying these constructions.

These definitons are compatible with `OracleComp.support` and `OracleComp.finSupport` in the sense
that values are in the support iff they have non-zero probability under `evalDist`.

We give many simp lemmas involving `tsum` a lower priority, as otherwise the simplifier will
always choose them over versions involving `sum` (as they require `DecidableEq` or `Fintype`)
-/

open OracleSpec Option ENNReal BigOperators

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {ι' : Type v} {spec' : OracleSpec ι'}
  {α β γ : Type w} [spec.FiniteRange] [spec'.FiniteRange]

section evalDist

noncomputable def evalDistWhen (oa : OracleComp spec α)
    (query_dist : {α : Type _} →
      OracleQuery spec α → OptionT PMF α) :
    OptionT PMF α :=
  oa.simulateQ ⟨query_dist⟩

/-- Associate a probability mass function to a computation, where the probability is the odds of
getting a given output assuming all oracles responded uniformly at random.
Implemented by simulating queries in the `PMF` monad. -/
noncomputable def evalDist (oa : OracleComp spec α) : OptionT PMF α :=
  oa.simulateQ ⟨fun (query i _) => PMF.uniformOfFintype (spec.range i)⟩

@[simp]
lemma evalDist_pure (x : α) : evalDist (pure x : OracleComp spec α) = pure x := simulateQ_pure _ _

@[simp]
lemma evalDist_liftM [Nonempty α] [Fintype α] (q : OracleQuery spec α) :
    evalDist (q : OracleComp spec α) = OptionT.lift (PMF.uniformOfFintype α) := by
  cases q; rw [evalDist, simulateQ_query]
  refine congr_arg OptionT.lift (PMF.ext λ x ↦ ?_)
  simp only [monadLift_self, PMF.uniformOfFintype_apply, inv_inj, Nat.cast_inj]
  refine congr_arg Finset.card (Finset.ext λ _ ↦ by simp)

@[simp]
lemma evalDist_query (i : ι) (t : spec.domain i) : evalDist (query i t : OracleComp spec _) =
    OptionT.lift (PMF.uniformOfFintype (spec.range i)) := simulateQ_query _ _

@[simp]
lemma evalDist_failure : evalDist (failure : OracleComp spec α) = failure := simulateQ_failure _

@[simp]
lemma evalDist_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    evalDist (oa >>= ob) = (evalDist oa) >>= (evalDist ∘ ob) := by
  simp [evalDist, Function.comp_def]

lemma evalDist_query_bind (i : ι) (t : spec.domain i) (ou : spec.range i → OracleComp spec α) :
    evalDist ((query i t : OracleComp spec _) >>= ou) =
      (OptionT.lift (PMF.uniformOfFintype (spec.range i))) >>= (evalDist ∘ ou) := by
  rw [evalDist_bind, evalDist_query]

@[simp]
lemma evalDist_map (oa : OracleComp spec α) (f : α → β) :
    evalDist (f <$> oa) = f <$> (evalDist oa) := simulateQ_map _ _ _

@[simp]
lemma evalDist_seq (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    evalDist (og <*> oa) = evalDist og <*> evalDist oa := simulateQ_seq _ _ _

@[simp]
lemma evalDist_eqRec (h : α = β) (oa : OracleComp spec α) :
    evalDist (h ▸ oa) = h ▸ evalDist oa := by induction h; rfl

@[simp]
lemma evalDist_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    evalDist (if p then oa else oa') = if p then evalDist oa else evalDist oa' := by
  by_cases hp : p <;> simp [hp]

@[simp]
lemma evalDist_coin : evalDist coin = OptionT.lift (PMF.uniformOfFintype Bool) := by
  rw [coin, evalDist_query]

@[simp]
lemma evalDist_uniformFin (n : ℕ) :
    evalDist $[0..n] = OptionT.lift (PMF.uniformOfFintype (Fin (n + 1))) := by
  rw [uniformFin, evalDist_query]

end evalDist

/-- `[= x | oa]` is the probability of getting the given output `x` from the computation `oa`,
assuming all oracles respond uniformly at random. -/
noncomputable def probOutput (oa : OracleComp spec α) (x : α) : ℝ≥0∞ :=
  (evalDist oa).run (some x)

notation "[=" x "|" oa "]" => probOutput oa x

lemma probOutput_def (oa : OracleComp spec α) (x : α) :
    [= x | oa] = (evalDist oa).run (some x) := rfl

lemma evalDist_apply_some (oa : OracleComp spec α) (x : α) :
    (evalDist oa).run (some x) = [= x | oa] := rfl

@[simp]
lemma evalDist_comp_some (oa : OracleComp spec α) :
    (evalDist oa).run ∘ some = ([= · | oa]) := rfl

/-- `[⊥ | oa]` is the probability of the computation `oa` failing. -/
noncomputable def probFailure (oa : OracleComp spec α) : ℝ≥0∞ :=
  (evalDist oa).run none

notation "[⊥" "|" oa "]" => probFailure oa

lemma probFailure_def (oa : OracleComp spec α) :
    [⊥ | oa] = (evalDist oa).run none := rfl

lemma evalDist_apply_none (oa : OracleComp spec α) :
    (evalDist oa).run none = [⊥ | oa] := rfl

/-- `[p | oa]` is the probability of getting a result that satisfies a predicate `p`
after running the computation `oa`, assuming all oracles respond uniformly at random.-/
noncomputable def probEvent (oa : OracleComp spec α) (p : α → Prop) : ℝ≥0∞ :=
  (evalDist oa).run.toOuterMeasure (Option.some '' {x | p x})

notation "[" p "|" oa "]" => probEvent oa p

lemma probEvent_def (oa : OracleComp spec α) (p : α → Prop) :
    [p | oa] = (evalDist oa).run.toOuterMeasure (Option.some '' {x | p x}) := rfl

lemma probEvent_eq_tsum_indicator (oa : OracleComp spec α) (p : α → Prop) :
    [p | oa] = ∑' x : α, {x | p x}.indicator ([= · | oa]) x := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, Set.indicator_image (Option.some_injective _),
    tsum_option _ ENNReal.summable]

/-- More explicit form of `probEvent_eq_tsum_indicator` when the predicate `p` is decidable. -/
lemma probEvent_eq_tsum_ite (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    [p | oa] = ∑' x : α, if p x then [= x | oa] else 0 := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, tsum_option _ ENNReal.summable,
    Set.indicator, probOutput_def]

noncomputable example : ℝ≥0∞ := [= 5 | do let x ←$[0..4]; return x + 1]
noncomputable example : ℝ≥0∞ := [⊥ | do let x ←$[0..4]; if x = 0 then failure else return x]
noncomputable example : ℝ≥0∞ := [(· + 1 ≤ 3) | do let x ←$[0..4]; return x]

@[simp]
lemma probFailure_add_tsum_probOutput (oa : OracleComp spec α) :
    [⊥ | oa] + ∑' x, [= x | oa] = 1 :=
  (tsum_option _ ENNReal.summable).symm.trans (evalDist oa).tsum_coe

@[simp]
lemma tsum_probOutput_add_probFailure (oa : OracleComp spec α) :
    ∑' x, [= x | oa] + [⊥ | oa] = 1 :=
  by rw [add_comm, probFailure_add_tsum_probOutput]

section bounds

variable {oa : OracleComp spec α} {x : α} {p : α → Prop}

@[simp] lemma probOutput_le_one : [= x | oa] ≤ 1 := PMF.coe_le_one (evalDist oa) x
@[simp] lemma probFailure_le_one : [⊥ | oa] ≤ 1 := PMF.coe_le_one (evalDist oa) none

@[simp] lemma tsum_probOutput_le_one : ∑' x : α, [= x | oa] ≤ 1 :=
  le_of_le_of_eq (le_add_self) (probFailure_add_tsum_probOutput oa)
@[simp] lemma tsum_probOutput_ne_top : ∑' x : α, [= x | oa] ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one

@[simp] lemma probEvent_le_one : [p | oa] ≤ 1 := by
  rw [probEvent_def, PMF.toOuterMeasure_apply]
  refine le_of_le_of_eq (ENNReal.tsum_le_tsum ?_) (oa.evalDist.tsum_coe)
  exact Set.indicator_le_self (some '' {x | p x}) _

@[simp] lemma probOutput_ne_top : [= x | oa] ≠ ∞ := PMF.apply_ne_top (evalDist oa) x
@[simp] lemma probOutput_lt_top : [= x | oa] < ∞ := PMF.apply_lt_top (evalDist oa) x
@[simp] lemma not_one_lt_probOutput : ¬ 1 < [= x | oa] := not_lt.2 probOutput_le_one

@[simp] lemma probEvent_ne_top : [p | oa] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
@[simp] lemma probEvent_lt_top : [p | oa] < ∞ := lt_top_iff_ne_top.2 probEvent_ne_top
@[simp] lemma not_one_lt_probEvent : ¬ 1 < [p | oa] := not_lt.2 probEvent_le_one

@[simp] lemma probFailure_ne_top : [⊥ | oa] ≠ ∞ := PMF.apply_ne_top (evalDist oa) none
@[simp] lemma probFailure_lt_top : [⊥ | oa] < ∞ := PMF.apply_lt_top (evalDist oa) none
@[simp] lemma not_one_lt_probFailure : ¬ 1 < [⊥ | oa] := not_lt.2 probFailure_le_one

@[simp] lemma one_le_probOutput_iff : 1 ≤ [= x | oa] ↔ [= x | oa] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probOutput, or_false, eq_comm]
@[simp] lemma one_le_probEvent_iff : 1 ≤ [p | oa] ↔ [p | oa] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probEvent, or_false, eq_comm]
@[simp] lemma one_le_probFailure_iff : 1 ≤ [⊥ | oa] ↔ [⊥ | oa] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probFailure, or_false, eq_comm]

end bounds

lemma tsum_probOutput_eq_sub (oa : OracleComp spec α) :
    ∑' x : α, [= x | oa] = 1 - [⊥ | oa] := by
  refine ENNReal.eq_sub_of_add_eq probFailure_ne_top (tsum_probOutput_add_probFailure oa)

lemma sum_probOutput_eq_sub [Fintype α] (oa : OracleComp spec α) :
    ∑ x : α, [= x | oa] = 1 - [⊥ | oa] := by
  rw [← tsum_fintype, tsum_probOutput_eq_sub]

lemma probFailure_eq_sub_tsum (oa : OracleComp spec α) :
    [⊥ | oa] = 1 - ∑' x : α, [= x | oa] := by
  refine ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
    (probFailure_add_tsum_probOutput oa)

lemma probFailure_eq_sub_sum [Fintype α] (oa : OracleComp spec α) :
    [⊥ | oa] = 1 - ∑ x : α, [= x | oa] := by
  rw [← tsum_fintype, probFailure_eq_sub_tsum]

lemma tsum_probOutput_eq_one (oa : OracleComp spec α) (h : [⊥ | oa] = 0) :
    ∑' x : α, [= x | oa] = 1 := by
  rw [tsum_probOutput_eq_sub, h, tsub_zero]

lemma sum_probOutput_eq_one [Fintype α] (oa : OracleComp spec α) (h : [⊥ | oa] = 0) :
    ∑ x : α, [= x | oa] = 1 := by
  rw [sum_probOutput_eq_sub, h, tsub_zero]

section support

-- TODO: maybe these should be implicit for some lemmas
variable (oa : OracleComp spec α) (x : α) (p q : α → Prop)

/-- An output has non-zero probability iff it is in the `support` of the computation. -/
@[simp]
lemma mem_support_evalDist_iff (oa : OracleComp spec α) (x : α) :
    some x ∈ (evalDist oa).run.support ↔ x ∈ oa.support := by
  induction oa using OracleComp.inductionOn with
  | pure => simp
  | query_bind i t oa hoa => simp [hoa, OptionT.lift, elimM]
  | failure => simp
alias ⟨mem_support_of_mem_support_evalDist, mem_support_evalDist⟩ := mem_support_evalDist_iff

/-- An output has non-zero probability iff it is in the `finSupport` of the computation. -/
@[simp]
lemma mem_support_evalDist_iff' [spec.DecidableEq] [DecidableEq α]
    (oa : OracleComp spec α) (x : α) :
    some x ∈ (evalDist oa).run.support ↔ x ∈ oa.finSupport := by
  rw [mem_support_evalDist_iff, mem_finSupport_iff_mem_support]
alias ⟨mem_finSupport_of_mem_support_evalDist, mem_support_evalDist'⟩ := mem_support_evalDist_iff'

@[simp]
lemma evalDist_apply_eq_zero_iff (x : Option α) :
    (evalDist oa).run x = 0 ↔ x.rec ([⊥ | oa] = 0) (· ∉ oa.support) :=
  match x with
  | none => by simp [probFailure_def]
  | some x => by simp [OptionT.run, ← mem_support_evalDist_iff]

@[simp]
lemma evalDist_apply_eq_zero_iff' [spec.DecidableEq] [DecidableEq α] (x : Option α) :
    (evalDist oa).run x = 0 ↔ x.rec ([⊥ | oa] = 0) (· ∉ oa.finSupport) := by
  cases x <;> simp [mem_finSupport_iff_mem_support]

/-- The support of `evalDist oa` is exactly `support oa`. -/
lemma support_evalDist : (evalDist oa).run.support = if [⊥ | oa] = 0 then
    some '' oa.support else insert none (some '' oa.support) := by
  rw [probFailure_def]
  refine Set.ext (λ x ↦ x.rec ?_ ?_)
  · split_ifs with h <;> simp [h]
  · split_ifs <;> simp

lemma support_evalDist' [spec.DecidableEq] [DecidableEq α] :
    (evalDist oa).run.support = if [⊥ | oa] = 0 then
      oa.finSupport.image some else insert none (oa.finSupport.image some) := by
  rw [support_evalDist]
  split_ifs with h <;> simp only [Finset.coe_insert, Finset.coe_image, coe_finSupport]

@[simp low]
lemma probOutput_eq_zero_iff : [= x | oa] = 0 ↔ x ∉ oa.support := by
  rw [probOutput, PMF.apply_eq_zero_iff, mem_support_evalDist_iff]
alias ⟨not_mem_support_of_probOutput_eq_zero, probOutput_eq_zero⟩ := probOutput_eq_zero_iff
@[simp low]
lemma zero_eq_probOutput_iff : 0 = [= x | oa] ↔ x ∉ oa.support := by
  rw [eq_comm, probOutput_eq_zero_iff]
alias ⟨_, zero_eq_probOutput⟩ := zero_eq_probOutput_iff

@[simp]
lemma probOutput_eq_zero_iff' [spec.DecidableEq] [DecidableEq α] :
    [= x | oa] = 0 ↔ x ∉ oa.finSupport := by
  rw [mem_finSupport_iff_mem_support, probOutput_eq_zero_iff]
alias ⟨not_mem_fin_support_of_probOutput_eq_zero, probOutput_eq_zero'⟩ := probOutput_eq_zero_iff
@[simp]
lemma zero_eq_probOutput_iff' [spec.DecidableEq] [DecidableEq α] :
    0 = [= x | oa] ↔ x ∉ oa.finSupport := by
  rw [eq_comm, probOutput_eq_zero_iff']
alias ⟨_, zero_eq_probOutput'⟩ := zero_eq_probOutput_iff'

lemma probOutput_ne_zero (h : x ∈ oa.support) : [= x | oa] ≠ 0 := by simp [h]

lemma probOutput_ne_zero' [DecidableEq α] (h : x ∈ oa.finSupport) : [= x | oa] ≠ 0 :=
  probOutput_ne_zero oa x (mem_support_of_mem_finSupport oa h)

@[simp low]
lemma probEvent_eq_zero_iff : [p | oa] = 0 ↔ ∀ x ∈ oa.support, ¬ p x := by
  rw [probEvent_def, PMF.toOuterMeasure_apply_eq_zero_iff]
  simp [Set.disjoint_iff_forall_ne, Option.forall]
  refine forall_congr' λ x ↦ forall_congr' λ hx ↦ ?_
  refine ⟨λ h hx ↦ h x hx rfl, λ h y hy hxy ↦ h (hxy ▸ hy)⟩
alias ⟨not_of_mem_support_of_probEvent_eq_zero, probEvent_eq_zero⟩ := probEvent_eq_zero_iff
@[simp low]
lemma zero_eq_probEvent_iff : 0 = [p | oa] ↔ ∀ x ∈ oa.support, ¬ p x := by
  rw [eq_comm, probEvent_eq_zero_iff]
alias ⟨_, zero_eq_probEvent⟩ := zero_eq_probEvent_iff

@[simp]
lemma probEvent_eq_zero_iff' [spec.DecidableEq] [DecidableEq α] :
    [p | oa] = 0 ↔ ∀ x ∈ oa.finSupport, ¬ p x := by
  simp only [probEvent_eq_zero_iff, mem_finSupport_iff_mem_support]
alias ⟨not_of_mem_finSupport_of_probEvent_eq_zero, probEvent_eq_zero'⟩ := probEvent_eq_zero_iff'
@[simp]
lemma zero_eq_probEvent_iff' [spec.DecidableEq] [DecidableEq α] :
    0 = [p | oa] ↔ ∀ x ∈ oa.finSupport, ¬ p x := by
  rw [eq_comm, probEvent_eq_zero_iff']
alias ⟨_, zero_eq_probEvent'⟩ := zero_eq_probEvent_iff'

@[simp low]
lemma probOutput_pos_iff : 0 < [= x | oa] ↔ x ∈ oa.support := by
  rw [pos_iff_ne_zero, ne_eq, probOutput_eq_zero_iff, not_not]
alias ⟨mem_support_of_probOutput_pos, probOutput_pos⟩ := probOutput_pos_iff

@[simp]
lemma probOutput_pos_iff' [spec.DecidableEq] [DecidableEq α] :
    0 < [= x | oa] ↔ x ∈ oa.finSupport := by
  rw [probOutput_pos_iff, mem_finSupport_iff_mem_support]
alias ⟨mem_finSupport_of_probOutput_pos, probOutput_pos'⟩ := probOutput_pos_iff'

@[simp low]
lemma probEvent_pos_iff : 0 < [p | oa] ↔ ∃ x ∈ oa.support, p x := by
  simp_rw [pos_iff_ne_zero, ne_eq, probEvent_eq_zero_iff, not_forall, not_not, exists_prop]
alias ⟨exists_mem_support_of_probEvent_pos, probEvent_pos⟩ := probEvent_pos_iff

@[simp]
lemma probEvent_pos_iff' [spec.DecidableEq] [DecidableEq α] :
    0 < [p | oa] ↔ ∃ x ∈ oa.finSupport, p x := by
  simp_rw [pos_iff_ne_zero, ne_eq, probEvent_eq_zero_iff', not_forall, not_not, exists_prop]
alias ⟨exists_mem_finSupport_of_probEvent_pos, probEvent_pos'⟩ := probEvent_pos_iff'

@[simp low]
lemma probOutput_eq_one_iff :
    [= x | oa] = 1 ↔ [⊥ | oa] = 0 ∧ oa.support = {x} := by
  simp [probOutput_def, PMF.apply_eq_one_iff, Set.ext_iff, Option.forall]
alias ⟨_, probOutput_eq_one⟩ := probOutput_eq_one_iff
@[simp low]
lemma one_eq_probOutput_iff :
    1 = [= x | oa] ↔ [⊥ | oa] = 0 ∧ oa.support = {x} := by
  rw [eq_comm, probOutput_eq_one_iff]
alias ⟨_, one_eq_probOutput⟩ := one_eq_probOutput_iff

@[simp]
lemma probOutput_eq_one_iff' [spec.DecidableEq] [DecidableEq α] :
    [= x | oa] = 1 ↔ [⊥ | oa] = 0 ∧ oa.finSupport = {x} := by
  rw [probOutput_eq_one_iff, finSupport_eq_iff_support_eq_coe, Finset.coe_singleton]
alias ⟨_, probOutput_eq_one'⟩ := probOutput_eq_one_iff'
@[simp]
lemma one_eq_probOutput_iff' [spec.DecidableEq] [DecidableEq α] :
    1 = [= x | oa] ↔ [⊥ | oa] = 0 ∧ oa.finSupport = {x} := by
  rw [eq_comm, probOutput_eq_one_iff']
alias ⟨_, one_eq_probOutput'⟩ := one_eq_probOutput_iff'

@[simp low]
lemma probEvent_eq_one_iff : [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x := by
  rw [probEvent, PMF.toOuterMeasure_apply_eq_one_iff]
  simp [support_evalDist]
  split_ifs with hoa
  · simp [hoa, Set.preimage_image_eq _ (some_injective α), Set.subset_def]
  · simp [hoa]
    intro h
    specialize h (Set.mem_insert none _)
    simp at h
alias ⟨_, probEvent_eq_one⟩ := probEvent_eq_one_iff
@[simp low]
lemma one_eq_probEvent_iff : 1 = [p | oa] ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x := by
  rw [eq_comm, probEvent_eq_one_iff]
alias ⟨_, one_eq_probEvent⟩ := probEvent_eq_one_iff

@[simp]
lemma probEvent_eq_one_iff' [spec.DecidableEq] [DecidableEq α] :
    [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.finSupport, p x := by
  simp_rw [probEvent_eq_one_iff, mem_finSupport_iff_mem_support]
alias ⟨_, probEvent_eq_one'⟩ := probEvent_eq_one_iff'
@[simp]
lemma one_eq_probEvent_iff' [spec.DecidableEq] [DecidableEq α] :
    1 = [p | oa] ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.finSupport, p x := by
  rw [eq_comm, probEvent_eq_one_iff']
alias ⟨_, one_eq_probEvent'⟩ := one_eq_probEvent_iff'

lemma mem_support_iff_probOutput_ne_zero : x ∈ oa.support ↔ [= x | oa] ≠ 0 := by
  simp only [ne_eq, probOutput_eq_zero_iff, not_not]
lemma mem_finSupport_iff_probOutput_ne_zero [spec.DecidableEq] [DecidableEq α] :
    x ∈ oa.finSupport ↔ [= x | oa] ≠ 0 := by
  rw [mem_finSupport_iff_mem_support, mem_support_iff_probOutput_ne_zero]

lemma mem_support_iff_probOutput_pos : x ∈ oa.support ↔ 0 < [= x | oa] := by
  simp only [probOutput_pos_iff]

lemma not_mem_support_iff_probOutput_eq_zero : x ∉ oa.support ↔ [= x | oa] = 0 := by
  simp only [probOutput_eq_zero_iff]

variable {oa x p q}

/-- If `p` implies `q` on the `support` of a computation then it is more likely to happen. -/
lemma probEvent_mono (h : ∀ x ∈ oa.support, p x → q x) : [p | oa] ≤ [q | oa] := by
  refine PMF.toOuterMeasure_mono _ λ x hx ↦ match x with
  | none => by simp at hx
  | some x => by
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, some.injEq, exists_eq_right,
        PMF.mem_support_iff, ne_eq, evalDist_apply_eq_zero_iff, not_not] at hx
      exact ⟨x, h x hx.2 hx.1, rfl⟩

/-- If `p` implies `q` on the `finSupport` of a computation then it is more likely to happen. -/
lemma probEvent_mono' [spec.DecidableEq] [DecidableEq α]
    (h : ∀ x ∈ oa.finSupport, p x → q x) : [p | oa] ≤ [q | oa] :=
  probEvent_mono (λ x hx hpx ↦ h x (mem_finSupport_of_mem_support oa hx) hpx)

-- NOTE: should allow `p` and `q` to differ outside the shared support.
lemma probEvent_congr {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : ∀ x, p x ↔ q x) (h2 : evalDist oa = evalDist oa') : [p | oa] = [q | oa'] := by
  simp only [probEvent, probOutput, h1, h2]

lemma probEvent_ext (h : ∀ x ∈ oa.support, p x ↔ q x) : [p | oa] = [q | oa] :=
  le_antisymm (probEvent_mono <| λ x hx hp ↦ (h x hx).1 hp)
    (probEvent_mono <| λ x hx hp ↦ (h x hx).2 hp)

lemma probEvent_ext' [spec.DecidableEq] [DecidableEq α]
    (h : ∀ x ∈ oa.finSupport, p x ↔ q x) : [p | oa] = [q | oa] :=
  le_antisymm (probEvent_mono' <| λ x hx hp ↦ (h x hx).1 hp)
    (probEvent_mono' <| λ x hx hp ↦ (h x hx).2 hp)

@[simp]
lemma function_support_probOutput : Function.support ([= · | oa]) = oa.support := by
  simp only [Function.support, ne_eq, probOutput_eq_zero_iff, not_not, Set.setOf_mem_eq]

lemma mem_support_iff_of_evalDist_eq {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : evalDist oa = evalDist oa') (x : α) : x ∈ oa.support ↔ x ∈ oa'.support := by
  simp only [mem_support_iff_probOutput_ne_zero, probOutput_def, h]

lemma mem_finSupport_iff_of_evalDist_eq [spec.DecidableEq] [spec'.DecidableEq]
    [DecidableEq α] {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : evalDist oa = evalDist oa') (x : α) : x ∈ oa.finSupport ↔ x ∈ oa'.finSupport := by
  simp only [mem_finSupport_iff_mem_support, mem_support_iff_of_evalDist_eq h]

end support

@[simp] lemma probEvent_eq_eq_probOutput (oa : OracleComp spec α) (x : α) :
    [(· = x) | oa] = [= x | oa] := by
  simp [probEvent_def, PMF.toOuterMeasure_apply_singleton, evalDist_apply_some]

@[simp] lemma probEvent_eq_eq_probOutput' (oa : OracleComp spec α) (x : α) :
    [(x = ·) | oa] = [= x | oa] :=
  (probEvent_congr (λ _ ↦ eq_comm) rfl).trans (probEvent_eq_eq_probOutput oa x)

section sums

variable (oa : OracleComp spec α) (p : α → Prop)

/-- The probability of an event written as a sum over the set `{x | p x}` viewed as a subtype.
This notably doesn't require decidability of the predicate `p` unlike many other lemmas. -/
lemma probEvent_eq_tsum_subtype : [p | oa] = ∑' x : {x | p x}, [= x | oa] := by
  rw [probEvent_eq_tsum_indicator, tsum_subtype]

/-- Version `probEvent_eq_tsum_subtype` that preemptively filters out elements that
aren't in the support, since they will have no mass contribution anyways.
This can make some proofs simpler by handling things on the level of subtypes. -/
lemma probEvent_eq_tsum_subtype_mem_support :
    [p | oa] = ∑' x : {x ∈ oa.support | p x}, [= x | oa] := by
  simp_rw [probEvent_eq_tsum_subtype, tsum_subtype]
  refine tsum_congr (λ x ↦ ?_)
  by_cases hpx : p x
  · refine (if_pos hpx).trans ?_
    by_cases hx : x ∈ oa.support
    · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_self, ↓reduceIte]
    · simp only [Set.indicator, Set.mem_setOf_eq, hx, hpx, and_true, ↓reduceIte,
      probOutput_eq_zero_iff, not_false_eq_true]
  · exact (if_neg hpx).trans (by simp [Set.indicator, hpx])

lemma probEvent_eq_tsum_subtype_support_ite [DecidablePred p] :
    [p | oa] = ∑' x : oa.support, if p x then [= x | oa] else 0 :=
calc
  [p | oa] = (∑' x, if p x then [= x | oa] else 0) := by rw [probEvent_eq_tsum_ite oa p]
  _ = ∑' x, oa.support.indicator (λ x ↦ if p x then [= x | oa] else 0) x := by
    refine tsum_congr (λ x ↦ ?_)
    unfold Set.indicator
    split_ifs with h1 h2 h2 <;> simp [h1, h2]
  _ = ∑' x : oa.support, if p x then [= x | oa] else 0 := by
    rw [tsum_subtype (support oa) (λ x ↦ if p x then [= x | oa] else 0)]

lemma probEvent_eq_sum_fintype_indicator [Fintype α] (oa : OracleComp spec α) (p : α → Prop) :
    [p | oa] = ∑ x : α, {x | p x}.indicator ([= · | oa]) x :=
  (probEvent_eq_tsum_indicator oa p).trans (tsum_fintype _)

lemma probEvent_eq_sum_fintype_ite [DecidablePred p] [Fintype α] :
    [p | oa] = ∑ x : α, if p x then [= x | oa] else 0 :=
  (probEvent_eq_tsum_ite oa p).trans (tsum_fintype _)

lemma probEvent_eq_sum_filter_univ [DecidablePred p] [Fintype α] :
    [p | oa] = ∑ x ∈ Finset.univ.filter p, [= x | oa] := by
  rw [probEvent_eq_sum_fintype_ite, Finset.sum_filter]

lemma probEvent_eq_sum_filter_finSupport [spec.DecidableEq] [DecidablePred p] [DecidableEq α] :
    [p | oa] = ∑ x ∈ oa.finSupport.filter p, [= x | oa] :=
  (probEvent_eq_tsum_ite oa p).trans <|
    (tsum_eq_sum' <| by simp; tauto).trans
      (Finset.sum_congr rfl <| λ x hx ↦ if_pos (Finset.mem_filter.1 hx).2)

lemma probEvent_eq_sum_finSupport_ite [spec.DecidableEq] [DecidablePred p] [DecidableEq α] :
    [p | oa] = ∑ x ∈ oa.finSupport, if p x then [= x | oa] else 0 := by
  rw [probEvent_eq_sum_filter_finSupport, Finset.sum_filter]

end sums

lemma probOutput_congr {x y : α} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : x = y) (h2 : evalDist oa = evalDist oa') : [= x | oa] = [= y | oa'] := by
  simp_rw [probOutput, h1, h2]

lemma probEvent_congr' {p q : α → Prop} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : ∀ x, x ∈ oa.support → x ∈ oa'.support → (p x ↔ q x))
    (h2 : evalDist oa = evalDist oa') : [p | oa] = [q | oa'] := by
  have h : ∀ x, x ∈ oa.support ↔ x ∈ oa'.support := mem_support_iff_of_evalDist_eq h2
  have h' : ∀ x, [= x | oa] = [= x | oa'] := λ x ↦ probOutput_congr rfl h2
  rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator]
  refine tsum_congr λ x ↦ ?_
  simp [Set.indicator, h']
  by_cases hp : p x
  · by_cases hq : q x
    · simp [hp, hq]
    · simp [hp, hq, h]
      refine λ hoa ↦ hq ?_
      refine (h1 _ ?_ hoa).1 hp
      refine (h _).2 hoa
  · by_cases hq : q x
    · simp [hp, hq]
      simp [h] at h1
      intro hoa
      specialize h1 _ hoa
      tauto
    · rw [if_neg hp, if_neg hq]


@[simp] lemma probEvent_const (oa : OracleComp spec α) (p : Prop) [Decidable p] :
    [λ _ ↦ p | oa] = if p then 1 - [⊥ | oa] else 0 := by
  rw [probEvent_eq_tsum_ite]
  split_ifs with hp <;> simp [hp, tsum_probOutput_eq_sub]

lemma probEvent_true (oa : OracleComp spec α) : [λ _ ↦ true | oa] = 1 - [⊥ | oa] := by simp
lemma probEvent_false (oa : OracleComp spec α) : [λ _ ↦ false | oa] = 0 := by simp

lemma probFailure_eq_sub_probEvent (oa : OracleComp spec α) :
    [⊥ | oa] = 1 - [λ _ ↦ true | oa] := by
  rw [probEvent_true, ENNReal.sub_sub_cancel one_ne_top probFailure_le_one]

lemma evalDist_ext_probEvent {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : ∀ x, [= x | oa] = [= x | oa']) : (evalDist oa).run = (evalDist oa').run :=
  PMF.ext λ x ↦ match x with
  | none => by simp [← probFailure_def, probFailure_eq_sub_tsum, h]
  | some x => h x

section pure

variable (x : α)

@[simp]
lemma probOutput_pure [DecidableEq α] (y : α) :
    [= y | (pure x : OracleComp spec α)] = if y = x then 1 else 0 := by
  simp [probOutput]

@[simp]
lemma probFailure_pure : [⊥ | (pure x : OracleComp spec α)] = 0 := by
  simp [probFailure]

lemma probOutput_pure_eq_zero {x y : α} (h : y ≠ x) :
    [= y | (pure x : OracleComp spec α)] = 0 := by simpa using h

lemma probOutput_pure_eq_one {x y : α} (h : y = x) :
    [= y | (pure x : OracleComp spec α)] = 1 := by simpa using h.symm

@[simp]
lemma probOutput_pure_self (x : α) : [= x | (pure x : OracleComp spec α)] = 1 := by simp

@[simp]
lemma probOutput_pure_subsingleton [Subsingleton α] (x y : α) :
    [= x | (pure y : OracleComp spec α)] = 1 := by
  simp [Subsingleton.elim x y]

@[simp]
lemma probEvent_pure (p : α → Prop) [DecidablePred p] :
    [p | (pure x : OracleComp spec α)] = if p x then 1 else 0 := by
  simp [probEvent_eq_tsum_ite]
  refine (tsum_eq_single x (by simp; tauto)).trans (by simp)

lemma probEvent_pure_eq_zero {p : α → Prop} {x : α} (h : ¬ p x) :
    [p | (pure x : OracleComp spec α)] = 0 := by simpa

lemma probEvent_pure_eq_one {p : α → Prop} {x : α} (h : p x) :
    [p | (pure x : OracleComp spec α)] = 1 := by simpa

end pure

section bind

variable (oa : OracleComp spec α) (ob : α → OracleComp spec β)

lemma probOutput_bind_eq_tsum (y : β) :
    [= y | oa >>= ob] = ∑' x : α, [= x | oa] * [= y | ob x] := by
  simp [probOutput, evalDist_bind, tsum_option _ ENNReal.summable, elimM]

lemma probFailure_bind_eq_tsum :
    [⊥ | oa >>= ob] = [⊥ | oa] + ∑' x : α, [= x | oa] * [⊥ | ob x] := by
  simp [probFailure, evalDist_bind, tsum_option _ ENNReal.summable, ← probOutput_def, elimM]

lemma probEvent_bind_eq_tsum (q : β → Prop) :
    [q | oa >>= ob] = ∑' x : α, [= x | oa] * [q | ob x] := by
  simp [probEvent_def, evalDist_bind, PMF.toOuterMeasure_bind_apply,
    tsum_option _ ENNReal.summable, evalDist_apply_some, elimM]

/-- Version of `probOutput_bind_eq_tsum` that sums only over the subtype given by the support
of the first computation. This can be useful to avoid looking at edge cases that can't actually
happen in practice after the first computation. A common example is if the first computation
does some error handling to avoids returning malformed outputs. -/
lemma probOutput_bind_eq_tsum_subtype (y : β) :
    [= y | oa >>= ob] = ∑' x : oa.support, [= x | oa] * [= y | ob x] := by
  rw [tsum_subtype _ (λ x ↦ [= x | oa] * [= y | ob x]), probOutput_bind_eq_tsum]
  refine tsum_congr (λ x ↦ ?_)
  by_cases hx : x ∈ oa.support
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_not_mem hx, probOutput_eq_zero _ _ hx, zero_mul]

lemma probEvent_bind_eq_tsum_subtype (q : β → Prop) :
    [q | oa >>= ob] = ∑' x : oa.support, [= x | oa] * [q | ob x] := by
  rw [tsum_subtype _ (λ x ↦ [= x | oa] * [q | ob x]), probEvent_bind_eq_tsum]
  refine tsum_congr (λ x ↦ ?_)
  by_cases hx : x ∈ oa.support
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_not_mem hx, probOutput_eq_zero _ _ hx, zero_mul]

lemma probOutput_bind_eq_sum_fintype [Fintype α] (y : β) :
    [= y | oa >>= ob] = ∑ x : α, [= x | oa] * [= y | ob x] :=
  (probOutput_bind_eq_tsum oa ob y).trans (tsum_fintype _)

lemma probFailure_bind_eq_sum_fintype [Fintype α] :
    [⊥ | oa >>= ob] = [⊥ | oa] + ∑ x : α, [= x | oa] * [⊥ | ob x] :=
  (probFailure_bind_eq_tsum oa ob).trans (congr_arg ([⊥ | oa] + ·) <| tsum_fintype _)

lemma probEvent_bind_eq_sum_fintype [Fintype α] (q : β → Prop) :
    [q | oa >>= ob] = ∑ x : α, [= x | oa] * [q | ob x] :=
  (probEvent_bind_eq_tsum oa ob q).trans (tsum_fintype _)

lemma probOutput_bind_eq_sum_finSupport [spec.DecidableEq] [DecidableEq α] (y : β) :
    [= y | oa >>= ob] = ∑ x ∈ oa.finSupport, [= x | oa] * [= y | ob x] :=
  (probOutput_bind_eq_tsum oa ob y).trans (tsum_eq_sum' <| by simp)

lemma probEvent_bind_eq_sum_finSupport [spec.DecidableEq] [DecidableEq α]
    (q : β → Prop) :
    [q | oa >>= ob] = ∑ x ∈ oa.finSupport, [= x | oa] * [q | ob x] :=
  (probEvent_bind_eq_tsum oa ob q).trans (tsum_eq_sum' <| by simp)

lemma probOutput_bind_of_const (y : β) (r : ℝ≥0∞) (h : ∀ x, [= y | ob x] = r) :
    [= y | oa >>= ob] = (1 - [⊥ | oa]) * r := by
  simp [probOutput_bind_eq_tsum, h, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]

lemma probFailure_bind_of_const [Nonempty α] (r : ℝ≥0∞) (h : ∀ x, [⊥ | ob x] = r) :
    [⊥ | oa >>= ob] = [⊥ | oa] + r - [⊥ | oa] * r := by
  have : r ≠ ⊤ := λ hr ↦ probFailure_ne_top ((h (Classical.arbitrary α)).trans hr)
  simp [probFailure_bind_eq_tsum, h, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]
  rw [ENNReal.sub_mul λ _ _ ↦ this, one_mul]
  refine symm (AddLECancellable.add_tsub_assoc_of_le ?_ ?_ _)
  · refine ENNReal.addLECancellable_iff_ne.2 (ENNReal.mul_ne_top probFailure_ne_top this)
  · by_cases hr : r = 0
    · simp only [hr, mul_zero, le_refl]
    refine mul_le_of_le_div (le_of_le_of_eq probFailure_le_one ?_)
    refine symm (ENNReal.div_self hr this)

lemma probFailure_bind_eq_sub_mul {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    (r : ℝ≥0∞) (h : ∀ x, [⊥ | ob x] = r) :
    [⊥ | oa >>= ob] = 1 - (1 - [⊥ | oa]) * (1 - r) := by
  rw [probFailure_bind_eq_tsum]
  rw [← tsum_probOutput_eq_sub]
  rw [← ENNReal.tsum_mul_right]
  have hl : ∀ x, [=x|oa] * [⊥|ob x] ≤ [=x|oa] :=
    λ x ↦ le_of_le_of_eq (mul_le_mul' le_rfl probFailure_le_one) (mul_one _)
  calc [⊥ | oa] + ∑' x, [= x | oa] * [⊥ | ob x]
    _ = 1 - (∑' x, [= x | oa]) + (∑' x, [= x | oa] * [⊥ | ob x]) := by
      rw [probFailure_eq_sub_tsum]
    _ = 1 - (∑' x, [= x | oa] - ∑' x, [= x | oa] * [⊥ | ob x]) := by
      exact Eq.symm (AddLECancellable.tsub_tsub_assoc
        (by simp) tsum_probOutput_le_one (ENNReal.tsum_le_tsum hl))
    _ = 1 - ∑' x, ([= x | oa] - [= x | oa] * [⊥ | ob x]) := by
      refine congr_arg (1 - ·) (ENNReal.eq_sub_of_add_eq ?_ ?_).symm
      · refine ne_top_of_le_ne_top one_ne_top ?_
        refine le_trans ?_ (@tsum_probOutput_le_one _ _ _ _ oa)
        refine ENNReal.tsum_le_tsum λ x ↦ ?_
        exact hl x
      rw [← ENNReal.tsum_add]
      refine tsum_congr λ x ↦ tsub_add_cancel_of_le (hl x)
    _ = 1 - ∑' x : α, [= x | oa] * (1 - r) := by
      refine congr_arg (1 - ·) (tsum_congr λ x ↦ ?_)
      rw [ENNReal.mul_sub (λ _ _ ↦ probOutput_ne_top), mul_one, ← h x]

lemma probFailure_bind_le_of_forall {oa : OracleComp spec α} {s : ℝ≥0∞}
    -- TODO: this should be a general type of `uniformOutput` computations
    (h' : [⊥ | oa] = s) (ob : α → OracleComp spec β) {r : ℝ≥0∞}
    (hr : ∀ x ∈ oa.support, [⊥ | ob x] ≤ r) : [⊥ | oa >>= ob] ≤ s + (1 - s) * r := sorry

/-- Version of `probFailure_bind_le_of_forall` with the `1 - s` factor ommited for convenience. -/
lemma probFailure_bind_le_of_forall' {oa : OracleComp spec α} {s : ℝ≥0∞}
    -- TODO: this should be a general type of `uniformOutput` computations
    (h' : [⊥ | oa] = s) (ob : α → OracleComp spec β) {r : ℝ≥0∞}
    (hr : ∀ x ∈ oa.support, [⊥ | ob x] ≤ r) : [⊥ | oa >>= ob] ≤ s + r := sorry

/-- Version of `probFailure_bind_le_of_forall` when `oa` never fails. -/
lemma probFailure_bind_le_of_le_of_neverFails {oa : OracleComp spec α}
    (h' : oa.neverFails) {ob : α → OracleComp spec β} {r : ℝ≥0∞}
    (hr : ∀ x ∈ oa.support, [⊥ | ob x] ≤ r) : [⊥ | oa >>= ob] ≤ r := sorry

lemma probFailure_bind_of_neverFails {oa : OracleComp spec α}
    (h : neverFails oa) (ob : α → OracleComp spec β) :
    [⊥ | oa >>= ob] = ∑' x : α, [= x | oa] * [⊥ | ob x] := sorry

end bind

section mul_le_probEvent_bind

lemma mul_le_probEvent_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {p : α → Prop} {q : β → Prop} {r r' : ℝ≥0∞}
    (h : r ≤ [p | oa]) (h' : ∀ x ∈ oa.support, p x → r' ≤ [q | ob x]) :
    r * r' ≤ [q | oa >>= ob] := by
  rw [probEvent_bind_eq_tsum]
  refine (mul_le_mul_right' h r').trans ?_
  rw [probEvent_eq_tsum_indicator, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← Set.indicator_mul_const]
  by_cases hx : x ∈ oa.support
  · refine Set.indicator_apply_le' (fun h => ?_) (fun _ => zero_le')
    exact (ENNReal.mul_le_mul_left (probOutput_ne_zero _ _ hx) probOutput_ne_top).mpr (h' x hx h)
  · simp [probOutput_eq_zero _ _ hx]

end mul_le_probEvent_bind

section bind_const

variable (oa : OracleComp spec α) (ob : OracleComp spec β)

-- lemma probFailure_bind_const :
--   [⊥ | do oa; ob] = [⊥ | oa] + [⊥ | ob] - [⊥ | oa] * [⊥ | ob]


end bind_const

section query

variable (i : ι) (t : spec.domain i)

@[simp]
lemma probOutput_liftM [Fintype α] (q : OracleQuery spec α) (u : α) :
    [= u | (q : OracleComp spec α)] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  have : Inhabited α := q.rangeInhabited
  simp [probOutput, PMF.monad_map_eq_map, OptionT.lift]
  refine (tsum_eq_single u ?_).trans ?_
  · simp [not_imp_not]
  · simp only [↓reduceIte, inv_inj, Nat.cast_inj]

lemma probOutput_query (u : spec.range i) :
    [= u | (query i t : OracleComp spec _)] = (Fintype.card (spec.range i) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_liftM]

@[simp]
lemma probFailure_liftM (q : OracleQuery spec α) :
    [⊥ | (q : OracleComp spec _)] = 0 := by
  have : Fintype α := q.rangeFintype
  have : Inhabited α := q.rangeInhabited
  simp only [probFailure, evalDist_liftM]
  erw [PMF.bind_apply]
  simp only [PMF.uniformOfFintype_apply, ENNReal.tsum_eq_zero, mul_eq_zero, ENNReal.inv_eq_zero,
    natCast_ne_top, false_or]
  intro i
  erw [PMF.pure_apply]
  simp

lemma probFailure_query : [⊥ | (query i t : OracleComp spec _)] = 0 := by
  rw [probFailure_liftM]

@[simp]
lemma probEvent_liftM_eq_mul_inv [Fintype α] (q : OracleQuery spec α)
    (p : α → Prop) [DecidablePred p] : [p | (q : OracleComp spec _)] =
      (Finset.univ.filter p).card * (↑(Fintype.card α))⁻¹ := by
  simp [probEvent_eq_sum_fintype_ite]

lemma probEvent_query_eq_mul_inv (p : spec.range i → Prop) [DecidablePred p] :
    [p | (query i t : OracleComp spec _)] =
      (Finset.univ.filter p).card * (↑(Fintype.card (spec.range i)))⁻¹ := by
  rw [probEvent_liftM_eq_mul_inv]

lemma probEvent_liftM_eq_inv_mul [Fintype α] (q : OracleQuery spec α)
    (p : α → Prop) [DecidablePred p] : [p | (q : OracleComp spec _)] =
      (↑(Fintype.card α))⁻¹ * (Finset.univ.filter p).card := by
  rw [probEvent_liftM_eq_mul_inv, mul_comm]

lemma probEvent_query_eq_inv_mul [spec.DecidableEq] (p : spec.range i → Prop) [DecidablePred p] :
    [p | (query i t : OracleComp spec _)] =
      (↑(Fintype.card (spec.range i)))⁻¹ * (Finset.univ.filter p).card := by
  rw [probEvent_query_eq_mul_inv, mul_comm]

lemma probEvent_liftM_eq_div [Fintype α] (q : OracleQuery spec α)
    (p : α → Prop) [DecidablePred p] : [p | (q : OracleComp spec _)] =
      (Finset.univ.filter p).card / (Fintype.card α) := by
  rw [div_eq_mul_inv, probEvent_liftM_eq_mul_inv]

lemma probEvent_query_eq_div [spec.DecidableEq] (p : spec.range i → Prop) [DecidablePred p] :
    [p | (query i t : OracleComp spec _)] =
      (Finset.univ.filter p).card / (Fintype.card (spec.range i)) := by
  rw [probEvent_liftM_eq_div]

end query

section failure

@[simp]
lemma probOutput_failure (x : α) : [= x | (failure : OracleComp spec α)] = 0 := by simp

@[simp]
lemma probFailure_failure : [⊥ | (failure : OracleComp spec α)] = 1 := by simp [probFailure]

@[simp]
lemma probEvent_failure (p : α → Prop) :
    [p | (failure : OracleComp spec α)] = 0 := by simp

end failure

section map

variable (oa : OracleComp spec α) (f : α → β)

/-- Write the probability of an output after mapping the result of a computation as a sum
over all outputs such that they map to the correct final output, using subtypes.
This lemma notably doesn't require decidable equality on the final type, unlike most
lemmas about probability when mapping a computation. -/
lemma probOutput_map_eq_tsum_subtype (y : β) :
    [= y | f <$> oa] = ∑' x : {x ∈ oa.support | y = f x}, [= x | oa] := by
  simp only [map_eq_bind_pure_comp, tsum_subtype _ (λ x ↦ [= x | oa]), probOutput_bind_eq_tsum,
    Function.comp_apply, probOutput_pure, mul_ite, mul_one, mul_zero,
    Set.indicator, Set.mem_setOf_eq]
  refine (tsum_congr (λ x ↦ ?_))
  by_cases hy : y = f x <;> by_cases hx : x ∈ oa.support <;> simp [hy, hx]

lemma probOutput_map_eq_tsum (y : β) :
    [= y | f <$> oa] = ∑' x, [= x | oa] * [= y | (pure (f x) : OracleComp spec β)] := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply]

lemma probOutput_map_eq_tsum_subtype_ite [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑' x : oa.support, if y = f x then [= x | oa] else 0 := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum_subtype, Function.comp_apply,
    probOutput_pure, mul_ite, mul_one, mul_zero]

lemma probOutput_map_eq_tsum_ite [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑' x : α, if y = f x then [= x | oa] else 0 := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply, probOutput_pure,
    mul_ite, mul_one, mul_zero]

lemma probOutput_map_eq_sum_fintype_ite [Fintype α] [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑ x : α, if y = f x then [= x | oa] else 0 :=
  (probOutput_map_eq_tsum_ite oa f y).trans (tsum_eq_sum' <|
    by simp only [Finset.coe_univ, Set.subset_univ])

lemma probOutput_map_eq_sum_finSupport_ite [spec.DecidableEq] [DecidableEq α] [DecidableEq β]
    (y : β) : [= y | f <$> oa] = ∑ x ∈ oa.finSupport, if y = f x then [= x | oa] else 0 :=
  (probOutput_map_eq_tsum_ite oa f y).trans (tsum_eq_sum' <|
    by simp only [coe_finSupport, Function.support_subset_iff, ne_eq, ite_eq_right_iff,
      probOutput_eq_zero_iff', mem_finSupport_iff_mem_support, Classical.not_imp, not_not, and_imp,
      imp_self, implies_true])

lemma probOutput_map_eq_sum_filter_finSupport [spec.DecidableEq] [DecidableEq α] [DecidableEq β]
    (y : β) : [= y | f <$> oa] = ∑ x ∈ oa.finSupport.filter (y = f ·), [= x | oa] := by
  rw [Finset.sum_filter, probOutput_map_eq_sum_finSupport_ite]

@[simp]
lemma probFailure_map : [⊥ | f <$> oa] = [⊥ | oa] := by
  simp [probFailure, evalDist_map, PMF.map_apply, PMF.monad_map_eq_map]
  refine (tsum_eq_single none λ x ↦ ?_).trans (if_pos rfl)
  cases x <;> simp

@[simp]
lemma probEvent_map (q : β → Prop) : [q | f <$> oa] = [q ∘ f | oa] := by
  simp only [probEvent, evalDist_map, PMF.toOuterMeasure_map_apply, Function.comp_apply]
  simp [PMF.monad_map_eq_map]
  refine congr_arg (oa.evalDist.toOuterMeasure) ?_
  simp only [Set.preimage, Set.mem_image, Set.mem_setOf_eq, Set.ext_iff]
  intro x
  cases x <;> simp
lemma probEvent_comp (q : β → Prop) : [q ∘ f | oa] = [q | f <$> oa] :=
  symm <| probEvent_map oa f q

lemma probOutput_map_eq_probOutput_inverse (f : α → β) (g : β → α)
    (hl : Function.LeftInverse f g) (hr : Function.RightInverse f g)
    (y : β) : [= y | f <$> oa] = [= g y | oa] := by
  rw [probOutput_map_eq_tsum]
  refine (tsum_eq_single (g y) (λ x hx ↦ ?_)).trans ?_
  · suffices y ≠ f x by simp [this]
    exact (λ h ↦ hx ((congr_arg g h).trans (hr x)).symm)
  · simp [hl y]

lemma probFailure_eq_sub_sum_probOutput_map [Fintype β] (oa : OracleComp spec α) (f : α → β) :
    [⊥ | oa] = 1 - ∑ y : β, [= y | f <$> oa] := by
  rw [← probFailure_map (f := f), probFailure_eq_sub_tsum, tsum_fintype]

end map

section neverFails

-- TODO: expand api and include `mayFail` versions for `probFailure_pos`.

@[simp]
lemma probFailure_eq_zero_iff (oa : OracleComp spec α) : [⊥ | oa] = 0 ↔ oa.neverFails := by
  sorry
  -- induction oa using OracleComp.inductionOn with
  -- | pure x => simp
  -- | failure => simp
  -- | query_bind i t oa h => simp [probFailure_bind_eq_tsum, h]

@[simp]
lemma probFailure_pos_iff (oa : OracleComp spec α) : 0 < [⊥ | oa] ↔ ¬ oa.neverFails := by
  sorry --rw [pos_iff_ne_zero, ne_eq, probFailure_eq_zero_iff]

lemma noFailure_of_probFailure_eq_zero {oa : OracleComp spec α} (h : [⊥ | oa] = 0) :
    neverFails oa := by rwa [← probFailure_eq_zero_iff]

lemma not_noFailure_of_probFailure_pos {oa : OracleComp spec α} (h : 0 < [⊥ | oa]) :
    ¬ neverFails oa := by rwa [← probFailure_pos_iff]

end neverFails

section unit

@[simp]
lemma probOutput_guard {p : Prop} [Decidable p] :
    [= () | (guard p : OracleComp spec _)] = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

@[simp]
lemma probFailure_guard {p : Prop} [Decidable p] :
    [⊥ | (guard p : OracleComp spec _)] = if p then 0 else 1 := by
  by_cases h : p <;> simp [h]

lemma probOutput_eq_sub_probFailure_of_unit {oa : OracleComp spec PUnit} :
    [= () | oa] = 1 - [⊥ | oa] := by
  rw [probFailure_eq_sub_sum, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
  rw [ENNReal.sub_sub_cancel (by simp) (by simp)]

lemma probOutput_guard_eq_sub_probOutput_guard_not {α : Type} {oa : OracleComp spec α}
    (h : oa.neverFails) {p : α → Prop} [DecidablePred p] :
    [= () | do let a ← oa; guard (p a)] = 1 - [= () | do let a ← oa; guard (¬ p a)] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simp
  sorry

end unit

section bool

lemma probOutput_true_eq_probOutput_false_not {ob : OracleComp spec Bool} :
    [= true | ob] = [= false | do let b ← ob; return !b] := by
  simp [probOutput_map_eq_sum_fintype_ite]

lemma probOutput_false_eq_probOutput_true_not {ob : OracleComp spec Bool} :
    [= false | ob] = [= true | do let b ← ob; return !b] := by
  simp [probOutput_true_eq_probOutput_false_not]

end bool

section eqRec

variable (oa : OracleComp spec α) (h : α = β)

lemma probOutput_eqRec (y : β) : [= y | h ▸ oa] = [= h ▸ y | oa] := by induction h; rfl

@[simp] lemma probFailure_eqRec : [⊥ | h ▸ oa] = [⊥ | oa] := by induction h; rfl

lemma probEvent_eqRec (q : β → Prop) :
    [q | h ▸ oa] = [λ x ↦ q (h ▸ x) | oa] := by induction h; rfl

end eqRec

section ite

variable (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)

@[simp]
lemma probOutput_ite (x : α) : [= x | if p then oa else oa'] =
    if p then [= x | oa] else [= x | oa'] := by
  by_cases hp : p <;> simp [hp]

@[simp]
lemma probFailure_ite : [⊥ | if p then oa else oa'] =
    if p then [⊥ | oa] else [⊥ | oa'] := by
  by_cases hp : p <;> simp [hp]

@[simp]
lemma probEvent_ite (q : α → Prop) : [q | if p then oa else oa'] =
    if p then [q | oa] else [q | oa'] := by
  by_cases hp : p <;> simp [hp]

end ite

section coin

@[simp]
lemma probOutput_coin (b : Bool) : [= b | coin] = 2⁻¹ := by
  simp only [coin, probOutput_liftM, Fintype.card_bool, Nat.cast_ofNat]

lemma probEvent_coin_eq_sum_subtype (p : Bool → Prop) :
    [p | coin] = ∑' _ : {x | p x}, 2⁻¹ := by
  simp only [probEvent_eq_tsum_subtype, Set.coe_setOf, Set.mem_setOf_eq, probOutput_coin]

@[simp]
lemma probEvent_coin (p : Bool → Prop) [DecidablePred p] : [p | coin] =
    if p true then (if p false then 1 else 2⁻¹) else (if p false then 2⁻¹ else 0) := by
  by_cases hpt : p true <;> by_cases hpf : p false <;>
    simp [probEvent, tsum_bool, hpt, hpf, inv_two_add_inv_two, PMF.monad_map_eq_map, OptionT.lift]

lemma probEvent_coin_eq_add (p : Bool → Prop) [DecidablePred p] :
    [p | coin] = (if p true then 2⁻¹ else 0) + (if p false then 2⁻¹ else 0) := by
  rw [probEvent_coin]; split_ifs <;> simp [inv_two_add_inv_two, PMF.monad_map_eq_map]

-- /-- The xor of two coin flips looks like flipping a single coin -/
-- example (x : Bool) : [= x | do let b ← coin; let b' ← coin; return xor b b'] = [= x | coin] := by
--   have : (↑2 : ℝ≥0∞) ≠ ∞ := by simp
--   cases x <;> simp [← mul_two, mul_comm (2 : ℝ≥0∞), mul_assoc,
--     ENNReal.inv_mul_cancel two_ne_zero this, probOutput_bind_eq_sum_fintype]
--   ·

end coin

section uniformFin

variable (n : ℕ)

@[simp]
lemma probOutput_uniformFin (x : Fin (n + 1)) : [= x | $[0..n]] = ((n : ℝ≥0∞) + 1)⁻¹ := by
  simp [uniformFin, probOutput_query (spec := unifSpec), OracleSpec.range]

@[simp]
lemma probFailure_uniformFin : [⊥ | $[0..n]] = 0 := probFailure_query _ _

@[simp]
lemma probEvent_uniformFin (p : Fin (n + 1) → Prop) [DecidablePred p] :
    [p | $[0..n]] = (Finset.univ.filter p).card * (n + 1 : ℝ≥0∞)⁻¹ := by
  simp only [probEvent_eq_sum_filter_finSupport, finSupport_uniformFin, probOutput_uniformFin,
    Finset.sum_const, nsmul_eq_mul]

end uniformFin

/-- Example of brute forcing a probability computation by expanding terms and using `ring_nf`. -/
example : [⊥ | do
    let x ←$[0..5]; let y ←$[0..3]
    guard (x = 0); guard (y.val ≠ x.val); return ()] = 21 / 24 := by
  -- would be nice not to need arithmetic facts
  have : (6 : ℝ≥0∞)⁻¹ * (4 : ℝ≥0∞)⁻¹ = (24 : ℝ≥0∞)⁻¹ :=
    by rw [← ENNReal.mul_inv (by tauto) (by tauto)]; ring_nf
  simp [probFailure_bind_eq_sum_fintype, Fin.sum_univ_succ, Fin.succ_ne_zero,
    div_eq_mul_inv, this]
  ring_nf
  rw [this]
  ring_nf

section hoare

variable {ι : Type u} {spec : OracleSpec ι} [spec.FiniteRange] {α β γ δ : Type v}
/-- If pre-condition `P` holds fox `x` then `comp x` satisfies
post-contdition `Q` with probability at least `r`-/
def HoareTriple (P : α → Prop) (comp : α → OracleComp spec β)
    (Q : β → Prop) (r : ℝ≥0∞) : Prop :=
  ∀ x : α, P x → r ≤ [Q | comp x]

notation "⦃" P "⦄ " comp " ⦃" Q "⦄ " r => HoareTriple P comp Q r

def HoareTriple.bind {P : α → Prop} {comp₁ : α → OracleComp spec β}
    {Q : β → Prop} {comp₂ : α → β → OracleComp spec γ} {R : γ → Prop} {r r' : ℝ≥0∞}
    (h1 : ⦃P⦄ comp₁ ⦃Q⦄ r) (h2 : ∀ x, ⦃Q⦄ comp₂ x ⦃R⦄ r') :
        ⦃P⦄ fun x => comp₁ x >>= comp₂ x ⦃R⦄ (r * r') := by
  refine fun x hx => (mul_le_mul_right' (h1 x hx) r').trans ?_
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_indicator, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun y => ?_
  rw [← Set.indicator_mul_const]
  refine Set.indicator_apply_le' ?_ ?_
  · exact fun hy => mul_le_mul_left' (h2 x y hy) [=y|comp₁ x]
  · simp only [zero_le, implies_true]

end hoare

end OracleComp
