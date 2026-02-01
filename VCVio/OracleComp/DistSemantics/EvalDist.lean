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
lemma evalDist_pure (x : α) : evalDist (pure x : OracleComp spec α) = pure x := simulateQ_pure ..

@[simp]
lemma evalDist_liftM [Nonempty α] [Fintype α] (q : OracleQuery spec α) :
    evalDist (q : OracleComp spec α) = OptionT.lift (PMF.uniformOfFintype α) := by
  cases q; simp only [evalDist, simulateQ_query]; convert rfl

@[simp]
lemma evalDist_query (i : ι) (t : spec.domain i) : evalDist (query i t : OracleComp spec _) =
    OptionT.lift (PMF.uniformOfFintype (spec.range i)) := simulateQ_query ..

@[simp]
lemma evalDist_failure : evalDist (failure : OracleComp spec α) = failure := simulateQ_failure _

@[simp]
lemma evalDist_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    evalDist (oa >>= ob) = evalDist oa >>= evalDist ∘ ob := by
  simp [evalDist, Function.comp_def]

lemma evalDist_query_bind (i : ι) (t : spec.domain i) (ou : spec.range i → OracleComp spec α) :
    evalDist ((query i t : OracleComp spec _) >>= ou) =
      (OptionT.lift (PMF.uniformOfFintype (spec.range i))) >>= (evalDist ∘ ou) := by
  simp

@[simp]
lemma evalDist_map (oa : OracleComp spec α) (f : α → β) :
    evalDist (f <$> oa) = f <$> (evalDist oa) := simulateQ_map ..

@[simp]
lemma evalDist_seq (oa : OracleComp spec α) (og : OracleComp spec (α → β)) :
    evalDist (og <*> oa) = evalDist og <*> evalDist oa := simulateQ_seq ..

@[simp]
lemma evalDist_eqRec (h : α = β) (oa : OracleComp spec α) :
    evalDist (h ▸ oa) = h ▸ evalDist oa := by subst h; rfl

@[simp]
lemma evalDist_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    evalDist (if p then oa else oa') = if p then evalDist oa else evalDist oa' :=
  apply_ite evalDist p oa oa'

@[simp]
lemma evalDist_coin : evalDist coin = OptionT.lift (PMF.uniformOfFintype Bool) := by
  simp [coin]

@[simp]
lemma evalDist_uniformFin (n : ℕ) :
    evalDist $[0..n] = OptionT.lift (PMF.uniformOfFintype (Fin (n + 1))) := by
  simp [uniformFin]

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
    [p | oa] = ∑' x, {x | p x}.indicator ([= · | oa]) x := by
  simp [probEvent_def, PMF.toOuterMeasure_apply, Set.indicator_image (Option.some_injective _),
    tsum_option _ ENNReal.summable]

/-- More explicit form of `probEvent_eq_tsum_indicator` when the predicate `p` is decidable. -/
lemma probEvent_eq_tsum_ite (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    [p | oa] = ∑' x, if p x then [= x | oa] else 0 := by
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
    ∑' x, [= x | oa] + [⊥ | oa] = 1 := by rw [add_comm, probFailure_add_tsum_probOutput]

section bounds

variable {oa : OracleComp spec α} {x : α} {p : α → Prop}

@[simp] lemma probOutput_le_one : [= x | oa] ≤ 1 := (evalDist oa).coe_le_one _

@[simp] lemma probFailure_le_one : [⊥ | oa] ≤ 1 := PMF.coe_le_one (evalDist oa) none

@[simp] lemma tsum_probOutput_le_one : ∑' x : α, [= x | oa] ≤ 1 :=
  le_add_self.trans_eq (probFailure_add_tsum_probOutput oa)

@[simp] lemma tsum_probOutput_ne_top : ∑' x : α, [= x | oa] ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one

@[simp] lemma probEvent_le_one : [p | oa] ≤ 1 := by
  rw [probEvent_def, PMF.toOuterMeasure_apply]
  grw [← oa.evalDist.tsum_coe]
  exact ENNReal.tsum_le_tsum (Set.indicator_le_self (some '' {x | p x}) _)

@[simp] lemma probOutput_ne_top : [= x | oa] ≠ ∞ := PMF.apply_ne_top (evalDist oa) x

@[simp] lemma probOutput_lt_top : [= x | oa] < ∞ := PMF.apply_lt_top ..

@[simp] lemma not_one_lt_probOutput : ¬ 1 < [= x | oa] := probOutput_le_one.not_gt

@[simp] lemma probEvent_ne_top : [p | oa] ≠ ∞ := ne_top_of_le_ne_top one_ne_top probEvent_le_one

@[simp] lemma probEvent_lt_top : [p | oa] < ∞ := probEvent_ne_top.lt_top

@[simp] lemma not_one_lt_probEvent : ¬ 1 < [p | oa] := probEvent_le_one.not_gt

@[simp] lemma probFailure_ne_top : [⊥ | oa] ≠ ∞ := (evalDist oa).apply_ne_top none

@[simp] lemma probFailure_lt_top : [⊥ | oa] < ∞ := probFailure_ne_top.lt_top

@[simp] lemma not_one_lt_probFailure : ¬ 1 < [⊥ | oa] := not_lt.2 probFailure_le_one

@[simp] lemma one_le_probOutput_iff : 1 ≤ [= x | oa] ↔ [= x | oa] = 1 :=
  probOutput_le_one.ge_iff_eq'.trans eq_comm

@[simp] lemma one_le_probEvent_iff : 1 ≤ [p | oa] ↔ [p | oa] = 1 :=
  ⟨le_antisymm probEvent_le_one, le_of_eq ∘ Eq.symm⟩

@[simp] lemma one_le_probFailure_iff : 1 ≤ [⊥ | oa] ↔ [⊥ | oa] = 1 := by
  simp only [le_iff_eq_or_lt, not_one_lt_probFailure, or_false, eq_comm]

end bounds

lemma tsum_probOutput_eq_sub (oa : OracleComp spec α) :
    ∑' x : α, [= x | oa] = 1 - [⊥ | oa] :=
  ENNReal.eq_sub_of_add_eq probFailure_ne_top (tsum_probOutput_add_probFailure oa)

lemma sum_probOutput_eq_sub [Fintype α] (oa : OracleComp spec α) :
    ∑ x : α, [= x | oa] = 1 - [⊥ | oa] :=
  tsum_fintype ([= · | oa]) ▸ tsum_probOutput_eq_sub oa

lemma probFailure_eq_sub_tsum (oa : OracleComp spec α) :
    [⊥ | oa] = 1 - ∑' x : α, [= x | oa] :=
  ENNReal.eq_sub_of_add_eq tsum_probOutput_ne_top (probFailure_add_tsum_probOutput oa)

lemma probFailure_eq_sub_sum [Fintype α] (oa : OracleComp spec α) :
    [⊥ | oa] = 1 - ∑ x : α, [= x | oa] := tsum_fintype ([= · | oa]) ▸ probFailure_eq_sub_tsum oa

lemma tsum_probOutput_eq_one (oa : OracleComp spec α) (h : [⊥|oa] = 0) :
    ∑' x : α, [= x | oa] = 1 := by simp [tsum_probOutput_eq_sub, h]

lemma sum_probOutput_eq_one [Fintype α] (oa : OracleComp spec α) (h : [⊥|oa] = 0) :
    ∑ x : α, [= x | oa] = 1 := by
  simp only [sum_probOutput_eq_sub, h, tsub_zero]

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
    some x ∈ (evalDist oa).run.support ↔ x ∈ oa.finSupport :=
  (mem_support_evalDist_iff oa x).trans (mem_finSupport_iff_mem_support oa x).symm

alias ⟨mem_finSupport_of_mem_support_evalDist, mem_support_evalDist'⟩ := mem_support_evalDist_iff'

@[simp]
lemma evalDist_apply_eq_zero_iff (x : Option α) :
    (evalDist oa).run x = 0 ↔ x.rec ([⊥ | oa] = 0) (· ∉ oa.support) := by
  cases x <;> simp [probFailure_def, ← mem_support_evalDist_iff]

@[simp]
lemma evalDist_apply_eq_zero_iff' [spec.DecidableEq] [DecidableEq α] (x : Option α) :
    (evalDist oa).run x = 0 ↔ x.rec ([⊥ | oa] = 0) (· ∉ oa.finSupport) := by
  simp only [evalDist_apply_eq_zero_iff, mem_finSupport_iff_mem_support]

/-- The support of `evalDist oa` is exactly `support oa`. -/
lemma support_evalDist : (evalDist oa).run.support = if [⊥ | oa] = 0 then
    some '' oa.support else insert none (some '' oa.support) := by
  rw [probFailure_def]; ext x; cases x <;> split_ifs <;> simp [*]

lemma support_evalDist' [spec.DecidableEq] [DecidableEq α] :
    (evalDist oa).run.support = if [⊥ | oa] = 0 then
      oa.finSupport.image some else insert none (oa.finSupport.image some) := by
  rw [support_evalDist]; split_ifs <;> simp [coe_finSupport]

@[simp low]
lemma probOutput_eq_zero_iff : [= x | oa] = 0 ↔ x ∉ oa.support := by
  rw [probOutput, PMF.apply_eq_zero_iff, mem_support_evalDist_iff]

alias ⟨not_mem_support_of_probOutput_eq_zero, probOutput_eq_zero⟩ := probOutput_eq_zero_iff

@[simp low]
lemma zero_eq_probOutput_iff : 0 = [= x | oa] ↔ x ∉ oa.support :=
  eq_comm.trans (probOutput_eq_zero_iff oa x)

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
  probOutput_ne_zero _ _ (mem_support_of_mem_finSupport _ h)

@[simp low]
lemma probEvent_eq_zero_iff : [p | oa] = 0 ↔ ∀ x ∈ oa.support, ¬ p x := by
  simp only [probEvent_def, PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_iff_forall_ne,
    mem_support_evalDist_iff, Set.mem_image, Set.mem_setOf_eq, Option.forall]
  grind

alias ⟨not_of_mem_support_of_probEvent_eq_zero, probEvent_eq_zero⟩ := probEvent_eq_zero_iff

@[simp low]
lemma zero_eq_probEvent_iff : 0 = [p | oa] ↔ ∀ x ∈ oa.support, ¬ p x :=
  eq_comm.trans (probEvent_eq_zero_iff oa p)

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
lemma probOutput_pos_iff : 0 < [= x | oa] ↔ x ∈ oa.support := by simp [pos_iff_ne_zero]

alias ⟨mem_support_of_probOutput_pos, probOutput_pos⟩ := probOutput_pos_iff

@[simp]
lemma probOutput_pos_iff' [spec.DecidableEq] [DecidableEq α] :
    0 < [= x | oa] ↔ x ∈ oa.finSupport :=
  (probOutput_pos_iff ..).trans (mem_finSupport_iff_mem_support ..).symm

alias ⟨mem_finSupport_of_probOutput_pos, probOutput_pos'⟩ := probOutput_pos_iff'

@[simp low]
lemma probEvent_pos_iff : 0 < [p | oa] ↔ ∃ x ∈ oa.support, p x := by
  simp only [pos_iff_ne_zero, ne_eq, probEvent_eq_zero_iff, not_forall, not_not, exists_prop]

alias ⟨exists_mem_support_of_probEvent_pos, probEvent_pos⟩ := probEvent_pos_iff

@[simp]
lemma probEvent_pos_iff' [spec.DecidableEq] [DecidableEq α] :
    0 < [p | oa] ↔ ∃ x ∈ oa.finSupport, p x := by
  simp only [probEvent_pos_iff, mem_finSupport_iff_mem_support]

alias ⟨exists_mem_finSupport_of_probEvent_pos, probEvent_pos'⟩ := probEvent_pos_iff'

@[simp low]
lemma probOutput_eq_one_iff : [= x | oa] = 1 ↔ [⊥ | oa] = 0 ∧ oa.support = {x} := by
  simp [probOutput_def, PMF.apply_eq_one_iff, Set.ext_iff, Option.forall]

alias ⟨_, probOutput_eq_one⟩ := probOutput_eq_one_iff

@[simp low]
lemma one_eq_probOutput_iff : 1 = [= x | oa] ↔ [⊥ | oa] = 0 ∧ oa.support = {x} :=
  eq_comm.trans (probOutput_eq_one_iff oa x)

alias ⟨_, one_eq_probOutput⟩ := one_eq_probOutput_iff

@[simp]
lemma probOutput_eq_one_iff' [spec.DecidableEq] [DecidableEq α] :
    [= x | oa] = 1 ↔ [⊥ | oa] = 0 ∧ oa.finSupport = {x} := by
  rw [probOutput_eq_one_iff, finSupport_eq_iff_support_eq_coe, Finset.coe_singleton]

alias ⟨_, probOutput_eq_one'⟩ := probOutput_eq_one_iff'

@[simp]
lemma one_eq_probOutput_iff' [spec.DecidableEq] [DecidableEq α] :
    1 = [= x | oa] ↔ [⊥ | oa] = 0 ∧ oa.finSupport = {x} :=
  eq_comm.trans (probOutput_eq_one_iff' _ _)

alias ⟨_, one_eq_probOutput'⟩ := one_eq_probOutput_iff'

@[simp low]
lemma probEvent_eq_one_iff : [p | oa] = 1 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x := by
  simp only [probEvent, PMF.toOuterMeasure_apply_eq_one_iff, support_evalDist]
  split_ifs with hoa
  · simp [hoa, Set.subset_def]
  · simpa [hoa] using fun h ↦ absurd (h (Set.mem_insert none _)) nofun

alias ⟨_, probEvent_eq_one⟩ := probEvent_eq_one_iff

@[simp low]
lemma one_eq_probEvent_iff : 1 = [p | oa] ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, p x :=
  eq_comm.trans (probEvent_eq_one_iff oa p)

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

lemma mem_support_iff_probOutput_ne_zero : x ∈ oa.support ↔ [= x | oa] ≠ 0 :=
  (probOutput_pos_iff ..).symm.trans pos_iff_ne_zero

lemma mem_finSupport_iff_probOutput_ne_zero [spec.DecidableEq] [DecidableEq α] :
    x ∈ oa.finSupport ↔ [= x | oa] ≠ 0 :=
  (mem_finSupport_iff_mem_support ..).trans (mem_support_iff_probOutput_ne_zero ..)

lemma mem_support_iff_probOutput_pos : x ∈ oa.support ↔ 0 < [= x | oa] :=
  (probOutput_pos_iff oa x).symm

lemma not_mem_support_iff_probOutput_eq_zero : x ∉ oa.support ↔ [= x | oa] = 0 :=
  (probOutput_eq_zero_iff oa x).symm

variable {oa x p q}

/-- If `p` implies `q` on the `support` of a computation then it is more likely to happen. -/
lemma probEvent_mono (h : ∀ x ∈ oa.support, p x → q x) : [p | oa] ≤ [q | oa] :=
  PMF.toOuterMeasure_mono _ fun | some _, hx => by simp_all

/-- If `p` implies `q` on the `finSupport` of a computation then it is more likely to happen. -/
lemma probEvent_mono' [spec.DecidableEq] [DecidableEq α]
    (h : ∀ x ∈ oa.finSupport, p x → q x) : [p | oa] ≤ [q | oa] :=
  probEvent_mono fun x hx hpx ↦ h x (mem_finSupport_of_mem_support _ hx) hpx

-- NOTE: should allow `p` and `q` to differ outside the shared support.
lemma probEvent_congr {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : ∀ x, p x ↔ q x) (h2 : evalDist oa = evalDist oa') : [p | oa] = [q | oa'] := by
  simp only [probEvent, h1, h2]

lemma probEvent_ext (h : ∀ x ∈ oa.support, p x ↔ q x) : [p | oa] = [q | oa] :=
  le_antisymm (probEvent_mono fun x hx ↦ (h x hx).1) (probEvent_mono fun x hx ↦ (h x hx).2)

lemma probEvent_ext' [spec.DecidableEq] [DecidableEq α]
    (h : ∀ x ∈ oa.finSupport, p x ↔ q x) : [p | oa] = [q | oa] :=
  le_antisymm (probEvent_mono' fun x hx ↦ (h x hx).1)
    (probEvent_mono' fun x hx ↦ (h x hx).2)

@[simp]
lemma function_support_probOutput : Function.support ([= · | oa]) = oa.support := by
  simp [Function.support]

lemma mem_support_iff_of_evalDist_eq {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : evalDist oa = evalDist oa') (x : α) : x ∈ oa.support ↔ x ∈ oa'.support := by
  simp only [← mem_support_evalDist_iff, h]

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
  (probEvent_ext (fun _ _ ↦ eq_comm)).trans (probEvent_eq_eq_probOutput oa x)

section sums

variable (oa : OracleComp spec α) (p : α → Prop)

/-- The probability of an event written as a sum over the set `{x | p x}` viewed as a subtype.
This notably doesn't require decidability of the predicate `p` unlike many other lemmas. -/
lemma probEvent_eq_tsum_subtype : [p | oa] = ∑' x : {x | p x}, [= x | oa] := by
  simp only [probEvent_eq_tsum_indicator, tsum_subtype]

/-- Version `probEvent_eq_tsum_subtype` that preemptively filters out elements that
aren't in the support, since they will have no mass contribution anyways.
This can make some proofs simpler by handling things on the level of subtypes. -/
lemma probEvent_eq_tsum_subtype_mem_support :
    [p | oa] = ∑' x : {x ∈ oa.support | p x}, [= x | oa] := by
  simp_rw [probEvent_eq_tsum_subtype, tsum_subtype, Set.setOf_and, Set.inter_comm,
    Set.setOf_mem_eq, ← function_support_probOutput, Set.indicator_inter_support]

lemma probEvent_eq_tsum_subtype_support_ite [DecidablePred p] :
    [p | oa] = ∑' x : oa.support, if p x then [= x | oa] else 0 := by
  rw [probEvent_eq_tsum_ite, ← tsum_subtype_eq_of_support_subset]
  intro x; simp only [Function.mem_support]; split_ifs <;> simp_all

lemma probEvent_eq_sum_fintype_indicator [Fintype α] (oa : OracleComp spec α) (p : α → Prop) :
    [p | oa] = ∑ x : α, {x | p x}.indicator ([= · | oa]) x :=
  (probEvent_eq_tsum_indicator oa p).trans (tsum_fintype _)

lemma probEvent_eq_sum_fintype_ite [DecidablePred p] [Fintype α] :
    [p | oa] = ∑ x : α, if p x then [= x | oa] else 0 :=
  (probEvent_eq_tsum_ite oa p).trans (tsum_fintype _)

lemma probEvent_eq_sum_filter_univ [DecidablePred p] [Fintype α] :
    [p | oa] = ∑ x ∈ Finset.univ.filter p, [= x | oa] := by
  simp [probEvent_eq_sum_fintype_ite, Finset.sum_filter]

lemma probEvent_eq_sum_filter_finSupport [spec.DecidableEq] [DecidablePred p] [DecidableEq α] :
    [p | oa] = ∑ x ∈ oa.finSupport.filter p, [= x | oa] :=
  (probEvent_eq_tsum_ite oa p).trans <|
    (tsum_eq_sum' <| by simp; tauto).trans
      (Finset.sum_ite_of_true (fun x hx ↦ (Finset.mem_filter.1 hx).2) ..)

lemma probEvent_eq_sum_finSupport_ite [spec.DecidableEq] [DecidablePred p] [DecidableEq α] :
    [p | oa] = ∑ x ∈ oa.finSupport, if p x then [= x | oa] else 0 := by
  simp only [probEvent_eq_sum_filter_finSupport, Finset.sum_filter]

end sums

lemma probOutput_congr {x y : α} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : x = y) (h2 : evalDist oa = evalDist oa') : [= x | oa] = [= y | oa'] := by
  simp only [probOutput, h1, h2]

lemma probEvent_congr' {p q : α → Prop} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : ∀ x, x ∈ oa.support → x ∈ oa'.support → (p x ↔ q x))
    (h2 : evalDist oa = evalDist oa') : [p | oa] = [q | oa'] := by
  rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator]
  refine tsum_congr fun x ↦ ?_
  simp only [Set.indicator, Set.mem_setOf_eq, probOutput_congr rfl h2,
      mem_support_iff_of_evalDist_eq h2] at h1 ⊢
  by_cases hp : p x <;> by_cases hq : q x <;>
    simp only [hp, hq, ↓reduceIte, probOutput_eq_zero_iff, zero_eq_probOutput_iff] <;> grind

@[simp] lemma probEvent_const (oa : OracleComp spec α) (p : Prop) [Decidable p] :
    [fun _ ↦ p | oa] = if p then 1 - [⊥ | oa] else 0 := by
  rw [probEvent_eq_tsum_ite]
  split_ifs <;> simp only [tsum_probOutput_eq_sub, tsum_zero]

lemma probEvent_true (oa : OracleComp spec α) : [fun _ ↦ true | oa] = 1 - [⊥ | oa] := by simp

lemma probEvent_false (oa : OracleComp spec α) : [fun _ ↦ false | oa] = 0 := by simp

lemma probFailure_eq_sub_probEvent (oa : OracleComp spec α) :
    [⊥ | oa] = 1 - [fun _ ↦ true | oa] :=
  probEvent_true oa ▸ (ENNReal.sub_sub_cancel one_ne_top probFailure_le_one).symm

lemma evalDist_ext_probEvent {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : ∀ x, [=x|oa] = [=x|oa']) : (evalDist oa).run = (evalDist oa').run :=
  PMF.ext fun x ↦ match x with
  | none => by simp [← probFailure_def, probFailure_eq_sub_tsum, h]
  | some x => h x

section pure

variable (x : α)

@[simp]
lemma probOutput_pure [DecidableEq α] (y : α) :
    [= y | (pure x : OracleComp spec α)] = if y = x then 1 else 0 := by
  simp [probOutput]

@[simp]
lemma probFailure_pure : [⊥ | (pure x : OracleComp spec α)] = 0 := by simp [probFailure]

lemma probOutput_pure_eq_zero {x y : α} (h : y ≠ x) :
    [= y | (pure x : OracleComp spec α)] = 0 := by simp [h]

lemma probOutput_pure_eq_one {x y : α} (h : y = x) :
    [= y | (pure x : OracleComp spec α)] = 1 := by simp [h]

@[simp]
lemma probOutput_pure_self (x : α) : [= x | (pure x : OracleComp spec α)] = 1 :=
  probOutput_pure_eq_one rfl

@[simp]
lemma probOutput_pure_subsingleton [Subsingleton α] (x y : α) :
    [= x | (pure y : OracleComp spec α)] = 1 :=
  Subsingleton.elim x y ▸ probOutput_pure_self y

@[simp]
lemma probEvent_pure (p : α → Prop) [DecidablePred p] :
    [p | (pure x : OracleComp spec α)] = if p x then 1 else 0 := by
  rw [probEvent_eq_tsum_ite, tsum_eq_single x fun _ h ↦ by simp [h]]
  simp

lemma probEvent_pure_eq_zero {p : α → Prop} {x : α} (h : ¬ p x) :
    [p | (pure x : OracleComp spec α)] = 0 := by simpa

lemma probEvent_pure_eq_one {p : α → Prop} {x : α} (h : p x) :
    [p | (pure x : OracleComp spec α)] = 1 := by simpa

end pure

section bind

variable (oa : OracleComp spec α) (ob : α → OracleComp spec β)

lemma probOutput_bind_eq_tsum (y : β) :
    [= y | oa >>= ob] = ∑' x : α, [= x | oa] * [= y | ob x] := by
  simp [probOutput, tsum_option _ ENNReal.summable, elimM]

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
  rw [tsum_subtype _ (fun x ↦ [= x | oa] * [= y | ob x]), probOutput_bind_eq_tsum,
    Set.indicator_eq_self.mpr ((Function.support_mul_subset_left _ _).trans
      function_support_probOutput.subset)]

lemma probEvent_bind_eq_tsum_subtype (q : β → Prop) :
    [q | oa >>= ob] = ∑' x : oa.support, [= x | oa] * [q | ob x] := by
  rw [tsum_subtype _ (fun x ↦ [= x | oa] * [q | ob x]), probEvent_bind_eq_tsum]
  exact tsum_congr fun _ ↦ by simp only [Set.indicator]; split_ifs <;> simp_all

lemma probOutput_bind_eq_sum_fintype [Fintype α] (y : β) :
    [= y | oa >>= ob] = ∑ x : α, [= x | oa] * [= y | ob x] :=
  (probOutput_bind_eq_tsum ..).trans (tsum_fintype _)

lemma probFailure_bind_eq_sum_fintype [Fintype α] :
    [⊥ | oa >>= ob] = [⊥ | oa] + ∑ x : α, [= x | oa] * [⊥ | ob x] :=
  (probFailure_bind_eq_tsum oa ob).trans <| congr_arg ([⊥ | oa] + ·) <| tsum_fintype _

lemma probEvent_bind_eq_sum_fintype [Fintype α] (q : β → Prop) :
    [q | oa >>= ob] = ∑ x : α, [= x | oa] * [q | ob x] :=
  (probEvent_bind_eq_tsum ..).trans (tsum_fintype _)

lemma probOutput_bind_eq_sum_finSupport [spec.DecidableEq] [DecidableEq α] (y : β) :
    [= y | oa >>= ob] = ∑ x ∈ oa.finSupport, [= x | oa] * [= y | ob x] :=
  (probOutput_bind_eq_tsum oa ob y).trans (tsum_eq_sum' <| by simp)

lemma probEvent_bind_eq_sum_finSupport [spec.DecidableEq] [DecidableEq α] (q : β → Prop) :
    [q | oa >>= ob] = ∑ x ∈ oa.finSupport, [= x | oa] * [q | ob x] :=
  (probEvent_bind_eq_tsum oa ob q).trans (tsum_eq_sum' <| by simp)

lemma probOutput_bind_of_const (y : β) (r : ℝ≥0∞) (h : ∀ x, [=y|ob x] = r) :
    [= y | oa >>= ob] = (1 - [⊥ | oa]) * r := by
  simp [probOutput_bind_eq_tsum, h, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]

lemma probFailure_bind_of_const [Nonempty α] (r : ℝ≥0∞) (h : ∀ x, [⊥|ob x] = r) :
    [⊥ | oa >>= ob] = [⊥ | oa] + r - [⊥ | oa] * r := by
  have : r ≠ ⊤ := (h (Classical.arbitrary α)).symm ▸ probFailure_ne_top
  simp only [probFailure_bind_eq_tsum, h, ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]
  rw [ENNReal.sub_mul fun _ _ ↦ this, one_mul]
  exact (ENNReal.addLECancellable_iff_ne.2 <| ENNReal.mul_ne_top probFailure_ne_top this)
    |>.add_tsub_assoc_of_le (mul_le_of_le_one_left' probFailure_le_one) _ |>.symm

lemma probFailure_bind_eq_sub_mul {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    (r : ℝ≥0∞) (h : ∀ x, [⊥|ob x] = r) :
    [⊥ | oa >>= ob] = 1 - (1 - [⊥ | oa]) * (1 - r) := by
  rw [probFailure_bind_eq_tsum, ← tsum_probOutput_eq_sub, ← ENNReal.tsum_mul_right]
  have hl : ∀ x, [=x|oa] * [⊥|ob x] ≤ [=x|oa] :=
    fun x ↦ (mul_le_mul' le_rfl probFailure_le_one).trans_eq (mul_one _)
  calc [⊥ | oa] + ∑' x, [= x | oa] * [⊥ | ob x]
    _ = 1 - (∑' x, [= x | oa]) + (∑' x, [= x | oa] * [⊥ | ob x]) :=
      congrArg (· + _) (probFailure_eq_sub_tsum oa)
    _ = 1 - (∑' x, [= x | oa] - ∑' x, [= x | oa] * [⊥ | ob x]) :=
      (AddLECancellable.tsub_tsub_assoc
        (by simp) tsum_probOutput_le_one (ENNReal.tsum_le_tsum hl)).symm
    _ = 1 - ∑' x, ([= x | oa] - [= x | oa] * [⊥ | ob x]) :=
      congr_arg (1 - ·) <| (ENNReal.eq_sub_of_add_eq
        (ne_top_of_le_ne_top one_ne_top <|
          (ENNReal.tsum_le_tsum hl).trans (@tsum_probOutput_le_one _ _ _ _ oa))
        (ENNReal.tsum_add ▸ tsum_congr fun x ↦ tsub_add_cancel_of_le (hl x))).symm
    _ = 1 - ∑' x : α, [= x | oa] * (1 - r) := congr_arg (1 - ·) <| tsum_congr fun x ↦ by
      rw [ENNReal.mul_sub (fun _ _ ↦ probOutput_ne_top), mul_one, ← h x]

lemma probFailure_bind_le_of_forall {oa : OracleComp spec α} {s : ℝ≥0∞}
    -- TODO: this should be a general type of `uniformOutput` computations
    (h' : [⊥|oa] = s) (ob : α → OracleComp spec β) {r : ℝ≥0∞}
    (hr : ∀ x ∈ oa.support, [⊥|ob x] ≤ r) : [⊥|oa >>= ob] ≤ s + (1 - s) * r := by
  convert (probFailure_bind_eq_tsum oa ob).le.trans _ using 1
  rw [mul_comm, ← h', ← tsum_probOutput_eq_sub oa, ← ENNReal.tsum_mul_left]
  refine add_le_add_left (ENNReal.tsum_le_tsum fun x ↦ ?_) ?_
  by_cases hx : x ∈ oa.support
  · rw [mul_comm]; gcongr; grind
  · simp [probOutput_eq_zero' oa x hx]

/-- Version of `probFailure_bind_le_of_forall` with the `1 - s` factor ommited for convenience. -/
lemma probFailure_bind_le_of_forall' {oa : OracleComp spec α} {s : ℝ≥0∞}
    -- TODO: this should be a general type of `uniformOutput` computations
    (h' : [⊥|oa] = s) (ob : α → OracleComp spec β) {r : ℝ≥0∞}
    (hr : ∀ x ∈ oa.support, [⊥|ob x] ≤ r) : [⊥|oa >>= ob] ≤ s + r :=
  calc [⊥|oa >>= ob] ≤ s + (1 - s) * r := probFailure_bind_le_of_forall h' ob hr
    _ ≤ s + r := add_le_add_left (mul_le_of_le_one_left' tsub_le_self) _

/- Version of `probFailure_bind_le_of_forall` when `oa` never fails. -/

/-
If a computation never fails, its probability of failure is 0.
-/
lemma probFailure_eq_zero_of_neverFails {ι : Type u} {spec : OracleSpec ι} {α : Type w}
    [OracleSpec.FiniteRange spec] {oa : OracleComp spec α} (h : neverFails oa) :
    probFailure oa = 0 := by
  induction' oa using OracleComp.inductionOn with i t oa ihop
  · exact probFailure_pure i
  · simp_all only [probFailure_bind_eq_tsum, neverFails_query_bind_iff, mul_zero,
      tsum_zero, add_zero]
    simp [probFailure, OptionT.run_lift]
  · simp_all [neverFails]

lemma probFailure_bind_le_of_le_of_neverFails {oa : OracleComp spec α}
    (h' : oa.neverFails) {ob : α → OracleComp spec β} {r : ℝ≥0∞}
    (hr : ∀ x ∈ oa.support, [⊥|ob x] ≤ r) : [⊥|oa >>= ob] ≤ r := by
  simpa [OracleComp.probFailure_eq_zero_of_neverFails h'] using
    probFailure_bind_le_of_forall' rfl ob hr

lemma probFailure_eq_zero_iff_neverFails {ι : Type _} {spec : OracleSpec ι} {α : Type _}
    [spec.FiniteRange] (oa : OracleComp spec α) :
    probFailure oa = 0 ↔ neverFails oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [neverFails_pure]
  | query_bind i t ob ih =>
    have h_ih : ∀ x, (ob x).neverFails ↔ (ob x).probFailure = 0 := fun x ↦ (ih x).symm
    simp [← h_ih, probFailure_bind_eq_tsum]
    simp [probFailure, OptionT.lift]
  | failure => simp [neverFails, probFailure]

lemma probFailure_bind_of_neverFails {oa : OracleComp spec α}
    (h : neverFails oa) (ob : α → OracleComp spec β) :
    [⊥ | oa >>= ob] = ∑' x : α, [= x | oa] * [⊥ | ob x] := by
  rw [probFailure_bind_eq_tsum, (probFailure_eq_zero_iff_neverFails oa).mpr h, zero_add]

end bind

section mul_le_probEvent_bind

lemma mul_le_probEvent_bind {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {p : α → Prop} {q : β → Prop} {r r' : ℝ≥0∞}
    (h : r ≤ [p|oa]) (h' : ∀ x ∈ oa.support, p x → r' ≤ [q|ob x]) :
    r * r' ≤ [q|oa >>= ob] := by
  rw [probEvent_bind_eq_tsum]
  refine (mul_le_mul_right' h r').trans ?_
  rw [probEvent_eq_tsum_indicator, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  rw [← Set.indicator_mul_const]
  refine Set.indicator_apply_le (g := fun x ↦ [=x|oa] * [q|ob x]) fun hpx ↦ ?_
  by_cases hx : x ∈ oa.support
  · exact mul_le_mul_left' (h' x hx hpx) _
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
  simp only [probOutput, evalDist_liftM, OptionT.lift, PMF.monad_pure_eq_pure,
    PMF.monad_bind_eq_bind, OptionT.run_mk, PMF.bind_apply, PMF.uniformOfFintype_apply,
    PMF.pure_apply, some.injEq, mul_ite, mul_one, mul_zero]
  refine (tsum_eq_single u ?_).trans ?_ <;> grind

lemma probOutput_query (u : spec.range i) :
    [= u | (query i t : OracleComp spec _)] = (Fintype.card (spec.range i) : ℝ≥0∞)⁻¹ :=
  probOutput_liftM (query i t) u

@[simp]
lemma probFailure_liftM (q : OracleQuery spec α) :
    [⊥ | (q : OracleComp spec _)] = 0 := by
  have : Fintype α := q.rangeFintype
  have : Inhabited α := q.rangeInhabited
  simp only [probFailure, evalDist_liftM]
  erw [PMF.bind_apply]
  simp [PMF.uniformOfFintype_apply, PMF.pure_apply]

lemma probFailure_query : [⊥ | (query i t : OracleComp spec _)] = 0 := probFailure_liftM ..

@[simp]
lemma probEvent_liftM_eq_mul_inv [Fintype α] (q : OracleQuery spec α)
    (p : α → Prop) [DecidablePred p] : [p | (q : OracleComp spec _)] =
      (Finset.univ.filter p).card * (↑(Fintype.card α))⁻¹ := by
  simp [probEvent_eq_sum_fintype_ite]

lemma probEvent_query_eq_mul_inv (p : spec.range i → Prop) [DecidablePred p] :
    [p | (query i t : OracleComp spec _)] =
      (Finset.univ.filter p).card * (↑(Fintype.card (spec.range i)))⁻¹ :=
  probEvent_liftM_eq_mul_inv ..

lemma probEvent_liftM_eq_inv_mul [Fintype α] (q : OracleQuery spec α)
    (p : α → Prop) [DecidablePred p] : [p | (q : OracleComp spec _)] =
      (↑(Fintype.card α))⁻¹ * (Finset.univ.filter p).card :=
  (probEvent_liftM_eq_mul_inv q p).trans (mul_comm _ _)

lemma probEvent_query_eq_inv_mul [spec.DecidableEq] (p : spec.range i → Prop) [DecidablePred p] :
    [p | (query i t : OracleComp spec _)] =
      (↑(Fintype.card (spec.range i)))⁻¹ * (Finset.univ.filter p).card := by
  rw [probEvent_query_eq_mul_inv, mul_comm]

lemma probEvent_liftM_eq_div [Fintype α] (q : OracleQuery spec α)
    (p : α → Prop) [DecidablePred p] : [p | (q : OracleComp spec _)] =
      (Finset.univ.filter p).card / (Fintype.card α) := by
  simp only [div_eq_mul_inv, probEvent_liftM_eq_mul_inv]

lemma probEvent_query_eq_div [spec.DecidableEq] (p : spec.range i → Prop) [DecidablePred p] :
    [p | (query i t : OracleComp spec _)] =
      (Finset.univ.filter p).card / (Fintype.card (spec.range i)) :=
  probEvent_liftM_eq_div ..

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
  simp only [map_eq_bind_pure_comp, tsum_subtype _ (fun x ↦ [= x | oa]), probOutput_bind_eq_tsum,
    Function.comp_apply, Set.indicator, Set.mem_setOf_eq]
  refine tsum_congr fun x ↦ ?_
  split_ifs <;> simp [*]; tauto

lemma probOutput_map_eq_tsum (y : β) :
    [= y | f <$> oa] = ∑' x, [= x | oa] * [= y | (pure (f x) : OracleComp spec β)] := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply]

lemma probOutput_map_eq_tsum_subtype_ite [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑' x : oa.support, if y = f x then [= x | oa] else 0 := by
  simp [map_eq_bind_pure_comp, probOutput_bind_eq_tsum_subtype]

lemma probOutput_map_eq_tsum_ite [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑' x : α, if y = f x then [= x | oa] else 0 := by
  simp only [probOutput_map_eq_tsum, probOutput_pure, mul_ite, mul_one, mul_zero]

lemma probOutput_map_eq_sum_fintype_ite [Fintype α] [DecidableEq β] (y : β) :
    [= y | f <$> oa] = ∑ x : α, if y = f x then [= x | oa] else 0 :=
  (probOutput_map_eq_tsum_ite oa f y).trans (tsum_eq_sum' fun _ _ ↦ Finset.mem_univ _)

lemma probOutput_map_eq_sum_finSupport_ite [spec.DecidableEq] [DecidableEq α] [DecidableEq β]
    (y : β) : [= y | f <$> oa] = ∑ x ∈ oa.finSupport, if y = f x then [= x | oa] else 0 :=
  (probOutput_map_eq_tsum_ite oa f y).trans
    (tsum_eq_sum' <| by simp [mem_finSupport_iff_mem_support])

lemma probOutput_map_eq_sum_filter_finSupport [spec.DecidableEq] [DecidableEq α] [DecidableEq β]
    (y : β) : [= y | f <$> oa] = ∑ x ∈ oa.finSupport.filter (y = f ·), [= x | oa] := by
  simp only [Finset.sum_filter, probOutput_map_eq_sum_finSupport_ite]

@[simp]
lemma probFailure_map : [⊥ | f <$> oa] = [⊥ | oa] := by
  simp only [probFailure, evalDist_map, OptionT.run_map, PMF.monad_map_eq_map, PMF.map_apply]
  exact (tsum_eq_single none fun x hx ↦ by cases x <;> grind).trans (if_pos rfl)

@[simp]
lemma probEvent_map (q : β → Prop) : [q | f <$> oa] = [q ∘ f | oa] := by
  simp only [probEvent, evalDist_map, Function.comp_apply, OptionT.run_map,
    PMF.monad_map_eq_map, PMF.toOuterMeasure_map_apply]
  congr 1 with x; cases x <;> grind

lemma probEvent_comp (q : β → Prop) : [q ∘ f | oa] = [q | f <$> oa] :=
  (probEvent_map oa f q).symm

lemma probOutput_map_eq_probOutput_inverse (f : α → β) (g : β → α)
    (hl : Function.LeftInverse f g) (hr : Function.RightInverse f g)
    (y : β) : [= y | f <$> oa] = [= g y | oa] := by
  rw [probOutput_map_eq_tsum]
  refine (tsum_eq_single (g y) (fun x hx ↦ ?_)).trans ?_
  · suffices y ≠ f x by simp [this]
    exact fun h ↦ hx <| (congrArg g h).trans (hr x) |>.symm
  · simp [hl y]

lemma probFailure_eq_sub_sum_probOutput_map [Fintype β] (oa : OracleComp spec α) (f : α → β) :
    [⊥ | oa] = 1 - ∑ y : β, [= y | f <$> oa] := by
  rw [← probFailure_map (f := f), probFailure_eq_sub_sum]

end map

section neverFails

-- TODO: expand api and include `mayFail` versions for `probFailure_pos`.

@[simp]
lemma probFailure_eq_zero_iff (oa : OracleComp spec α) : [⊥ | oa] = 0 ↔ oa.neverFails := by
  induction' oa using OracleComp.inductionOn with x p q t f a ih
  · aesop
  · simp +decide [neverFails_bind_iff, probFailure_bind_eq_tsum]
    aesop
  · simp +decide [neverFails]

@[simp]
lemma probFailure_pos_iff (oa : OracleComp spec α) : 0 < [⊥ | oa] ↔ ¬ oa.neverFails := by
  simp only [zero_lt_iff, ne_eq, probFailure_eq_zero_iff]

lemma noFailure_of_probFailure_eq_zero {oa : OracleComp spec α} (h : [⊥|oa] = 0) :
    neverFails oa := (probFailure_eq_zero_iff _).mp h

lemma not_noFailure_of_probFailure_pos {oa : OracleComp spec α} (h : 0 < [⊥|oa]) :
    ¬ neverFails oa := (probFailure_pos_iff _).1 h

end neverFails

section unit

@[simp]
lemma probOutput_guard {p : Prop} [Decidable p] :
    [= () | (guard p : OracleComp spec _)] = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

@[simp]
lemma probFailure_guard {p : Prop} [Decidable p] :
    [⊥ | (guard p : OracleComp spec _)] = if p then 0 else 1 := by
  split <;> simp [*]

lemma probOutput_eq_sub_probFailure_of_unit {oa : OracleComp spec PUnit} :
    [= () | oa] = 1 - [⊥ | oa] := by simp [probFailure_eq_sub_sum, ENNReal.sub_sub_cancel]

lemma probOutput_guard_eq_sub_probOutput_guard_not {α : Type} {oa : OracleComp spec α}
    (h : oa.neverFails) {p : α → Prop} [DecidablePred p] :
    [= () | do let a ← oa; guard (p a)] = 1 - [= () | do let a ← oa; guard (¬ p a)] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simp only [probOutput_guard, mul_ite, mul_one, mul_zero]
  rw [ENNReal.sub_eq_of_eq_add]
  · exact ne_top_of_le_ne_top tsum_probOutput_ne_top <|
      ENNReal.tsum_le_tsum (f := fun a ↦ if ¬p a then [=a|oa] else 0) (g := fun a ↦ [=a|oa])
        fun a ↦ by simp only [ite_not]; split <;> simp
  · have h_eq : (fun a ↦ (if p a then oa.probOutput a else 0) + if ¬p a then oa.probOutput a else 0)
        = fun a ↦ oa.probOutput a := by ext; split <;> simp
    rw [← ENNReal.tsum_add, h_eq, tsum_probOutput_eq_one]
    exact (probFailure_eq_zero_iff oa).mpr h

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

lemma probOutput_eqRec (y : β) : [= y | h ▸ oa] = [= h ▸ y | oa] := by subst h; rfl

@[simp] lemma probFailure_eqRec : [⊥ | h ▸ oa] = [⊥ | oa] := by grind

lemma probEvent_eqRec (q : β → Prop) :
    [q | h ▸ oa] = [fun x ↦ q (h ▸ x) | oa] := by subst h; rfl

end eqRec

section ite

variable (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)

@[simp]
lemma probOutput_ite (x : α) : [= x | if p then oa else oa'] =
    if p then [= x | oa] else [= x | oa'] :=
  apply_ite ([= x | ·]) p oa oa'

@[simp]
lemma probFailure_ite : [⊥ | if p then oa else oa'] = if p then [⊥ | oa] else [⊥ | oa'] :=
  apply_ite probFailure p oa oa'

@[simp]
lemma probEvent_ite (q : α → Prop) : [q | if p then oa else oa'] =
    if p then [q | oa] else [q | oa'] := by
  grind

end ite

section coin

@[simp]
lemma probOutput_coin (b : Bool) : [= b | coin] = 2⁻¹ := by simp

lemma probEvent_coin_eq_sum_subtype (p : Bool → Prop) :
    [p | coin] = ∑' _ : {x | p x}, 2⁻¹ := by
  simp only [probEvent_eq_tsum_subtype, probOutput_coin]

@[simp]
lemma probEvent_coin (p : Bool → Prop) [DecidablePred p] : [p | coin] =
    if p true then (if p false then 1 else 2⁻¹) else (if p false then 2⁻¹ else 0) := by
  by_cases hpt : p true <;> by_cases hpf : p false <;>
    simp [probEvent, hpt, hpf, inv_two_add_inv_two]

lemma probEvent_coin_eq_add (p : Bool → Prop) [DecidablePred p] :
    [p | coin] = (if p true then 2⁻¹ else 0) + (if p false then 2⁻¹ else 0) := by
  rw [probEvent_coin]; split_ifs <;> simp [inv_two_add_inv_two]

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
lemma probFailure_uniformFin : [⊥ | $[0..n]] = 0 := probFailure_query ..

@[simp]
lemma probEvent_uniformFin (p : Fin (n + 1) → Prop) [DecidablePred p] :
    [p | $[0..n]] = (Finset.univ.filter p).card * (n + 1 : ℝ≥0∞)⁻¹ := by
  simp [probEvent_liftM_eq_mul_inv]

end uniformFin

/-- Example of brute forcing a probability computation by expanding terms and using `ring_nf`. -/
example : [⊥ | do
    let x ←$[0..5]; let y ←$[0..3]
    guard (x = 0); guard (y.val ≠ x.val); return ()] = 21 / 24 := by
  have : (6 : ℝ≥0∞)⁻¹ * (4 : ℝ≥0∞)⁻¹ = (24 : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.mul_inv (by tauto) (by tauto)]; ring_nf
  simp [probFailure_bind_eq_sum_fintype, Fin.sum_univ_succ, Fin.succ_ne_zero, div_eq_mul_inv, this]
  ring_nf; rw [this]; ring

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
    ⦃P⦄ fun x ↦ comp₁ x >>= comp₂ x ⦃R⦄ (r * r') :=
  fun x hx ↦ mul_le_probEvent_bind (h1 x hx) fun y _ hy ↦ h2 x y hy

end hoare

end OracleComp
