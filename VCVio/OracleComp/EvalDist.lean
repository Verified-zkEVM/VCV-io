/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.NeverFails
import VCVio.EvalDist.Instances.OptionT
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Output Distribution of Computations

This file defines `HasEvalDist` and related instances for `OracleComp`.
-/

open OracleSpec Option ENNReal BigOperators

universe u v w

namespace OracleComp

variable {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β γ : Type w}

section support

/-- The possible outputs of `mx` when queries can output values in the specified sets.
NOTE: currently proofs using this should reduce to `simulateQ`. A full API would be better -/
def supportWhen (o : QueryImpl spec Set) (mx : OracleComp spec α) : Set α :=
  simulateQ (r := SetM) o mx

/-- The `support` instance for `OracleComp`, defined as  -/
instance hasEvalSet : HasEvalSet (OracleComp spec) where
  toSet := simulateQ' (r := SetM) fun _ : spec.Domain => Set.univ

lemma support_eq_simulateQ (mx : OracleComp spec α) :
    support mx = simulateQ (r := SetM) (fun _ : spec.Domain => Set.univ) mx := rfl

@[simp, grind =] lemma support_liftM (q : OracleQuery spec α) :
    support (liftM q : OracleComp spec α) = Set.range q.cont := by
  simp [support_eq_simulateQ]

@[grind =] lemma support_query (t : spec.Domain) :
    support (liftM (query t) : OracleComp spec _) = Set.univ := by simp

lemma mem_support_liftM_iff (q : OracleQuery spec α) (u : α) :
    u ∈ support (liftM q : OracleComp spec α) ↔ ∃ t, q.cont t = u := by grind

lemma mem_support_query (t : spec.Domain) (u : spec.Range t) :
    u ∈ support (liftM (query t) : OracleComp spec _) := by grind

alias support_liftM_query := support_query

end support

section finSupport

variable [spec.Fintype]

/-- Finite version of support for when oracles have a finite set of possible outputs.
NOTE: we can't use `simulateQ` because `Finset` lacks a `Monad` instance. -/
instance : HasEvalFinset (OracleComp spec) where
  finSupport {α} _ mx := OracleComp.construct
    (fun x => {x}) (fun _ _ r => Finset.univ.biUnion r) mx
  coe_finSupport {α} _ mx := by
    induction mx using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t mx h => simp [h]

@[simp, grind =] lemma finSupport_liftM [DecidableEq α] (q : OracleQuery spec α) :
    finSupport (liftM q : OracleComp spec α) = Finset.univ.image q.cont := by grind

lemma finSupport_query [spec.DecidableEq] (t : spec.Domain) :
    finSupport (liftM (query t) : OracleComp spec _) = Finset.univ := by grind

lemma mem_finSupport_liftM_iff [DecidableEq α] (q : OracleQuery spec α) (x : α) :
    x ∈ finSupport (liftM q : OracleComp spec α) ↔ ∃ t, q.cont t = x := by simp

lemma mem_finSupport_query [spec.DecidableEq] (t : spec.Domain) (u : spec.Range t) :
    u ∈ finSupport (liftM (query t) : OracleComp spec _) := by grind

end finSupport

section evalDist

/-- The output distribution of `mx` when queries follow the specified distribution.
NOTE: currently proofs using this should reduce to `simulateQ`. A full API would be better -/
noncomputable def evalDistWhen (d : QueryImpl spec SPMF)
    (mx : OracleComp spec α) : SPMF α :=
  simulateQ (r := SPMF) d mx

variable [spec.Fintype] [spec.Inhabited]

/-- Embed `OracleComp` into `SPMF` by mapping queries to uniform distributions over their range. -/
noncomputable instance : HasEvalPMF (OracleComp spec) where
  toPMF := simulateQ' fun t => PMF.uniformOfFintype (spec.Range t)
  support_eq mx := by induction mx using OracleComp.inductionOn with
    | pure x => simp
    | query_bind t mx ht => simp [ht]
  toSPMF_eq mx := rfl
  __ := OracleComp.hasEvalSet (spec := spec)

lemma evalDist_eq_simulateQ (mx : OracleComp spec α) :
    evalDist mx = simulateQ (fun t => PMF.uniformOfFintype (spec.Range t)) mx := rfl

@[simp low, grind =]
lemma evalDist_liftM (q : OracleQuery spec α) :
    evalDist (liftM q : OracleComp spec α) =
      (PMF.uniformOfFintype (spec.Range q.input)).map q.cont := by
  simp [evalDist_eq_simulateQ, SPMF.liftM_eq_map, PMF.map_comp, PMF.monad_map_eq_map]

@[simp, grind =]
lemma evalDist_query (t : spec.Domain) :
    evalDist (liftM (query t) : OracleComp spec _) = PMF.uniformOfFintype (spec.Range t) := by
  simp [PMF.map_id]

@[simp low, grind =]
lemma probOutput_liftM_eq_div (q : OracleQuery spec α) (x : α) :
    Pr[= x | (liftM q : OracleComp spec α)] =
      (∑' u : spec.Range q.input, Pr[= x | (return q.cont u : OracleComp spec α)])
        / Fintype.card (spec.Range q.input) := by
  have : DecidableEq α := Classical.decEq α
  simp [probOutput_def, div_eq_mul_inv]

@[simp, grind =]
lemma probOutput_query (t : spec.Domain) (u : spec.Range t) :
    Pr[= u | (query t : OracleComp spec _)] = (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by simp

@[grind =]
lemma probEvent_liftM_eq_div (q : OracleQuery spec α) (p : α → Prop) :
    Pr[p | (liftM q : OracleComp spec α)] =
      (∑' u : spec.Range q.input, Pr[p | (return q.cont u : OracleComp spec α)])
        / Fintype.card (spec.Range q.input) := by
  have : DecidablePred p := Classical.decPred p
  simp only [probEvent_eq_tsum_ite, probOutput_liftM_eq_div, tsum_fintype, div_eq_mul_inv]
  rw [sum_eq_tsum_indicator]
  simp only [Finset.coe_univ, Set.mem_univ, Set.indicator_of_mem]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => by aesop

@[grind =]
lemma probOutput_query_eq_div (t : spec.Domain) (u : spec.Range t) :
    Pr[= u | (query t : OracleComp spec _)] = 1 / Fintype.card (spec.Range t) := by simp

@[simp, grind =]
lemma probEvent_query (t : spec.Domain) (p : spec.Range t → Prop) [DecidablePred p] :
    Pr[p | (query t : OracleComp spec _)] =
      Finset.card {x | p x} / Fintype.card (spec.Range t) := by
  simp [probEvent_liftM_eq_div]

end evalDist

section supportEvalDist

variable [spec.Fintype] [spec.Inhabited] (oa : OracleComp spec α) (x : α)

/-- An output has non-zero probability in `evalDist` iff it is in computation support. -/
@[simp]
lemma mem_support_evalDist_iff :
    some x ∈ (evalDist oa).run.support ↔ x ∈ support oa := by
  rw [PMF.mem_support_iff]
  simpa [probOutput_def, SPMF.apply_eq_toPMF_some] using
    (mem_support_iff (mx := oa) (x := x)).symm

alias ⟨mem_support_of_mem_support_evalDist, mem_support_evalDist⟩ := mem_support_evalDist_iff

/-- Finite-support variant of `mem_support_evalDist_iff`. -/
@[simp]
lemma mem_support_evalDist_iff' [DecidableEq α] :
    some x ∈ (evalDist oa).run.support ↔ x ∈ finSupport oa := by
  rw [mem_support_evalDist_iff (oa := oa) (x := x), mem_finSupport_iff_mem_support]

alias ⟨mem_finSupport_of_mem_support_evalDist, mem_support_evalDist'⟩ := mem_support_evalDist_iff'

end supportEvalDist

section NeverFail

variable [spec.Fintype] [spec.Inhabited]

@[simp]
lemma probFailure_eq_zero_iff (oa : OracleComp spec α) : probFailure oa = 0 ↔ NeverFail oa := by
  simp [HasEvalSPMF.neverFail_iff]

@[simp]
lemma probFailure_pos_iff (oa : OracleComp spec α) : 0 < probFailure oa ↔ ¬ NeverFail oa := by
  simp [HasEvalSPMF.neverFail_iff]

lemma noFailure_of_probFailure_eq_zero {oa : OracleComp spec α} (h : probFailure oa = 0) :
    NeverFail oa := by rwa [← probFailure_eq_zero_iff]

lemma not_noFailure_of_probFailure_pos {oa : OracleComp spec α} (h : 0 < probFailure oa) :
    ¬ NeverFail oa := by rwa [← probFailure_pos_iff]

end NeverFail

end OracleComp
