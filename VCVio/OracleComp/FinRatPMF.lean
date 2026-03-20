/- 
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.EvalDist
import VCVio.EvalDist.Instances.FinRatPMF

/-!
# Executable `FinRatPMF` Semantics for `OracleComp`

This file provides a computable oracle evaluator using `FinRatPMF.Raw` and proves that its
denotational semantics agree with the existing `evalDist` semantics of `OracleComp`.
-/

open OracleSpec OracleComp

universe u v

namespace FinRatPMF

variable {ι : Type u} {spec : OracleSpec ι}

/-- Computable query implementation using the executable `FinRatPMF.Raw` monad. -/
def finRatImpl [spec.Inhabited] [∀ t : spec.Domain, FinEnum (spec.Range t)] :
    QueryImpl spec Raw :=
  fun t => Raw.uniform (α := spec.Range t)

namespace finRatImpl

variable [spec.Inhabited] [∀ t : spec.Domain, FinEnum (spec.Range t)]

local instance instSpecFintypeOfFinEnum : spec.Fintype where
  fintype_B _ := inferInstance

lemma uniformOfFintype_eq {α : Type u} (f1 f2 : Fintype α) :
    @PMF.uniformOfFintype α f1 = @PMF.uniformOfFintype α f2 := by
  ext x
  simp [PMF.uniformOfFintype_apply, @Fintype.card_congr α α f1 f2 (Equiv.refl α)]

@[simp] lemma toPMF_apply (t : spec.Domain) :
    @Raw.toPMF _ (Classical.decEq _) (finRatImpl (spec := spec) t) =
      PMF.uniformOfFintype (spec.Range t) := by
  classical
  ext x
  have hprob :
      @Raw.prob _ (Classical.decEq _) (Raw.uniform (α := spec.Range t)) x =
        (Fintype.card (spec.Range t) : ℚ≥0)⁻¹ := by
    calc
      @Raw.prob _ (Classical.decEq _) (Raw.uniform (α := spec.Range t)) x
          = @Raw.prob _ (FinEnum.decEq) (Raw.uniform (α := spec.Range t)) x := by
              exact Raw.prob_eq_prob (Classical.decEq _) (FinEnum.decEq)
                (Raw.uniform (α := spec.Range t)) x
      _ = (Fintype.card (spec.Range t) : ℚ≥0)⁻¹ := Raw.prob_uniform (α := spec.Range t) x
  rw [PMF.uniformOfFintype_apply]
  change (((@Raw.prob _ (Classical.decEq _) (Raw.uniform (α := spec.Range t)) x : NNReal) : ENNReal))
      = ((Fintype.card (spec.Range t) : ENNReal)⁻¹)
  calc
    (((@Raw.prob _ (Classical.decEq _) (Raw.uniform (α := spec.Range t)) x : NNReal) : ENNReal))
        = (((((Fintype.card (spec.Range t) : ℚ≥0)⁻¹ : ℚ≥0) : NNReal) : ENNReal)) := by
            exact congrArg
              (fun q : ℚ≥0 => ((q : NNReal) : ENNReal))
              hprob
    _ = ((Fintype.card (spec.Range t) : ENNReal)⁻¹) := by
          simp [NNRat.cast_inv]

@[simp] lemma evalDist_apply (t : spec.Domain) :
    evalDist (finRatImpl (spec := spec) t) = liftM (PMF.uniformOfFintype (spec.Range t)) := by
  rw [HasEvalPMF.evalDist_of_hasEvalPMF_def]
  change liftM (@Raw.toPMF _ (Classical.decEq _) (finRatImpl (spec := spec) t)) = _
  rw [toPMF_apply]

@[simp] lemma evalDist_simulateQ {α : Type v} (oa : OracleComp spec α) :
    evalDist (simulateQ (finRatImpl (spec := spec)) oa) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h =>
      let g : PMF (spec.Range t) → SPMF α := fun p =>
        (liftM p : SPMF (spec.Range t)) >>= fun x => evalDist (mx x)
      simp [evalDist_bind, evalDist_apply, OracleComp.evalDist_query, h]

@[simp] lemma probOutput_simulateQ {α : Type v}
    (oa : OracleComp spec α) (x : α) :
    Pr[= x | simulateQ (finRatImpl (spec := spec)) oa] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ (spec := spec) oa)) x

@[simp] lemma probEvent_simulateQ {α : Type v}
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr[p | simulateQ (finRatImpl (spec := spec)) oa] = Pr[p | oa] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_simulateQ]

@[simp] lemma support_simulateQ {α : Type v} (oa : OracleComp spec α) :
    support (simulateQ (finRatImpl (spec := spec)) oa) = support oa := by
  ext x
  exact mem_support_iff_of_evalDist_eq (evalDist_simulateQ (spec := spec) oa) x

@[simp] lemma finSupport_simulateQ {α : Type v} [DecidableEq α]
    (oa : OracleComp spec α) :
    finSupport (simulateQ (finRatImpl (spec := spec)) oa) = finSupport oa := by
  ext x
  exact mem_finSupport_iff_of_evalDist_eq (evalDist_simulateQ (spec := spec) oa) x

end finRatImpl
end FinRatPMF
