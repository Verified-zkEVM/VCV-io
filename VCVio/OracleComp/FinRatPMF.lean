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
          = @Raw.prob _ (FinEnum.decEq) (Raw.uniform (α := spec.Range t)) x :=
              Raw.prob_eq_prob (Classical.decEq _) (FinEnum.decEq)
                (Raw.uniform (α := spec.Range t)) x
      _ = (Fintype.card (spec.Range t) : ℚ≥0)⁻¹ := Raw.prob_uniform (α := spec.Range t) x
  rw [PMF.uniformOfFintype_apply]
  change (((@Raw.prob _ (Classical.decEq _)
    (Raw.uniform (α := spec.Range t)) x : NNReal) : ENNReal))
      = ((Fintype.card (spec.Range t) : ENNReal)⁻¹)
  calc
    (((@Raw.prob _ (Classical.decEq _) (Raw.uniform (α := spec.Range t)) x : NNReal) : ENNReal))
        = (((((Fintype.card (spec.Range t) : ℚ≥0)⁻¹ : ℚ≥0) : NNReal) : ENNReal)) :=
            congrArg
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
  | query_bind t mx h => simp [evalDist_bind, evalDist_apply, OracleComp.evalDist_query, h]

@[simp] lemma probOutput_simulateQ {α : Type v}
    (oa : OracleComp spec α) (x : α) :
    Pr[= x | simulateQ (finRatImpl (spec := spec)) oa] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ (spec := spec) oa)) x

@[simp] lemma probEvent_simulateQ {α : Type v}
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr[ p | simulateQ (finRatImpl (spec := spec)) oa] = Pr[ p | oa] := by
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

/-! ## Demo -/

namespace Demo

local instance : FinEnum Bool where
  card := 2
  equiv :=
    { toFun := fun b => if b then ⟨1, by decide⟩ else ⟨0, by decide⟩
      invFun := fun i => i.1 = 1
      left_inv := by
        intro b
        cases b <;> rfl
      right_inv := by
        intro i
        fin_cases i <;> rfl }
  decEq := inferInstance

instance : (t : coinSpec.Domain) → FinEnum (coinSpec.Range t) := by
  intro t
  change FinEnum Bool
  infer_instance

def xorTwoCoins : FinRatPMF.Raw Bool := do
  let b1 <- FinRatPMF.Raw.coin
  let b2 <- FinRatPMF.Raw.coin
  pure (b1 != b2)

def threeCoinCount : FinRatPMF.Raw Nat := do
  let b1 <- FinRatPMF.Raw.coin
  let b2 <- FinRatPMF.Raw.coin
  let b3 <- FinRatPMF.Raw.coin
  pure (cond b1 1 0 + cond b2 1 0 + cond b3 1 0)

def twoCoinQueries : OracleComp coinSpec Nat := do
  let b1 <- OracleComp.coin
  let b2 <- OracleComp.coin
  pure (cond b1 1 0 + cond b2 1 0)

/-
#eval FinRatPMF.Raw.coin
#eval xorTwoCoins
#eval xorTwoCoins.normalize
#eval threeCoinCount.normalize
#eval! simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries
#eval! (simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries).normalize
#eval! (simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries).normalize.prob 1)
-/

end Demo
end FinRatPMF
