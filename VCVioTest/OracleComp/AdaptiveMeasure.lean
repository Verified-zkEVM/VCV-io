/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.OnlineBound
public import VCVio.EvalDist.PFunctorMeasure.Core

/-!
# Structural cache coherence and measure-based stopping bounds

Repeated hits retain log consistency without equality on response values. A direct
uniform measure interpretation supplies the query law of the stopping bounds.
The dependency check traverses theorem types and proofs, including definitions,
to prevent the measure inductions from using discrete probability facts indirectly.
-/

public section

open OracleSpec OracleComp MeasureTheory

run_cmd do
  let env ← Lean.getEnv
  let mut pending := [``OracleComp.measure_adaptivePrefixRunFrom_le,
    ``MerkleTreeMultiExtractability.measure_onlineAdaptivePrefixRunFrom_logged_le]
  let mut visited : Std.HashSet Lean.Name := {}
  while let name :: rest := pending do
    pending := rest
    unless visited.contains name do
      visited := visited.insert name
      for forbidden in [`PMF, `SPMF, `evalSPMF, `probEvent, `probOutput, `expectedValue] do
        if forbidden.isPrefixOf name then
          throwError "measure induction depends on the discrete probability declaration {name}"
      if let some info := env.find? name then
        pending := info.getUsedConstantsAsSet.toList ++ pending

namespace VCVioTest.AdaptiveMeasure

example {Y : Type} (value : Y) :
    ∀ entry ∈ ([⟨0, value⟩, ⟨0, value⟩] : (ℕ →ₒ Y).QueryLog),
      ((∅ : (ℕ →ₒ Y).QueryCache).cacheQuery 0 value) entry.1 = some entry.2 := by
  have hfirst := QueryCache.log_consistent_cacheQuery_append
    (∅ : (ℕ →ₒ Y).QueryCache) [] 0 value rfl (by simp)
  exact QueryCache.log_consistent_append _ [⟨0, value⟩] 0 value
    (QueryCache.cacheQuery_self ..) hfirst

example {Y : Type} (value : Y) :
    ∃ keys : Finset ℕ, keys.card ≤ 1 ∧ ∀ input,
      ((∅ : (ℕ →ₒ Y).QueryCache).cacheQuery 7 value) input ≠ none → input ∈ keys := by
  exact QueryCache.domain_bound_cacheQuery ∅ 7 value 0 ⟨∅, by simp, by simp⟩

noncomputable local instance : (ℕ →ₒ Bool).toPFunctor.IsMeasureSpec :=
  PFunctor.IsMeasureSpec.uniformOfFintypeInhabited _

example (t : ℕ) : 𝒟[(liftM ((ℕ →ₒ Bool).query t) : OracleComp (ℕ →ₒ Bool) Bool)] =
    ProbabilityTheory.uniformOn Set.univ := by
  exact PFunctor.FreeM.evalDist_lift (P := (ℕ →ₒ Bool).toPFunctor) t

end VCVioTest.AdaptiveMeasure
