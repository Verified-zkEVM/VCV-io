/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.EvalDist
public import VCVio.EvalDist.Monad.Measure

/-!
# Measure congruence from structural support

Continuations that denote the same measure on all syntactically reachable outputs may
be interchanged. The proof inducts on the free program, so no probability/support bridge
or positivity assumption on query answers is necessary.
-/

public section

open OracleComp OracleSpec MeasureTheory

namespace OracleComp

/-- Equal continuation measures on structural support give equal composed measures. -/
theorem evalDist_bind_congr_of_support {ι α β : Type} {spec : OracleSpec ι}
    [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [MeasurableSpace β]
    [EvalDistSemantics (OracleComp spec)] [LawfulEvalDistSemantics (OracleComp spec)]
    (mx : OracleComp spec α) (f g : α → OracleComp spec β)
    (h : ∀ a ∈ support mx, 𝒟[f a] = 𝒟[g a]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, bind_assoc, evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro u
    exact ih u fun a ha => h a ((mem_support_bind_iff _ _ _).mpr ⟨u, by simp, ha⟩)

end OracleComp
