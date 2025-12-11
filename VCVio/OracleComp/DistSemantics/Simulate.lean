/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.DistSemantics.EvalDist
import ToMathlib.Control.WriterT

/-!
# Lemmas About the Distribution Semantics of `simulateQ`

This file collects various lemmas about the output distributions of `simulateQ`

TODO: probably put these in simulate folder as about the query impl itself
-/


open OracleSpec Option ENNReal BigOperators

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u} [hs : spec.FiniteRange]

-- /-- If `fst <$> so i (t, s)` has the same distribution as `query i t` for any state `s`,
-- Then `simulate' so` doesn't change the output distribution.
-- Stateless oracles are the most common example of this
-- TODO: move-/
-- lemma evalDist_simulate'_eq_evalDist {σ α : Type u}
--     (so : QueryImpl spec (StateT σ (OracleComp spec)))
--     (h : ∀ i t s, (evalDist ((so.impl (query i t)).run' s)) =
--       OptionT.lift (PMF.uniformOfFintype (spec.range i)))
--     (s : σ) (oa : OracleComp spec α) : evalDist ((simulateQ so oa).run' s) = evalDist oa := by
--   revert s
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa hoa => exact (λ s ↦ by
--       simp only [StateT.run'_eq] at h
--       simp [← h i t s, Function.comp_def]

--       sorry
--       )
--   | failure => intro s; simp

-- lemma probFailure_simulateQ_WriterT_eq_probFailure {ω : Type u} [Monoid ω]
--     (so : QueryImpl spec (WriterT ω (OracleComp spec)))
--     (h : ∀ {α}, ∀ q : OracleQuery spec α, [⊥ | (so.impl q).run] = 0) (oa : OracleComp spec α) :
--     [⊥ | (simulateQ so oa).run] = [⊥ | oa] := by
--   -- revert s
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | failure => simp
--   | query_bind i t oa hq => {
--     simp [probFailure_bind_eq_tsum, h, hq]
--     intro s
--     rw [ENNReal.tsum_prod']
--     refine tsum_congr fun x => ?_
--     simp [ENNReal.tsum_mul_right]
--     congr 1

--     sorry
--   }

end OracleComp
