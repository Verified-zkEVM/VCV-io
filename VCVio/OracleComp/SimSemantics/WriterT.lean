/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.EvalDist
import VCVio.EvalDist.Prod
import ToMathlib.Control.WriterT

/-!
# Simulation using `WriterT` Monad Transformers

Lemmas about `simulateQ` with output monad `WriterT ω (OracleComp spec)` for some `ω`

Note we only handle `monoid` version of `WriterT`, append should be added eventually.
-/

open OracleSpec Function Prod

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α : Type u} {ω : Type u} [Monoid ω]

/-- Taking the first component of the WriterT output recovers the original computation,
when the query implementation preserves the underlying oracle behavior (hso). -/
lemma fst_map_writerT_run_simulateQ
    {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (hso : ∀ t, fst <$> (so t).run = liftM (query t))
    (oa : OracleComp spec α) : fst <$> (simulateQ so oa).run = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [WriterT.run_pure]
  | query_bind t oa ih =>
    rw [simulateQ_bind, simulateQ_query, WriterT.run_bind, map_bind]
    have heq : ((query t).cont <$> so (query t).input) = so t := by
      rw [OracleQuery.cont_query t, id_map]
      simp only [OracleQuery.input_query]
    rw [heq]
    refine (bind_congr fun x => ?_).trans (by rw [← bind_map_left, hso t])
    rw [fst_map_prod_map]
    simp only [Function.id_comp]
    exact ih x.1

lemma probFailure_writerT_run_simulateQ [spec.Fintype] [spec.Inhabited]
    {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (oa : OracleComp spec α) : Pr[⊥ | (simulateQ so oa).run] = Pr[⊥ | oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa h => simp

lemma NeverFail_writerT_run_simulateQ_iff [spec.Fintype] [spec.Inhabited]
    {so : QueryImpl spec (WriterT ω (OracleComp spec))}
    (oa : OracleComp spec α) :
    NeverFail ((simulateQ so oa).run : OracleComp spec _) ↔
      NeverFail (oa : OracleComp spec α) := by
  rw [← probFailure_eq_zero_iff, ← probFailure_eq_zero_iff,
    probFailure_writerT_run_simulateQ oa]

end OracleComp
