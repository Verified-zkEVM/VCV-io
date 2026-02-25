/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.EvalDist
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

-- TODO: prove fst_map_writerT_run_simulateQ (query_bind case needs WriterT.run_bind reasoning)

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
