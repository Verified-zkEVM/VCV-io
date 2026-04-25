/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.EvalDist
import ToMathlib.Control.WriterT

/-!
# Simulation through `WriterT` Handlers

Output-preservation lemmas for writer-instrumented query implementations.
-/

open OracleSpec Function Prod

universe u v w

open scoped OracleSpec.PrimitiveQuery

namespace QueryImpl

variable {ι : Type u} {spec : OracleSpec ι} {α : Type u}
variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

section monoid

variable {ω : Type u} [Monoid ω]

/-- A `WriterT`-valued handler preserves the output marginal of a whole
simulation as soon as it preserves the output marginal of each query.

This is the generic output-preservation principle for writer-style handler
instrumentation. Specializations such as trace, cost, and counting handlers
only need to prove the one-query hypothesis. -/
lemma simulateQ_writerT_fst_map_run_eq_of_query
    (implW : QueryImpl spec (WriterT ω m)) (impl : QueryImpl spec m)
    (himpl : ∀ t, Prod.fst <$> (implW t).run = impl t)
    (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ implW oa).run = simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [WriterT.run_pure]
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, WriterT.run_bind, map_bind,
        Functor.map_map, ih]
      calc
        (do
            let a ← (implW t).run
            simulateQ impl (oa a.1))
            = (Prod.fst <$> (implW t).run >>= fun x => simulateQ impl (oa x)) := by
                exact (bind_map_left (m := m) Prod.fst (implW t).run
                  (fun x => simulateQ impl (oa x))).symm
        _ = (impl t >>= fun x => simulateQ impl (oa x)) := by rw [himpl t]

end monoid

section append

variable {ω : Type u} [EmptyCollection ω] [Append ω] [LawfulAppend ω]

/-- Append-flavoured version of
`QueryImpl.simulateQ_writerT_fst_map_run_eq_of_query`.

This targets the `WriterT` instance that accumulates logs via `∅` and `++`,
used by query logging. -/
lemma simulateQ_writerT_append_fst_map_run_eq_of_query
    (implW : QueryImpl spec (WriterT ω m)) (impl : QueryImpl spec m)
    (himpl : ∀ t, Prod.fst <$> (implW t).run = impl t)
    (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ implW oa).run = simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, WriterT.run_bind', map_bind,
        Functor.map_map, map_fst, id_eq, ih]
      calc
        (do
            let a ← (implW t).run
            simulateQ impl (oa a.1))
            = (Prod.fst <$> (implW t).run >>= fun x => simulateQ impl (oa x)) := by
                exact (bind_map_left (m := m) Prod.fst (implW t).run
                  (fun x => simulateQ impl (oa x))).symm
        _ = (impl t >>= fun x => simulateQ impl (oa x)) := by rw [himpl t]

end append

end QueryImpl

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
      simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]
    rw [heq]
    refine (bind_congr fun x => ?_).trans (by rw [← bind_map_left, hso t])
    obtain ⟨a, w₁⟩ := x
    dsimp only []
    rw [← LawfulFunctor.comp_map]
    have : Prod.fst ∘ (fun x : α × ω ↦ (x.1, w₁ * x.2)) = Prod.fst :=
      funext fun ⟨_, _⟩ => rfl
    rw [this]
    exact ih a

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
