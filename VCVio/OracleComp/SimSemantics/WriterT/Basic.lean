/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.EvalDist
import ToMathlib.Control.WriterT

/-!
# Simulation through `WriterT` Handlers

Combinators and output-preservation lemmas for writer-instrumented query implementations.
The combinators here mirror the StateT/ReaderT versions in
`SimSemantics/StateT/Basic.lean` and `SimSemantics/ReaderT/Basic.lean`.
-/

open OracleSpec Function Prod

universe u v w

open scoped OracleSpec.PrimitiveQuery

namespace QueryImpl

/-- Given implementations for oracles in `spec₁` and `spec₂` in terms of writer monads for
two different log monoids `ω₁` and `ω₂`, implement the combined set `spec₁ + spec₂` in terms
of the product monoid `ω₁ × ω₂`. Each side leaves the other component at the identity. -/
def parallelWriterT {ι₁ ι₂ : Type _}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type _ → Type _} [Functor m] {ω₁ ω₂ : Type _} [Monoid ω₁] [Monoid ω₂]
    (impl₁ : QueryImpl spec₁ (WriterT ω₁ m))
    (impl₂ : QueryImpl spec₂ (WriterT ω₂ m)) :
    QueryImpl (spec₁ + spec₂) (WriterT (ω₁ × ω₂) m)
  | .inl t => WriterT.mk <| Prod.map id (·, (1 : ω₂)) <$> (impl₁ t).run
  | .inr t => WriterT.mk <| Prod.map id ((1 : ω₁), ·) <$> (impl₂ t).run

/-- Indexed version of `QueryImpl.parallelWriterT`. Each query for index `t` writes into the
`t`-th component of the pi-product `(t : τ) → ω t`, leaving every other component at the
identity. Note that `m` cannot vary with `t`. -/
def sigmaWriterT {τ : Type} [DecidableEq τ] {ι : τ → Type _}
    {spec : (t : τ) → OracleSpec (ι t)}
    {m : Type _ → Type _} [Functor m] {ω : τ → Type _} [(t : τ) → Monoid (ω t)]
    (impl : (t : τ) → QueryImpl (spec t) (WriterT (ω t) m)) :
    QueryImpl (OracleSpec.sigma spec) (WriterT ((t : τ) → ω t) m)
  | ⟨t, q⟩ => WriterT.mk <| Prod.map id (Function.update (fun _ => 1) t) <$> (impl t q).run

/-- Reassociate a nested writer transformer into one product log.

The outer log is the first component of the product; the inner/base log is the second. This
is the writer-transformer analogue of `flattenStateT`. Requires `[Monoid ω₂]` to lift the
inner writer's run; the resulting `WriterT (ω₁ × ω₂) m` carries both logs as a product. -/
def flattenWriterT {ι : Type _} {spec : OracleSpec ι}
    {m : Type u → Type v} [Monad m] {ω₁ ω₂ : Type u} [Monoid ω₂]
    (impl : QueryImpl spec (WriterT ω₁ (WriterT ω₂ m))) :
    QueryImpl spec (WriterT (ω₁ × ω₂) m) := fun t =>
  WriterT.mk <| do
    let ((a, w₁), w₂) ← (impl t).run.run
    pure (a, (w₁, w₂))

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
