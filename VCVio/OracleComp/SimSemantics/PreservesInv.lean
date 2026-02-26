/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.SimSemantics.StateT
import VCVio.EvalDist.Monad.Basic

/-!
# Oracle State Invariants for Shared-Oracle Simulations

This module provides minimal, **model-agnostic** infrastructure for reasoning about
shared, stateful oracle simulations (ROM/AGM/hybrids) via a user-supplied invariant
`Inv : σ → Prop` on oracle states.

We use **support-based** formulations (rather than `Pr[...] = 1`) to keep downstream
proofs lightweight.

## Main definitions

- `QueryImpl.PreservesInv` — every oracle query implementation step preserves `Inv`
- `OracleComp.simulateQ_run_preservesInv` — simulating any oracle computation
  with a preserving implementation preserves `Inv` on the final state
-/

noncomputable section

open OracleComp OracleSpec

namespace QueryImpl

/-- `PreservesInv impl Inv` means every oracle query implementation step preserves `Inv`
on all reachable post-states (support-based). -/
def PreservesInv {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop) : Prop :=
  ∀ t σ0, Inv σ0 → ∀ z ∈ support ((impl t).run σ0), Inv z.2

end QueryImpl

namespace OracleComp

open QueryImpl

/-- If `impl` preserves `Inv`, then simulating *any* oracle computation with `simulateQ impl`
preserves `Inv` on the final state (support-wise). -/
theorem simulateQ_run_preservesInv
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop)
    (himpl : QueryImpl.PreservesInv impl Inv) :
    ∀ oa : OracleComp spec α,
    ∀ σ0, Inv σ0 →
      ∀ z ∈ support ((simulateQ impl oa).run σ0), Inv z.2 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro σ0 hσ0 z hz
      have : z = (a, σ0) := by
        simpa using (show z ∈ support (pure (a, σ0) : ProbComp (α × σ)) from by
          simpa using hz)
      simpa [this] using hσ0
  | query_bind t oa ih =>
      intro σ0 hσ0 z hz
      have hz' :
          z ∈ support
            (((simulateQ impl
                  (liftM (OracleQuery.query t) : OracleComp spec (spec.Range t))).run σ0) >>=
              fun us => (simulateQ impl (oa us.1)).run us.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using hz
      rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
      have hq_run :
          (simulateQ impl (liftM (OracleQuery.query t) : OracleComp spec (spec.Range t))).run σ0 =
            (impl t).run σ0 := by
        have hq :
            simulateQ impl (liftM (OracleQuery.query t) : OracleComp spec (spec.Range t)) =
              (impl t) := by
          simp [OracleQuery.query_def, simulateQ_query]
        simp [hq]
      have hus' : us ∈ support ((impl t).run σ0) := by simpa [hq_run] using hus
      have hσ1 : Inv us.2 := himpl t σ0 hσ0 us hus'
      exact ih us.1 us.2 hσ1 z hzcont

end OracleComp
