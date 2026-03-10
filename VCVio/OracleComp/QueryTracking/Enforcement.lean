/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Enforcement Oracle

Oracle wrapper that enforces a query budget by silently dropping queries beyond
the budget. This implements EasyCrypt's `Enforce`/`Bounder` pattern.

## Main Definitions

- `enforceOracle`: Oracle that tracks remaining budget via `StateT` and returns
  `default` for queries exceeding the budget.

## Main Results

- `enforceOracle.fst_map_run_simulateQ`: Enforcement is transparent for computations
  within their query bound.
-/

set_option autoImplicit false

open OracleSpec OracleComp

universe u

variable {ι : Type u} {spec : OracleSpec ι} {α : Type u}

/-- Enforcement oracle: wraps the original oracle with a per-index budget tracked via `StateT`.
When the remaining budget for the queried oracle is positive, the query is forwarded and
the budget decremented. When the budget is exhausted, `default` is returned silently. -/
def enforceOracle [DecidableEq ι] [spec.Inhabited] :
    QueryImpl spec (StateT (ι → ℕ) (OracleComp spec)) :=
  fun t => StateT.mk fun budget =>
    if 0 < budget t then
      (·, Function.update budget t (budget t - 1)) <$> liftM (query t)
    else
      pure (default, budget)

namespace enforceOracle

variable [DecidableEq ι] [spec.Inhabited]

@[simp]
lemma run_apply (t : ι) (budget : ι → ℕ) :
    (enforceOracle (spec := spec) t).run budget =
      if 0 < budget t then
        (·, Function.update budget t (budget t - 1)) <$> liftM (query t)
      else
        pure (default, budget) := rfl

/-- When the computation is within its query bound, enforcement is transparent:
the output distribution is identical to running without enforcement. -/
theorem fst_map_run_simulateQ
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    Prod.fst <$> (simulateQ enforceOracle oa).run qb = oa := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ => simp
  | query_bind t mx ih =>
    rw [isPerIndexQueryBound_query_bind_iff] at h
    obtain ⟨hpos, hcont⟩ := h
    simp only [simulateQ_query_bind]
    show Prod.fst <$> ((enforceOracle (spec := spec) t).run qb >>=
      fun p => (simulateQ enforceOracle (mx p.1)).run p.2) = liftM (query t) >>= mx
    rw [run_apply, if_pos hpos]
    simp only [map_eq_bind_pure_comp, Function.comp, bind_assoc, pure_bind]
    congr 1
    ext u
    exact ih u (hcont u)

end enforceOracle
