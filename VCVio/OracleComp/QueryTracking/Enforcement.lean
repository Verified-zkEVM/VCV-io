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

section Probability

variable [spec.Fintype]

/-- For a computation that is structurally within budget, the budget check in the
counting semantics is redundant on the support. -/
theorem probEvent_counting_budget_eq
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    Pr[fun z => p z.1 ∧ z.2 ≤ qb | countingOracle.simulate oa 0] = Pr[p | oa] := by
  calc
    Pr[fun z => p z.1 ∧ z.2 ≤ qb | countingOracle.simulate oa 0]
      = Pr[fun z => p z.1 | countingOracle.simulate oa 0] := by
          refine probEvent_congr' (oa := countingOracle.simulate oa 0)
            (oa' := countingOracle.simulate oa 0) ?_ rfl
          intro z hz
          constructor
          · intro hz'
            exact hz'.1
          · intro hp
            exact ⟨hp, h.counting_bounded hz⟩
    _ = Pr[p | oa] := by
        rw [countingOracle.simulate]
        simp only [zero_add]
        rw [show (fun z : α × QueryCount ι => p z.1) = p ∘ Prod.fst from rfl, ← probEvent_map]
        simp only [Functor.map_map]
        change Pr[p | (fun a : α × QueryCount ι => (Prod.map id (fun q : QueryCount ι => q) a).1) <$>
          (simulateQ countingOracle oa).run] = Pr[p | oa]
        have hfst :
            (fun a : α × QueryCount ι => (Prod.map id (fun q : QueryCount ι => q) a).1) = Prod.fst := by
          funext a
          cases a
          rfl
        rw [hfst, countingOracle.fst_map_run_simulateQ]

/-- Penalty characterization under a structural query bound: the probability of an
event together with staying within budget under counting equals the event probability
under enforcement. -/
theorem probEvent_counting_budget_eq_enforce
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    Pr[fun z => p z.1 ∧ z.2 ≤ qb | countingOracle.simulate oa 0] =
      Pr[p | Prod.fst <$> (simulateQ enforceOracle oa).run qb] := by
  rw [fst_map_run_simulateQ h]
  exact probEvent_counting_budget_eq h p

/-- EasyCrypt-style penalty inequality, obtained here as an equality under the
structural boundedness hypothesis. -/
theorem probEvent_counting_budget_le_enforce
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    Pr[fun z => p z.1 ∧ z.2 ≤ qb | countingOracle.simulate oa 0] ≤
      Pr[p | Prod.fst <$> (simulateQ enforceOracle oa).run qb] := by
  rw [probEvent_counting_budget_eq_enforce h p]

end Probability

end enforceOracle
