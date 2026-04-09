/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.EvalDist.TVDist
import VCVio.ProgramLogic.Notation
import VCVio.ProgramLogic.Relational.SimulateQ
import Examples.CommitmentScheme.Support

/-!
# Random Oracle Commitment Scheme — Shared Definitions

Shared oracle/model definitions and helper lemmas for the random oracle commitment
scheme proof split.
-/

open OracleSpec OracleComp ENNReal
/-! ## Oracle Specification -/

/-- Oracle spec for the commitment scheme: maps `(M × S) → C`. -/
abbrev CMOracle (M : Type) (S : Type) (C : Type) : OracleSpec (M × S) := fun _ => C

variable {M S C : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C]

instance : DecidableEq (M × S) := instDecidableEqProd

/-! ## Commit and Check

These are the commitment scheme algorithms, defined as oracle computations
that query H. When run under `cachingOracle`, all queries share the same
random function. -/

/-- Commit to message `m` with salt `s` by querying the random oracle. -/
def CMCommit (m : M) (s : S) : OracleComp (CMOracle M S C) C :=
  query (spec := CMOracle M S C) (m, s)

/-- Check commitment `c` against opening `(m, s)`: query oracle and compare. -/
def CMCheck (c : C) (m : M) (s : S) : OracleComp (CMOracle M S C) Bool := do
  let c' ← query (spec := CMOracle M S C) (m, s)
  return (c == c')


lemma simulateQ_cachingOracle_query (idx : (CMOracle M S C).Domain) :
    (simulateQ cachingOracle (liftM (query (spec := CMOracle M S C) idx))) =
    (cachingOracle (spec := CMOracle M S C) idx) := by
  simp [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query]

/-- After running `cachingOracle` on a single query at index `idx`, the resulting cache
has an entry at `idx`. -/
lemma cachingOracle_query_caches (idx : (CMOracle M S C).Domain)
    (cache₀ : QueryCache (CMOracle M S C))
    (v : (CMOracle M S C).Range idx) (cache₁ : QueryCache (CMOracle M S C))
    (hmem : (v, cache₁) ∈ support ((cachingOracle (spec := CMOracle M S C) idx).run cache₀)) :
    cache₁ idx = some v := by
  simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hmem
  cases hc : cache₀ idx with
  | some u =>
    simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    exact hc
  | none =>
    simp only [hc, StateT.run_bind] at hmem
    rw [show (liftM (query (spec := CMOracle M S C) idx) :
        StateT (QueryCache (CMOracle M S C)) (OracleComp (CMOracle M S C)) _).run cache₀ =
        ((liftM (query (spec := CMOracle M S C) idx) : OracleComp _ _) >>= fun u =>
          pure (u, cache₀)) from rfl] at hmem
    rw [bind_assoc] at hmem; simp only [pure_bind] at hmem
    rw [support_bind] at hmem; simp only [Set.mem_iUnion] at hmem
    obtain ⟨u, _, hmem⟩ := hmem
    simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    exact QueryCache.cacheQuery_self cache₀ idx v

/-- If a fixed fresh query is the only way to win, its success probability is `1 / |C|`. -/
lemma probEvent_from_fresh_query_le_inv
    (t : (CMOracle M S C).Domain)
    (target : C)
    (cache₀ : QueryCache (CMOracle M S C))
    (hfresh : cache₀ t = none)
    (cont : C → OracleComp (CMOracle M S C) Bool)
    (hzero : ∀ u, u ≠ target →
      Pr[fun z => z.1 = true |
        (simulateQ cachingOracle (cont u)).run (cache₀.cacheQuery t u)] = 0) :
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle
        ((liftM (query (spec := CMOracle M S C) t)) >>= cont)).run cache₀] ≤
      (Fintype.card C : ℝ≥0∞)⁻¹ := by
  have hrun :
      (simulateQ cachingOracle
        ((liftM (query (spec := CMOracle M S C) t)) >>= cont)).run cache₀ =
      (liftM (query (spec := CMOracle M S C) t) >>= fun u =>
        (simulateQ cachingOracle (cont u)).run (cache₀.cacheQuery t u)) := by
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
    have hstep :
        (liftM (cachingOracle (spec := CMOracle M S C) t) :
          StateT (QueryCache (CMOracle M S C))
            (OracleComp (CMOracle M S C)) _).run cache₀ =
        (liftM (query (spec := CMOracle M S C) t) >>= fun u =>
          pure (u, cache₀.cacheQuery t u) : OracleComp (CMOracle M S C) _) := by
      simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.run_bind, StateT.run_get, pure_bind, hfresh]
      show (StateT.lift (PFunctor.FreeM.lift (query (spec := CMOracle M S C) t)) cache₀ >>= _) = _
      simp only [StateT.lift, bind_assoc, pure_bind,
        modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.run]
    rw [hstep, bind_assoc]
    simpa [OracleQuery.cont_query]
  rw [hrun, probEvent_bind_eq_tsum]
  calc
    ∑' u, Pr[= u | (liftM (query (spec := CMOracle M S C) t) : OracleComp _ _)] *
        Pr[fun z => z.1 = true |
          (simulateQ cachingOracle (cont u)).run (cache₀.cacheQuery t u)]
      ≤ ∑' u, if u = target then (Fintype.card C : ℝ≥0∞)⁻¹ else 0 := by
        refine ENNReal.tsum_le_tsum fun u => ?_
        by_cases hu : u = target
        · calc
            Pr[= u | (liftM (query (spec := CMOracle M S C) t) : OracleComp _ _)] *
                Pr[fun z => z.1 = true |
                  (simulateQ cachingOracle (cont u)).run
                    (cache₀.cacheQuery t u)]
              ≤ Pr[= u | (liftM (query (spec := CMOracle M S C) t) : OracleComp _ _)] * 1 :=
                  mul_le_mul' le_rfl probEvent_le_one
            _ = (Fintype.card C : ℝ≥0∞)⁻¹ := by
                rw [mul_one]
                simpa using (probOutput_query (spec := CMOracle M S C) t u)
            _ = if u = target then (Fintype.card C : ℝ≥0∞)⁻¹ else 0 := by simp [hu]
        · rw [hzero u hu]
          simp [hu]
    _ = (Fintype.card C : ℝ≥0∞)⁻¹ := by
        rw [tsum_ite_eq target]

omit [DecidableEq C] [Inhabited C] in
/-- Arithmetic: `a/(2C) + b/C = (a + 2b)/(2C)`. -/
lemma add_div_two_card
    (a b : ℕ) :
    ((a : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
      ((b : ℕ) : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ =
    ((a + 2 * b : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
  set D := (2 * (Fintype.card C : ℝ≥0∞))
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [mul_comm (((b : ℕ) : ℝ≥0∞)) ((Fintype.card C : ℝ≥0∞)⁻¹)]
  have hD_inv : (Fintype.card C : ℝ≥0∞)⁻¹ = D⁻¹ * 2 := by
    simp only [D]
    rw [ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)),
      mul_comm (2 : ℝ≥0∞)⁻¹ _, mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), mul_one]
  rw [hD_inv, mul_assoc, ← mul_add]
  congr 1
  push_cast
  ring
