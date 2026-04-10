/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.Unpredictability
import VCVio.EvalDist.TVDist
import VCVio.ProgramLogic.Notation
import VCVio.ProgramLogic.Relational.SimulateQ

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

open scoped Classical in
omit [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] [DecidableEq C] in
/-- If a fixed fresh query is the only way to win, its success probability is `1 / |C|`. -/
lemma probEvent_from_fresh_query_le_inv
    (t : (CMOracle M S C).Domain)
    (target : C)
    (cache₀ : QueryCache (CMOracle M S C))
    (hfresh : cache₀ t = none)
    (cont : C → OracleComp (CMOracle M S C) Bool)
    (hzero : ∀ u, u ≠ target →
      Pr[ fun z => z.1 = true |
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
      change (StateT.lift (PFunctor.FreeM.lift (query (spec := CMOracle M S C) t)) cache₀ >>= _) = _
      simp only [StateT.lift, bind_assoc, pure_bind,
        modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.run]
    rw [hstep, bind_assoc]
    simp [OracleQuery.cont_query]
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
                simp
            _ = if u = target then (Fintype.card C : ℝ≥0∞)⁻¹ else 0 := by simp [hu]
        · rw [hzero u hu]
          simp [hu]
    _ = (Fintype.card C : ℝ≥0∞)⁻¹ := by
        rw [tsum_ite_eq target]
