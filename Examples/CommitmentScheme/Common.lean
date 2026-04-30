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
# Random-oracle commitment scheme — shared definitions

Shared oracle and scheme definitions plus the basic single-fresh-query
unpredictability lemma used throughout the binding, extractability, and
hiding proofs in `Examples/CommitmentScheme/`.

The scheme: commit to a message `m : M` by sampling a uniform salt
`s : S` and outputting `(H(m, s), s)`, where `H : (M × S) → C` is the
random oracle.

* `CMOracle M S C` — the random-oracle spec `H : (M × S) → C`.
* `CMCommit m s` — the commit algorithm (queries `H` at `(m, s)`).
* `CMCheck c m s` — the verification algorithm (queries `H` at `(m, s)`,
  compares to the supplied commitment).
* `probEvent_from_fresh_query_le_inv` — basic `1/|C|` unpredictability
  bound for a single fresh oracle query.

When run under `cachingOracle` from an empty cache, all queries by both
adversary and verifier share the same random function — this is how we
model the *shared* random oracle.

`probEvent_from_fresh_query_le_inv` is the atomic building block that all
three security proofs reduce to: a single fresh oracle answer is
distributionally `Uniform C`, so it hits any fixed target with probability
exactly `1/|C|`. Composed with the birthday bound on cache collisions and
identical-until-bad TV-distance bounds, this fact powers the binding,
extractability, and hiding theorems.
-/

open OracleSpec OracleComp ENNReal

/-! ## Oracle and scheme algorithms -/

/-- Oracle spec for the random-oracle commitment scheme:
the random oracle has signature `H : (M × S) → C`. -/
abbrev CMOracle (M : Type) (S : Type) (C : Type) : OracleSpec (M × S) := fun _ => C

variable {M S C : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C]

instance : DecidableEq (M × S) := instDecidableEqProd

/-- Commit to message `m` with salt `s` by querying the random oracle at `(m, s)`. -/
def CMCommit (m : M) (s : S) : OracleComp (CMOracle M S C) C :=
  (CMOracle M S C).query (m, s)

/-- Check commitment `c` against opening `(m, s)`: query the oracle at `(m, s)` and
compare to `c`. Under a shared `cachingOracle` this returns the same value the
honest commit phase wrote into the cache. -/
def CMCheck (c : C) (m : M) (s : S) : OracleComp (CMOracle M S C) Bool := do
  let c' ← (CMOracle M S C).query (m, s)
  return (c == c')

/-! ## Single-fresh-query unpredictability -/

open scoped Classical in
omit [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] [DecidableEq C] in
/-- **Single fresh-query unpredictability bound (`1/|C|`).**

If `t` is *fresh* in the cache `cache₀` and the only way for the
continuation `cont` to win is for the fresh query at `t` to return a fixed
target value, then the win probability is at most `1/|C|`. The atomic
fact: a fresh random-oracle answer is uniform on `C`, so it equals any
specific target with probability exactly `1/|C|`. -/
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
      (simulateQ (CMOracle M S C).cachingOracle do
        let u ← (CMOracle M S C).query t
        cont u).run cache₀] ≤
      (Fintype.card C : ℝ≥0∞)⁻¹ := by
  have hrun :
      (simulateQ (CMOracle M S C).cachingOracle do
        let u ← (CMOracle M S C).query t
        cont u).run cache₀ =
      (do
        let u ← (CMOracle M S C).query t
        (simulateQ cachingOracle (cont u)).run (cache₀.cacheQuery t u)) := by
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
    have hstep :
        (liftM ((CMOracle M S C).cachingOracle t) :
          StateT (QueryCache (CMOracle M S C))
            (OracleComp (CMOracle M S C)) _).run cache₀ =
        (do
          let u ← (CMOracle M S C).query t
          pure (u, cache₀.cacheQuery t u)) := by
      simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.run_bind, StateT.run_get, pure_bind, hfresh]
      change (StateT.lift (PFunctor.FreeM.lift ((CMOracle M S C).query t)) cache₀ >>= _) = _
      simp only [StateT.lift, bind_assoc, pure_bind,
        modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.run]
      rfl
    rw [hstep, bind_assoc]
    simp [OracleQuery.cont_query]
  rw [hrun, probEvent_bind_eq_tsum]
  calc
    ∑' u, Pr[= u | ((CMOracle M S C).query t : OracleComp (CMOracle M S C) _)] *
        Pr[fun z => z.1 = true |
          (simulateQ cachingOracle (cont u)).run (cache₀.cacheQuery t u)]
      ≤ ∑' u, if u = target then (Fintype.card C : ℝ≥0∞)⁻¹ else 0 := by
        refine ENNReal.tsum_le_tsum fun u => ?_
        by_cases hu : u = target
        · calc
            Pr[= u | ((CMOracle M S C).query t : OracleComp (CMOracle M S C) _)] *
                Pr[fun z => z.1 = true |
                  (simulateQ cachingOracle (cont u)).run
                    (cache₀.cacheQuery t u)]
              ≤ Pr[= u | ((CMOracle M S C).query t : OracleComp (CMOracle M S C) _)] * 1 :=
                  mul_le_mul' le_rfl probEvent_le_one
            _ = (Fintype.card C : ℝ≥0∞)⁻¹ := by
                rw [mul_one]
                simp
            _ = if u = target then (Fintype.card C : ℝ≥0∞)⁻¹ else 0 := by simp [hu]
        · rw [hzero u hu]
          simp [hu]
    _ = (Fintype.card C : ℝ≥0∞)⁻¹ := by
        rw [tsum_ite_eq target]
