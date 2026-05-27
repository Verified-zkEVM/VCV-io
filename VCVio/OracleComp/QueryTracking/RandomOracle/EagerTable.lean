/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Lazy Random Oracle Equals Eager Full-Table Sampling

For an oracle specification `D →ₒ R` with a single constant range `R`, running an
`OracleComp (D →ₒ R) α` under the lazy random oracle (`OracleSpec.randomOracle`,
i.e. `uniformSampleImpl.withCaching`) has the same output distribution as the eager
strategy: sample a *full* answer table `f : D → R` uniformly, then evaluate the
computation deterministically against `f` via `evalWithAnswerFn`.

The lazy oracle samples a fresh uniform value on first query and caches it for
consistency, so caching only ever affects *repeated* queries. Since every fresh
table entry is uniform and independent, lazily sampling on demand is
distributionally identical to pre-sampling the whole table. The marginalization
lemma `evalDist_uniformSample_bind_update` is the workhorse: it absorbs each
fresh on-demand uniform draw into the pre-sampled table.

## Main results

* `evalDist_simulateQ_randomOracle_run'_eq_tableExtending`: the generalized,
  cache-parametrized form, the induction vehicle.
* `evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable`: the empty-cache
  corollary — the lazy-vs-eager equivalence proper.
-/

open OracleComp OracleSpec

universe u v w

namespace OracleComp

variable {D R : Type} [DecidableEq D] [Finite D] [Finite R] [Nonempty R]
  [SampleableType R] [SampleableType (D → R)]

/-- View a function `f : D → R` as a total answer function (`QueryImpl (D →ₒ R) Id`) for the
single-oracle constant-range specification `D →ₒ R`. Each query at index `t : D` is answered by
`f t`. -/
@[reducible] def tableImpl (f : D → R) : QueryImpl (D →ₒ R) Id := fun t => f t

/-- The total answer table obtained by overlaying a `QueryCache` on top of a full function table:
cached entries take priority, uncached coordinates fall through to `g`. -/
@[reducible] def tableExtending (c : (D →ₒ R).QueryCache) (g : D → R) : D → R :=
  fun t => (c t).getD (g t)

omit [Finite D] [Finite R] [Nonempty R] [SampleableType R] [SampleableType (D → R)] in
/-- Overlaying `c.cacheQuery t u` on `g` is the `t`-update of overlaying `c` on `g`. -/
lemma tableExtending_cacheQuery (c : (D →ₒ R).QueryCache) (g : D → R)
    (t : D) (u : R) :
    tableExtending (c.cacheQuery t u) g = Function.update (tableExtending c g) t u := by
  funext t'
  by_cases ht : t' = t
  · subst ht; simp [tableExtending, QueryCache.cacheQuery]
  · simp [tableExtending, QueryCache.cacheQuery_of_ne _ _ ht, Function.update_of_ne ht]

omit [Finite D] [Finite R] [Nonempty R] [SampleableType R] [SampleableType (D → R)] in
/-- When `t` is uncached, updating the overlaid table at `t` equals overlaying the cache on the
updated full table. -/
lemma tableExtending_update_of_none (c : (D →ₒ R).QueryCache) (g : D → R)
    {t : D} (hc : c t = none) (u : R) :
    Function.update (tableExtending c g) t u = tableExtending c (Function.update g t u) := by
  funext t'
  by_cases ht : t' = t
  · subst ht; simp [tableExtending, hc]
  · simp [tableExtending, Function.update_of_ne ht]

/-- **Marginalization, post-composed.** For any continuation `ψ : (D → R) → α`, drawing a fresh
uniform `u`, then a full uniform table `g`, and evaluating `ψ` on `Function.update g t u` has the
same distribution as evaluating `ψ` on a directly drawn uniform table. -/
lemma evalDist_uniformSample_bind_update_map {α : Type} (t : D) (ψ : (D → R) → α) :
    𝒟[do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (ψ (Function.update g t u))] =
      𝒟[do let g ← $ᵗ (D → R); pure (ψ g)] := by
  have hL : (do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (ψ (Function.update g t u))) =
      ψ <$> (do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u)) := by
    simp [map_bind, bind_pure_comp]
  have hR : (do let g ← $ᵗ (D → R); pure (ψ g)) = ψ <$> ($ᵗ (D → R)) := by
    simp [bind_pure_comp]
  rw [hL, hR, evalDist_map, evalDist_map, evalDist_uniformSample_bind_update t]

/-- **Lazy random oracle equals eager full-table sampling — cache-parametrized form.**

Running `oa` under the lazy random oracle starting from cache `c` yields the same output
distribution as: sample a full table `g : D → R` uniformly, then evaluate `oa` deterministically
against the table that overlays `c` on `g`.

This is the induction vehicle: the cache `c` is generalized so the `query`/`bind` step can recurse
through `cacheQuery`. -/
theorem evalDist_simulateQ_randomOracle_run'_eq_tableExtending
    {α : Type} (oa : OracleComp (D →ₒ R) α) (c : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ randomOracle oa).run' c] =
      𝒟[do let g ← $ᵗ (D → R); pure (evalWithAnswerFn (tableImpl (tableExtending c g)) oa)] := by
  classical
  letI := Fintype.ofFinite D
  letI := Fintype.ofFinite R
  haveI : Nonempty (D → R) := ⟨fun _ => Classical.arbitrary R⟩
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    have hlhs : (simulateQ randomOracle (pure a : OracleComp (D →ₒ R) α)).run' c
        = (pure a : ProbComp α) := by
      rw [simulateQ_pure]
      change (fun x => x.1) <$> (pure (a, c) : ProbComp (α × _)) = pure a
      rw [map_pure]
    rw [hlhs]
    simp only [evalWithAnswerFn_pure]
    symm
    refine evalDist_ext fun x => ?_
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
      tsum_probOutput_eq_one' (mx := $ᵗ (D → R)) (by simp), one_mul]
  | query_bind t k ih =>
    have hred :
        (simulateQ randomOracle (liftM ((D →ₒ R).query t) >>= k)).run' c
          = ((randomOracle (spec := (D →ₒ R)) t).run c) >>=
            fun p : R × (D →ₒ R).QueryCache =>
              (simulateQ randomOracle (k p.1)).run' p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query]
      change Prod.fst <$> (((randomOracle (spec := (D →ₒ R)) t).run c) >>= fun p =>
        (simulateQ randomOracle (k p.1)).run p.2) = _
      rw [map_bind]
      rfl
    have heval : ∀ g : D → R,
        evalWithAnswerFn (tableImpl (tableExtending c g)) (liftM ((D →ₒ R).query t) >>= k)
          = evalWithAnswerFn (tableImpl (tableExtending c g))
              (k (tableExtending c g t)) := by
      intro g
      rw [evalWithAnswerFn_bind]
      change evalWithAnswerFn (tableImpl (tableExtending c g))
        (k (simulateQ (tableImpl (tableExtending c g)) (liftM ((D →ₒ R).query t)))) = _
      rw [simulateQ_spec_query]
    rw [hred]
    simp_rw [heval]
    rcases hc : c t with _ | u
    · -- Cache miss: a fresh uniform draw, absorbed by marginalization.
      rw [show ((randomOracle (spec := (D →ₒ R)) t).run c) =
            (fun u => (u, c.cacheQuery t u)) <$> ($ᵗ R) from
            QueryImpl.withCaching_run_none _ hc]
      rw [show (((fun u => (u, c.cacheQuery t u)) <$> ($ᵗ R)) >>=
              fun p : R × (D →ₒ R).QueryCache =>
                (simulateQ randomOracle (k p.1)).run' p.2)
            = (($ᵗ R) >>= fun u =>
                (simulateQ randomOracle (k u)).run' (c.cacheQuery t u)) from by
        rw [map_eq_bind_pure_comp]; simp [bind_assoc]]
      -- The continuation, abstracted as a function of the full table.
      set ψ : (D → R) → α := fun g' =>
        evalWithAnswerFn (tableImpl (tableExtending c g')) (k (tableExtending c g' t)) with hψ
      have hfun : ∀ u : R, (fun g : D → R =>
            evalWithAnswerFn (tableImpl (tableExtending (c.cacheQuery t u) g)) (k u))
          = fun g : D → R => ψ (Function.update g t u) := by
        intro u
        funext g
        simp only [hψ]
        rw [tableExtending_cacheQuery, ← tableExtending_update_of_none c g hc u]
        simp only [Function.update_self]
      trans 𝒟[do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (ψ (Function.update g t u))]
      · rw [evalDist_bind, evalDist_bind]
        refine congrArg _ (funext fun u => ?_)
        rw [ih u (c.cacheQuery t u), bind_pure_comp, bind_pure_comp, hfun u]
      · exact evalDist_uniformSample_bind_update_map t ψ
    · -- Cache hit: no new sample, table already has `c t = some u`.
      rw [show ((randomOracle (spec := (D →ₒ R)) t).run c) = (pure (u, c) : ProbComp _) from
            QueryImpl.withCaching_run_some _ hc]
      rw [pure_bind]
      rw [ih u c]
      refine congrArg _ ?_
      refine congrArg _ (funext fun g => ?_)
      congr 1
      have : tableExtending c g t = u := by simp [tableExtending, hc]
      rw [this]

omit [DecidableEq D] [Finite D] [Finite R] [Nonempty R] [SampleableType R]
  [SampleableType (D → R)] in
/-- Overlaying the empty cache leaves a full table unchanged. -/
lemma tableExtending_empty (g : D → R) :
    tableExtending (∅ : (D →ₒ R).QueryCache) g = g := by
  funext t; simp [tableExtending]

/-- **Lazy random oracle equals eager full-table sampling.**

Running an `OracleComp (D →ₒ R) α` under the lazy random oracle from the empty cache yields the
same output distribution as: sample a full answer table `g : D → R` uniformly, then evaluate the
computation deterministically against `g`.

This is the empty-cache specialization of
`evalDist_simulateQ_randomOracle_run'_eq_tableExtending`: the classic lazy-vs-eager-sampling
equivalence. Lazy caching only affects repeated queries, and since each fresh table entry is
uniform and independent, sampling on demand matches pre-sampling the whole table. -/
theorem evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable
    {α : Type} (oa : OracleComp (D →ₒ R) α) :
    𝒟[(simulateQ randomOracle oa).run' ∅] =
      𝒟[do let g ← $ᵗ (D → R); pure (evalWithAnswerFn (tableImpl g) oa)] := by
  rw [evalDist_simulateQ_randomOracle_run'_eq_tableExtending oa ∅]
  refine congrArg _ ?_
  refine congrArg _ (funext fun g => ?_)
  rw [tableExtending_empty]

end OracleComp
