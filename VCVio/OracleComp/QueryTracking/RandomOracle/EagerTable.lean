/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
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

/-- **Two-cell marginalization, post-composed.** For any continuation `ψ : (D → R) → α` and any
two distinct coordinates `t₁ ≠ t₂`, drawing fresh independent uniforms `u₁, u₂`, then a full
uniform table `g`, and evaluating `ψ` on the table with both coordinates overwritten yields the
same distribution as evaluating `ψ` on a directly drawn uniform table.

This is the joint marginal independence at the coordinate pair `(t₁, t₂)`: those two coordinates
are jointly uniform and independent of the rest, so replacing them with fresh independent uniforms
leaves the joint distribution unchanged. Two-cell analogue of
`evalDist_uniformSample_bind_update_map`.

Used at the slot-positive case of the DC unlinkability reduction to marginalize the two cells
`((tag, 0), n)` (read by M) and `((tag, slotK), n)` (read by S, with `slotK ≠ 0`) as independent
uniforms, enabling the IH-rename closure without any per-step cacheBadReader charge. -/
lemma evalDist_uniformSample_bind_update_two_map {α : Type} {t₁ t₂ : D} (hne : t₁ ≠ t₂)
    (ψ : (D → R) → α) :
    𝒟[do let u₁ ← $ᵗ R; let u₂ ← $ᵗ R; let g ← $ᵗ (D → R);
         pure (ψ (Function.update (Function.update g t₁ u₁) t₂ u₂))] =
      𝒟[do let g ← $ᵗ (D → R); pure (ψ g)] := by
  -- Commute the two updates (distinct coords) so `t₂` is the OUTER update; the inner shape then
  -- matches `evalDist_uniformSample_bind_update_map` at `t₂` for each fixed `u₁`.
  have hcomm : (do let u₁ ← $ᵗ R; let u₂ ← $ᵗ R; let g ← $ᵗ (D → R);
                   pure (ψ (Function.update (Function.update g t₁ u₁) t₂ u₂)))
      = (do let u₁ ← $ᵗ R; let u₂ ← $ᵗ R; let g ← $ᵗ (D → R);
            pure (ψ (Function.update (Function.update g t₂ u₂) t₁ u₁))) := by
    refine bind_congr fun u₁ => bind_congr fun u₂ => bind_congr fun g => ?_
    rw [Function.update_comm hne]
  rw [hcomm]
  -- Inner collapse: for each `u₁`, the `u₂; g; pure (ψ (update (update g t₂ u₂) t₁ u₁))` binder
  -- chain collapses to `g; pure (ψ (update g t₁ u₁))` by single-cell marginalization at `t₂`.
  have hInner : ∀ u₁ : R,
      𝒟[(do let u₂ ← $ᵗ R; let g ← $ᵗ (D → R);
            pure (ψ (Function.update (Function.update g t₂ u₂) t₁ u₁)))]
        = 𝒟[(do let g ← $ᵗ (D → R); pure (ψ (Function.update g t₁ u₁)))] := fun u₁ =>
    evalDist_uniformSample_bind_update_map t₂ (fun h => ψ (Function.update h t₁ u₁))
  -- Outer rewrite: `evalDist_bind` exposes the inner under PMF.bind; pointwise apply `hInner`.
  -- Express the LHS and the single-cell-collapsed midpoint as monadic binds so `evalDist_bind`
  -- + `congrArg` + `funext` can apply `hInner` pointwise in `u₁`.
  have hOuter :
      𝒟[($ᵗ R) >>= fun u₁ =>
            (do let u₂ ← $ᵗ R; let g ← $ᵗ (D → R);
                pure (ψ (Function.update (Function.update g t₂ u₂) t₁ u₁)))]
        = 𝒟[($ᵗ R) >>= fun u₁ =>
            (do let g ← $ᵗ (D → R); pure (ψ (Function.update g t₁ u₁)))] := by
    rw [evalDist_bind, evalDist_bind]
    refine congrArg _ (funext fun u₁ => ?_)
    exact hInner u₁
  -- The LHS of `hOuter` is definitionally the same as `(u₁;u₂;g; …)`.
  change 𝒟[($ᵗ R) >>= fun u₁ =>
            (do let u₂ ← $ᵗ R; let g ← $ᵗ (D → R);
                pure (ψ (Function.update (Function.update g t₂ u₂) t₁ u₁)))] = _
  rw [hOuter]
  -- Outer-`t₁` single-cell collapse: `u₁; g; pure (ψ (update g t₁ u₁))` → `g; pure (ψ g)`.
  exact evalDist_uniformSample_bind_update_map t₁ ψ

/-- **Lazy random oracle equals eager full-table sampling — cache-parametrized form.**

Running `oa` under the lazy random oracle starting from cache `c` yields the same output
distribution as: sample a full table `g : D → R` uniformly, then evaluate `oa` deterministically
against the table that overlays `c` on `g`.

This is the induction vehicle: the cache `c` is generalized so the `query`/`bind` step can recurse
through `cacheQuery`. -/
theorem evalDist_simulateQ_randomOracle_run'_eq_tableExtending
    {α : Type} (oa : OracleComp (D →ₒ R) α) (c : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ randomOracle oa).run' c] =
      𝒟[do let g ← $ᵗ (D → R);
            pure (evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g)) oa)] := by
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
        evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g)) (liftM ((D →ₒ R).query t) >>= k)
          = evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g))
              (k (tableExtending c g t)) := by
      intro g
      rw [evalWithAnswerFn_bind]
      change evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g))
        (k (simulateQ (QueryImpl.ofFn (tableExtending c g))
          (liftM ((D →ₒ R).query t)))) = _
      rw [simulateQ_spec_query]
      rfl
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
        evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g')) (k (tableExtending c g' t))
        with hψ
      have hfun : ∀ u : R, (fun g : D → R =>
            evalWithAnswerFn (QueryImpl.ofFn (tableExtending (c.cacheQuery t u) g)) (k u))
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
      𝒟[do let g ← $ᵗ (D → R); pure (evalWithAnswerFn (QueryImpl.ofFn g) oa)] := by
  rw [evalDist_simulateQ_randomOracle_run'_eq_tableExtending oa ∅]
  refine congrArg _ ?_
  refine congrArg _ (funext fun g => ?_)
  rw [tableExtending_empty]

end OracleComp
