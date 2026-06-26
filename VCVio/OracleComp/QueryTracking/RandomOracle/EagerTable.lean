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
  by_cases ht : t' = t <;> simp_all [tableExtending, QueryCache.cacheQuery, Function.update]

omit [Finite D] [Finite R] [Nonempty R] [SampleableType R] [SampleableType (D → R)] in
/-- When `t` is uncached, updating the overlaid table at `t` equals overlaying the cache on the
updated full table. -/
lemma tableExtending_update_of_none (c : (D →ₒ R).QueryCache) (g : D → R)
    {t : D} (hc : c t = none) (u : R) :
    Function.update (tableExtending c g) t u = tableExtending c (Function.update g t u) := by
  funext t'
  rcases eq_or_ne t' t with rfl | ht <;> simp_all [tableExtending]

/-- **Marginalization, post-composed.** For any continuation `ψ : (D → R) → α`, drawing a fresh
uniform `u`, then a full uniform table `g`, and evaluating `ψ` on `Function.update g t u` has the
same distribution as evaluating `ψ` on a directly drawn uniform table. -/
lemma evalDist_uniformSample_bind_update_map {α : Type} (t : D) (ψ : (D → R) → α) :
    𝒟[do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (ψ (Function.update g t u))] =
      𝒟[do let g ← $ᵗ (D → R); pure (ψ g)] := by
  rw [bind_pure_comp, evalDist_map, ← evalDist_uniformSample_bind_update t]
  simp [map_bind, bind_pure_comp]

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
  simp_rw [Function.update_comm hne]
  rw [evalDist_bind]
  refine (congrArg _ (funext fun u₁ =>
    evalDist_uniformSample_bind_update_map t₂ fun h => ψ (Function.update h t₁ u₁))).trans ?_
  rw [← evalDist_bind]
  exact evalDist_uniformSample_bind_update_map t₁ ψ

omit [Finite D] [Finite R] [Nonempty R] in
/-- Pure-case base step for `evalDist_simulateQ_randomOracle_run'_eq_tableExtending`: running
`pure a` under the lazy oracle ignores the table, so its distribution is the constant `pure a`,
matching the eager side after the (discarded) uniform table draw. -/
private lemma evalDist_simulateQ_randomOracle_run'_pure_eq_tableExtending {α : Type} (a : α)
    (c : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ randomOracle (pure a : OracleComp (D →ₒ R) α)).run' c] =
      𝒟[do let g ← $ᵗ (D → R);
            pure (evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g)) (pure a))] := by
  refine evalDist_ext fun x => ?_
  simp [simulateQ_pure, evalWithAnswerFn_pure]

/-- Inductive `query`/`bind` step for `evalDist_simulateQ_randomOracle_run'_eq_tableExtending`:
given the eager-table identity for every continuation `k u`, it holds for `liftM (query t) >>= k`.
On a cache miss the fresh uniform draw is absorbed into the table by
`evalDist_uniformSample_bind_update_map`; on a cache hit the table already answers with `c t`. -/
private lemma evalDist_simulateQ_randomOracle_run'_query_bind_eq_tableExtending {α : Type} (t : D)
    (k : R → OracleComp (D →ₒ R) α)
    (ih : ∀ (u : R) (c : (D →ₒ R).QueryCache),
      𝒟[(simulateQ randomOracle (k u)).run' c] =
        𝒟[do let g ← $ᵗ (D → R);
              pure (evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g)) (k u))])
    (c : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ randomOracle (liftM ((D →ₒ R).query t) >>= k)).run' c] =
      𝒟[do let g ← $ᵗ (D → R);
            pure (evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g))
              (liftM ((D →ₒ R).query t) >>= k))] := by
  classical
  letI := Fintype.ofFinite R
  haveI : Nonempty (D → R) := ⟨fun _ => Classical.arbitrary R⟩
  have hred :
      (simulateQ randomOracle (liftM ((D →ₒ R).query t) >>= k)).run' c
        = ((randomOracle (spec := (D →ₒ R)) t).run c) >>=
          fun p : R × (D →ₒ R).QueryCache =>
            (simulateQ randomOracle (k p.1)).run' p.2 := by
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rfl
  have heval : ∀ g : D → R,
      evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g)) (liftM ((D →ₒ R).query t) >>= k)
        = evalWithAnswerFn (QueryImpl.ofFn (tableExtending c g))
            (k (tableExtending c g t)) := by
    intro g
    rw [evalWithAnswerFn_bind]
    simp only [evalWithAnswerFn, simulateQ_spec_query, QueryImpl.ofFn_apply]
  rw [hred]
  simp_rw [heval]
  rcases hc : c t with _ | u
  · rw [QueryImpl.withCaching_run_none _ hc, map_eq_bind_pure_comp]
    simp only [Function.comp, bind_assoc, pure_bind]
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
  · rw [QueryImpl.withCaching_run_some _ hc, pure_bind, ih u c]
    have h : ∀ g : D → R, tableExtending c g t = u := fun g => by simp [tableExtending, hc]
    simp_rw [h]

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
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => exact evalDist_simulateQ_randomOracle_run'_pure_eq_tableExtending a c
  | query_bind t k ih =>
    exact evalDist_simulateQ_randomOracle_run'_query_bind_eq_tableExtending t k ih c

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
  simp_rw [tableExtending_empty]

end OracleComp
