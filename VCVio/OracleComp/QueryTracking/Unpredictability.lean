/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters, Quang Dao
-/
import VCVio.OracleComp.QueryTracking.Birthday
import VCVio.OracleComp.QueryTracking.ProgrammingOracle
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.ProgramLogic.Relational.ProgrammingOracle

/-!
# ROM Unpredictability and Collision Win Bounds

Fresh query uniformity, cache preimage bounds, and the collision-based win
probability theorem.

## Unpredictability

`HasUnpredictableSample samples β` packages "the probability of any specific outcome of
`samples : ProbComp α` is at most `β`". It is the abstract handle through which downstream
collision bounds (notably `programming_collision_bound`) ingest min-entropy of a
sample distribution without re-deriving uniform-sample arithmetic at each call site.

Instances:
* `HasUnpredictableSample.uniformSample`: `$ᵗ α` is `1/|α|`-unpredictable.
* `HasUnpredictableSample.mono`: `β`-unpredictability transports up to any `β' ≥ β`.

## Programming collision bound

`programming_collision_bound` then gives the headline corollary used by Fiat-Shamir-style
"identical-until-bad" reductions: the TV-distance between running an oracle computation
under pure caching versus under a `qP`-point programming policy is bounded by `qP * qH * β`,
when the adversary's queries are drawn from a `β`-unpredictable distribution and `oa`
makes at most `qH` queries.
-/

open OracleSpec OracleComp ENNReal Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

/-! ## Unpredictability -/

section Unpredictability

variable {spec' : OracleSpec.{0, 0} ι} [spec'.DecidableEq] [spec'.Fintype] [spec'.Inhabited]

omit [spec'.DecidableEq] in
/-- **Fresh query uniformity**: querying `cachingOracle` at an uncached point
yields each value with probability `1/|C|`. -/
theorem probOutput_fresh_cachingOracle_query
    (t : spec'.Domain) (u : spec'.Range t)
    (cache₀ : QueryCache spec') (hfresh : cache₀ t = none) :
    Pr[= (u, cache₀.cacheQuery t u) | (cachingOracle t).run cache₀] =
      (Fintype.card (spec'.Range t) : ℝ≥0∞)⁻¹ := by
  simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind, hfresh]
  simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.run_lift, bind_assoc,
    pure_bind]
  simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, StateT.run]
  erw [probOutput_map_injective _ (fun a b hab => by exact Prod.ext_iff.mp hab |>.1)]
  exact probOutput_query t u

omit [spec'.DecidableEq] in
/-- **WARNING: trivially true.** The proof uses only `probEvent_le_one`; the query bound
`hbound` and `target` are completely unused. The conclusion `Pr[...] * |C|⁻¹ ≤ |C|⁻¹`
holds for any computation regardless of how many queries it makes.

A meaningful unpredictability bound should use `hbound` to establish that the queried point
is fresh, giving a tight `1/|C|` bound on the probability of guessing the ROM output. -/
theorem probEvent_unqueried_match_le {α : Type} {t : ℕ}
    (oa : OracleComp spec' α)
    (_hbound : IsPerIndexQueryBound oa (fun _ => t))
    (predict : spec'.Domain) (_target : spec'.Range predict) :
    Pr[fun z => z.2 predict = none |
      (simulateQ cachingOracle oa).run ∅] *
      (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ ≤
      (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ := by
  calc Pr[fun z => z.2 predict = none | (simulateQ cachingOracle oa).run ∅] *
      (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹
      ≤ 1 * (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ :=
        mul_le_mul' probEvent_le_one le_rfl
    _ = (Fintype.card (spec'.Range predict) : ℝ≥0∞)⁻¹ := one_mul _

/-- **Cache preimage bound**: if the initial cache contains at most one preimage
of a target value `v₀`, then the probability that `simulateQ cachingOracle oa`
creates a fresh cache entry equal to `v₀` is at most `n / |C|`, where `n` is the
total query bound. Each cache miss is a fresh uniform draw, so a union bound
over the at most `n` misses gives the result.

This is the reusable ROM lemma for the extractability "fresh target hit" case. -/
theorem probEvent_cache_has_value_le_of_unique_preimage {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (v₀ : spec.Range default)
    (cache₀ : QueryCache spec)
    (hunique_v₀ :
      ∀ t₀ t₁ : spec.Domain,
        ∀ v₁ : spec.Range t₀, ∀ v₂ : spec.Range t₁,
          cache₀ t₀ = some v₁ →
          cache₀ t₁ = some v₂ →
          HEq v₁ v₀ →
          HEq v₂ v₀ →
          t₀ = t₁) :
    Pr[fun z => ∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
        z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀ |
      (simulateQ cachingOracle oa).run cache₀] ≤
      (n : ℝ≥0∞) * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  classical
  let C := (Fintype.card (spec.Range default) : ℝ≥0∞)
  induction oa using OracleComp.inductionOn generalizing n cache₀ with
  | pure x =>
    -- Pure: cache unchanged, event is False (no new entries)
    have : Pr[fun z => ∃ t₀ v, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀ |
        (simulateQ cachingOracle (pure x)).run cache₀] = 0 := by
      rw [simulateQ_pure]
      refine probEvent_eq_zero fun z hz h => ?_
      simp only [StateT.run] at hz; obtain ⟨_, rfl⟩ := hz
      obtain ⟨t₀, v, hcache, hnone, _⟩ := h
      simp [hnone] at hcache
    rw [this]; exact zero_le _
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at hbound
    obtain ⟨hpos, hrest⟩ := hbound
    by_cases ht : ∃ v, cache₀ t = some v
    · -- Cache hit: cache unchanged
      obtain ⟨v, hv⟩ := ht
      have hrun : (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
          (simulateQ cachingOracle (mx v)).run cache₀ := by
        simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
        have hcache : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
            pure (v, cache₀) := by
          simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
            StateT.run_bind, StateT.run_get, hv, pure_bind, StateT.run_pure]
        rw [hcache, pure_bind]
        simp [OracleQuery.cont_query]
      rw [hrun]
      calc Pr[fun z => ∃ t₀ v, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀ |
            (simulateQ cachingOracle (mx v)).run cache₀]
          ≤ ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ := ih v (n - 1) (hrest v) cache₀ hunique_v₀
        _ ≤ (n : ℝ≥0∞) * C⁻¹ := by
            gcongr
            exact_mod_cast Nat.sub_le n 1
    · -- Cache miss
      push Not at ht
      have ht_none : cache₀ t = none := by
        cases h : cache₀ t with | none => rfl | some v => exact absurd h (ht v)
      have hrun : (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
          (liftM (query t) >>= fun u =>
            (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)) := by
        simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
        have hstep : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
            (liftM (query t) >>= fun u =>
              pure (u, cache₀.cacheQuery t u) : OracleComp spec _) := by
          simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
            StateT.run_bind, StateT.run_get, pure_bind, ht_none]
          change (StateT.lift (PFunctor.FreeM.lift (query t)) cache₀ >>= _) = _
          simp only [StateT.lift, bind_assoc, pure_bind,
            modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, StateT.run]
          rfl
        rw [hstep, bind_assoc]; simp [pure_bind]
      rw [hrun]
      -- Decompose: ∑ u, Pr[=u|query t] * Pr[event | cont(u)]
      rw [probEvent_bind_eq_tsum]
      -- Each term: Pr[= u | query t] * Pr[event | cont(u)]
      -- For u with HEq u v₀: Pr[event | cont] ≤ 1, contribution ≤ 1/|C|
      -- For u without HEq u v₀: IH gives ≤ (n-1)/|C|, contribution ≤ Pr[=u]*((n-1)/|C|)
      -- Total ≤ 1/|C| + (n-1)/|C| = n/|C|
      -- Split sum into u with HEq u v₀ and u without.
      -- For u with HEq u v₀: contribution ≤ Pr[=u|query t] * 1 ≤ C⁻¹
      -- For u without: IH gives inner ≤ (n-1) * C⁻¹
      -- Total ≤ C⁻¹ + (n-1) * C⁻¹ = n * C⁻¹
      have hih : ∀ u : spec.Range t, ¬HEq u v₀ →
          Pr[fun z => ∃ t₀ v, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀ |
            (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)] ≤
          ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ := by
        intro u heq_v₀
        have hunique_v₀' :
            ∀ t₀ t₁ : spec.Domain,
              ∀ v₁ : spec.Range t₀, ∀ v₂ : spec.Range t₁,
                (cache₀.cacheQuery t u) t₀ = some v₁ →
                (cache₀.cacheQuery t u) t₁ = some v₂ →
                HEq v₁ v₀ →
                HEq v₂ v₀ →
                t₀ = t₁ := by
          intro t₀ t₁ v₁ v₂ hcache₁ hcache₂ hheq₁ hheq₂
          by_cases heq_t₀ : t₀ = t
          · subst heq_t₀
            rw [QueryCache.cacheQuery_self] at hcache₁
            cases hcache₁
            exact False.elim (heq_v₀ hheq₁)
          · by_cases heq_t₁ : t₁ = t
            · subst heq_t₁
              rw [QueryCache.cacheQuery_self] at hcache₂
              cases hcache₂
              exact False.elim (heq_v₀ hheq₂)
            · rw [QueryCache.cacheQuery_of_ne _ _ heq_t₀] at hcache₁
              rw [QueryCache.cacheQuery_of_ne _ _ heq_t₁] at hcache₂
              exact hunique_v₀ t₀ t₁ v₁ v₂ hcache₁ hcache₂ hheq₁ hheq₂
        calc Pr[fun z => ∃ t₀ v, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀ |
              (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)]
            ≤ Pr[fun z => ∃ t₀ v, z.2 t₀ = some v ∧
                (cache₀.cacheQuery t u) t₀ = none ∧ HEq v v₀ |
              (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)] := by
              apply probEvent_mono
              intro z hz ⟨t₀, v, hcache_f, hnone₀, hheq⟩
              by_cases heq_t : t₀ = t
              · -- t₀ = t: by cache monotonicity, z.2 t = some u, so v = u.
                -- Then HEq v v₀ = HEq u v₀, contradicting ¬HEq u v₀.
                exfalso
                subst heq_t
                have hle := simulateQ_cachingOracle_cache_le (mx u)
                  (cache₀.cacheQuery t₀ u) _ hz
                have hcu := QueryCache.cacheQuery_self cache₀ t₀ u
                have hzu : z.2 t₀ = some u := hle hcu
                rw [hzu] at hcache_f; cases hcache_f
                exact heq_v₀ hheq
              · exact ⟨t₀, v, hcache_f, QueryCache.cacheQuery_of_ne _ _ heq_t ▸ hnone₀, hheq⟩
          _ ≤ ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ := ih u (n - 1) (hrest u) _ hunique_v₀'
      -- Strategy: each Pr[=u]*inner ≤ C⁻¹ (for match) or Pr[=u]*(n-1)*C⁻¹ (for non-match)
      -- Summing: ≤ C⁻¹ + (n-1)*C⁻¹ = n*C⁻¹
      -- Key: the "match" terms sum to ≤ C⁻¹ because Pr[=u|query t] ≤ 1/|Range t| ≤ C⁻¹
      -- and at most one u satisfies HEq u v₀ (when types match).
      calc ∑' u, Pr[= u | (spec.query t : OracleComp spec _)] *
            Pr[fun z => ∃ t₀ v, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀ |
              (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)]
          ≤ ∑' u, ((if HEq u v₀ then C⁻¹ else 0) +
              Pr[= u | (spec.query t : OracleComp spec _)] *
                (((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹)) := by
            refine ENNReal.tsum_le_tsum fun u => ?_
            by_cases h : HEq u v₀
            · -- Match: Pr[=u] * inner ≤ Pr[=u] ≤ C⁻¹ ≤ C⁻¹ + rest
              simp only [h, ite_true]
              calc Pr[= u | (spec.query t : OracleComp spec _)] *
                    Pr[fun z => ∃ t₀ v, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀ |
                      (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)]
                  ≤ Pr[= u | (spec.query t : OracleComp spec _)] * 1 :=
                    mul_le_mul' le_rfl probEvent_le_one
                _ = Pr[= u | (spec.query t : OracleComp spec _)] := mul_one _
                _ ≤ (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
                    rw [show (spec.query t : OracleComp spec _) =
                      (query t : OracleComp spec _) from rfl]
                    exact le_of_eq (probOutput_query t u)
                _ ≤ C⁻¹ := ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (hrange t))
                _ ≤ C⁻¹ + _ := le_add_right le_rfl
            · -- No match: 0 + Pr[=u] * (n-1)*C⁻¹
              simp only [h, ite_false, zero_add]
              exact mul_le_mul' le_rfl (hih u h)
        _ = (∑' u, (if HEq u v₀ then C⁻¹ else 0)) +
            (∑' u, Pr[= u | (spec.query t : OracleComp spec _)]) *
              (((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        _ ≤ C⁻¹ + 1 * (((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹) := by
            apply add_le_add
            · -- ∑ (if HEq u v₀ then C⁻¹ else 0) ≤ C⁻¹
              -- At most one u satisfies HEq u v₀ per type.
              calc ∑' u, (if HEq u v₀ then C⁻¹ else (0 : ℝ≥0∞))
                  ≤ ∑' u, (if HEq u v₀ then (1 : ℝ≥0∞) else 0) * C⁻¹ := by
                    refine ENNReal.tsum_le_tsum fun u => ?_
                    split_ifs <;> simp
                _ = (∑' u, if HEq u v₀ then (1 : ℝ≥0∞) else 0) * C⁻¹ :=
                    ENNReal.tsum_mul_right
                _ ≤ 1 * C⁻¹ := by
                    apply mul_le_mul' _ le_rfl
                    -- At most one u : spec.Range t satisfies HEq u v₀
                    have hsub : ∀ (a b : spec.Range t), HEq a v₀ → HEq b v₀ → a = b :=
                      fun a b ha hb => eq_of_heq (ha.trans hb.symm)
                    rw [tsum_eq_sum (s := Finset.univ) (by simp),
                      show ∑ u : spec.Range t, (if HEq u v₀ then (1 : ℝ≥0∞) else 0) =
                        ((Finset.univ.filter (fun u : spec.Range t => HEq u v₀)).card : ℝ≥0∞)
                        from by rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
                          Finset.sum_const, nsmul_eq_mul, mul_one]]
                    exact_mod_cast Finset.card_le_one.mpr fun a ha b hb => by
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
                      exact hsub a b ha hb
                _ = C⁻¹ := one_mul _
            · exact mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = C⁻¹ + ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ := by rw [one_mul]
        _ = (n : ℝ≥0∞) * C⁻¹ := by
            rw [show C⁻¹ + ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ = (1 + (n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ from
              by rw [add_mul, one_mul]]
            congr 1
            have h1n : 1 + (n - 1 : ℕ) = n := Nat.add_sub_cancel' (by omega : 1 ≤ n)
            rw [show (1 : ℝ≥0∞) + ((n - 1 : ℕ) : ℝ≥0∞) = ((1 + (n - 1) : ℕ) : ℝ≥0∞) from by
              push_cast; rfl, h1n]

/-- Special case of
`probEvent_cache_has_value_le_of_unique_preimage` when the initial cache
contains at most one preimage of `v₀` because the cache is collision-free. -/
theorem probEvent_cache_has_value_le_of_noCollision {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (v₀ : spec.Range default)
    (cache₀ : QueryCache spec)
    (hno : ¬ CacheHasCollision cache₀) :
    Pr[fun z => ∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
        z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀ |
      (simulateQ cachingOracle oa).run cache₀] ≤
      (n : ℝ≥0∞) * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  refine probEvent_cache_has_value_le_of_unique_preimage
    (oa := oa) (n := n) hbound hrange v₀ cache₀ ?_
  intro t₀ t₁ v₁ v₂ hcache₀ hcache₁ hheq₀ hheq₁
  by_contra hne
  exact hno ⟨t₀, t₁, v₁, v₂, hne, hcache₀, hcache₁, hheq₀.trans hheq₁.symm⟩

/-- Special case of
`probEvent_cache_has_value_le_of_unique_preimage` when the initial cache
contains no preimage of `v₀`. -/
theorem probEvent_cache_has_value_le {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (v₀ : spec.Range default)
    (cache₀ : QueryCache spec)
    (hno_v₀ : ∀ t₀ : spec.Domain, ∀ v : spec.Range t₀, cache₀ t₀ = some v → ¬HEq v v₀) :
    Pr[fun z => ∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
        z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀ |
      (simulateQ cachingOracle oa).run cache₀] ≤
      (n : ℝ≥0∞) * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  refine probEvent_cache_has_value_le_of_unique_preimage
    (oa := oa) (n := n) hbound hrange v₀ cache₀ ?_
  intro t₀ t₁ v₁ _ hcache₁ _ hheq₁ _
  exact False.elim ((hno_v₀ t₀ v₁ hcache₁) hheq₁)

end Unpredictability

/-! ## Collision-Based Win Bound -/

/-- **WARNING: vacuously true.** The `[Unique ι]` hypothesis means `ι` has exactly one element,
but `CacheHasCollision` (used via `probEvent_cacheCollision_le_birthday'`) requires two *distinct*
oracle indices `t₁ ≠ t₂ : ι`, which is impossible when `ι` is unique. The event
`CacheHasCollision z.2` is therefore always false, making the bound trivially `0 ≤ ...`.

For a useful single-oracle collision bound, state it over `LogHasCollision` (which checks for
equal outputs on distinct *inputs* within the same oracle index) rather than `CacheHasCollision`
(which requires distinct indices). -/
theorem probEvent_collision_win_le {α : Type} {t : ℕ}
    [Inhabited ι] [Unique ι]
    (oa : OracleComp spec α)
    (win : α × QueryCache spec → Prop)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hC : 0 < Fintype.card (spec.Range default))
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (hwin : ∀ z ∈ support ((simulateQ cachingOracle oa).run ∅),
      win z → CacheHasCollision z.2) :
    Pr[win | (simulateQ cachingOracle oa).run ∅] ≤
      (t ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) :=
  le_trans (probEvent_mono hwin) (probEvent_cacheCollision_le_birthday' oa hbound hC hrange)

/-! ## `HasUnpredictableSample` -/

/-- A probabilistic computation `samples : ProbComp α` is **`β`-unpredictable** if every specific
outcome occurs with probability at most `β`. This is the standard "min-entropy at level
`log₂(1/β)`" notion, packaged as a structured proposition so that downstream collision bounds
can ingest it generically.

Equivalent to `∀ x, Pr[= x | samples] ≤ β`; the structure shape lets it serve as the canonical
abstract hypothesis for "values drawn from `samples` are hard to guess". -/
@[mk_iff]
structure HasUnpredictableSample {α : Type} (samples : ProbComp α) (β : ℝ≥0∞) : Prop where
  prob_le : ∀ x : α, Pr[= x | samples] ≤ β

namespace HasUnpredictableSample

variable {α : Type} {samples : ProbComp α} {β β' : ℝ≥0∞}

/-- Monotonicity in the bound: a `β`-unpredictable sample is also `β'`-unpredictable for any
`β' ≥ β`. -/
lemma mono (h : HasUnpredictableSample samples β) (hβ : β ≤ β') :
    HasUnpredictableSample samples β' :=
  ⟨fun x => (h.prob_le x).trans hβ⟩

/-- `$ᵗ α` is `(|α|)⁻¹`-unpredictable for any nonempty `Fintype`. -/
lemma uniformSample {α : Type} [SampleableType α] [Fintype α] [Nonempty α] :
    HasUnpredictableSample ($ᵗ α) ((Fintype.card α : ℝ≥0∞)⁻¹) :=
  ⟨fun x => le_of_eq (probOutput_uniformSample α x)⟩

end HasUnpredictableSample

/-! ## Sanity check: uniform sampling reproduces the canonical `1/|α|` shape -/

/-- For a `β`-unpredictable sampling distribution from a fintype, the per-sample bound
matches `(Fintype.card α)⁻¹` exactly when `samples = $ᵗ α`. This makes downstream uses of
`programming_collision_bound` reduce algebraically to the textbook `qP * qH / |α|` form. -/
lemma HasUnpredictableSample.uniformSample_apply
    {α : Type} [SampleableType α] [Fintype α] [Nonempty α] (x : α) :
    Pr[= x | ($ᵗ α : ProbComp α)] = (Fintype.card α : ℝ≥0∞)⁻¹ :=
  probOutput_uniformSample α x

/-! ## Programming collision bound -/

/-- The bad-event probability of `withProgramming policy` on input `oa`, started from an empty
cache and `bad := false`. The bad flag flips on the first cache-miss whose query input lies in
the policy's support; this abbreviation isolates that probability so downstream union-bound
arguments can name it. -/
noncomputable abbrev probEventBadOfWithProgramming
    {α : Type} (so : QueryImpl spec (OracleComp spec))
    (policy : ProgrammingPolicy spec) (oa : OracleComp spec α) : ℝ≥0∞ :=
  Pr[fun z : α × spec.QueryCache × Bool => z.2.2 = true |
      (simulateQ (so.withProgramming policy) oa).run (∅, false)]

omit [spec.DecidableEq] in
/-- **Programming collision bound.**

The TV-distance between running `oa` under pure caching and under a `policy`-programming
oracle is bounded by any upper bound `B` on the bad-event probability of
`withProgramming policy` (provided `B < ∞`).

This is the user-facing wrapper around
`OracleComp.ProgramLogic.Relational.tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad`:
the heavy lifting (the identical-until-bad bridge between `withCaching` and `withProgramming`)
lives in `ProgramLogic/Relational/ProgrammingOracle.lean`; here we just expose it under the
canonical name and combine it with a user-supplied bad-event bound `hBad`.

The canonical `qP * qH * β` Fiat-Shamir slack is recovered by instantiating
`B := (qP : ℝ≥0∞) * qH * β` (see `programming_collision_bound_qP_qH_β`) and discharging `hBad`
via a union bound over the at most `qP` programmed points (each contributing at most `qH * β`
by per-step unpredictability of the queried inputs). For Schnorr with `spec.Domain = M × Commit`,
`β = 1/|G|`, `qP = qS`, and effective `qH = qS + qH`, this matches `collisionSlack qS qH G`.

The per-point union bound itself depends on the structure of `oa`'s queries (specifically, an
unpredictability hypothesis on each query's input distribution); it is discharged in the
caller's setting. See `Examples/CommitmentScheme/` and `CryptoFoundations/FiatShamir/Sigma/`
for FS-flavored applications. -/
theorem programming_collision_bound
    {α : Type}
    (oa : OracleComp spec α)
    (so : QueryImpl spec (OracleComp spec))
    (policy : ProgrammingPolicy spec)
    {B : ℝ≥0∞} (hB_lt_top : B < ∞)
    (hBad : probEventBadOfWithProgramming so policy oa ≤ B) :
    tvDist
        ((simulateQ so.withCaching oa).run' ∅)
        ((simulateQ (so.withProgramming policy) oa).run' (∅, false))
      ≤ B.toReal := by
  open OracleComp.ProgramLogic.Relational in
  have hbridge :=
    tvDist_simulateQ_withCaching_withProgramming_le_probEvent_bad so policy oa ∅
  exact hbridge.trans (ENNReal.toReal_mono hB_lt_top.ne hBad)

omit [spec.DecidableEq] in
/-- Convenience repackaging of `programming_collision_bound`: when the user has a bad-event
bound of the canonical `qP * qH * β` shape, we get the canonical FS slack as the TV-distance
bound. The caller need only discharge `hBad` (typically by a union bound over at most `qP`
programmed points, each hit with probability `≤ qH * β`). -/
theorem programming_collision_bound_qP_qH_β
    {α : Type}
    (oa : OracleComp spec α) (qH qP : ℕ) (β : ℝ≥0∞) (hβ_lt_top : β < ∞)
    (so : QueryImpl spec (OracleComp spec))
    (policy : ProgrammingPolicy spec)
    (hBad : probEventBadOfWithProgramming so policy oa ≤ (qP : ℝ≥0∞) * qH * β) :
    tvDist
        ((simulateQ so.withCaching oa).run' ∅)
        ((simulateQ (so.withProgramming policy) oa).run' (∅, false))
      ≤ ((qP : ℝ≥0∞) * qH * β).toReal := by
  have hBound_lt_top : (qP : ℝ≥0∞) * qH * β < ∞ := by
    have hqPqH : (qP : ℝ≥0∞) * qH < ∞ :=
      ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.natCast_lt_top _)
    exact ENNReal.mul_lt_top hqPqH hβ_lt_top
  exact programming_collision_bound oa so policy hBound_lt_top hBad

end OracleComp
