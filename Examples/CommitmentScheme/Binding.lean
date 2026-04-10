/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import Examples.CommitmentScheme.Common

open OracleSpec OracleComp ENNReal

variable {M S C : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C]
/-! ## 1. Binding

**Textbook (Lemma cm-binding)**: For every `t`-query adversary A^H that outputs
`(c, m₀, s₀, m₁, s₁)`:
  Pr[m₀ ≠ m₁ ∧ Check^H(c, m₀, s₀) = 1 ∧ Check^H(c, m₁, s₁) = 1] ≤ ½ · t² / |C|

The adversary and Check use the **same** random oracle H. We model this by
running the entire game (adversary + verification) inside `simulateQ cachingOracle`. -/

/-- A binding adversary with query bound `t`. -/
structure BindingAdversary (M : Type) (S : Type) (C : Type) (t : ℕ)
    [DecidableEq M] [DecidableEq S] where
  /-- The adversary's computation, producing `(c, m₀, s₀, m₁, s₁)`. -/
  run : OracleComp (CMOracle M S C) (C × M × S × M × S)
  /-- The adversary makes at most `t` total queries. -/
  queryBound : IsTotalQueryBound run t

/-- The binding game in the random oracle model.

The adversary outputs `(c, m₀, s₀, m₁, s₁)`, then Check verifies both openings
using the **same** random oracle. Win condition: `m₀ ≠ m₁` and both checks pass.

The game runs inside `simulateQ cachingOracle` starting from an empty cache,
so all queries (adversary's and verification's) share the same random function. -/
def bindingGame {t : ℕ} (A : BindingAdversary M S C t) :
    OracleComp (CMOracle M S C) (Bool × QueryCache (CMOracle M S C)) :=
  (simulateQ cachingOracle (do
    let (c, m₀, s₀, m₁, s₁) ← A.run
    let c₀ ← query (spec := CMOracle M S C) (m₀, s₀)
    let c₁ ← query (spec := CMOracle M S C) (m₁, s₁)
    return (decide (m₀ ≠ m₁) && (c₀ == c) && (c₁ == c)))).run ∅

/-- The inner oracle computation of the binding game (before `simulateQ`). -/
private def bindingInner {t : ℕ} (A : BindingAdversary M S C t) :
    OracleComp (CMOracle M S C) Bool := do
  let (c, m₀, s₀, m₁, s₁) ← A.run
  let c₀ ← query (spec := CMOracle M S C) (m₀, s₀)
  let c₁ ← query (spec := CMOracle M S C) (m₁, s₁)
  return (decide (m₀ ≠ m₁) && (c₀ == c) && (c₁ == c))

omit [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
/-- The binding game equals `simulateQ cachingOracle` on `bindingInner`. -/
private lemma bindingGame_eq {t : ℕ} (A : BindingAdversary M S C t) :
    bindingGame A = (simulateQ cachingOracle (bindingInner A)).run ∅ := rfl

omit [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
private lemma binding_win_implies_collision {t : ℕ} (A : BindingAdversary M S C t) :
    ∀ z ∈ support ((simulateQ cachingOracle (bindingInner A)).run ∅),
      z.1 = true → CacheHasCollision z.2 := by
  intro z hz hwin
  simp only [bindingInner, simulateQ_bind, simulateQ_pure] at hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨c, m₀, s₀, m₁, s₁⟩, cache₁⟩, hmem₁, hz⟩ := hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c₀, cache₂⟩, hmem₂, hz⟩ := hz
  rw [StateT.run_bind] at hz
  rw [support_bind] at hz; simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c₁, cache₃⟩, hmem₃, hz⟩ := hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz] at hwin ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwin
  obtain ⟨⟨hne, hc₀⟩, hc₁⟩ := hwin
  have hpair_ne : (m₀, s₀) ≠ (m₁, s₁) := fun h => hne (Prod.ext_iff.mp h).1
  -- cache₂ has entry at (m₀, s₀) with value c₀
  rw [cachingOracle.simulateQ_query] at hmem₂
  have hcache₂ : cache₂ (m₀, s₀) = some c₀ :=
    cachingOracle_query_caches (m₀, s₀) cache₁ c₀ cache₂ hmem₂
  -- cache₃ has entry at (m₁, s₁) with value c₁
  -- Cache monotonicity: cache₂ ≤ cache₃, so cache₃ also has (m₀, s₀) ↦ c₀
  have hcache_mono : cache₂ ≤ cache₃ := by
    have hmem₃_co : (c₁, cache₃) ∈ support
        ((cachingOracle (spec := CMOracle M S C) (m₁, s₁)).run cache₂) := by
      simp only [cachingOracle.simulateQ_query] at hmem₃; exact hmem₃
    unfold cachingOracle at hmem₃_co
    exact QueryImpl.withCaching_cache_le
      (QueryImpl.ofLift (CMOracle M S C) (OracleComp (CMOracle M S C)))
      (m₁, s₁) cache₂ (c₁, cache₃) hmem₃_co
  rw [cachingOracle.simulateQ_query] at hmem₃
  have hcache₃ : cache₃ (m₁, s₁) = some c₁ :=
    cachingOracle_query_caches (m₁, s₁) cache₂ c₁ cache₃ hmem₃
  have hcache₃_m₀ : cache₃ (m₀, s₀) = some c₀ :=
    hcache_mono hcache₂
  exact ⟨(m₀, s₀), (m₁, s₁), c₀, c₁, hpair_ne, hcache₃_m₀, hcache₃,
    heq_of_eq (by rw [hc₀, hc₁])⟩

omit [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
/-- `IsTotalQueryBound` for the binding game's inner computation: `t + 2`
(adversary's `t` queries + 2 verification queries). -/
private lemma bindingInner_totalBound {t : ℕ} (A : BindingAdversary M S C t) :
    IsTotalQueryBound (bindingInner A) (t+2) := by
  apply isTotalQueryBound_bind A.queryBound
  intro ⟨c, m₀, s₀, m₁, s₁⟩
  change IsTotalQueryBound _ 2
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun c₀ => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ => trivial⟩

/- In a collision-free cache, a value determines at most one query input. -/
omit [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
private lemma binding_rest_noCollision_le_inv
    (c : C) (m₀ m₁ : M) (s₀ s₁ : S)
    (cache₁ : QueryCache (CMOracle M S C))
    (hno : ¬ CacheHasCollision cache₁) :
    Pr[fun z => z.1 = true |
      (simulateQ cachingOracle
        ((liftM (query (spec := CMOracle M S C) (m₀, s₀))) >>= fun c₀ =>
          (liftM (query (spec := CMOracle M S C) (m₁, s₁))) >>= fun c₁ =>
          pure (decide (m₀ ≠ m₁) && (c₀ == c) && (c₁ == c)))).run cache₁] ≤
      (Fintype.card C : ℝ≥0∞)⁻¹ := by
  by_cases hneq : m₀ ≠ m₁
  · let q₀ : (CMOracle M S C).Domain := (m₀, s₀)
    let q₁ : (CMOracle M S C).Domain := (m₁, s₁)
    have hqne : q₀ ≠ q₁ := by
      intro hq
      exact hneq (Prod.ext_iff.mp hq).1
    by_cases hq₀_none : cache₁ q₀ = none
    · simpa [q₀, q₁] using probEvent_from_fresh_query_le_inv
        (t := q₀) (target := c) (cache₀ := cache₁) hq₀_none
        (cont := fun u =>
          (liftM (query (spec := CMOracle M S C) q₁)) >>= fun c₁ =>
            pure (decide (m₀ ≠ m₁) && (u == c) && (c₁ == c))) (by
          intro u hu
          apply probEvent_eq_zero
          intro z hz hwin
          simp only [simulateQ_bind, simulateQ_pure] at hz
          rw [StateT.run_bind] at hz
          rw [support_bind] at hz
          simp only [Set.mem_iUnion] at hz
          obtain ⟨⟨c₁, cache₂⟩, _, hz⟩ := hz
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz] at hwin
          simp [hneq, hu] at hwin)
    · rcases Option.ne_none_iff_exists'.mp hq₀_none with ⟨v₀, hq₀⟩
      have hrun₀ :
          (simulateQ cachingOracle
            ((liftM (query (spec := CMOracle M S C) q₀)) >>= fun c₀ =>
              (liftM (query (spec := CMOracle M S C) q₁)) >>= fun c₁ =>
              pure (decide (m₀ ≠ m₁) && (c₀ == c) && (c₁ == c)))).run cache₁ =
          (simulateQ cachingOracle
            ((liftM (query (spec := CMOracle M S C) q₁)) >>= fun c₁ =>
              pure (decide (m₀ ≠ m₁) && (v₀ == c) && (c₁ == c)))).run cache₁ := by
        simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
        have hcache :
            (liftM (cachingOracle (spec := CMOracle M S C) q₀) :
              StateT (QueryCache (CMOracle M S C))
                (OracleComp (CMOracle M S C)) _).run cache₁ =
            pure (v₀, cache₁) := by
          simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
            StateT.run_bind, StateT.run_get, hq₀, pure_bind, StateT.run_pure]
        rw [hcache, pure_bind]
        simp [OracleQuery.cont_query]
      by_cases hv₀ : v₀ = c
      · by_cases hq₁_none : cache₁ q₁ = none
        · rw [hrun₀]
          simpa [hv₀, q₁] using probEvent_from_fresh_query_le_inv
            (t := q₁) (target := c) (cache₀ := cache₁) hq₁_none
            (cont := fun u =>
              pure (decide (m₀ ≠ m₁) && (v₀ == c) && (u == c))) (by
              intro u hu
              simp [simulateQ_pure, StateT.run_pure, hv₀, hneq, hu])
        · rcases Option.ne_none_iff_exists'.mp hq₁_none with ⟨v₁, hq₁⟩
          have hv₁ : v₁ ≠ c := by
            intro hv₁
            apply hqne
            exact cache_lookup_eq_of_noCollision hno (hv₀ ▸ hq₀)
              ⟨v₁, hq₁, heq_of_eq hv₁⟩
          have hrun₁ :
              (simulateQ cachingOracle
                ((liftM (query (spec := CMOracle M S C) q₁)) >>= fun c₁ =>
                  pure (decide (m₀ ≠ m₁) && (v₀ == c) && (c₁ == c)))).run cache₁ =
              pure (decide (m₀ ≠ m₁) && (v₀ == c) && (v₁ == c), cache₁) := by
            simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
            have hcache :
                (liftM (cachingOracle (spec := CMOracle M S C) q₁) :
                  StateT (QueryCache (CMOracle M S C))
                    (OracleComp (CMOracle M S C)) _).run cache₁ =
                pure (v₁, cache₁) := by
              simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
                StateT.run_bind, StateT.run_get, hq₁, pure_bind, StateT.run_pure]
            rw [hcache, pure_bind]
            simp [OracleQuery.cont_query, StateT.run_pure]
          rw [hrun₀]
          rw [hrun₁]
          simp [hneq, hv₀, hv₁]
      · rw [hrun₀]
        refine le_of_eq_of_le ?_ (zero_le _)
        apply probEvent_eq_zero
        intro z hz hwin
        simp only [simulateQ_bind, simulateQ_pure] at hz
        rw [StateT.run_bind] at hz
        rw [support_bind] at hz
        simp only [Set.mem_iUnion] at hz
        obtain ⟨⟨c₁, cache₂⟩, _, hz⟩ := hz
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz] at hwin
        simp [hneq, hv₀] at hwin
  · refine le_of_eq_of_le ?_ (zero_le _)
    apply probEvent_eq_zero
    intro z hz hwin
    simp only [simulateQ_bind, simulateQ_pure] at hz
    rw [StateT.run_bind] at hz
    rw [support_bind] at hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨⟨c₀, cache₂⟩, _, hz⟩ := hz
    rw [StateT.run_bind] at hz
    rw [support_bind] at hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨⟨c₁, cache₃⟩, _, hz⟩ := hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz] at hwin
    simp [hneq] at hwin

/- Winning the binding game either implies a collision in the adversary's cache
 (the cache after `A.run`, before verification) or that a fresh verification query
 matched the commitment `c`. We bound each case separately:
 - Case 1 (collision in adversary's cache): ≤ `t(t-1)/(2|C|)` by tight birthday bound
 - Case 2 (no collision, fresh query matches `c`): ≤ `1/|C|` by unpredictability -/
omit [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
private lemma binding_win_le_advCollision_add_fresh {t : ℕ}
    (A : BindingAdversary M S C t) :
    Pr[fun z => z.1 = true | bindingGame A] ≤
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle A.run).run ∅] +
    (Fintype.card C : ℝ≥0∞)⁻¹ := by
  let restPart : (C × M × S × M × S) → OracleComp (CMOracle M S C) Bool
    | (c, m₀, s₀, m₁, s₁) =>
        (liftM (query (spec := CMOracle M S C) (m₀, s₀))) >>= fun c₀ =>
          (liftM (query (spec := CMOracle M S C) (m₁, s₁))) >>= fun c₁ =>
          pure (decide (m₀ ≠ m₁) && (c₀ == c) && (c₁ == c))
  have hdecomp : bindingInner A = A.run >>= restPart := by
    simp [bindingInner, restPart]
  rw [bindingGame_eq, hdecomp, simulateQ_bind, StateT.run_bind]
  simpa using
    (probEvent_bind_le_add
      (mx := (simulateQ cachingOracle A.run).run ∅)
      (my := fun x => (simulateQ cachingOracle (restPart x.1)).run x.2)
      (p := fun x => ¬ CacheHasCollision x.2)
      (q := fun z => z.1 ≠ true)
      (ε₁ := Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle A.run).run ∅])
      (ε₂ := (Fintype.card C : ℝ≥0∞)⁻¹)
      (by simp)
      (by
        rintro ⟨⟨c, m₀, s₀, m₁, s₁⟩, cache₁⟩ _ hno
        simpa [restPart] using binding_rest_noCollision_le_inv c m₀ m₁ s₀ s₁ cache₁ hno))

/- **Binding theorem (Lemma cm-binding)**: `Pr[win] ≤ (t(t-1)+2) / (2|C|)`.

Decomposes via `binding_win_le_advCollision_add_fresh` into birthday bound on the
adversary's `t` queries (`t(t-1)/(2|C|)`) plus unpredictability (`1/|C|`). -/
omit [Fintype M] [Fintype S] in
theorem binding_bound {t : ℕ} (A : BindingAdversary M S C t) :
    Pr[fun z => z.1 = true | bindingGame A] ≤
    ((t * (t - 1) + 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
  calc Pr[fun z => z.1 = true | bindingGame A]
      ≤ Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle A.run).run ∅] +
        (Fintype.card C : ℝ≥0∞)⁻¹ := binding_win_le_advCollision_add_fresh A
    _ ≤ ((t * (t - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) +
        (Fintype.card C : ℝ≥0∞)⁻¹ := by
        gcongr
        exact probEvent_cacheCollision_le_birthday_total_tight A.run t A.queryBound
          Fintype.card_pos (fun _ => le_refl _)
    _ = ((t * (t - 1) + 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card C) := by
        simpa [Nat.mul_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          add_div_two_mul_nat (t * (t - 1)) 1 (Fintype.card C)
