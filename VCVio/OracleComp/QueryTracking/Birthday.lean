/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import VCVio.OracleComp.QueryTracking.Collision
import ToMathlib.Combinatorics.FinPairs
import ToMathlib.Data.ENNReal.Gauss

/-!
# ROM Birthday Bound

Per-pair collision bounds and union bound birthday argument for random oracle
collision probability. Covers both log-based and cache-based collision bounds,
with per-index corollaries.
-/

open OracleSpec OracleComp ENNReal Finset

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [spec.DecidableEq] [IsUniformSpec spec]

/-! ## Per-Pair Collision Bound (Textbook Step 3)

For each pair (i,j) of positions in the log with distinct inputs,
Pr[outputs equal] ≤ 1/|C|. This is because in the evalDist model,
each query returns an independent uniform sample. -/

omit [DecidableEq ι] [spec.DecidableEq] in
private lemma tsum_query_mul_probEvent_le_aux {α : Type}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α)
    (p : spec.Range t → α × QueryLog spec → Prop) (c : ℝ≥0∞)
    (h : ∀ u, Pr[ p u | (simulateQ loggingOracle (mx u)).run] ≤ c) :
    (∑' u, Pr[= u | (query t : OracleComp spec _)] *
      Pr[ p u | (simulateQ loggingOracle (mx u)).run]) ≤ c :=
  le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (h u))
    (le_trans ENNReal.tsum_mul_right.le
      (le_trans (mul_le_mul' tsum_probOutput_le_one le_rfl) (one_mul c).le))

omit [DecidableEq ι] in
/-- **ROM uniformity at a log position**: For any `loggingOracle` trace, the
probability that the k-th log entry matches a fixed sigma-typed value `⟨t, v⟩`
is at most `1/|Range t|`. Each query response is an independent uniform draw. -/
theorem probEvent_log_entry_eq_le {α : Type}
    (oa : OracleComp spec α)
    (k : ℕ) (entry : (t : spec.Domain) × spec.Range t) :
    Pr[fun z => z.2[k]? = some entry |
      (simulateQ loggingOracle oa).run] ≤
      (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing k with
  | pure _ => simp [loggingOracle, simulateQ_pure]
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind]
    cases k with
    | zero =>
      rw [probEvent_bind_eq_tsum]
      simp_rw [probEvent_map, Function.comp_def, List.getElem?_cons_zero, Option.some.injEq,
        probOutput_query, probEvent_const]
      by_cases ht : t = entry.1
      · subst ht
        calc _ ≤ ∑' x : spec.Range entry.1,
                (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ * if x = entry.2 then 1 else 0 :=
              ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl <| by
                split <;> simp_all [Sigma.ext_iff]
          _ = _ := by simp
      · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun x => ?_) zero_le
        rw [if_neg fun h => ht (by cases h; rfl), mul_zero]
    | succ k' =>
      rw [probEvent_bind_eq_tsum]
      simp_rw [probEvent_map, Function.comp_def, List.getElem?_cons_succ]
      exact tsum_query_mul_probEvent_le_aux t mx _ _ fun u => ih u k'

omit [DecidableEq ι] in
/-- **Uniformized log entry bound**: the probability that position `k` of a `loggingOracle`
trace equals a fixed sigma-typed entry is at most `1/|Range default|`, assuming `|Range default|`
is minimal across all oracle indices.

This is a corollary of `probEvent_log_entry_eq_le` (which gives `1/|Range entry.1|`) combined
with the `hrange` monotonicity hypothesis. -/
theorem probEvent_log_output_heq_le {α : Type}
    [Inhabited ι]
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (oa : OracleComp spec α)
    (k : ℕ) (entry : (t : spec.Domain) × spec.Range t) :
    Pr[fun z => z.2[k]? = some entry |
      (simulateQ loggingOracle oa).run] ≤
      (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
  (probEvent_log_entry_eq_le oa k entry).trans
    (ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (hrange entry.1)))

omit [DecidableEq ι] [spec.DecidableEq] in
/-- Probability that the k-th log entry's output is HEq to a fixed value `u₀ : spec.Range t₀`.
Unlike `probEvent_log_entry_eq_le` which matches the full sigma entry, this only constrains
the output component. The bound uses `hrange` to get `1/|Range default|`. -/
theorem probEvent_log_output_match_le {α : Type}
    [Inhabited ι]
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (oa : OracleComp spec α)
    (k : ℕ) (t₀ : spec.Domain) (u₀ : spec.Range t₀) :
    Pr[fun z => ∃ (s : spec.Domain) (v : spec.Range s),
        z.2[k]? = some ⟨s, v⟩ ∧ HEq u₀ v |
      (simulateQ loggingOracle oa).run] ≤
      (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  classical
  induction oa using OracleComp.inductionOn generalizing k with
  | pure _ =>
    refine le_of_eq_of_le (probEvent_eq_zero fun z hmem h => ?_) zero_le
    simp only [simulateQ_pure, WriterT.run_pure', List.empty_eq, support_pure,
      Set.mem_singleton_iff] at hmem
    obtain ⟨_, rfl⟩ := hmem
    obtain ⟨s, v, hlog, _⟩ := h; simp at hlog
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind, probEvent_bind_eq_tsum]
    simp_rw [probEvent_map, Function.comp_def]
    cases k with
    | zero =>
      have hpred : ∀ u' : spec.Range t,
          (fun z : α × QueryLog spec =>
            ∃ (s : spec.Domain) (v : spec.Range s),
              ((⟨t, u'⟩ : (i : spec.Domain) × spec.Range i) :: z.2)[0]? = some ⟨s, v⟩ ∧
              HEq u₀ v) =
          (fun _ => HEq u₀ u') := by
        intro u'; ext z
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        exact ⟨fun ⟨s, v, heq, hheq⟩ => by cases heq; exact hheq, fun h => ⟨t, u', rfl, h⟩⟩
      simp_rw [hpred, probEvent_const, probFailure_of_liftM_PMF, tsub_zero, probOutput_query]
      rw [ENNReal.tsum_mul_left]
      have hind_le : ∑' (u' : spec.Range t), (if HEq u₀ u' then (1 : ℝ≥0∞) else 0) ≤ 1 := by
        rw [tsum_eq_sum (s := Finset.univ) (by simp), Finset.sum_ite, Finset.sum_const_zero,
          add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast Finset.card_le_one.mpr fun a ha b hb => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact eq_of_heq (ha.symm.trans hb)
      exact le_trans (mul_le_of_le_one_right' hind_le)
        (ENNReal.inv_le_inv.mpr (by exact_mod_cast hrange t))
    | succ k' =>
      simp_rw [List.getElem?_cons_succ]
      exact tsum_query_mul_probEvent_le_aux t mx _ _ fun u => ih u k'

omit [DecidableEq ι] [spec.DecidableEq] in
/-- **Per-pair collision bound**: For any two positions in a `loggingOracle` trace
with distinct inputs, the probability that their outputs are HEq-equal is ≤ 1/|C|.

This is the core ROM property: distinct oracle inputs yield independent uniform outputs.
The `hrange` hypothesis ensures `|Range default|` is minimal across all oracle indices,
so the bound holds uniformly with `|C| = |Range default|`. -/
theorem probEvent_pair_collision_le {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (i j : Fin n) (hij : i ≠ j) :
    Pr[fun z => z.2.length > i.val ∧ z.2.length > j.val ∧
        z.2[i]?.bind (fun ei => z.2[j]?.map (fun ej =>
          ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true |
      (simulateQ loggingOracle oa).run] ≤
      (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  apply le_trans (probEvent_mono fun z _ h => h.2.2)
  suffices h : ∀ (β : Type) (ob : OracleComp spec β) (i j : ℕ) (_ : i ≠ j),
      Pr[fun z => z.2[i]?.bind (fun ei => z.2[j]?.map (fun ej =>
        ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true |
        (simulateQ loggingOracle ob).run] ≤
        (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ from
    h α oa i.val j.val (Fin.val_ne_of_ne hij)
  intro β ob
  induction ob using OracleComp.inductionOn with
  | pure x => intro i j _; simp [simulateQ_pure]
  | query_bind t mx ih =>
    intro i j hij
    rw [run_simulateQ_loggingOracle_query_bind, probEvent_bind_eq_tsum]
    simp_rw [probEvent_map, Function.comp_def]
    -- The matched output lives at position `k` in the log; both end cases reduce to
    -- `probEvent_log_output_match_le` after extracting the sigma entry.
    have key : ∀ (u : spec.Range t) (k : ℕ) (e : β × QueryLog spec → Prop),
        (∀ z, e z → ∃ s v, z.2[k]? = some ⟨s, v⟩ ∧ HEq u v) →
        Pr[e | (simulateQ loggingOracle (mx u)).run] ≤
          (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := fun u k e he =>
      (probEvent_mono fun z _ => he z).trans (probEvent_log_output_match_le hrange (mx u) k t u)
    match i, j, hij with
    | 0, 0, hij => exact absurd rfl hij
    | 0, j' + 1, _ =>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind_some]
      refine tsum_query_mul_probEvent_le_aux t mx _ _ fun u => key u j' _ fun z hev => ?_
      match hz : z.2[j']? with
      | none => simp [hz] at hev
      | some ⟨s, v⟩ => exact ⟨s, v, rfl, by simp_all⟩
    | i' + 1, 0, _ =>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
      refine tsum_query_mul_probEvent_le_aux t mx _ _ fun u => key u i' _ fun z hev => ?_
      match hz : z.2[i']? with
      | none => simp [hz] at hev
      | some ⟨s, v⟩ => exact ⟨s, v, rfl, (by simp_all : v ≍ u).symm⟩
    | i' + 1, j' + 1, hij =>
      simp only [List.getElem?_cons_succ]
      exact tsum_query_mul_probEvent_le_aux t mx _ _ fun u => ih u i' j' (by lia)

/-! ## Union Bound Birthday (Textbook Steps 4-5)

Collision = ∃ pair with collision. Union bound over C(n,2) pairs gives n²/(2|C|). -/

omit [DecidableEq ι] in
/-- **Tight birthday bound for `loggingOracle`** (total query bound):
The probability of a collision in the query log is ≤ `C(n,2)/|C|`, where `C(n,2)`
is the exact number of unordered pairs of query positions. -/
theorem probEvent_logCollision_le_birthday_total_tight {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => LogHasCollision z.2 |
      (simulateQ loggingOracle oa).run] ≤
      (Nat.choose n 2 : ℝ≥0∞) / (Fintype.card (spec.Range default)) := by
  let E : Fin n × Fin n → α × QueryLog spec → Prop := fun ij z =>
    z.2.length > ij.1.val ∧ z.2.length > ij.2.val ∧
      z.2[ij.1]?.bind (fun ei => z.2[ij.2]?.map (fun ej =>
        ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true
  let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)
  calc Pr[fun z => LogHasCollision z.2 | (simulateQ loggingOracle oa).run]
      ≤ ∑ _ij ∈ pairs, (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
        apply le_trans (probEvent_mono (q := fun z => ∃ ij ∈ pairs, E ij z) ?_)
        · refine (probEvent_exists_finset_le_sum pairs _ E).trans (Finset.sum_le_sum ?_)
          intro ⟨i, j⟩ hij
          simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij
          exact probEvent_pair_collision_le oa n hrange i j (Fin.ne_of_lt hij)
        · intro z hz hcoll
          obtain ⟨i, j, hij, hdist, heq⟩ := hcoll
          have hlen := log_length_le_of_mem_support_run_simulateQ hbound hz
          have hi_lt : i.val < n := i.isLt.trans_le hlen
          have hj_lt : j.val < n := j.isLt.trans_le hlen
          have key : ∀ (a b : Fin z.2.length) (ha : a.val < n) (hb : b.val < n),
              a.val < b.val → z.2[a].1 ≠ z.2[b].1 → HEq z.2[a].2 z.2[b].2 →
              ∃ ij ∈ pairs, E ij z := fun a b ha hb hab hd he =>
            ⟨(⟨a.val, ha⟩, ⟨b.val, hb⟩), by simpa [pairs] using hab, a.isLt, b.isLt, by
              rw [show z.2[(⟨a.val, ha⟩ : Fin n)]? = some z.2[a] by simp,
                show z.2[(⟨b.val, hb⟩ : Fin n)]? = some z.2[b] by simp]
              simp_all⟩
          rcases lt_or_gt_of_ne hij with hlt | hgt
          · exact key i j hi_lt hj_lt hlt hdist heq
          · exact key j i hj_lt hi_lt hgt hdist.symm heq.symm
    _ = (Nat.choose n 2 : ℝ≥0∞) / (Fintype.card (spec.Range default)) := by
        rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, Finset.card_filter_fst_lt_snd]

omit [DecidableEq ι] in
/-- **Birthday bound for `loggingOracle`** (total query bound):
The probability of a collision in the query log is ≤ n²/(2|C|).

A loose corollary of `probEvent_logCollision_le_birthday_total_tight`. -/
theorem probEvent_logCollision_le_birthday_total {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => LogHasCollision z.2 |
      (simulateQ loggingOracle oa).run] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  calc Pr[fun z => LogHasCollision z.2 | (simulateQ loggingOracle oa).run]
      ≤ (Nat.choose n 2 : ℝ≥0∞) / (Fintype.card (spec.Range default)) :=
        probEvent_logCollision_le_birthday_total_tight oa n hbound hrange
    _ ≤ (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
        rw [← ENNReal.mul_div_mul_left (c := 2) (↑(Nat.choose n 2))
          (↑(Fintype.card (spec.Range default))) (by norm_num) (by norm_num)]
        gcongr
        exact_mod_cast (show 2 * Nat.choose n 2 ≤ n ^ 2 by
          rw [Nat.choose_two_right, pow_two]
          exact (Nat.mul_div_le (n * (n - 1)) 2).trans (by gcongr; lia))

open Classical in
omit [spec.DecidableEq] in
private lemma card_cacheQuery_collision_le_aux {cache₀ : QueryCache spec} {t : spec.Domain}
    {S : Finset spec.Domain} (hnocoll : ¬CacheHasCollision cache₀)
    (hSmem : ∀ t', cache₀ t' ≠ none → t' ∈ S) :
    (Finset.univ.filter (fun u => CacheHasCollision (cache₀.cacheQuery t u))).card ≤ S.card := by
  have hmust : ∀ u, CacheHasCollision (cache₀.cacheQuery t u) →
      ∃ t' : spec.Domain, t' ≠ t ∧ ∃ v : spec.Range t', cache₀ t' = some v ∧ HEq u v := by
    intro u ⟨t₁, t₂, u₁, u₂, hne, h1, h2, hequ⟩
    by_cases ht1 : t₁ = t
    · subst ht1
      refine ⟨t₂, hne.symm, u₂, by rwa [QueryCache.cacheQuery_of_ne _ _ hne.symm] at h2, ?_⟩
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at h1
      subst h1; exact hequ
    · by_cases ht2 : t₂ = t
      · subst ht2
        refine ⟨t₁, hne, u₁, by rwa [QueryCache.cacheQuery_of_ne _ _ ht1] at h1, ?_⟩
        simp only [QueryCache.cacheQuery_self, Option.some.injEq] at h2
        subst h2; exact hequ.symm
      · exact absurd ⟨t₁, t₂, u₁, u₂, hne, by rwa [QueryCache.cacheQuery_of_ne _ _ ht1] at h1,
          by rwa [QueryCache.cacheQuery_of_ne _ _ ht2] at h2, hequ⟩ hnocoll
  let f : spec.Range t → spec.Domain := fun u =>
    if h : CacheHasCollision (cache₀.cacheQuery t u) then (hmust u h).choose else t
  refine Finset.card_le_card_of_injOn f (fun u hu => ?_) (fun u₁ hu₁ u₂ hu₂ hfeq => ?_)
  · have hu' := (Finset.mem_filter.mp hu).2
    obtain ⟨_, v, hcache, _⟩ := (hmust u hu').choose_spec
    rw [show f u = _ from dif_pos hu']
    exact hSmem _ (hcache ▸ Option.some_ne_none v)
  · have hu₁' := (Finset.mem_filter.mp hu₁).2
    have hu₂' := (Finset.mem_filter.mp hu₂).2
    rw [show f u₁ = _ from dif_pos hu₁', show f u₂ = _ from dif_pos hu₂'] at hfeq
    obtain ⟨_, v₁, hcache₁, heq₁⟩ := (hmust u₁ hu₁').choose_spec
    obtain ⟨_, v₂, hcache₂, heq₂⟩ := (hmust u₂ hu₂').choose_spec
    suffices aux : ∀ (a b : spec.Domain) (va : spec.Range a) (vb : spec.Range b),
        cache₀ a = some va → cache₀ b = some vb → a = b → HEq va vb from
      eq_of_heq (heq₁.trans ((aux _ _ _ _ hcache₁ hcache₂ hfeq).trans heq₂.symm))
    intro a b va vb ha hb hab
    subst hab; rw [ha] at hb; exact heq_of_eq (Option.some.inj hb)

omit [spec.DecidableEq] [IsUniformSpec spec] in
private lemma run_simulateQ_cachingOracle_query_bind_of_hit {α : Type} {t : spec.Domain}
    {mx : spec.Range t → OracleComp spec α} {cache₀ : QueryCache spec} {v : spec.Range t}
    (hv : cache₀ t = some v) :
    (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
      (simulateQ cachingOracle (mx v)).run cache₀ := by
  simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
  have hcache : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
      pure (v, cache₀) := by
    simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
      StateT.run_bind, StateT.run_get, hv, pure_bind, StateT.run_pure]
  rw [hcache, pure_bind]
  simp [OracleQuery.cont_query]

omit [spec.DecidableEq] [IsUniformSpec spec] in
private lemma run_simulateQ_cachingOracle_query_bind_of_miss {α : Type} {t : spec.Domain}
    {mx : spec.Range t → OracleComp spec α} {cache₀ : QueryCache spec}
    (ht_none : cache₀ t = none) :
    (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
      liftM (query t) >>= fun u =>
        (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u) := by
  simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
  have hstep : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
      (liftM (query t) >>= fun u => pure (u, cache₀.cacheQuery t u) : OracleComp spec _) := by
    simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
      StateT.run_bind, StateT.run_get, pure_bind, ht_none]
    change (StateT.lift (PFunctor.FreeM.lift (query t)) cache₀ >>= _) = _
    simp only [StateT.lift, monad_norm, modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run]; rfl
  rw [hstep]; simp [monad_norm]

omit [spec.DecidableEq] in
/-- **Cache-collision induction core**: running any computation `ob` (bounded by `m` queries)
through `cachingOracle` starting from a collision-free cache `cache₀` whose populated keys fit
in a set of size at most `k` produces a collision with probability at most
`∑ j ∈ range m, (k + j) / |Range default|`.

Generalizing over the starting cache and its key budget `k` lets the bound thread through each
fresh query: a cache miss enlarges the support set by one and shifts the per-step factor from
`k` to `k + 1`. The `hrange` hypothesis ensures `|Range default|` is minimal across oracle
indices, so the uniform per-query bound `1/|Range t|` is dominated by `1/|Range default|`.
This is the inductive engine behind `probEvent_cacheCollision_le_birthday_total_tight`. -/
private lemma probEvent_cacheCollision_run_le_sum_aux [Inhabited ι]
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    {β : Type} (ob : OracleComp spec β) (m k : ℕ)
    (hm : IsTotalQueryBound ob m)
    (cache₀ : QueryCache spec)
    (hnocoll : ¬CacheHasCollision cache₀)
    (hbnd : ∃ S : Finset spec.Domain, S.card ≤ k ∧ ∀ t, cache₀ t ≠ none → t ∈ S) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle ob).run cache₀] ≤
      ∑ j ∈ range m, ((k + j : ℕ) : ℝ≥0∞) *
        (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  let C := (Fintype.card (spec.Range default) : ℝ≥0∞)
  induction ob using OracleComp.inductionOn generalizing m k cache₀ with
  | pure x =>
    rw [simulateQ_pure]
    refine le_of_eq_of_le (probEvent_eq_zero fun z hz h => ?_) zero_le
    change z ∈ support (pure (x, cache₀) : OracleComp _ _) at hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hnocoll h
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at hm
    obtain ⟨hpos, hrest⟩ := hm
    by_cases ht : ∃ v, cache₀ t = some v
    · obtain ⟨v, hv⟩ := ht
      rw [run_simulateQ_cachingOracle_query_bind_of_hit hv]
      calc Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle (mx v)).run cache₀]
          ≤ ∑ j ∈ range (m - 1), ((k + j : ℕ) : ℝ≥0∞) * C⁻¹ :=
            ih v (m - 1) k (hrest v) cache₀ hnocoll hbnd
        _ ≤ ∑ j ∈ range m, ((k + j : ℕ) : ℝ≥0∞) * C⁻¹ :=
            Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le m 1))
    · push Not at ht
      have ht_none : cache₀ t = none := Option.eq_none_iff_forall_ne_some.mpr ht
      rw [run_simulateQ_cachingOracle_query_bind_of_miss ht_none]
      have hε₁ : Pr[fun u => CacheHasCollision (cache₀.cacheQuery t u) |
          (spec.query t : OracleComp spec _)] ≤ (k : ℝ≥0∞) * C⁻¹ := by
        classical
        obtain ⟨S, hScard, hSmem⟩ := hbnd
        rw [probEvent_query]
        have hbad_le_k := (card_cacheQuery_collision_le_aux (t := t) hnocoll hSmem).trans hScard
        calc (↑(Finset.univ.filter (fun u => CacheHasCollision (cache₀.cacheQuery t u))).card :
                ℝ≥0∞) / ↑(Fintype.card (spec.Range t))
            ≤ (k : ℝ≥0∞) / ↑(Fintype.card (spec.Range t)) :=
              ENNReal.div_le_div_right (by exact_mod_cast hbad_le_k) _
          _ ≤ (k : ℝ≥0∞) * C⁻¹ := by
              rw [ENNReal.div_eq_inv_mul, mul_comm]
              gcongr
              change (Fintype.card (spec.Range default) : ℝ≥0∞) ≤ ↑(Fintype.card (spec.Range t))
              exact_mod_cast hrange t
      have hε₂ : ∀ u ∈ support (spec.query t : OracleComp spec _),
          ¬CacheHasCollision (cache₀.cacheQuery t u) →
          Pr[fun z => CacheHasCollision z.2 |
            (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)] ≤
              ∑ j ∈ range (m - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) * C⁻¹ := by
        intro u _ hnocoll'
        apply ih u (m - 1) (k + 1) (hrest u) _ hnocoll'
        obtain ⟨S, hScard, hSmem⟩ := hbnd
        exact ⟨insert t S,
          le_trans (Finset.card_insert_le t S) (by lia),
          fun t' ht' => by
            by_cases heq : t' = t
            · exact heq ▸ Finset.mem_insert_self _ S
            · rw [QueryCache.cacheQuery_of_ne cache₀ _ heq] at ht'
              exact Finset.mem_insert_of_mem (hSmem t' ht')⟩
      have hcombine := probEvent_bind_le_add
        (mx := (spec.query t : OracleComp spec _))
        (my := fun u => (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u))
        (p := fun u => ¬CacheHasCollision (cache₀.cacheQuery t u))
        (q := fun z => ¬CacheHasCollision z.2)
        (ε₁ := (k : ℝ≥0∞) * C⁻¹)
        (ε₂ := ∑ j ∈ range (m - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) * C⁻¹)
        (by simpa [not_not] using hε₁)
        (by simpa [not_not] using hε₂)
      simp only [not_not] at hcombine
      calc Pr[fun z => CacheHasCollision z.2 |
              liftM (query t) >>= fun u =>
                (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)]
          ≤ (k : ℝ≥0∞) * C⁻¹ + ∑ j ∈ range (m - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) * C⁻¹ :=
            hcombine
        _ = ∑ j ∈ range m, ((k + j : ℕ) : ℝ≥0∞) * C⁻¹ := by
            conv_rhs => rw [show m = (m - 1) + 1 from by lia]
            rw [Finset.sum_range_succ' (fun j => ((k + j : ℕ) : ℝ≥0∞) * C⁻¹)]
            simp only [Nat.add_zero]
            rw [add_comm, Finset.sum_congr rfl fun j _ => by
              rw [show k + 1 + j = k + (j + 1) from by lia]]

omit [spec.DecidableEq] in
/-- **Tight birthday bound for `cachingOracle`** (total query bound):
The probability of a collision in the cache is ≤ n*(n-1)/(2|C|). -/
theorem probEvent_cacheCollision_le_birthday_total_tight {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  let C := (Fintype.card (spec.Range default) : ℝ≥0∞)
  calc Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅]
      ≤ ∑ j ∈ range n, ((0 + j : ℕ) : ℝ≥0∞) * C⁻¹ :=
        probEvent_cacheCollision_run_le_sum_aux hrange oa n 0 hbound ∅
          (by intro ⟨t₁, _, _, _, _, h1, _, _⟩; simp at h1)
          ⟨∅, by simp, fun t ht => absurd (by simp : (∅ : QueryCache spec) t = none) ht⟩
    _ = ∑ j ∈ range n, (j : ℝ≥0∞) * C⁻¹ := by simp
    _ = ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * C) := ENNReal.gauss_sum_inv_eq n C

omit [spec.DecidableEq] in
/-- **Loose birthday bound for `cachingOracle`** (total query bound):
The probability of a collision in the cache is ≤ n²/(2|C|).

A loose corollary of `probEvent_cacheCollision_le_birthday_total_tight`. -/
theorem probEvent_cacheCollision_le_birthday_total {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  calc Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅]
      ≤ ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) :=
        probEvent_cacheCollision_le_birthday_total_tight oa n hbound hrange
    _ ≤ (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
        gcongr; exact_mod_cast (show n * (n - 1) ≤ n ^ 2 by rw [pow_two]; gcongr; lia)

/-! ## Per-Index Bound Versions -/

omit [spec.DecidableEq] in
/-- Birthday bound for `cachingOracle` with per-index query bound. -/
theorem probEvent_cacheCollision_le_birthday {α : Type} {t : ℕ}
    [Inhabited ι] [Fintype ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      ((Fintype.card ι * t) ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have htotal := IsTotalQueryBound.of_perIndex hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at htotal
  exact_mod_cast probEvent_cacheCollision_le_birthday_total oa _ htotal hrange

omit [spec.DecidableEq] in
/-- **WARNING: vacuously true.** The `[Unique ι]` hypothesis means `ι` has exactly one element,
but `CacheHasCollision` requires two *distinct* oracle indices `t₁ ≠ t₂ : ι`, which is impossible.
The event `CacheHasCollision z.2` is therefore always false, making the bound trivially `0 ≤ ...`.

The non-vacuous birthday bound is `probEvent_cacheCollision_le_birthday_total_tight`. -/
theorem probEvent_cacheCollision_le_birthday' {α : Type} {t : ℕ}
    [Inhabited ι] [Unique ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      (t ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  simpa using probEvent_cacheCollision_le_birthday oa hbound hrange

end OracleComp
