/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import VCVio.OracleComp.QueryTracking.Collision

/-!
# ROM Birthday Bound

Per-pair collision bounds and union bound birthday argument for random oracle
collision probability. Covers both log-based and cache-based collision bounds,
with per-index corollaries.
-/

open OracleSpec OracleComp ENNReal Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [spec.DecidableEq] [spec.Fintype] [spec.Inhabited]

/-! ## Per-Pair Collision Bound (Textbook Step 3)

For each pair (i,j) of positions in the log with distinct inputs,
Pr[outputs equal] ≤ 1/|C|. This is because in the evalDist model,
each query returns an independent uniform sample. -/

omit [DecidableEq ι] in
/-- **ROM uniformity at a log position**: For any `loggingOracle` trace, the
probability that the k-th log entry matches a fixed sigma-typed value `⟨t, v⟩`
is at most `1/|Range t|`. Each query response is an independent uniform draw.

Proof by structural induction on the computation. For `query t >>= mx`:
- The log is `[⟨t, u⟩] ++ sub_log` where `u` is uniform from `Range t`.
- For k = 0: the event is `⟨t, u⟩ = entry`, bounded by `Pr[= v | query t] = 1/|Range t|`.
- For k > 0: the event is `sub_log[k-1]? = entry`, bounded by the inductive hypothesis. -/
theorem probEvent_log_entry_eq_le {α : Type}
    (oa : OracleComp spec α)
    (k : ℕ) (entry : (t : spec.Domain) × spec.Range t) :
    Pr[fun z => z.2[k]? = some entry |
      (simulateQ loggingOracle oa).run] ≤
      (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing k with
  | pure _ =>
    -- Pure computation: log is empty, so z.2[k]? = none ≠ some entry.
    simp [loggingOracle, simulateQ_pure]
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind]
    cases k with
    | zero =>
      -- k = 0: The 0-th log entry is ⟨t, u⟩. Decompose, simplify predicate.
      rw [probEvent_bind_eq_tsum]
      simp_rw [probEvent_map, Function.comp_def]
      have hpred : ∀ u : spec.Range t,
          (fun z : α × QueryLog spec =>
            ((⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: z.2)[0]? = some entry) =
          (fun _ => (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) = entry) := by
        intro u; ext z; simp only [show ((⟨t, u⟩ : (i : spec.Domain) × spec.Range i) :: z.2)[0]? =
          some (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) from rfl, Option.some_inj]
      simp_rw [hpred]
      -- Goal: ∑' u, Pr[= u | query t] * Pr[fun _ => ⟨t,u⟩ = entry | sim.run] ≤ 1/|R|
      -- Replace inner Pr by: 0 (if ⟨t,u⟩ ≠ entry) or ≤ 1 (if ⟨t,u⟩ = entry).
      -- So the sum ≤ Pr[= entry.2 | query t] when t = entry.1, else 0.
      -- Direct bound: each term ≤ Pr[= u | query t] * 1 = 1/|Range t|.
      -- And at most one term is nonzero (the one with ⟨t,u⟩ = entry).
      -- So sum ≤ 1/|Range t| = 1/|Range entry.1| when t = entry.1, else 0.
      -- Use: probOutput_query gives Pr[= u | query t] = 1/|Range t|.
      -- Substitute and bound.
      -- Case split on whether t = entry.1
      by_cases ht : t = entry.1
      · -- t = entry.1: Range t = Range entry.1, so card⁻¹ match.
        subst ht
        simp_rw [probOutput_query]
        rw [ENNReal.tsum_mul_left]
        apply le_of_le_of_eq (mul_le_mul' le_rfl _) (mul_one _)
        -- Need: ∑' u, Pr[fun _ => ⟨entry.1, u⟩ = entry | sim.run] ≤ 1
        -- Only u = entry.2 can satisfy ⟨entry.1, u⟩ = entry.
        -- For u ≠ entry.2, the Sigma can't be equal (same fst, different snd).
        -- Reduce Sigma equality to component equality
        -- entry = ⟨entry.1, entry.2⟩ and t was subst'd to entry.1
        -- So ⟨entry.1, u⟩ = entry ↔ u = entry.2
        have hsigma : ∀ w : spec.Range entry.1,
            (⟨entry.1, w⟩ : (i : spec.Domain) × spec.Range i) = entry ↔ w = entry.2 := by
          intro w; constructor
          · intro h; exact eq_of_heq (Sigma.mk.inj h).2
          · intro h; subst h; exact Sigma.eta entry
        simp_rw [show ∀ w : spec.Range entry.1,
            (fun _ : α × QueryLog spec =>
              (⟨entry.1, w⟩ : (i : spec.Domain) × spec.Range i) = entry) =
            fun _ => w = entry.2 from fun w => by ext; exact hsigma w]
        exact le_trans
          (ENNReal.tsum_le_tsum fun w => by
            by_cases hw : w = entry.2
            · exact le_trans probEvent_le_one (by simp [hw])
            · exact le_of_eq_of_le (probEvent_eq_zero fun _ _ => hw) (by simp [hw]))
          (le_of_eq (tsum_ite_eq entry.2 (fun _ => (1 : ℝ≥0∞))))
      · -- t ≠ entry.1: ⟨t, u⟩ ≠ entry for all u, so inner Pr = 0.
        have hne : ∀ u : spec.Range t,
            ¬ (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) = entry :=
          fun _ h => ht (by cases h; rfl)
        have hzero : ∀ u : spec.Range t,
            Pr[fun _ => (⟨t, u⟩ : (i : spec.Domain) × spec.Range i) = entry |
              (simulateQ loggingOracle (mx u)).run] = 0 :=
          fun u => probEvent_eq_zero fun _ _ => hne u
        simp only [hzero, mul_zero, tsum_zero]
        exact zero_le _
    | succ k' =>
      -- k > 0: decompose with probEvent_bind_eq_tsum, use ih.
      rw [probEvent_bind_eq_tsum]
      simp_rw [probEvent_map, Function.comp_def, List.getElem?_cons_succ]
      calc ∑' u, Pr[= u | (query t : OracleComp spec _)] *
            Pr[fun z => z.2[k']? = some entry | (simulateQ loggingOracle (mx u)).run]
        ≤ ∑' u, Pr[= u | (query t : OracleComp spec _)] *
            (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ :=
          ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (ih u k')
        _ = (∑' u, Pr[= u | (query t : OracleComp spec _)]) *
            (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ :=
          ENNReal.tsum_mul_right
        _ ≤ 1 * (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ :=
          mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ := one_mul _

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
  le_trans (probEvent_log_entry_eq_le oa k entry)
    (ENNReal.inv_le_inv.mpr (by exact_mod_cast hrange entry.1))

omit [DecidableEq ι] [spec.DecidableEq] in
/-- Probability that the k-th log entry's output is HEq to a fixed value `u₀ : spec.Range t₀`.
Unlike `probEvent_log_entry_eq_le` which matches the full sigma entry, this only constrains
the output component. The bound uses `hrange` to get `1/|Range default|`.

Proof by structural induction on the computation, same shape as `probEvent_log_entry_eq_le`. -/
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
    simp only [simulateQ_pure]
    refine le_of_eq_of_le (probEvent_eq_zero fun z hmem h => ?_) (zero_le _)
    simp only [WriterT.run_pure', List.empty_eq, support_pure,
      Set.mem_singleton_iff] at hmem; obtain ⟨_, rfl⟩ := hmem
    obtain ⟨s, v, hlog, _⟩ := h; simp at hlog
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind, probEvent_bind_eq_tsum]
    simp_rw [probEvent_map, Function.comp_def]
    cases k with
    | zero =>
      -- k = 0: position 0 is ⟨t, u'⟩, event becomes HEq u₀ u' (constant in z).
      have hpred : ∀ u' : spec.Range t,
          (fun z : α × QueryLog spec =>
            ∃ (s : spec.Domain) (v : spec.Range s),
              ((⟨t, u'⟩ : (i : spec.Domain) × spec.Range i) :: z.2)[0]? = some ⟨s, v⟩ ∧
              HEq u₀ v) =
          (fun _ => HEq u₀ u') := by
        intro u'; ext z
        constructor
        · rintro ⟨s, v, heq, hheq⟩
          have : (⟨t, u'⟩ : (i : spec.Domain) × spec.Range i) = ⟨s, v⟩ := by
            simpa using heq
          cases this; exact hheq
        · intro h; exact ⟨t, u', by simp, h⟩
      simp_rw [hpred]
      -- Inner Pr is constant: either 1 (if HEq u₀ u') or 0 (otherwise).
      simp_rw [probEvent_const, HasEvalPMF.probFailure_eq_zero, tsub_zero]
      -- Goal: ∑' u', Pr[=u'|query t] * (if HEq u₀ u' then 1 else 0) ≤ 1/|Range default|
      simp_rw [probOutput_query]
      rw [ENNReal.tsum_mul_left]
      -- Bound: each term ≤ (card t)⁻¹ * (if HEq u₀ u' then 1 else 0),
      -- then factor out and bound the indicator sum by 1.
      have hind_le : ∑' (u' : spec.Range t), (if HEq u₀ u' then (1 : ℝ≥0∞) else 0) ≤ 1 := by
        -- At most one u' satisfies HEq u₀ u'.
        have hsubsingleton : ∀ (a b : spec.Range t), HEq u₀ a → HEq u₀ b → a = b :=
          fun a b ha hb => eq_of_heq (ha.symm.trans hb)
        rw [tsum_eq_sum (s := Finset.univ) (by simp)]
        rw [show ∑ u' : spec.Range t, (if HEq u₀ u' then (1 : ℝ≥0∞) else 0) =
            ((Finset.univ.filter (fun u' : spec.Range t => HEq u₀ u')).card : ℝ≥0∞) from by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one]]
        exact_mod_cast Finset.card_le_one.mpr fun a ha b hb => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact hsubsingleton a b ha hb
      calc (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ *
            ∑' u', (if HEq u₀ u' then (1 : ℝ≥0∞) else 0)
        ≤ (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * 1 :=
          mul_le_mul' le_rfl hind_le
        _ = (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := mul_one _
        _ ≤ (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
          ENNReal.inv_le_inv.mpr (by exact_mod_cast hrange t)
    | succ k' =>
      -- k > 0: position k'+1 in the prepended log = position k' in sub-log.
      have hshift : ∀ u' : spec.Range t,
          (fun z : α × QueryLog spec =>
            ∃ (s : spec.Domain) (v : spec.Range s),
              ((⟨t, u'⟩ : (i : spec.Domain) × spec.Range i) :: z.2)[k' + 1]? = some ⟨s, v⟩ ∧
              HEq u₀ v) =
          (fun z => ∃ (s : spec.Domain) (v : spec.Range s),
              z.2[k']? = some ⟨s, v⟩ ∧ HEq u₀ v) := by
        intro u'; ext z; simp only [List.getElem?_cons_succ]
      simp_rw [hshift]
      calc ∑' u, Pr[= u | (query t : OracleComp spec _)] *
            Pr[fun z => ∃ (s : spec.Domain) (v : spec.Range s),
                z.2[k']? = some ⟨s, v⟩ ∧ HEq u₀ v |
              (simulateQ loggingOracle (mx u)).run]
        ≤ ∑' u, Pr[= u | (query t : OracleComp spec _)] *
            (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
          ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (ih u k')
        _ = (∑' u, Pr[= u | (query t : OracleComp spec _)]) *
            (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
          ENNReal.tsum_mul_right
        _ ≤ 1 * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
          mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := one_mul _

omit [DecidableEq ι] [spec.DecidableEq] in
/-- **Per-pair collision bound**: For any two positions in a `loggingOracle` trace
with distinct inputs, the probability that their outputs are HEq-equal is ≤ 1/|C|.

This is the core ROM property: distinct oracle inputs yield independent uniform outputs.
In the `evalDist` model, each `query` call returns a fresh uniform sample.

The proof is by structural induction on the computation. For `query t >>= mx`:
- If both positions ≥ 1: they refer to sub-log positions, and the IH applies directly.
- If one position is 0: the collision involves the fresh response `u` from `query t` and
  a sub-log entry. By `probEvent_log_output_heq_le`, sub-log position k matching any
  fixed entry has prob ≤ 1/|Range default|.

The `hrange` hypothesis ensures that `|Range default|` is minimal across all oracle
indices, so the per-entry bound `1/|Range s| ≤ 1/|Range default|` holds uniformly. -/
theorem probEvent_pair_collision_le {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (_hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (i j : Fin n) (hij : i ≠ j) :
    Pr[fun z => z.2.length > i.val ∧ z.2.length > j.val ∧
        z.2[i]?.bind (fun ei => z.2[j]?.map (fun ej =>
          ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true |
      (simulateQ loggingOracle oa).run] ≤
      (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  -- Weaken to drop the length conditions (they only strengthen the event).
  apply le_trans (probEvent_mono fun z _ h => h.2.2)
  -- Prove the generalized statement by induction on the computation,
  -- dropping the Fin n / query bound structure (only needed for the union bound).
  suffices h : ∀ (β : Type) (ob : OracleComp spec β) (i j : ℕ) (_ : i ≠ j),
      Pr[fun z => z.2[i]?.bind (fun ei => z.2[j]?.map (fun ej =>
        ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true |
        (simulateQ loggingOracle ob).run] ≤
        (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ from
    h α oa i.val j.val (Fin.val_ne_of_ne hij)
  intro β ob
  induction ob using OracleComp.inductionOn with
  | pure x =>
    intro i j _
    simp [simulateQ_pure]
  | query_bind t mx ih =>
    intro i j hij
    rw [run_simulateQ_loggingOracle_query_bind, probEvent_bind_eq_tsum]
    simp_rw [probEvent_map, Function.comp_def]
    -- Log = [⟨t, u⟩] ++ sub_log(u). Position 0 → ⟨t,u⟩, position k+1 → sub_log[k].
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j' =>
        -- i = 0, j = j'+1. Collision between fresh entry ⟨t,u⟩ and sub_log[j'].
        -- The collision event asks: t ≠ sub_log(u)[j'].1 ∧ HEq u sub_log(u)[j'].2.
        -- For each u, the sub_log entry at j' is bounded by probEvent_log_output_heq_le.
        -- We weaken the collision predicate to just asking that sub_log[j'] exists and
        -- matches a specific sigma-typed entry determined by u, then sum over entries.
        --
        -- The bound 1/|Range default| per inner term follows because for each u,
        -- the collision implies sub_log[j']? = some ⟨s, v⟩ for specific s, v with
        -- HEq u v. By probEvent_log_entry_eq_le, Pr[sub_log[j']? = some ⟨s,v⟩] ≤ 1/|Range s|.
        -- With hrange: ≤ 1/|Range default|.
        -- The key: the event implies sub_log[j']? equals a SPECIFIC entry (not a union),
        -- because position j' has exactly one value in each realization.
        --
        -- Formal argument: weaken inner Pr to ≤ 1, then factor. This gives ≤ 1, too loose.
        -- Instead: use probEvent_mono to bound inner by probEvent_log_output_heq_le.
        -- But the collision event (Option.map predicate = some true) implies
        -- z.2[j']? = some ej for some ej. We bound by summing over all possible ej.
        -- Since only ej with HEq u ej.2 contribute, and for each s there is at most one
        -- such ej, we get ≤ ∑_s 1/|Range s|. With hrange this is ≤ |Domain|/|Range default|.
        -- This is too loose for |Domain| > 1.
        --
        -- Use probEvent_log_output_match_le: for each u, the collision event at position j'
        -- implies ∃ s v, z.2[j']? = some ⟨s, v⟩ ∧ HEq u v.
        -- Simplify position 0 and j'+1 in the prepended log.
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind_some]
        -- Step 1: Weaken inner event to ∃ form via probEvent_mono, then apply helper.
        have hweaken : ∀ u, Pr[fun z =>
              z.2[j']?.map (fun ej => (⟨t, u⟩ : (i : spec.Domain) × spec.Range i).1 ≠ ej.1 ∧
                HEq (⟨t, u⟩ : (i : spec.Domain) × spec.Range i).2 ej.2) = some true |
              (simulateQ loggingOracle (mx u)).run] ≤
            (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := fun u =>
          le_trans (probEvent_mono fun z _ hev => by
            match hz : z.2[j']? with
            | none => simp [hz] at hev
            | some ⟨s, v⟩ =>
              simp only [ne_eq, hz, Option.map_some, Option.pure_def,
                Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
                eq_iff_iff, iff_true] at hev
              exact ⟨s, v, rfl, hev.2⟩)
            (probEvent_log_output_match_le hrange (mx u) j' t u)
        calc ∑' u, Pr[= u | (query t : OracleComp spec _)] * _
          ≤ ∑' u, Pr[= u | (query t : OracleComp spec _)] *
              (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
            ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (hweaken u)
          _ = (∑' u, Pr[= u | (query t : OracleComp spec _)]) *
              (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
            ENNReal.tsum_mul_right
          _ ≤ 1 * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
            mul_le_mul' tsum_probOutput_le_one le_rfl
          _ = (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := one_mul _
    | succ i' =>
      cases j with
      | zero =>
        -- j = 0, i = i'+1. Symmetric to the (0, j'+1) case.
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
        -- Step 1: Weaken inner event to ∃ form via probEvent_mono, then apply helper.
        have hweaken : ∀ u, Pr[fun z =>
              z.2[i']?.bind (fun ei =>
                (some (⟨t, u⟩ : (i : spec.Domain) × spec.Range i)).map (fun ej =>
                  ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true |
              (simulateQ loggingOracle (mx u)).run] ≤
            (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := fun u =>
          le_trans (probEvent_mono fun z _ hev => by
            match hz : z.2[i']? with
            | none => simp [hz] at hev
            | some ⟨s, v⟩ =>
              simp only [hz, ne_eq, Option.map_some, Option.bind_some,
                Option.pure_def, Option.bind_eq_bind, Option.some.injEq,
                eq_iff_iff, iff_true] at hev
              exact ⟨s, v, rfl, hev.2.symm⟩)
            (probEvent_log_output_match_le hrange (mx u) i' t u)
        calc ∑' u, Pr[= u | (query t : OracleComp spec _)] * _
          ≤ ∑' u, Pr[= u | (query t : OracleComp spec _)] *
              (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
            ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (hweaken u)
          _ = (∑' u, Pr[= u | (query t : OracleComp spec _)]) *
              (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
            ENNReal.tsum_mul_right
          _ ≤ 1 * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
            mul_le_mul' tsum_probOutput_le_one le_rfl
          _ = (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := one_mul _
      | succ j' =>
        -- Both i = i'+1, j = j'+1: collision in sub_log at (i', j'). Apply IH directly.
        simp only [List.getElem?_cons_succ]
        calc ∑' u, Pr[= u | (query t : OracleComp spec _)] *
              Pr[fun z => z.2[i']?.bind (fun ei => z.2[j']?.map (fun ej =>
                ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true |
                (simulateQ loggingOracle (mx u)).run]
          ≤ ∑' u, Pr[= u | (query t : OracleComp spec _)] *
              (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
            ENNReal.tsum_le_tsum fun u => mul_le_mul' le_rfl (ih u i' j' (by omega))
        _ = (∑' u, Pr[= u | (query t : OracleComp spec _)]) *
              (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
            ENNReal.tsum_mul_right
        _ ≤ 1 * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
            mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := one_mul _

/-! ## Union Bound Birthday (Textbook Steps 4-5)

Collision = ∃ pair with collision. Union bound over C(n,2) pairs gives n²/(2|C|). -/

omit [DecidableEq ι] in
/-- **Birthday bound for `loggingOracle`** (total query bound):
The probability of a collision in the query log is ≤ n²/(2|C|).

Proof: express collision as ∃ pair (i,j), then union bound using
`probEvent_pair_collision_le` for each pair. -/
theorem probEvent_logCollision_le_birthday_total {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hC : 0 < Fintype.card (spec.Range default))
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => LogHasCollision z.2 |
      (simulateQ loggingOracle oa).run] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  -- Strategy: express LogHasCollision as ∃ (i,j) ∈ Fin n × Fin n with i < j,
  -- then apply union bound, bounding each pair by 1/|C|.
  -- Step 1: LogHasCollision z.2 implies there exist indices i < j < n
  -- (assuming the log length is ≤ n from the query bound)
  -- Step 2: Union bound over pairs
  -- Step 3: Each pair contributes ≤ 1/|C| by probEvent_pair_collision_le
  -- Step 4: Number of pairs × 1/|C| = gauss_sum_inv_le
  let C := Fintype.card (spec.Range default)
  -- Bound by union over pairs using probEvent_pair_collision_le
  calc Pr[fun z => LogHasCollision z.2 | (simulateQ loggingOracle oa).run]
      ≤ ∑ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
          (C : ℝ≥0∞)⁻¹ := by
        -- Step A: Log length ≤ n for elements in support
        have hlog_le : ∀ z ∈ support ((simulateQ loggingOracle oa).run),
            z.2.length ≤ n :=
          fun z hz => log_length_le_of_mem_support_run_simulateQ hbound hz
        -- Step B: Define the per-pair collision event (matching probEvent_pair_collision_le)
        let E : Fin n × Fin n → α × QueryLog spec → Prop := fun ij z =>
          z.2.length > ij.1.val ∧ z.2.length > ij.2.val ∧
            z.2[ij.1]?.bind (fun ei => z.2[ij.2]?.map (fun ej =>
              ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true
        let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)
        -- Step C: probEvent_mono + union bound + per-pair bound
        apply le_trans (probEvent_mono (q := fun z => ∃ ij ∈ pairs, E ij z) ?_)
        · apply le_trans (probEvent_exists_finset_le_sum pairs _ E)
          apply Finset.sum_le_sum
          intro ⟨i, j⟩ hij
          simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij
          exact probEvent_pair_collision_le oa n hbound hrange i j (Fin.ne_of_lt hij)
        · -- Show LogHasCollision z.2 → ∃ pair in pairs, E pair z
          intro z hz hcoll
          obtain ⟨i, j, hij, hdist, heq⟩ := hcoll
          have hlen := hlog_le z hz
          have hi_lt : i.val < n := Nat.lt_of_lt_of_le i.isLt hlen
          have hj_lt : j.val < n := Nat.lt_of_lt_of_le j.isLt hlen
          -- Helper: reduce getElem? for Fin n index when val < list length
          have getElem?_fin (l : QueryLog spec) (k : Fin n) (hk : k.val < l.length) :
              l[k]? = some l[k.val] := by
            simp [hk]
          rcases lt_or_gt_of_ne hij with hlt | hgt
          · refine ⟨(⟨i.val, hi_lt⟩, ⟨j.val, hj_lt⟩), ?_, ?_⟩
            · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt
            · refine ⟨i.isLt, j.isLt, ?_⟩
              rw [getElem?_fin _ _ i.isLt, getElem?_fin _ _ j.isLt]
              change some _ = some _
              congr 1; exact propext ⟨fun _ => rfl, fun _ => ⟨hdist, heq⟩⟩
          · refine ⟨(⟨j.val, hj_lt⟩, ⟨i.val, hi_lt⟩), ?_, ?_⟩
            · simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]; exact hgt
            · refine ⟨j.isLt, i.isLt, ?_⟩
              rw [getElem?_fin _ _ j.isLt, getElem?_fin _ _ i.isLt]
              change some _ = some _
              congr 1; exact propext ⟨fun _ => rfl, fun _ => ⟨Ne.symm hdist, heq.symm⟩⟩
    _ ≤ (n ^ 2 : ℝ≥0∞) / (2 * C) := by
        -- The sum of constant C⁻¹ over pairs = |pairs| * C⁻¹
        rw [Finset.sum_const, nsmul_eq_mul]
        -- Suffices to show |pairs| * C⁻¹ ≤ n²/(2C)
        -- |pairs| = n*(n-1)/2, and n*(n-1)/2 ≤ n²/2
        -- We use gauss_sum_inv_le: ∑ k < n, k * C⁻¹ ≤ n²/(2C)
        -- Note ∑ k < n, k = n*(n-1)/2 = |pairs|
        -- So it suffices to show |pairs| ≤ ∑ k < n, k ... actually they're equal!
        -- |{(i,j) : Fin n × Fin n | i < j}| = ∑_{j<n} j = n(n-1)/2
        have hcard_eq : ((Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card : ℝ≥0∞)
            = ∑ k ∈ range n, (k : ℝ≥0∞) := by
          -- |{(i,j) | i < j}| = ∑_{j<n} j = n*(n-1)/2
          -- |{(i,j) : Fin n × Fin n | i < j}| = ∑_{k<n} k
          -- Proved as a separate lemma for clarity.
          have hcard_nat : ∀ m : ℕ,
              (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).card =
                ∑ k ∈ range m, k := by
            intro m; induction m with
            | zero => simp
            | succ k ih =>
              rw [Finset.sum_range_succ, ← ih]
              -- Split the set of pairs in Fin (k+1) into:
              -- (1) pairs (i,j) with both < k (embedded from Fin k), and
              -- (2) pairs (i, last k) for i < last k
              -- Count: |old pairs| + k
              have hsplit :
                  (Finset.univ.filter (fun p : Fin (k+1) × Fin (k+1) => p.1 < p.2)).card =
                  (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).card + k := by
                -- Define the embedding from Fin k pairs to Fin (k+1) pairs
                let emb : Fin k × Fin k ↪ Fin (k+1) × Fin (k+1) :=
                  ⟨fun p => (p.1.castSucc, p.2.castSucc), fun a b h => by
                    simp only [Prod.ext_iff, Fin.castSucc_inj] at h; exact Prod.ext h.1 h.2⟩
                -- Define the embedding for new pairs (i, last k)
                let newEmb : Fin k ↪ Fin (k+1) × Fin (k+1) :=
                  ⟨fun i => (i.castSucc, Fin.last k), fun a b h => by
                    simp only [Prod.ext_iff, Fin.castSucc_inj, and_true] at h; exact h⟩
                -- The filtered set splits as a disjoint union
                have hunion :
                    Finset.univ.filter (fun p : Fin (k+1) × Fin (k+1) => p.1 < p.2) =
                    (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).map emb ∪
                    Finset.univ.map newEmb := by
                  ext ⟨i, j⟩
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    Finset.mem_union, Finset.mem_map, emb, newEmb,
                    Function.Embedding.coeFn_mk]
                  constructor
                  · intro hij
                    by_cases hj : j = Fin.last k
                    · subst hj; right
                      exact ⟨i.castPred (Fin.ne_last_of_lt hij), by
                        ext <;> simp [Fin.castSucc_castPred]⟩
                    · left
                      have hj' : j ≠ Fin.last k := hj
                      have hi' : i ≠ Fin.last k :=
                        Fin.ne_last_of_lt (lt_trans hij (lt_of_le_of_ne (Fin.le_last j) hj'))
                      refine ⟨(i.castPred hi', j.castPred hj'), ?_, ?_⟩
                      · exact Fin.castPred_lt_castPred hij hj'
                      · ext <;> simp [Fin.castSucc_castPred]
                  · intro hij
                    rcases hij with ⟨⟨a, b⟩, hab, heq⟩ | ⟨a, heq⟩
                    · have h1 := congr_arg Prod.fst heq
                      have h2 := congr_arg Prod.snd heq
                      simp only at h1 h2
                      rw [← h1, ← h2]
                      exact Fin.castSucc_lt_castSucc_iff.mpr hab
                    · have h1 := congr_arg Prod.fst heq
                      have h2 := congr_arg Prod.snd heq
                      simp only at h1 h2
                      rw [← h1, ← h2]
                      exact Fin.castSucc_lt_last a
                have hdisj : Disjoint
                    ((Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).map emb)
                    (Finset.univ.map newEmb) := by
                  rw [Finset.disjoint_left]
                  intro ⟨x, y⟩ hmem1 hmem2
                  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
                    emb, newEmb, Function.Embedding.coeFn_mk] at hmem1 hmem2
                  obtain ⟨⟨a, b⟩, _, heq1⟩ := hmem1
                  obtain ⟨c, heq2⟩ := hmem2
                  have h1 := congr_arg Prod.snd heq1
                  have h2 := congr_arg Prod.snd heq2
                  simp only at h1 h2
                  rw [← h1] at h2
                  exact absurd h2.symm (Fin.castSucc_ne_last b)
                rw [hunion, Finset.card_union_of_disjoint hdisj,
                  Finset.card_map, Finset.card_map, Finset.card_univ, Fintype.card_fin]
              omega
          have := hcard_nat n; push_cast [this]; rfl
        rw [hcard_eq, Finset.sum_mul]
        exact ENNReal.gauss_sum_inv_le n C (by exact_mod_cast hC)

/-- **Tight birthday bound for `cachingOracle`** (total query bound):
The probability of a collision in the cache is ≤ n*(n-1)/(2|C|). -/
theorem probEvent_cacheCollision_le_birthday_total_tight {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (_hbound : IsTotalQueryBound oa n)
    (_hC : 0 < Fintype.card (spec.Range default))
    (_hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  -- Direct proof strategy (does NOT use cachingOracle.withLogging or WriterT):
  --
  -- The cache from `cachingOracle` starting at `∅` after `n` queries has ≤ n entries,
  -- each drawn uniformly and independently on cache miss. A CacheHasCollision requires
  -- two distinct inputs t₁ ≠ t₂ with HEq outputs. By the same birthday argument as
  -- the log version:
  --   1. Each pair of distinct cache entries collides with probability ≤ 1/|C|
  --      (since fresh queries draw uniformly via `probOutput_fresh_cachingOracle_query`)
  --   2. Union bound over ≤ C(n,2) pairs gives n²/(2|C|)
  --
  -- The formal proof requires a simulation relation showing that the cache entries
  -- at positions corresponding to distinct fresh queries have independent uniform
  -- marginals — the same core ROM property used in `probEvent_pair_collision_le`
  -- for logs but adapted to the cache's function representation.
  --
  -- Proof by induction on `oa`, with a generalized cache-size bound.
  -- CacheBounded k cache := at most k domain values have cache entries.
  -- This allows tracking the implicit cache size through the induction
  -- without requiring Fintype spec.Domain.
  let C := (Fintype.card (spec.Range default) : ℝ≥0∞)
  let CacheBounded (k : ℕ) (cache : QueryCache spec) : Prop :=
    ∃ S : Finset spec.Domain, S.card ≤ k ∧ ∀ t, cache t ≠ none → t ∈ S
  suffices gen : ∀ (β : Type) (ob : OracleComp spec β) (m k : ℕ),
      IsTotalQueryBound ob m →
      ∀ cache₀ : QueryCache spec,
      ¬CacheHasCollision cache₀ →
      CacheBounded k cache₀ →
      Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle ob).run cache₀] ≤
        ∑ j ∈ range m, ((k + j : ℕ) : ℝ≥0∞) * C⁻¹ by
    -- Instantiate with cache₀ = ∅, k = 0
    have h0 : ¬CacheHasCollision (∅ : QueryCache spec) := by
      intro ⟨t₁, _, _, _, _, h1, _, _⟩; simp at h1
    have hbnd : CacheBounded 0 (∅ : QueryCache spec) :=
      ⟨∅, by simp, fun t ht => absurd (by simp : (∅ : QueryCache spec) t = none) ht⟩
    calc Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅]
        ≤ ∑ j ∈ range n, ((0 + j : ℕ) : ℝ≥0∞) * C⁻¹ := gen α oa n 0 _hbound ∅ h0 hbnd
      _ = ∑ j ∈ range n, (j : ℝ≥0∞) * C⁻¹ := by simp
      _ = ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * C) := ENNReal.gauss_sum_inv_eq n C
  -- Main induction
  intro β ob
  induction ob using OracleComp.inductionOn with
  | pure x =>
    intro m k _ cache₀ hnocoll _
    -- simulateQ on pure returns (x, cache₀) unchanged. CacheHasCollision cache₀ is False.
    have : Pr[fun z => CacheHasCollision z.2 |
        (simulateQ cachingOracle (pure x)).run cache₀] = 0 := by
      rw [simulateQ_pure]
      refine probEvent_eq_zero fun z hz h => ?_
      simp only [StateT.run] at hz
      obtain ⟨rfl, rfl⟩ := hz
      exact hnocoll h
    rw [this]; exact zero_le _
  | query_bind t mx ih =>
    intro m k hm cache₀ hnocoll hbnd
    rw [isTotalQueryBound_query_bind_iff] at hm
    obtain ⟨hpos, hrest⟩ := hm
    -- Decompose: simulateQ on query_bind unfolds via cachingOracle
    -- Case split on whether t is already cached
    by_cases ht : ∃ v, cache₀ t = some v
    · -- Cache hit: cache unchanged, run mx v with same cache
      obtain ⟨v, hv⟩ := ht
      -- The computation simplifies to (simulateQ cachingOracle (mx v)).run cache₀
      have hrun : (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
          (simulateQ cachingOracle (mx v)).run cache₀ := by
        simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
        -- Goal: (liftM (cachingOracle t)).run cache₀ >>= ... = ...
        -- cachingOracle t at cache₀ with cache₀ t = some v returns (v, cache₀)
        have hcache : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
            pure (v, cache₀) := by
          simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
            StateT.run_bind, StateT.run_get, hv, pure_bind, StateT.run_pure]
        rw [hcache, pure_bind]
        simp [OracleQuery.cont_query]
      rw [hrun]
      -- Apply IH: mx v has bound m - 1, cache₀ has ≤ k entries
      calc Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle (mx v)).run cache₀]
          ≤ ∑ j ∈ range (m - 1), ((k + j : ℕ) : ℝ≥0∞) * C⁻¹ :=
            ih v (m - 1) k (hrest v) cache₀ hnocoll hbnd
        _ ≤ ∑ j ∈ range m, ((k + j : ℕ) : ℝ≥0∞) * C⁻¹ := by
            apply Finset.sum_le_sum_of_subset
            exact Finset.range_mono (Nat.sub_le m 1)
    · -- Cache miss: cache₀ t = none
      push_neg at ht
      have ht_none : cache₀ t = none := by
        cases h : cache₀ t with | none => rfl | some v => exact absurd h (ht v)
      -- The computation becomes: query t >>= fun u =>
      -- (sim cachingOracle (mx u)).run (cache₀.cacheQuery t u)
      -- We prove this by showing the unfolded cachingOracle at a miss is a query + cacheQuery.
      have hrun : (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
          (liftM (query t) >>= fun u =>
            (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)) := by
        simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
        -- Show the oracle step unfolds to query + cacheQuery
        have hstep : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
            (liftM (query t) >>= fun u =>
              pure (u, cache₀.cacheQuery t u) : OracleComp spec _) := by
          simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
            StateT.run_bind, StateT.run_get, pure_bind, ht_none]
          -- Goal involves StateT.lift ... cache₀
          change (StateT.lift (PFunctor.FreeM.lift (query t)) cache₀ >>= _) = _
          simp only [StateT.lift, bind_assoc, pure_bind,
            modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, StateT.run]
        rw [hstep, bind_assoc]; simp [pure_bind]
      rw [hrun]
      -- Apply probEvent_bind_le_add to decompose:
      -- ε₁ = Pr[CacheHasCollision (cache₀.cacheQuery t u) | u ← query t] ≤ k * C⁻¹
      -- ε₂ = Pr[CacheHasCollision final | continuation, given no collision] by IH
      have hε₁ : Pr[fun u => CacheHasCollision (cache₀.cacheQuery t u) |
          (liftM (query t) : OracleComp spec _)] ≤ (k : ℝ≥0∞) * C⁻¹ := by
        open Classical in
        rw [show (liftM (query t) : OracleComp spec _) = (query t : OracleComp spec _) from rfl,
            probEvent_query]
        -- Goal: ↑|{u | CacheHasCollision (cache₀.cacheQuery t u)}| / ↑|Range t| ≤ k * C⁻¹
        -- Bound the bad set cardinality by k
        suffices hbad_le_k : (Finset.univ.filter
            (fun u => CacheHasCollision (cache₀.cacheQuery t u))).card ≤ k by
          calc (↑(Finset.univ.filter (fun u => CacheHasCollision (cache₀.cacheQuery t u))).card
                  : ℝ≥0∞) / ↑(Fintype.card (spec.Range t))
              ≤ (k : ℝ≥0∞) / ↑(Fintype.card (spec.Range t)) := by
                apply ENNReal.div_le_div_right
                exact_mod_cast hbad_le_k
            _ ≤ (k : ℝ≥0∞) / C := by
                gcongr
                change (Fintype.card (spec.Range default) : ℝ≥0∞) ≤ ↑(Fintype.card (spec.Range t))
                exact_mod_cast (_hrange t)
            _ = (k : ℝ≥0∞) * C⁻¹ := by rw [ENNReal.div_eq_inv_mul, mul_comm]
        obtain ⟨S, hScard, hSmem⟩ := hbnd
        -- Any collision in cache₀.cacheQuery t u must involve t
        -- (since ¬CacheHasCollision cache₀)
        have hmust : ∀ u, CacheHasCollision (cache₀.cacheQuery t u) →
            ∃ t' : spec.Domain, t' ≠ t ∧
              ∃ v : spec.Range t', cache₀ t' = some v ∧ HEq u v := by
          intro u ⟨t₁, t₂, u₁, u₂, hne, h1, h2, hequ⟩
          by_cases ht1 : t₁ = t
          · subst ht1
            refine ⟨t₂, hne.symm, u₂, ?_, ?_⟩
            · rwa [QueryCache.cacheQuery_of_ne _ _ hne.symm] at h2
            · simp only [QueryCache.cacheQuery_self, Option.some.injEq] at h1
              subst h1; exact hequ
          · by_cases ht2 : t₂ = t
            · subst ht2
              refine ⟨t₁, hne, u₁, ?_, ?_⟩
              · rwa [QueryCache.cacheQuery_of_ne _ _ ht1] at h1
              · simp only [QueryCache.cacheQuery_self, Option.some.injEq] at h2
                subst h2; exact hequ.symm
            · exfalso; apply hnocoll
              exact ⟨t₁, t₂, u₁, u₂, hne,
                by rwa [QueryCache.cacheQuery_of_ne _ _ ht1] at h1,
                by rwa [QueryCache.cacheQuery_of_ne _ _ ht2] at h2, hequ⟩
        -- Define witness function: for each bad u, pick t' with cache₀ t' = some v, HEq u v
        let f : spec.Range t → spec.Domain := fun u =>
          if h : CacheHasCollision (cache₀.cacheQuery t u)
          then (hmust u h).choose
          else default
        -- f maps bad set into S
        have hf_maps : ∀ u ∈ Finset.univ.filter
            (fun u => CacheHasCollision (cache₀.cacheQuery t u)),
            f u ∈ S := by
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          change (if h : CacheHasCollision (cache₀.cacheQuery t u)
            then (hmust u h).choose else default) ∈ S
          rw [dif_pos hu]
          obtain ⟨_, v, hcache, _⟩ := (hmust u hu).choose_spec
          exact hSmem _ (by rw [hcache]; exact Option.some_ne_none v)
        -- f is injective on bad set
        have hf_inj : Set.InjOn f
            (Finset.univ.filter (fun u => CacheHasCollision (cache₀.cacheQuery t u))) := by
          intro u₁ hu₁ u₂ hu₂ hfeq
          have hu₁' := (Finset.mem_filter.mp hu₁).2
          have hu₂' := (Finset.mem_filter.mp hu₂).2
          -- Unfold f in hfeq
          change (if h : CacheHasCollision _ then (hmust u₁ h).choose else default) =
            (if h : CacheHasCollision _ then (hmust u₂ h).choose else default) at hfeq
          rw [dif_pos hu₁', dif_pos hu₂'] at hfeq
          -- Both u₁, u₂ are HEq to the cache value at the same index
          obtain ⟨_, v₁, hcache₁, heq₁⟩ := (hmust u₁ hu₁').choose_spec
          obtain ⟨_, v₂, hcache₂, heq₂⟩ := (hmust u₂ hu₂').choose_spec
          -- Prove via an auxiliary lemma that avoids dependent rewriting
          -- Key: if cache₀ t₁' = some v₁ and cache₀ t₂' = some v₂ and t₁' = t₂'
          -- then HEq v₁ v₂ (since cache₀ is a dependent function)
          suffices aux : ∀ (a b : spec.Domain) (va : spec.Range a) (vb : spec.Range b),
              cache₀ a = some va → cache₀ b = some vb → a = b → HEq va vb by
            exact eq_of_heq (heq₁.trans ((aux _ _ _ _ hcache₁ hcache₂ hfeq).trans heq₂.symm))
          intro a b va vb ha hb hab
          subst hab; rw [ha] at hb; exact heq_of_eq (Option.some.inj hb)
        calc (Finset.univ.filter (fun u => CacheHasCollision (cache₀.cacheQuery t u))).card
            ≤ S.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
          _ ≤ k := hScard
      have hε₂ : ∀ u ∈ support (liftM (query t) : OracleComp spec _),
          ¬CacheHasCollision (cache₀.cacheQuery t u) →
          Pr[fun z => CacheHasCollision z.2 |
            (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)] ≤
              ∑ j ∈ range (m - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) * C⁻¹ := by
        intro u _ hnocoll'
        apply ih u (m - 1) (k + 1) (hrest u) _ hnocoll'
        -- CacheBounded (k+1) for cache₀.cacheQuery t u
        obtain ⟨S, hScard, hSmem⟩ := hbnd
        exact ⟨insert t S,
          le_trans (Finset.card_insert_le t S) (by omega),
          fun t' ht' => by
            by_cases heq : t' = t
            · exact heq ▸ Finset.mem_insert_self _ S
            · rw [QueryCache.cacheQuery_of_ne cache₀ _ heq] at ht'
              exact Finset.mem_insert_of_mem (hSmem t' ht')⟩
      -- Combine via probEvent_bind_le_add
      have hcombine := probEvent_bind_le_add
        (mx := (liftM (query t) : OracleComp spec _))
        (my := fun u => (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u))
        (p := fun u => ¬CacheHasCollision (cache₀.cacheQuery t u))
        (q := fun z => ¬CacheHasCollision z.2)
        (ε₁ := (k : ℝ≥0∞) * C⁻¹)
        (ε₂ := ∑ j ∈ range (m - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) * C⁻¹)
        (by simpa [not_not] using hε₁)
        (by simpa [not_not] using hε₂)
      simp only [not_not] at hcombine
      -- Now show k * C⁻¹ + ∑ j in range (m-1), (k+1+j) * C⁻¹ = ∑ j in range m, (k+j) * C⁻¹
      calc Pr[fun z => CacheHasCollision z.2 |
              liftM (query t) >>= fun u =>
                (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)]
          ≤ (k : ℝ≥0∞) * C⁻¹ + ∑ j ∈ range (m - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) * C⁻¹ :=
            hcombine
        _ = ∑ j ∈ range m, ((k + j : ℕ) : ℝ≥0∞) * C⁻¹ := by
            -- k * C⁻¹ + ∑_{j<m-1} (k+1+j) * C⁻¹ = ∑_{j<m} (k+j) * C⁻¹
            -- RHS = (k+0)*C⁻¹ + ∑_{j<m-1} (k+(j+1))*C⁻¹
            have hm1 : m = (m - 1) + 1 := by omega
            conv_rhs => rw [hm1]
            rw [Finset.sum_range_succ' (fun j => ((k + j : ℕ) : ℝ≥0∞) * C⁻¹)]
            simp only [Nat.add_zero]
            -- LHS: k*C⁻¹ + ∑_{j<m-1} (k+1+j)*C⁻¹
            -- RHS: k*C⁻¹ + ∑_{j<m-1} (k+(j+1))*C⁻¹
            -- Equal since k+1+j = k+(j+1) in ℕ
            have hsums : ∀ j ∈ range (m - 1),
                ((k + 1 + j : ℕ) : ℝ≥0∞) * C⁻¹ = ((k + (j + 1) : ℕ) : ℝ≥0∞) * C⁻¹ :=
              fun j _ => by congr 1; push_cast; ring
            rw [Finset.sum_congr rfl hsums, add_comm]


/-- **Loose birthday bound for `cachingOracle`** (total query bound):
The probability of a collision in the cache is ≤ n²/(2|C|).
Derived from the tight bound `n*(n-1)/(2|C|)` since `n*(n-1) ≤ n²`. -/
theorem probEvent_cacheCollision_le_birthday_total {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hC : 0 < Fintype.card (spec.Range default))
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  calc Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅]
      ≤ ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) :=
        probEvent_cacheCollision_le_birthday_total_tight oa n hbound hC hrange
    _ ≤ (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
        gcongr; exact_mod_cast (show n * (n - 1) ≤ n ^ 2 by nlinarith [Nat.sub_le n 1])

/-! ## Per-Index Bound Versions -/

/-- Birthday bound for `cachingOracle` with per-index query bound. -/
theorem probEvent_cacheCollision_le_birthday {α : Type} {t : ℕ}
    [Inhabited ι] [Fintype ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hC : 0 < Fintype.card (spec.Range default))
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      ((Fintype.card ι * t) ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have htotal := IsTotalQueryBound.of_perIndex hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at htotal
  have h := probEvent_cacheCollision_le_birthday_total oa _ htotal hC hrange
  simp only [Nat.cast_mul] at h; exact h

/-- Birthday bound for single-index oracle specs (typical ROM case: `t²/(2|C|)`). -/
theorem probEvent_cacheCollision_le_birthday' {α : Type} {t : ℕ}
    [Inhabited ι] [Unique ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hC : 0 < Fintype.card (spec.Range default))
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ cachingOracle oa).run ∅] ≤
      (t ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have h := probEvent_cacheCollision_le_birthday oa hbound hC hrange
  simp only [Fintype.card_unique, Nat.cast_one, one_mul] at h
  exact h


end OracleComp
