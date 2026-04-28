/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.Constructions.Replicate

/-!
# Query Bounds for Iteration Constructs

This file lifts the structural query-bound predicates (`IsTotalQueryBound`,
`IsQueryBoundP`, `IsPerIndexQueryBound`) across the iteration combinators
`OracleComp.replicate`, `OracleComp.replicateTR`, `List.mapM`, and `List.foldlM`.

For the fixed-body case `replicate n oa`, the bound is exactly multiplicative —
we get an iff between the loop bound `n * k` and the body bound `k` (when
`0 < n`) for `IsTotalQueryBound` and `IsQueryBoundP`. The reverse direction
goes through `isTotalQueryBound_iff_counting_total_le` /
`isQueryBoundP_iff_counting_filter_le` and a witness lemma showing every
counting-oracle support point of `oa` lifts to an `n`-fold copy in
`replicate n oa`.

For the variable-body case (`List.mapM` / `List.foldlM`), only the forward
direction is available: the loop bound is the element-wise sum of body bounds.
-/

open OracleSpec

universe u v

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

/-! ### Forward `replicate` bounds -/

lemma isTotalQueryBound_replicate {oa : OracleComp spec α} {k : ℕ}
    (h : IsTotalQueryBound oa k) (n : ℕ) :
    IsTotalQueryBound (oa.replicate n) (n * k) := by
  induction n with
  | zero => rw [replicate_zero, Nat.zero_mul]; exact trivial
  | succ n ih =>
      rw [replicate_succ_bind, show (n + 1) * k = k + n * k from by ring]
      refine isTotalQueryBound_bind h fun x => ?_
      have hrest : IsTotalQueryBound (oa.replicate n >>= fun xs => pure (x :: xs))
          (n * k + 0) :=
        isTotalQueryBound_bind ih fun _ => trivial
      simpa using hrest

lemma isQueryBoundP_replicate {oa : OracleComp spec α} {p : ι → Prop}
    [DecidablePred p] {k : ℕ}
    (h : IsQueryBoundP oa p k) (n : ℕ) :
    IsQueryBoundP (oa.replicate n) p (n * k) := by
  induction n with
  | zero => rw [replicate_zero, Nat.zero_mul]; exact trivial
  | succ n ih =>
      rw [replicate_succ_bind, show (n + 1) * k = k + n * k from by ring]
      refine isQueryBoundP_bind h fun x _ => ?_
      have hrest : IsQueryBoundP (oa.replicate n >>= fun xs => pure (x :: xs)) p
          (n * k + 0) :=
        isQueryBoundP_bind ih fun _ _ => trivial
      simpa using hrest

lemma isPerIndexQueryBound_replicate [DecidableEq ι]
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (n : ℕ) :
    IsPerIndexQueryBound (oa.replicate n) (n • qb) := by
  induction n with
  | zero => rw [replicate_zero, zero_nsmul]; exact trivial
  | succ n ih =>
      rw [replicate_succ_bind, succ_nsmul, add_comm]
      refine isPerIndexQueryBound_bind h fun x => ?_
      have hrest : IsPerIndexQueryBound (oa.replicate n >>= fun xs => pure (x :: xs))
          (n • qb + 0) :=
        isPerIndexQueryBound_bind ih fun _ => trivial
      simpa using hrest

/-! ### Divide-trick iff for the fixed-body case

When the body `oa` is fixed, the loop bound `n * k` is exactly characterized by the body
bound `k`: forward by `isTotalQueryBound_replicate`, reverse by lifting any
counting-oracle support point of `oa` to an `n`-fold copy in `replicate n oa`. -/

/-- Compositional support characterization for `countingOracle.simulate (oa >>= ob) 0`:
the support decomposes as the sum of a path through `oa` and a path through `ob x`. -/
private lemma countingOracle.mem_support_simulate_bind_iff [DecidableEq ι]
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {z : β × QueryCount ι} :
    z ∈ support (countingOracle.simulate (oa >>= ob) 0) ↔
      ∃ x qc1 qc2, (x, qc1) ∈ support (countingOracle.simulate oa 0) ∧
        (z.1, qc2) ∈ support (countingOracle.simulate (ob x) 0) ∧
        z.2 = qc1 + qc2 := by
  -- Rewrite both sides to drop the (0 + ·) wrapper, then unfold the WriterT bind.
  have hzero_add : ((0 : QueryCount ι) + · ) = (id : QueryCount ι → QueryCount ι) := by
    funext qc; rw [zero_add]; rfl
  have hsim : ∀ {γ : Type u} (oc : OracleComp spec γ),
      support (countingOracle.simulate oc 0) =
      support (((simulateQ countingOracle oc).run) : OracleComp spec (γ × QueryCount ι)) := by
    intro γ oc
    change support (Prod.map id ((0 : QueryCount ι) + ·) <$> _) = _
    rw [hzero_add, Prod.map_id, id_map]
  rw [hsim, hsim, simulateQ_bind, WriterT.run_bind]
  simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨a, qc1⟩, ha, ⟨b, qc2⟩, hb, hb_eq⟩
    refine ⟨a, qc1, qc2, ha, ?_, ?_⟩
    · -- need (z.1, qc2) ∈ support, which is the same as (b, qc2) since b = z.1
      have hb_fst : b = z.1 := by
        have := congrArg Prod.fst hb_eq
        simpa [Prod.map] using this
      rw [hsim]; rw [← hb_fst]; exact hb
    · have := congrArg Prod.snd hb_eq
      simp [QueryCount.monoid_mul_def] at this
      exact this.symm
  · rintro ⟨a, qc1, qc2, ha, hb, hsum⟩
    rw [hsim] at hb
    refine ⟨(a, qc1), ha, (z.1, qc2), hb, ?_⟩
    refine Prod.ext rfl ?_
    simp only [QueryCount.monoid_mul_def]
    exact hsum.symm

/-- Every counting-oracle support point of the body `oa` lifts to a counting-oracle
support point of `replicate n oa` whose query count is `n` times the body's. -/
private lemma countingOracle.support_simulate_replicate_const [DecidableEq ι]
    {oa : OracleComp spec α} {z : α × QueryCount ι}
    (hz : z ∈ support (countingOracle.simulate oa 0)) :
    ∀ n, ∃ ys, (ys, fun i => n * z.2 i) ∈
      support (countingOracle.simulate (oa.replicate n) 0) := by
  intro n
  induction n with
  | zero =>
      refine ⟨[], ?_⟩
      have h0 : (([] : List α), (0 : QueryCount ι)) ∈
          support (countingOracle.simulate (oa.replicate 0) 0) := by
        rw [replicate_zero]
        exact (countingOracle.mem_support_simulate_pure_iff _ _ _).mpr rfl
      have hzero : (fun i => (0 : ℕ) * z.2 i) = (0 : QueryCount ι) := by
        funext i; simp
      rw [show (fun i => 0 * z.2 i) = (0 : QueryCount ι) from hzero]
      exact h0
  | succ n ih =>
      obtain ⟨ys, hys⟩ := ih
      refine ⟨z.1 :: ys, ?_⟩
      rw [replicate_succ_bind]
      rw [countingOracle.mem_support_simulate_bind_iff]
      refine ⟨z.1, z.2, fun i => n * z.2 i, hz, ?_, ?_⟩
      · rw [countingOracle.mem_support_simulate_bind_iff]
        refine ⟨ys, fun i => n * z.2 i, 0, hys, ?_, ?_⟩
        · exact (countingOracle.mem_support_simulate_pure_iff _ _ _).mpr rfl
        · funext i; simp
      · funext i; simp [Pi.add_apply]; ring

theorem isTotalQueryBound_replicate_iff [Finite ι] [spec.Inhabited]
    {oa : OracleComp spec α} {n k : ℕ} (hn : 0 < n) :
    IsTotalQueryBound (oa.replicate n) (n * k) ↔ IsTotalQueryBound oa k := by
  letI : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨fun h => ?_, fun h => isTotalQueryBound_replicate h n⟩
  rw [isTotalQueryBound_iff_counting_total_le]
  intro z' hz'
  obtain ⟨ys, hys⟩ := countingOracle.support_simulate_replicate_const hz' n
  have := IsTotalQueryBound.counting_total_le h hys
  have hsum : (∑ i, (fun i => n * z'.2 i) i) = n * ∑ i, z'.2 i := by
    simp [Finset.mul_sum]
  rw [hsum] at this
  exact Nat.le_of_mul_le_mul_left this hn

theorem isQueryBoundP_replicate_iff [Finite ι] [spec.Inhabited]
    {oa : OracleComp spec α} {p : ι → Prop} [DecidablePred p] {n k : ℕ} (hn : 0 < n) :
    IsQueryBoundP (oa.replicate n) p (n * k) ↔ IsQueryBoundP oa p k := by
  letI : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨fun h => ?_, fun h => isQueryBoundP_replicate h n⟩
  rw [isQueryBoundP_iff_counting_filter_le]
  intro z' hz'
  obtain ⟨ys, hys⟩ := countingOracle.support_simulate_replicate_const hz' n
  have := IsQueryBoundP.counting_bounded h hys
  have hsum : (∑ i ∈ Finset.univ.filter p, (fun i => n * z'.2 i) i) =
      n * ∑ i ∈ Finset.univ.filter p, z'.2 i := by
    simp [Finset.mul_sum]
  rw [hsum] at this
  exact Nat.le_of_mul_le_mul_left this hn

/-! ### `replicateTR` corollaries -/

lemma isTotalQueryBound_replicateTR {oa : OracleComp spec α} {k : ℕ}
    (h : IsTotalQueryBound oa k) (n : ℕ) :
    IsTotalQueryBound (oa.replicateTR n) (n * k) := by
  rw [replicateTR_eq_replicate]; exact isTotalQueryBound_replicate h n

lemma isQueryBoundP_replicateTR {oa : OracleComp spec α} {p : ι → Prop}
    [DecidablePred p] {k : ℕ}
    (h : IsQueryBoundP oa p k) (n : ℕ) :
    IsQueryBoundP (oa.replicateTR n) p (n * k) := by
  rw [replicateTR_eq_replicate]; exact isQueryBoundP_replicate h n

lemma isPerIndexQueryBound_replicateTR [DecidableEq ι]
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (n : ℕ) :
    IsPerIndexQueryBound (oa.replicateTR n) (n • qb) := by
  rw [replicateTR_eq_replicate]; exact isPerIndexQueryBound_replicate h n

theorem isTotalQueryBound_replicateTR_iff [Finite ι] [spec.Inhabited]
    {oa : OracleComp spec α} {n k : ℕ} (hn : 0 < n) :
    IsTotalQueryBound (oa.replicateTR n) (n * k) ↔ IsTotalQueryBound oa k := by
  rw [replicateTR_eq_replicate]; exact isTotalQueryBound_replicate_iff hn

theorem isQueryBoundP_replicateTR_iff [Finite ι] [spec.Inhabited]
    {oa : OracleComp spec α} {p : ι → Prop} [DecidablePred p] {n k : ℕ} (hn : 0 < n) :
    IsQueryBoundP (oa.replicateTR n) p (n * k) ↔ IsQueryBoundP oa p k := by
  rw [replicateTR_eq_replicate]; exact isQueryBoundP_replicate_iff hn

/-! ### `List.mapM` and `List.foldlM` (forward only) -/

lemma isTotalQueryBound_listMapM
    {f : α → OracleComp spec β} {k : α → ℕ}
    (h : ∀ x, IsTotalQueryBound (f x) (k x)) (xs : List α) :
    IsTotalQueryBound (xs.mapM f) ((xs.map k).sum) := by
  induction xs with
  | nil => simpa [List.mapM_nil] using
      (trivial : IsTotalQueryBound (pure ([] : List β) : OracleComp spec _) 0)
  | cons a xs ih =>
      rw [List.mapM_cons, List.map_cons, List.sum_cons]
      refine isTotalQueryBound_bind (h a) fun y => ?_
      have hrest : IsTotalQueryBound (xs.mapM f >>= fun ys => pure (y :: ys))
          ((xs.map k).sum + 0) :=
        isTotalQueryBound_bind ih fun _ => trivial
      simpa using hrest

lemma isTotalQueryBound_listMapM_const
    {f : α → OracleComp spec β} {k : ℕ}
    (h : ∀ x, IsTotalQueryBound (f x) k) (xs : List α) :
    IsTotalQueryBound (xs.mapM f) (xs.length * k) := by
  have := isTotalQueryBound_listMapM h xs
  rwa [show (xs.map fun _ => k).sum = xs.length * k by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]] at this

lemma isTotalQueryBound_listFoldlM
    {f : β → α → OracleComp spec β} {k : α → ℕ}
    (h : ∀ b x, IsTotalQueryBound (f b x) (k x)) (b₀ : β) (xs : List α) :
    IsTotalQueryBound (xs.foldlM f b₀) ((xs.map k).sum) := by
  induction xs generalizing b₀ with
  | nil => simpa [List.foldlM_nil] using
      (trivial : IsTotalQueryBound (pure b₀ : OracleComp spec _) 0)
  | cons a xs ih =>
      rw [List.foldlM_cons, List.map_cons, List.sum_cons]
      refine isTotalQueryBound_bind (h b₀ a) fun b' => ?_
      exact ih b'

lemma isQueryBoundP_listMapM
    {f : α → OracleComp spec β} {p : ι → Prop} [DecidablePred p] {k : α → ℕ}
    (h : ∀ x, IsQueryBoundP (f x) p (k x)) (xs : List α) :
    IsQueryBoundP (xs.mapM f) p ((xs.map k).sum) := by
  induction xs with
  | nil => simp [List.mapM_nil]
  | cons a xs ih =>
      rw [List.mapM_cons, List.map_cons, List.sum_cons]
      refine isQueryBoundP_bind (h a) fun y _ => ?_
      have hrest : IsQueryBoundP (xs.mapM f >>= fun ys => pure (y :: ys)) p
          ((xs.map k).sum + 0) :=
        isQueryBoundP_bind ih fun _ _ => trivial
      simpa using hrest

lemma isQueryBoundP_listMapM_const
    {f : α → OracleComp spec β} {p : ι → Prop} [DecidablePred p] {k : ℕ}
    (h : ∀ x, IsQueryBoundP (f x) p k) (xs : List α) :
    IsQueryBoundP (xs.mapM f) p (xs.length * k) := by
  have := isQueryBoundP_listMapM h xs
  rwa [show (xs.map fun _ => k).sum = xs.length * k by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]] at this

lemma isQueryBoundP_listFoldlM
    {f : β → α → OracleComp spec β} {p : ι → Prop} [DecidablePred p] {k : α → ℕ}
    (h : ∀ b x, IsQueryBoundP (f b x) p (k x)) (b₀ : β) (xs : List α) :
    IsQueryBoundP (xs.foldlM f b₀) p ((xs.map k).sum) := by
  induction xs generalizing b₀ with
  | nil => simp [List.foldlM_nil]
  | cons a xs ih =>
      rw [List.foldlM_cons, List.map_cons, List.sum_cons]
      refine isQueryBoundP_bind (h b₀ a) fun b' _ => ?_
      exact ih b'

lemma isPerIndexQueryBound_listMapM [DecidableEq ι]
    {f : α → OracleComp spec β} {qb : α → ι → ℕ}
    (h : ∀ x, IsPerIndexQueryBound (f x) (qb x)) (xs : List α) :
    IsPerIndexQueryBound (xs.mapM f) ((xs.map qb).sum) := by
  induction xs with
  | nil => simp [List.mapM_nil]
  | cons a xs ih =>
      rw [List.mapM_cons, List.map_cons, List.sum_cons]
      refine isPerIndexQueryBound_bind (h a) fun y => ?_
      have hrest : IsPerIndexQueryBound (xs.mapM f >>= fun ys => pure (y :: ys))
          ((xs.map qb).sum + 0) :=
        isPerIndexQueryBound_bind ih fun _ => trivial
      simpa using hrest

lemma isPerIndexQueryBound_listMapM_const [DecidableEq ι]
    {f : α → OracleComp spec β} {qb : ι → ℕ}
    (h : ∀ x, IsPerIndexQueryBound (f x) qb) (xs : List α) :
    IsPerIndexQueryBound (xs.mapM f) (xs.length • qb) := by
  have := isPerIndexQueryBound_listMapM h xs
  rwa [show (xs.map fun _ => qb).sum = xs.length • qb by
    rw [List.map_const', List.sum_replicate]] at this

lemma isPerIndexQueryBound_listFoldlM [DecidableEq ι]
    {f : β → α → OracleComp spec β} {qb : α → ι → ℕ}
    (h : ∀ b x, IsPerIndexQueryBound (f b x) (qb x)) (b₀ : β) (xs : List α) :
    IsPerIndexQueryBound (xs.foldlM f b₀) ((xs.map qb).sum) := by
  induction xs generalizing b₀ with
  | nil => simp [List.foldlM_nil]
  | cons a xs ih =>
      rw [List.foldlM_cons, List.map_cons, List.sum_cons]
      refine isPerIndexQueryBound_bind (h b₀ a) fun b' => ?_
      exact ih b'

end OracleComp
