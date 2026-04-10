/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import Examples.CommitmentScheme.Hiding.Defs

open OracleSpec OracleComp ENNReal

variable {M S C : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq C]
  [Fintype M] [Fintype S] [Fintype C]
  [Inhabited M] [Inhabited S] [Inhabited C]
omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma hidingImplCountAll_run_totalBound_current {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    IsTotalQueryBound
      ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
      (t + 1) := by
  exact (hidingOa_totalBound_current A s).simulateQ_run_of_step
    (fun ms st => hidingImplCountAll_step_totalBound ms st) (∅, fun _ => 0)

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- Run-level projection: for any fixed `s`, the shared counted implementation
projects to the `hidingImpl₁ s` execution on `hidingOa`. -/
theorem hidingRun_countAll_proj_eq_impl₁ {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    (simulateQ hidingImplCountAll (hidingOa A s)).run' (∅, fun _ => 0) =
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run' (∅, 0) := by
  simpa [StateT.run'] using
    (OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq'
      hidingImplCountAll (hidingImpl₁ s) (fun st => (st.1, st.2 s))
      (fun ms st => by
        simpa [Prod.map] using hidingImplCountAll_proj_eq_hidingImpl₁
          (M := M) (S := S) (C := C) s ms st)
      (hidingOa A s) (∅, fun _ => 0))

omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
/-- Probability bridge for bad events:
`Pr[bad]` under `hidingImpl₁ s` is equal to the corresponding event on the
shared counted run, projected at `s`. -/
theorem probEvent_hidingBad_eq_countAll {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    Pr[hidingBad ∘ Prod.snd |
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)] =
    Pr[fun z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ)) => 2 ≤ z.2.2 s |
      (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)] := by
  have hrun :
      Prod.map id (fun st : QueryCache (CMOracle M S C) × (S → ℕ) => (st.1, st.2 s)) <$>
          (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0) =
        (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0) := by
    simpa using
      (OracleComp.ProgramLogic.Relational.map_run_simulateQ_eq_of_query_map_eq'
        hidingImplCountAll (hidingImpl₁ s) (fun st => (st.1, st.2 s))
        (fun ms st => by
          simpa [Prod.map] using hidingImplCountAll_proj_eq_hidingImpl₁
            (M := M) (S := S) (C := C) s ms st)
        (hidingOa A s) (∅, fun _ => 0))
  rw [← hrun]
  rw [probEvent_map]
  rfl

omit [DecidableEq C] [Fintype M] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
/-- One-step growth bound for the shared counted hiding implementation:
the total count increases by at most one. -/
lemma sum_counts_step_le_succ_hidingImplCountAll (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    (∑ s' : S, x.2.2 s') ≤ (∑ s' : S, st.2 s') + 1 := by
  obtain ⟨cache, counts⟩ := st
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
      exact Nat.le_succ _
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      rw [hx]
      simp [sum_update_succ_count]

omit [DecidableEq C] [Fintype M] [Fintype C] [Inhabited M] in
lemma hiding_distinguish_totalBound_of_choose_count_support
    [Finite M] [Finite C]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {x : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hx : x ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    ∀ cm : C, IsTotalQueryBound (A.distinguish x.1.2 cm) (t - ∑ s : S, x.2.2 s) := by
  haveI : Fintype M := Fintype.ofFinite M
  haveI : Fintype C := Fintype.ofFinite C
  have hres :
      IsTotalQueryBound
        ((liftM (query (spec := CMOracle M S C) (x.1.1, default))) >>= fun cm =>
          A.distinguish x.1.2 cm)
        ((t + 1) - (∑ s : S, x.2.2 s)) := by
    simpa [hidingOa] using
      (IsTotalQueryBound.residual_of_mem_support_run_simulateQ_le_cost
        (spec := CMOracle M S C)
        (oa := A.choose)
        (ob := fun a =>
          (liftM (query (spec := CMOracle M S C) (a.1, default))) >>= fun cm =>
            A.distinguish a.2 cm)
        (n := t + 1)
        (impl := hidingImplCountAll)
        (cost := fun st : QueryCache (CMOracle M S C) × (S → ℕ) => ∑ s : S, st.2 s)
        (hstep := fun t st y hy =>
          sum_counts_step_le_succ_hidingImplCountAll (M := M) (S := S) (C := C) t st y hy)
        (h := A.totalBound default)
        hx)
  rw [isTotalQueryBound_query_bind_iff] at hres
  intro cm
  have hcm :
      IsTotalQueryBound (A.distinguish x.1.2 cm)
        ((((t + 1) - ∑ s : S, x.2.2 s)) - 1) := by
    simpa using hres.2 cm
  have hbudget : ((((t + 1) - ∑ s : S, x.2.2 s)) - 1) = t - ∑ s : S, x.2.2 s := by
    omega
  simpa [hbudget] using hcm

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- A single counted query can only increase a fixed salt counter. -/
lemma count_mono_step_hidingImplCountAll (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    st.2 s ≤ x.2.2 s := by
  obtain ⟨cache, counts⟩ := st
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      rw [hx]
      by_cases hs : ms.2 = s
      · subst hs
        simp [Function.update]
      · have hs' : s ≠ ms.2 := by
          intro hEq
          exact hs hEq.symm
        simp [Function.update_of_ne hs']

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- A single counted query changes any fixed salt counter by at most one. -/
lemma count_coord_le_succ_of_mem_support_step_hidingImplCountAll
    (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    st.2 s ≤ x.2.2 s ∧ x.2.2 s ≤ st.2 s + 1 := by
  obtain ⟨cache, counts⟩ := st
  have hmono :
      counts s ≤ x.2.2 s :=
    count_mono_step_hidingImplCountAll (M := M) (S := S) (C := C) s ms (cache, counts) x hx
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hmono, Nat.le_succ _⟩
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      constructor
      · exact hmono
      · by_cases hs : ms.2 = s
        · subst hs
          simp [Function.update]
        · have hs' : s ≠ ms.2 := by
            intro hEq
            exact hs hEq.symm
          simp [Function.update_of_ne hs']

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- A single counted query only changes the counter at its queried salt. -/
lemma count_coord_le_add_hit_of_mem_support_step_hidingImplCountAll
    (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    x.2.2 s ≤ st.2 s + if ms.2 = s then 1 else 0 := by
  obtain ⟨cache, counts⟩ := st
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      by_cases hs : ms.2 = s
      · subst hs
        simp
      · have hs' : s ≠ ms.2 := by
          intro hEq
          exact hs hEq.symm
        simp [hs]
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      by_cases hs : ms.2 = s
      · subst hs
        simp [Function.update]
      · have hs' : s ≠ ms.2 := by
          intro hEq
          exact hs hEq.symm
        change Function.update counts ms.2 (counts ms.2 + 1) s ≤
          counts s + if ms.2 = s then 1 else 0
        rw [Function.update_of_ne hs']
        simp [hs]

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- After the challenge step at salt `s`, removing the mandatory challenge hit leaves
at most the pre-challenge salt count. -/
lemma challenge_countPred_le_initialCount_of_mem_support_step_hidingImplCountAll
    (m : M) (s : S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    {x : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st)) :
    x.2.2 s - 1 ≤ st.2 s := by
  have hsucc :
      x.2.2 s ≤ st.2 s + 1 :=
    (count_coord_le_succ_of_mem_support_step_hidingImplCountAll
      (M := M) (S := S) (C := C) s (m, s) st x hx).2
  omega

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- Any support point of a counted step caches the queried point with the returned value. -/
lemma self_mem_cache_of_mem_support_step_hidingImplCountAll (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    x.2.1 ms = some x.1 := by
  obtain ⟨cache, counts⟩ := st
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms with
  | some u =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simp [hcache]
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      simp

/-- The counted hiding invariant: every cached salt has a positive counter. -/
def HidingCountInv (st : QueryCache (CMOracle M S C) × (S → ℕ)) : Prop :=
  ∀ ms : M × S, ∀ u : C, st.1 ms = some u → 1 ≤ st.2 ms.2

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- The counted implementation preserves the hiding count invariant. -/
lemma hidingCountInv_step_hidingImplCountAll (ms₀ : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) (hInv : HidingCountInv st)
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms₀).run st)) :
    HidingCountInv x.2 := by
  obtain ⟨cache, counts⟩ := st
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hcache : cache ms₀ with
  | some u₀ =>
      simp only [hcache, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simpa using hInv
  | none =>
      simp only [hcache, StateT.run_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u₀, _, hx⟩ := hx
      simp only [StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      intro ms u hms
      by_cases hEq : ms = ms₀
      · subst hEq
        simp
      · have hcache_ms : cache ms = some u := by
          simpa [QueryCache.cacheQuery, Function.update, hEq] using hms
        have h_old : 1 ≤ counts ms.2 := hInv ms u hcache_ms
        have h_mono : counts ms.2 ≤ Function.update counts ms₀.2 (counts ms₀.2 + 1) ms.2 := by
          by_cases hs : ms.2 = ms₀.2
          · rw [hs]
            simp [Function.update_self]
          · simp [Function.update_of_ne hs]
        exact le_trans h_old h_mono

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- Support points of `simulateQ hidingImplCountAll` have coordinatewise monotone counts. -/
lemma count_mono_of_mem_support_run_hidingImplCountAll {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ))
    (z : α × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀))
    (s : S) :
    st₀.2 s ≤ z.2.2 s := by
  suffices h : ∀ {β : Type} (ob : OracleComp (CMOracle M S C) β)
      (st : QueryCache (CMOracle M S C) × (S → ℕ))
      (y : β × (QueryCache (CMOracle M S C) × (S → ℕ))),
      y ∈ support ((simulateQ hidingImplCountAll ob).run st) →
      ∀ s' : S, st.2 s' ≤ y.2.2 s' by
    exact h oa st₀ z hz s
  intro β ob
  induction ob using OracleComp.inductionOn with
  | pure x =>
      intro st y hy s'
      simp only [simulateQ_pure] at hy
      subst y
      exact Nat.le_refl _
  | query_bind t mx ih =>
      intro st y hy s'
      rw [simulateQ_query_bind, StateT.run_bind] at hy
      rw [support_bind] at hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨qu, hqu, hy'⟩ := hy
      exact le_trans
        (count_mono_step_hidingImplCountAll (M := M) (S := S) (C := C) s' t st qu hqu)
        (ih qu.1 qu.2 y hy' s')

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- Every cached salt has a positive counter along the support of the counted run. -/
lemma hidingCountInv_of_mem_support_run_hidingImplCountAll {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ))
    (hInv : HidingCountInv st₀)
    (z : α × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    HidingCountInv z.2 := by
  suffices h : ∀ (β : Type) (ob : OracleComp (CMOracle M S C) β)
      (st : QueryCache (CMOracle M S C) × (S → ℕ)),
      HidingCountInv st →
      ∀ y : β × (QueryCache (CMOracle M S C) × (S → ℕ)),
        y ∈ support ((simulateQ hidingImplCountAll ob).run st) →
        HidingCountInv y.2 from
    h α oa st₀ hInv z hz
  intro β ob
  induction ob using OracleComp.inductionOn with
  | pure x =>
      intro st hInv y hy
      simp only [simulateQ_pure] at hy
      subst hy
      exact hInv
  | query_bind t mx ih =>
      intro st hInv y hy
      rw [simulateQ_query_bind, StateT.run_bind] at hy
      rw [support_bind] at hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨qu, hqu, hy'⟩ := hy
      have hInv' :
          HidingCountInv qu.2 :=
        hidingCountInv_step_hidingImplCountAll (M := M) (S := S) (C := C) t st hInv qu hqu
      exact ih qu.1 qu.2 hInv' y hy'

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- On the support of the counted choose run, a zero salt-count means no cache entry
at that salt can already exist. -/
lemma cache_none_of_zero_count_of_mem_support_run_hidingChoose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (m : M) (s : S)
    (hzero : qchoose.2.2 s = 0) :
    qchoose.2.1 (m, s) = none := by
  have hInv₀ : HidingCountInv ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0) := by
    intro ms u hms
    simp at hms
  have hInv :
      HidingCountInv qchoose.2 :=
    hidingCountInv_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C)
      (oa := A.choose)
      (st₀ := ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0))
      hInv₀
      (z := qchoose)
      hqchoose
  by_cases hcache : qchoose.2.1 (m, s) = none
  · exact hcache
  · cases hsome : qchoose.2.1 (m, s) with
    | none =>
        contradiction
    | some u =>
        have hpos : 1 ≤ qchoose.2.2 s :=
          hInv (m, s) u hsome
        omega

/-- For a fresh salt after the choose phase, the challenge step of
`hidingImplCountAll` is necessarily the cache-miss branch and sets that salt count to `1`. -/
abbrev HidingCountState (M : Type) (S : Type) (C : Type) :=
  QueryCache (CMOracle M S C) × (S → ℕ)

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma fresh_step_state_of_mem_support_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    (hzero : qchoose.2.2 s = 0)
    {qch : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqch : qch ∈ support
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)) :
    qch.2 =
      (qchoose.2.1.cacheQuery (qchoose.1.1, s) qch.1,
        Function.update qchoose.2.2 s 1) := by
  have hnone : qchoose.2.1 (qchoose.1.1, s) = none :=
    cache_none_of_zero_count_of_mem_support_run_hidingChoose
      (M := M) (S := S) (C := C) A hqchoose qchoose.1.1 s hzero
  simp only [hidingImplCountAll, StateT.run_bind, StateT.run_get, pure_bind, hnone] at hqch
  rw [mem_support_bind_iff] at hqch
  obtain ⟨u, _, hu⟩ := hqch
  simp only [StateT.run_set, StateT.run_pure] at hu
  rcases hu with ⟨rfl, rfl⟩
  simp [hzero]

omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
lemma wp_fresh_challenge_branch_eq
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    (hzero : qchoose.2.2 s = 0)
    (F : C × (QueryCache (CMOracle M S C) × (S → ℕ)) → ℝ≥0∞) :
    OracleComp.ProgramLogic.wp
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
      F
    =
    OracleComp.ProgramLogic.wp
      (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
        OracleComp (CMOracle M S C) C)
      (fun cm =>
        F (cm, (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
          Function.update qchoose.2.2 s 1))) := by
  have hnone : qchoose.2.1 (qchoose.1.1, s) = none :=
    cache_none_of_zero_count_of_mem_support_run_hidingChoose
      (M := M) (S := S) (C := C) A hqchoose qchoose.1.1 s hzero
  simp only [hidingImplCountAll, bind_pure_comp, StateT.run_bind, StateT.run_get,
    pure_bind, hnone, hzero, zero_add, StateT.run_monadLift, StateT.run_map,
    StateT.run_set, map_pure, Functor.map_map]
  rw [OracleComp.ProgramLogic.wp_map]
  rfl

omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
lemma wp_freshDistinguishIncrement_eq
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S) :
    OracleComp.ProgramLogic.wp
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)
      (fun qch : C × HidingCountState M S C =>
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
          (fun z : Bool × HidingCountState M S C =>
            OracleComp.ProgramLogic.propInd
              (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))) =
      OracleComp.ProgramLogic.propInd (qchoose.2.2 s = 0) *
        OracleComp.ProgramLogic.wp
          (liftM (query (spec := CMOracle M S C) (qchoose.1.1, s)) :
            OracleComp (CMOracle M S C) C)
          (fun cm =>
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run
                (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
                  Function.update qchoose.2.2 s 1))
              (fun z : Bool × HidingCountState M S C =>
                OracleComp.ProgramLogic.propInd (1 < z.2.2 s))) := by
  by_cases hzero : qchoose.2.2 s = 0
  · rw [wp_fresh_challenge_branch_eq
        (M := M) (S := S) (C := C) A hqchoose s hzero]
    simp [hzero]
  · have hpost :
        (fun qch : C × HidingCountState M S C =>
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)
            (fun z : Bool × HidingCountState M S C =>
              OracleComp.ProgramLogic.propInd
                (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))) = fun _ => 0 := by
      funext qch
      simp [hzero]
    rw [hpost, OracleComp.ProgramLogic.wp_const]
    simp [hzero]

omit [DecidableEq C] [Fintype M] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
/-- On the support of the counted hiding run, the total count is at most `n`
plus the initial total count. -/
lemma sum_counts_le_of_mem_support_run_hidingImplCountAll
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    {st₀ : QueryCache (CMOracle M S C) × (S → ℕ)}
    {z : α × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    (∑ s' : S, z.2.2 s') ≤ n + ∑ s' : S, st₀.2 s' := by
  suffices h : ∀ {β : Type} (ob : OracleComp (CMOracle M S C) β)
      (m : ℕ), IsTotalQueryBound ob m →
      ∀ (st : QueryCache (CMOracle M S C) × (S → ℕ))
        (y : β × (QueryCache (CMOracle M S C) × (S → ℕ))),
        y ∈ support ((simulateQ hidingImplCountAll ob).run st) →
        (∑ s' : S, y.2.2 s') ≤ m + ∑ s' : S, st.2 s' by
    exact h oa n hbound st₀ z hz
  intro β ob m hm st y hy
  induction ob using OracleComp.inductionOn generalizing m st y with
  | pure x =>
      simp only [simulateQ_pure] at hy
      subst y
      exact Nat.le_add_left _ _
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at hm
      rw [simulateQ_query_bind, StateT.run_bind] at hy
      rw [support_bind] at hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨qu, hqu, hy'⟩ := hy
      have hstep :
          (∑ s' : S, qu.2.2 s') ≤ (∑ s' : S, st.2 s') + 1 :=
        sum_counts_step_le_succ_hidingImplCountAll (M := M) (S := S) (C := C) t st qu hqu
      have hrest :
          (∑ s' : S, y.2.2 s') ≤ (m - 1) + ∑ s' : S, qu.2.2 s' :=
        (ih (u := qu.1) (m := m - 1) (hm.2 qu.1)) (st := qu.2) (y := y) hy'
      omega

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma cache_le_of_mem_support_run_hidingImplCountAll
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {st₀ : HidingCountState M S C}
    {z : α × HidingCountState M S C}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    st₀.1 ≤ z.2.1 := by
  have hz' :
      (z.1, z.2.1) ∈ support ((simulateQ cachingOracle oa).run st₀.1) := by
    have hzmap :
        (z.1, z.2.1) ∈ support
          (Prod.map id Prod.fst <$> (simulateQ hidingImplCountAll oa).run st₀) := by
      rw [support_map]
      exact ⟨z, hz, by simp [Prod.map]⟩
    simpa [run_hidingImplCountAll_proj_eq_cachingOracle
      (M := M) (S := S) (C := C) oa st₀] using hzmap
  exact simulateQ_cachingOracle_cache_le (spec := CMOracle M S C) oa st₀.1 (z.1, z.2.1) hz'

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma exists_new_salt_cacheEntry_of_count_gt_one
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    (m0 : M) (s : S)
    {cache₀ : QueryCache (CMOracle M S C)} {counts₀ : S → ℕ}
    (hcount : counts₀ s = 1)
    (hself : ∃ v : C, cache₀ (m0, s) = some v)
    (hunique : ∀ m : M, m ≠ m0 → cache₀ (m, s) = none)
    {z : α × HidingCountState M S C}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run (cache₀, counts₀)))
    (hgt : 1 < z.2.2 s) :
    ∃ m : M, ∃ v : C, m ≠ m0 ∧ z.2.1 (m, s) = some v := by
  induction oa using OracleComp.inductionOn generalizing cache₀ counts₀ z with
  | pure x =>
      simp only [simulateQ_pure] at hz
      subst z
      exfalso
      simp [hcount] at hgt
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz'⟩ := hz
      cases hcache : cache₀ t with
      | some u =>
          have hqu_eq : qu = (u, (cache₀, counts₀)) := by
            simpa [hidingImplCountAll, hcache, StateT.run_bind, StateT.run_get, pure_bind] using hqu
          subst qu
          exact ih (u := u) (cache₀ := cache₀) (counts₀ := counts₀) (z := z)
            hcount hself hunique hz' hgt
      | none =>
          have hqu_eq :
              ∃ u : C,
                (u,
                  (cache₀.cacheQuery t u,
                    Function.update counts₀ t.2 (counts₀ t.2 + 1))) = qu := by
            simpa [hidingImplCountAll, hcache, StateT.run_bind, StateT.run_get, pure_bind]
              using hqu
          obtain ⟨u, rfl⟩ := hqu_eq
          by_cases hs : t.2 = s
          · have htne : t.1 ≠ m0 := by
              intro hEq
              subst hEq
              rcases hself with ⟨v0, hv0⟩
              have ht_some : cache₀ t = some v0 := by
                change cache₀ (t.1, t.2) = some v0
                rw [hs]
                exact hv0
              have : some v0 = none := ht_some.symm.trans hcache
              cases this
            have hentry : (cache₀.cacheQuery t u) (t.1, s) = some u := by
              subst s
              simp
            have hmono :
                cache₀.cacheQuery t u ≤ z.2.1 :=
              cache_le_of_mem_support_run_hidingImplCountAll
                (M := M) (S := S) (C := C) (oa := mx u)
                (st₀ := (cache₀.cacheQuery t u, Function.update counts₀ t.2 (counts₀ t.2 + 1)))
                (z := z) hz'
            refine ⟨t.1, u, htne, ?_⟩
            exact hmono hentry
          · have hcount' :
                (Function.update counts₀ t.2 (counts₀ t.2 + 1)) s = 1 := by
              by_cases hst : s = t.2
              · exact False.elim (hs hst.symm)
              · simp [Function.update, hst, hcount]
            have hself' : ∃ v : C, (cache₀.cacheQuery t u) (m0, s) = some v := by
              rcases hself with ⟨v0, hv0⟩
              refine ⟨v0, ?_⟩
              have hne : (m0, s) ≠ t := by
                intro hEq
                exact hs (by simpa using congrArg Prod.snd hEq.symm)
              simpa [QueryCache.cacheQuery_of_ne cache₀ u hne] using hv0
            have hunique' : ∀ m : M, m ≠ m0 → (cache₀.cacheQuery t u) (m, s) = none := by
              intro m hm
              have hne : (m, s) ≠ t := by
                intro hEq
                exact hs (by simpa using congrArg Prod.snd hEq.symm)
              simpa [QueryCache.cacheQuery_of_ne cache₀ u hne] using hunique m hm
            exact ih (u := u) (cache₀ := cache₀.cacheQuery t u)
              (counts₀ := Function.update counts₀ t.2 (counts₀ t.2 + 1)) (z := z)
              hcount' hself' hunique' hz' hgt

omit [DecidableEq C] [Fintype M] [Fintype C] [Inhabited M] in
/-- Along the counted choose run, the total per-salt miss count is bounded by the
adversary query budget `t`. -/
lemma sum_counts_le_queryBound_of_mem_support_run_hidingChoose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S, qchoose.2.2 s) ≤ t := by
  simpa using
    (sum_counts_le_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C)
      (oa := A.choose)
      (hbound := hiding_choose_totalBound (M := M) (S := S) (C := C) A)
      (st₀ := ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0))
      (z := qchoose)
      hqchoose)

omit [DecidableEq C] [Fintype M] [Inhabited M] in
lemma wp_choose_sumCounts_le_queryBound
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
      (fun qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
        (∑ s : S, qchoose.2.2 s : ℝ≥0∞)) ≤ t := by
  rw [OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' qchoose,
        Pr[= qchoose | (simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)] *
          (∑ s : S, qchoose.2.2 s : ℝ≥0∞)
      ≤
        ∑' qchoose,
          Pr[= qchoose | (simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)] * t := by
            refine ENNReal.tsum_le_tsum fun qchoose => ?_
            by_cases hqchoose :
                qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))
            · exact mul_le_mul'
                le_rfl
                (by
                  exact_mod_cast
                    (sum_counts_le_queryBound_of_mem_support_run_hidingChoose
                      (M := M) (S := S) (C := C) A hqchoose))
            · rw [probOutput_eq_zero_of_not_mem_support hqchoose]
              simp
    _ = t := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

omit [DecidableEq C] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
/-- Every support point of `simulateQ hidingImplCountAll` is dominated by some
`countingOracle.simulate` support point: the total count across all salts is
bounded by the initial counts plus the counting oracle's total query cost. -/
lemma exists_counting_support_of_mem_support_run_hidingImplCountAll
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {st₀ : QueryCache (CMOracle M S C) × (S → ℕ)}
    {z : α × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    ∃ qc : QueryCount (M × S),
      (z.1, qc) ∈ support (countingOracle.simulate oa 0) ∧
      (∑ s : S, z.2.2 s) ≤ (∑ s : S, st₀.2 s) + ∑ ms : M × S, qc ms := by
  classical
  induction oa using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure] at hz
      subst z
      refine ⟨0, ?_, ?_⟩
      · simpa using
          (countingOracle.mem_support_simulate_pure_iff
            (x := x) (qc := (0 : QueryCount (M × S))) (z := (x, 0))).2 rfl
      · simp
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz'⟩ := hz
      rcases ih qu.1 (st₀ := qu.2) (z := z) hz' with ⟨qcRest, hqcRest, hsumRest⟩
      have hstep :
          (∑ s : S, qu.2.2 s) ≤ (∑ s : S, st₀.2 s) + 1 :=
        sum_counts_step_le_succ_hidingImplCountAll
          (M := M) (S := S) (C := C) t st₀ qu hqu
      let qc : QueryCount (M × S) := Function.update qcRest t (qcRest t + 1)
      have hpred : Function.update qc t (qc t - 1) = qcRest := by
        funext j
        by_cases hj : j = t
        · subst hj
          simp [qc]
        · simp [qc, Function.update, hj]
      have hqc :
          (z.1, qc) ∈ support
            (countingOracle.simulate
              (((liftM (query (spec := CMOracle M S C) t)) : OracleComp (CMOracle M S C) _) >>=
                mx) 0) := by
        rw [countingOracle.mem_support_simulate_queryBind_iff]
        refine ⟨by simp [qc], qu.1, ?_⟩
        simpa [hpred] using hqcRest
      have hqcsum : (∑ ms : M × S, qc ms) = (∑ ms : M × S, qcRest ms) + 1 := by
        simpa [qc] using sum_update_succ_count (counts := qcRest) t
      refine ⟨qc, hqc, ?_⟩
      omega

omit [DecidableEq C] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
/-- Per-coordinate variant of `exists_counting_support_of_mem_support_run_hidingImplCountAll`:
for each salt `t`, the per-salt count `z.2.2 t` is bounded by the initial count
plus the counting oracle's per-index query count at `t`. -/
lemma exists_counting_support_of_mem_support_run_hidingImplCountAll_coord
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {st₀ : QueryCache (CMOracle M S C) × (S → ℕ)}
    {z : α × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    ∃ qc : QueryCount (M × S),
      (z.1, qc) ∈ support (countingOracle.simulate oa 0) ∧
      ∀ s : S, z.2.2 s ≤ st₀.2 s + ∑ m : M, qc (m, s) := by
  classical
  induction oa using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure] at hz
      subst z
      refine ⟨0, ?_, ?_⟩
      · simpa using
          (countingOracle.mem_support_simulate_pure_iff
            (x := x) (qc := (0 : QueryCount (M × S))) (z := (x, 0))).2 rfl
      · intro s
        simp
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz'⟩ := hz
      rcases ih qu.1 (st₀ := qu.2) (z := z) hz' with ⟨qcRest, hqcRest, hcoordRest⟩
      let qc : QueryCount (M × S) := Function.update qcRest t (qcRest t + 1)
      have hpred : Function.update qc t (qc t - 1) = qcRest := by
        funext j
        by_cases hj : j = t
        · subst hj
          simp [qc]
        · simp [qc, Function.update, hj]
      have hqc :
          (z.1, qc) ∈ support
            (countingOracle.simulate
              (((liftM (query (spec := CMOracle M S C) t)) : OracleComp (CMOracle M S C) _) >>=
                mx) 0) := by
        rw [countingOracle.mem_support_simulate_queryBind_iff]
        refine ⟨by simp [qc], qu.1, ?_⟩
        simpa [hpred] using hqcRest
      refine ⟨qc, hqc, ?_⟩
      intro s
      have hstep :
          qu.2.2 s ≤ st₀.2 s + if t.2 = s then 1 else 0 :=
        count_coord_le_add_hit_of_mem_support_step_hidingImplCountAll
          (M := M) (S := S) (C := C) s t st₀ qu hqu
      have hrest :
          z.2.2 s ≤ qu.2.2 s + ∑ m : M, qcRest (m, s) :=
        hcoordRest s
      by_cases hs : t.2 = s
      · subst hs
        have hcoord :
            (fun m : M => qc (m, t.2)) =
              Function.update (fun m : M => qcRest (m, t.2)) t.1 (qcRest t + 1) := by
          funext m
          by_cases hm : m = t.1
          · subst hm
            simp [qc]
          · have hne : (m, t.2) ≠ t := by
              intro hEq
              exact hm (by simpa using congrArg Prod.fst hEq)
            simp [qc, Function.update_of_ne hne, hm]
        have hsum :
            (∑ m : M, qc (m, t.2)) = (∑ m : M, qcRest (m, t.2)) + 1 := by
          rw [hcoord]
          simpa using
            sum_update_succ_count (counts := fun m : M => qcRest (m, t.2)) t.1
        have hstep' :
            qu.2.2 t.2 + ∑ m : M, qcRest (m, t.2) ≤
              st₀.2 t.2 + ∑ m : M, qc (m, t.2) := by
          rw [hsum]
          have := add_le_add_right hstep (∑ m : M, qcRest (m, t.2))
          simpa [add_assoc, add_left_comm, add_comm] using this
        exact le_trans hrest hstep'
      · have hsum :
            (∑ m : M, qc (m, s)) = ∑ m : M, qcRest (m, s) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          have hne : (m, s) ≠ t := by
            intro hEq
            exact hs (by simpa using congrArg Prod.snd hEq.symm)
          rw [show qc (m, s) = qcRest (m, s) by
            simp [qc, Function.update_of_ne hne]]
        have hstep' :
            qu.2.2 s + ∑ m : M, qcRest (m, s) ≤
              st₀.2 s + ∑ m : M, qc (m, s) := by
          rw [hsum]
          have := add_le_add_right hstep (∑ m : M, qcRest (m, s))
          simpa [hs, add_assoc, add_left_comm, add_comm] using this
        exact le_trans hrest hstep'

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- On the support of the counted hiding run, the challenge salt count is positive. -/
theorem challenge_count_pos_of_mem_support_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    1 ≤ z.2.2 s := by
  have hInv0 : HidingCountInv (M := M) (S := S) (C := C)
      ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0) := by
    intro ms u h
    simp at h
  rw [hidingOa, simulateQ_bind, StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨qchoose, hchoose, hz⟩ := hz
  rcases qchoose with ⟨⟨m, aux⟩, st₁⟩
  have hInv₁ : HidingCountInv st₁ :=
    hidingCountInv_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C) (oa := A.choose)
      (st₀ := ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0))
      (hInv := hInv0) (z := ((m, aux), st₁)) hchoose
  rw [simulateQ_query_bind, StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨qch, hch, hz'⟩ := hz
  have hInv₂ : HidingCountInv qch.2 :=
    hidingCountInv_step_hidingImplCountAll
      (M := M) (S := S) (C := C) (m, s) st₁ hInv₁ qch hch
  have hcache₂ : qch.2.1 (m, s) = some qch.1 :=
    self_mem_cache_of_mem_support_step_hidingImplCountAll
      (M := M) (S := S) (C := C) (m, s) st₁ qch hch
  have hqch_pos : 1 ≤ qch.2.2 s :=
    hInv₂ (m, s) qch.1 hcache₂
  exact le_trans hqch_pos
    (count_mono_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C) (oa := A.distinguish aux qch.1)
      (st₀ := qch.2) (z := z) hz' s)

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- On support of the counted hiding run, the bad-event indicator at the challenge salt
is bounded by the excess of that salt count over the mandatory challenge hit. -/
lemma bad_indicator_le_count_pred_of_mem_support_run_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    (if 2 ≤ z.2.2 s then (1 : ℝ≥0∞) else 0) ≤ z.2.2 s - 1 := by
  have hpos : 1 ≤ z.2.2 s :=
    challenge_count_pos_of_mem_support_hidingImplCountAll
      (M := M) (S := S) (C := C) A s hz
  by_cases hbad : 2 ≤ z.2.2 s
  · have hcount : (1 : ℕ) ≤ z.2.2 s - 1 := by omega
    simp only [ge_iff_le, hbad, ↓reduceIte]
    exact_mod_cast hcount
  · simp [hbad]

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- On support of the counted hiding run, bad at salt `s` can only happen if the
choose phase already queried salt `s`, or if the distinguish phase later
increased the salt-`s` counter after the challenge step. -/
lemma bad_indicator_le_chooseHitIndicator_add_distinguishIncrementIndicator
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (_hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    {qch : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqch : qch ∈ support
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2))
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)) :
    OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s) ≤
      OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.propInd (qch.2.2 s < z.2.2 s) := by
  by_cases hbad : 2 ≤ z.2.2 s
  · by_cases hchoose : 0 < qchoose.2.2 s
    · simp [OracleComp.ProgramLogic.propInd, hbad, hchoose]
    · have hqzero : qchoose.2.2 s = 0 := Nat.eq_zero_of_not_pos hchoose
      have hmono :
          qch.2.2 s ≤ z.2.2 s :=
        count_mono_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C)
          (oa := A.distinguish qchoose.1.2 qch.1)
          (st₀ := qch.2) (z := z) hz s
      have hstep :
          qch.2.2 s ≤ qchoose.2.2 s + 1 :=
        (count_coord_le_succ_of_mem_support_step_hidingImplCountAll
          (M := M) (S := S) (C := C) s (qchoose.1.1, s) qchoose.2 qch hqch).2
      have hinc : qch.2.2 s < z.2.2 s := by
        by_contra hnot
        have hzle : z.2.2 s ≤ qch.2.2 s := Nat.le_of_not_gt hnot
        have hEq : z.2.2 s = qch.2.2 s := le_antisymm hzle hmono
        have hzle1 : z.2.2 s ≤ 1 := by
          rw [hEq]
          simpa [hqzero] using hstep
        omega
      simp [OracleComp.ProgramLogic.propInd, hbad, hchoose, hinc]
  · simp [OracleComp.ProgramLogic.propInd, hbad]

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- Strengthened version of
`bad_indicator_le_chooseHitIndicator_add_distinguishIncrementIndicator`:
the distinguish-increment term is only charged on salts that were fresh after
the choose phase. -/
lemma bad_indicator_le_chooseHitIndicator_add_freshDistinguishIncrementIndicator
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (_hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    {qch : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqch : qch ∈ support
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2))
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)) :
    OracleComp.ProgramLogic.propInd (2 ≤ z.2.2 s) ≤
      OracleComp.ProgramLogic.propInd (0 < qchoose.2.2 s) +
        OracleComp.ProgramLogic.propInd
          (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s) := by
  by_cases hbad : 2 ≤ z.2.2 s
  · by_cases hchoose : 0 < qchoose.2.2 s
    · simp [OracleComp.ProgramLogic.propInd, hbad, hchoose]
    · have hqzero : qchoose.2.2 s = 0 := Nat.eq_zero_of_not_pos hchoose
      have hmono :
          qch.2.2 s ≤ z.2.2 s :=
        count_mono_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C)
          (oa := A.distinguish qchoose.1.2 qch.1)
          (st₀ := qch.2) (z := z) hz s
      have hstep :
          qch.2.2 s ≤ qchoose.2.2 s + 1 :=
        (count_coord_le_succ_of_mem_support_step_hidingImplCountAll
          (M := M) (S := S) (C := C) s (qchoose.1.1, s) qchoose.2 qch hqch).2
      have hinc : qch.2.2 s < z.2.2 s := by
        by_contra hnot
        have hzle : z.2.2 s ≤ qch.2.2 s := Nat.le_of_not_gt hnot
        have hEq : z.2.2 s = qch.2.2 s := le_antisymm hzle hmono
        have hzle1 : z.2.2 s ≤ 1 := by
          rw [hEq]
          simpa [hqzero] using hstep
        omega
      simp [OracleComp.ProgramLogic.propInd, hbad, hqzero, hinc]
  · simp [OracleComp.ProgramLogic.propInd, hbad]

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- On support of the counted hiding run, the challenge-salt excess count is bounded
by the adversary's total query budget. -/
lemma count_pred_le_queryBound_of_mem_support_run_hidingImplCountAll
    [Finite S]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    z.2.2 s - 1 ≤ t := by
  haveI : Fintype S := Fintype.ofFinite S
  have hsum :
      (∑ s' : S, z.2.2 s') ≤ t + 1 :=
    by
      simpa using
        (sum_counts_le_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C)
          (oa := hidingOa A s)
          (hbound := hidingOa_totalBound_current (M := M) (S := S) (C := C) A s)
          (st₀ := (∅, fun _ => 0)) (z := z) hz)
  have hs_le : z.2.2 s ≤ ∑ s' : S, z.2.2 s' := by
    classical
    simpa using Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  omega

/- Combined pointwise bound used when converting the bad event to an indicator
expectation over counted support points. -/
omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma bad_indicator_le_queryBound_of_mem_support_run_hidingImplCountAll
    [Finite S]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    (if 2 ≤ z.2.2 s then (1 : ℝ≥0∞) else 0) ≤ t := by
  haveI : Fintype S := Fintype.ofFinite S
  exact le_trans
    (bad_indicator_le_count_pred_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C) A s hz)
    (by
      exact_mod_cast
        (count_pred_le_queryBound_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C) A s hz))

omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
/-- Fixed-salt bridge from the counted bad event to the expected excess count. -/
lemma probEvent_countAll_bad_le_wp_countPred
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    Pr[fun z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ)) => 2 ≤ z.2.2 s |
      (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)] ≤
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
      (fun z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞)) := by
  rw [OracleComp.ProgramLogic.probEvent_eq_wp_propInd,
    OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
  · simp only [OracleComp.ProgramLogic.propInd_eq_ite]
    exact mul_le_mul'
      le_rfl
      (bad_indicator_le_count_pred_of_mem_support_run_hidingImplCountAll
        (M := M) (S := S) (C := C) A s hz)
  · rw [probOutput_eq_zero_of_not_mem_support hz]
    simp [OracleComp.ProgramLogic.propInd_eq_ite]

/- Fixed-salt expectation bound for the counted excess at the challenge salt. -/
omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
lemma wp_countPred_le_queryBound_of_run_hidingImplCountAll
    [Finite S]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
      (fun z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
        (z.2.2 s - 1 : ℝ≥0∞)) ≤ t := by
  haveI : Fintype S := Fintype.ofFinite S
  rw [OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' z, Pr[= z | (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)] *
        (z.2.2 s - 1 : ℝ≥0∞)
      ≤
        ∑' z,
          Pr[= z | (simulateQ hidingImplCountAll (hidingOa A s)).run
            (∅, fun _ => 0)] * t := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz :
              z ∈ support ((simulateQ hidingImplCountAll
                (hidingOa A s)).run (∅, fun _ => 0))
          · exact mul_le_mul'
              le_rfl
              (by
                exact_mod_cast
                  (count_pred_le_queryBound_of_mem_support_run_hidingImplCountAll
                    (M := M) (S := S) (C := C) A s hz))
          · rw [probOutput_eq_zero_of_not_mem_support hz]
            simp
    _ = t := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

omit [DecidableEq C] [Fintype M] [Inhabited M] [Inhabited S] in
/-- For a fixed computation under the shared counted implementation, the sum of
expected per-salt count increments is bounded by the total query bound. -/
lemma sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ)) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
          (z.2.2 s - st₀.2 s : ℝ≥0∞))) ≤ n := by
  classical
  let run := ((simulateQ hidingImplCountAll oa).run st₀)
  have hsum :
      (∑ s : S,
        OracleComp.ProgramLogic.wp run
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
            (z.2.2 s - st₀.2 s : ℝ≥0∞))) =
      OracleComp.ProgramLogic.wp run
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
          ∑ s : S, (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
    have hsumFin :
        ∀ ss : Finset S,
          (ss.sum fun s =>
            OracleComp.ProgramLogic.wp run
              (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
                (z.2.2 s - st₀.2 s : ℝ≥0∞))) =
          OracleComp.ProgramLogic.wp run
            (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
              ss.sum fun s => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
      intro ss
      refine Finset.induction_on ss ?_ ?_
      · simp [OracleComp.ProgramLogic.wp_const]
      · intro s ss hs ih
        simp [hs, ih, OracleComp.ProgramLogic.wp_add]
    simpa [run] using hsumFin Finset.univ
  rw [hsum, OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' z, Pr[= z | run] * (∑ s : S, (z.2.2 s - st₀.2 s : ℝ≥0∞))
      ≤ ∑' z, Pr[= z | run] * (n : ℝ≥0∞) := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : z ∈ support run
          · have hmono :
                ∀ s : S, st₀.2 s ≤ z.2.2 s :=
              fun s =>
                count_mono_of_mem_support_run_hidingImplCountAll
                  (M := M) (S := S) (C := C) (oa := oa) (st₀ := st₀) (z := z) hz s
            have hsum_counts :
                (∑ s : S, z.2.2 s) ≤ n + ∑ s : S, st₀.2 s :=
              sum_counts_le_of_mem_support_run_hidingImplCountAll
                (M := M) (S := S) (C := C) (oa := oa) hbound (st₀ := st₀) (z := z) hz
            have hdecomp :
                (∑ s : S, (z.2.2 s - st₀.2 s)) + ∑ s : S, st₀.2 s =
                  ∑ s : S, z.2.2 s := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro s hs
              exact Nat.sub_add_cancel (hmono s)
            have hdiff :
                (∑ s : S, (z.2.2 s - st₀.2 s)) ≤ n := by
              omega
            exact mul_le_mul'
              le_rfl
              (by
                exact_mod_cast hdiff)
          · rw [probOutput_eq_zero_of_not_mem_support hz]
            simp
    _ = (n : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

omit [DecidableEq C] [Fintype M] [Inhabited M] [Inhabited S] in
/-- For a fixed computation under the shared counted implementation, the sum of
expected indicators of whether each salt counter ever increases is bounded by the
total query bound. -/
lemma sum_wp_countIncrementIndicators_le_queryBound_of_run_hidingImplCountAll
    [Finite M]
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ)) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
          OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s))) ≤ n := by
  haveI : Fintype M := Fintype.ofFinite M
  classical
  let run := ((simulateQ hidingImplCountAll oa).run st₀)
  have hsum :
      (∑ s : S,
        OracleComp.ProgramLogic.wp run
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
            OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s))) =
      OracleComp.ProgramLogic.wp run
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
          ∑ s : S, OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s)) := by
    have hsumFin :
        ∀ ss : Finset S,
          (ss.sum fun s =>
            OracleComp.ProgramLogic.wp run
              (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
                OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s))) =
          OracleComp.ProgramLogic.wp run
            (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
              ss.sum fun s => OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s)) := by
      intro ss
      refine Finset.induction_on ss ?_ ?_
      · simp [OracleComp.ProgramLogic.wp_const]
      · intro s ss hs ih
        simp [hs, ih, OracleComp.ProgramLogic.wp_add]
    simpa [run] using hsumFin Finset.univ
  rw [hsum, OracleComp.ProgramLogic.wp_eq_tsum]
  calc
    ∑' z, Pr[= z | run] *
        (∑ s : S, OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s))
      ≤
        ∑' z, Pr[= z | run] * (n : ℝ≥0∞) := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : z ∈ support run
          · rcases
                exists_counting_support_of_mem_support_run_hidingImplCountAll_coord
                  (M := M) (S := S) (C := C)
                  (oa := oa) (st₀ := st₀) (z := z) hz with
              ⟨qc, hqc, hcoord⟩
            have hcoordSum :
                (∑ s : S, OracleComp.ProgramLogic.propInd (st₀.2 s < z.2.2 s) : ℝ≥0∞) ≤
                  (∑ s : S, ∑ m : M, qc (m, s) : ℝ≥0∞) := by
              refine Finset.sum_le_sum ?_
              intro s hs
              by_cases hslt : st₀.2 s < z.2.2 s
              · have hsle : z.2.2 s ≤ st₀.2 s + ∑ m : M, qc (m, s) := hcoord s
                have hnat : 1 ≤ ∑ m : M, qc (m, s) := by
                  omega
                simp only [OracleComp.ProgramLogic.propInd, hslt, ↓reduceIte, ge_iff_le]
                exact_mod_cast hnat
              · simp [OracleComp.ProgramLogic.propInd, hslt]
            have htotal :
                (∑ ms : M × S, qc ms) ≤ n := by
              exact IsTotalQueryBound.counting_total_le
                (spec := CMOracle M S C)
                (ι := M × S)
                (oa := oa)
                (n := n)
                (h := hbound)
                hqc
            have hswap :
                (∑ s : S, ∑ m : M, qc (m, s)) = ∑ ms : M × S, qc ms := by
              calc
                (∑ s : S, ∑ m : M, qc (m, s)) = ∑ m : M, ∑ s : S, qc (m, s) := by
                  simpa using (Finset.sum_comm : (∑ s : S, ∑ m : M, qc (m, s)) =
                    ∑ m : M, ∑ s : S, qc (m, s))
                _ = ∑ ms : M × S, qc ms := by
                  symm
                  simp [Fintype.sum_prod_type]
            have hswap' :
                (∑ s : S, ∑ m : M, qc (m, s) : ℝ≥0∞) =
                  ∑ ms : M × S, qc ms := by
              exact_mod_cast hswap
            have htotal' : (∑ ms : M × S, qc ms : ℝ≥0∞) ≤ n := by
              exact_mod_cast htotal
            exact mul_le_mul'
              le_rfl
              (le_trans hcoordSum (by simpa [hswap'] using htotal'))
          · rw [probOutput_eq_zero_of_not_mem_support hz]
            simp
    _ = (n : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]

omit [DecidableEq C] [Fintype M] [Fintype S] [Inhabited M] [Inhabited S] in
/-- A selected final count decomposes into the initial selected count plus the
new increments made during the run. -/
lemma wp_countPred_le_initialPred_add_wp_countIncrement
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ))
    (s : S) :
    OracleComp.ProgramLogic.wp
      ((simulateQ hidingImplCountAll oa).run st₀)
      (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞)) ≤
    (st₀.2 s - 1 : ℝ≥0∞) +
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
  let run := ((simulateQ hidingImplCountAll oa).run st₀)
  calc
    OracleComp.ProgramLogic.wp run
      (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞))
      ≤
        OracleComp.ProgramLogic.wp run
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
            ((st₀.2 s - 1 : ℝ≥0∞) + (z.2.2 s - st₀.2 s : ℝ≥0∞))) := by
              rw [OracleComp.ProgramLogic.wp_eq_tsum, OracleComp.ProgramLogic.wp_eq_tsum]
              refine ENNReal.tsum_le_tsum fun z => ?_
              by_cases hz : z ∈ support run
              · have hmono :
                    st₀.2 s ≤ z.2.2 s :=
                  count_mono_of_mem_support_run_hidingImplCountAll
                    (M := M) (S := S) (C := C) (oa := oa) (st₀ := st₀) (z := z) hz s
                have hnat :
                    z.2.2 s - 1 ≤ (st₀.2 s - 1) + (z.2.2 s - st₀.2 s) := by
                  omega
                exact mul_le_mul'
                  le_rfl
                  (by exact_mod_cast hnat)
              · rw [probOutput_eq_zero_of_not_mem_support hz]
                simp
    _ =
      (st₀.2 s - 1 : ℝ≥0∞) +
        OracleComp.ProgramLogic.wp run
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
            rw [OracleComp.ProgramLogic.wp_add, OracleComp.ProgramLogic.wp_const]

omit [DecidableEq C] [Fintype M] [Inhabited M] [Inhabited S] in
lemma sum_wp_countPred_le_sum_initialPred_add_sum_wp_countIncrements
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ)) :
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞))) ≤
    (∑ s : S, (st₀.2 s - 1 : ℝ≥0∞)) +
      ∑ s : S,
        OracleComp.ProgramLogic.wp
          ((simulateQ hidingImplCountAll oa).run st₀)
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
  calc
    (∑ s : S,
      OracleComp.ProgramLogic.wp
        ((simulateQ hidingImplCountAll oa).run st₀)
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞)))
      ≤
        ∑ s : S,
          ((st₀.2 s - 1 : ℝ≥0∞) +
            OracleComp.ProgramLogic.wp
              ((simulateQ hidingImplCountAll oa).run st₀)
              (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
                (z.2.2 s - st₀.2 s : ℝ≥0∞))) := by
                refine Finset.sum_le_sum ?_
                intro s hs
                exact wp_countPred_le_initialPred_add_wp_countIncrement
                  (M := M) (S := S) (C := C) oa st₀ s
    _ =
      (∑ s : S, (st₀.2 s - 1 : ℝ≥0∞)) +
        ∑ s : S,
          OracleComp.ProgramLogic.wp
            ((simulateQ hidingImplCountAll oa).run st₀)
            (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
              (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
              rw [Finset.sum_add_distrib]

/-- The simulated hiding game, parametrized by salt `s`.

The adversary runs `hidingOa A s` (which includes the challenge query `(m, s)`)
through `hidingImplSim`, which redirects ALL salt-`s` cache misses to
`(default, default)`. This makes the challenge commitment independent of `m`:
the challenge `query (m, s)` is redirected → returns fresh uniform, independent
of `m`. The salt counter is discarded by `run'`.

Using `hidingImplSim` allows direct application of the distributional
identical-until-bad lemma (`tvDist_simulateQ_le_probEvent_bad_dist`) to bound
the distance between `hidingReal` and `hidingSim`. -/
def hidingSim {AUX : Type} {t : ℕ} (A : HidingAdversary M S C AUX t) (s : S) :
    OracleComp (CMOracle M S C) Bool :=
  (simulateQ (hidingImplSim s) (hidingOa A s)).run' (∅, 0)

abbrev HidingAvgSpec (M : Type) (S : Type) (C : Type) :=
  (Unit →ₒ S) + CMOracle M S C

abbrev hidingAvgLeftImpl :
    QueryImpl (Unit →ₒ S)
      (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C))) :=
  (QueryImpl.ofLift (Unit →ₒ S) (OracleComp (HidingAvgSpec M S C))).liftTarget
    (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C)))

abbrev hidingAvgRightImpl :
    QueryImpl (CMOracle M S C)
      (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C))) :=
  fun t =>
    StateT.mk fun st =>
      OracleComp.liftComp
        ((hidingImplCountAll (M := M) (S := S) (C := C) t).run st)
        (HidingAvgSpec M S C)

