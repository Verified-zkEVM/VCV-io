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
/-! ## 3. Hiding

**Textbook (Lemma cm-hiding)**: There exists a simulator S such that for every
`t`-query adversary A, the following two distributions are `t / |S|`-close:
  Real: A^H(state, H(m, s))  where (m, state) ← A^H, s ← S
  Sim:  A^H(state, S^H)      where (m, state) ← A^H, S^H outputs uniform C

The simulator simply outputs a random element of C.

The proof uses identical-until-bad with a counter-based bad predicate.
The state tracks `(cache, saltCount)` where `saltCount` counts how many
queries with salt `s` have been processed (including the challenge query).
Bad is defined as `saltCount ≥ 2`, meaning at least one ADVERSARY query
had salt `s` in addition to the challenge commitment query.

Since the challenge query always increments `saltCount` by 1, we have:
- `saltCount = 0`: no salt-s queries yet (before challenge, no adversary salt-s)
- `saltCount = 1`: only the challenge query had salt s (no adversary salt-s)
- `saltCount ≥ 2`: at least one adversary query had salt s

When `¬bad` (`saltCount < 2`), both implementations agree on every query,
because the redirect condition in impl₂ requires `saltCount ≥ 2`.

**Note on the `Pr[bad]` bound**: `Pr[bad]` = `Pr[saltCount ≥ 2 at end]`
= `Pr[∃ adversary query with salt = s]` ≤ `t / |S|`. -/

/-- A hiding adversary with two phases and total adversary query budget `t`.

The computation includes one additional challenge query between the phases, so
the full two-phase game computation has total bound `t + 1`. -/
structure HidingAdversary (M : Type) (S : Type) (C : Type) (AUX : Type) (t : ℕ)
    [DecidableEq M] [DecidableEq S] where
  /-- Phase 1: choose a message and auxiliary state (with oracle access). -/
  choose : OracleComp (CMOracle M S C) (M × AUX)
  /-- Phase 2: given auxiliary state and a commitment, output a guess bit. -/
  distinguish : AUX → C → OracleComp (CMOracle M S C) Bool
  /-- Total query bound for the full two-phase game computation, including the
  single challenge query between the phases. Equivalently, the adversary itself
  makes at most `t` oracle queries across both phases. -/
  totalBound : ∀ s : S, IsTotalQueryBound
    (choose >>= fun x =>
      let (m, aux) := x
      (liftM (query (spec := CMOracle M S C) (m, s)) >>= fun cm =>
        distinguish aux cm))
    (t + 1)

/-- The real hiding game, parametrized by salt `s`.

The adversary chooses `m`, then receives commitment `cm = H(m, s)` computed
using the same caching oracle. -/
def hidingReal {AUX : Type} {t : ℕ} (A : HidingAdversary M S C AUX t) (s : S) :
    OracleComp (CMOracle M S C) Bool :=
  (simulateQ cachingOracle (do
    let (m, aux) ← A.choose
    let cm ← query (spec := CMOracle M S C) (m, s)
    A.distinguish aux cm)).run' ∅

/-! ### Identical-until-bad infrastructure for hiding

State: `QueryCache (CMOracle M S C) × ℕ` — cache plus a counter of how many
queries with salt `s` have been processed.

Bad: `saltCount ≥ 2` — at least two salt-`s` queries have occurred. Since the
challenge query `(m, s)` always contributes one, bad means at least one
ADVERSARY query also had salt `s`.

**`hidingImpl₁`** (real): standard caching + increments counter on salt `s`.
**`hidingImpl₂`** (intermediate): same as `hidingImpl₁` EXCEPT when
`saltCount ≥ 2` and cache miss with salt `s`, queries at `(default, default)`.

When `¬bad` (`saltCount < 2`): both implementations are literally identical
(the redirect condition `saltCount ≥ 2 && salt = s` is `false`).
-/

/-- The "bad" predicate: at least 2 salt-`s` queries have occurred (the challenge
counts as 1, so bad means at least one adversary query also had salt `s`). -/
def hidingBad : QueryCache (CMOracle M S C) × ℕ → Prop := fun p => p.2 ≥ 2

instance : DecidablePred (hidingBad (M := M) (S := S) (C := C)) :=
  fun p => Nat.decLe 2 p.2

/-- Real oracle implementation for the hiding game.
Standard caching + increments salt counter when any query has salt `s`. -/
def hidingImpl₁ (s : S) :
    QueryImpl (CMOracle M S C)
      (StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C))) :=
  fun (ms : M × S) => do
    let (cache, cnt) ← get
    match cache ms with
    | some u => return u
    | none => do
      let u ← (liftM (query (spec := CMOracle M S C) ms) :
        StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C)) C)
      let cnt' := if ms.2 == s then cnt + 1 else cnt
      set (cache.cacheQuery ms u, cnt')
      return u

/-- Shared counted hiding implementation: same cache semantics as `cachingOracle`,
with a per-salt miss counter `S → ℕ` updated at the queried salt on cache miss. -/
def hidingImplCountAll :
    QueryImpl (CMOracle M S C)
      (StateT (QueryCache (CMOracle M S C) × (S → ℕ)) (OracleComp (CMOracle M S C))) :=
  fun (ms : M × S) => do
    let (cache, counts) ← get
    match cache ms with
    | some u => return u
    | none => do
      let u ← (liftM (query (spec := CMOracle M S C) ms) :
        StateT (QueryCache (CMOracle M S C) × (S → ℕ)) (OracleComp (CMOracle M S C)) C)
      let counts' := Function.update counts ms.2 (counts ms.2 + 1)
      set (cache.cacheQuery ms u, counts')
      return u

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma hidingImpl₁_step_totalBound (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × ℕ) :
    IsTotalQueryBound ((hidingImpl₁ s ms).run st) 1 := by
  obtain ⟨cache, cnt⟩ := st
  cases hcache : cache ms with
  | some u =>
      simpa [hidingImpl₁, hcache, StateT.run_bind, StateT.run_get, pure_bind] using
        (show IsTotalQueryBound
            (pure (u, (cache, cnt)) :
              OracleComp (CMOracle M S C) (C × (QueryCache (CMOracle M S C) × ℕ))) 1 from
          trivial)
  | none =>
      simpa [hidingImpl₁, hcache, StateT.run_bind, StateT.run_get, pure_bind,
        StateT.run_set, StateT.run_pure, OracleComp.liftM_run_StateT, MonadLift.monadLift]
        using
          (show IsTotalQueryBound
              (((liftM (query (spec := CMOracle M S C) ms) :
                  OracleComp (CMOracle M S C) C) >>= fun u =>
                pure (u, (cache.cacheQuery ms u,
                  if ms.2 == s then cnt + 1 else cnt))))
              1 from by
            rw [isTotalQueryBound_query_bind_iff]
            exact ⟨Nat.one_pos, fun _ => trivial⟩)

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma hidingImplCountAll_step_totalBound (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) :
    IsTotalQueryBound ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st) 1 := by
  obtain ⟨cache, counts⟩ := st
  cases hcache : cache ms with
  | some u =>
      simpa [hidingImplCountAll, hcache, StateT.run_bind, StateT.run_get, pure_bind] using
        (show IsTotalQueryBound
            (pure (u, (cache, counts)) :
              OracleComp (CMOracle M S C)
                (C × (QueryCache (CMOracle M S C) × (S → ℕ)))) 1 from
          trivial)
  | none =>
      simpa [hidingImplCountAll, hcache, StateT.run_bind, StateT.run_get, pure_bind,
        StateT.run_set, StateT.run_pure, OracleComp.liftM_run_StateT, MonadLift.monadLift]
        using
          (show IsTotalQueryBound
              (((liftM (query (spec := CMOracle M S C) ms) :
                  OracleComp (CMOracle M S C) C) >>= fun u =>
                pure (u, (cache.cacheQuery ms u,
                  Function.update counts ms.2 (counts ms.2 + 1)))))
              1 from by
            rw [isTotalQueryBound_query_bind_iff]
            exact ⟨Nat.one_pos, fun _ => trivial⟩)

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- Single-step projection: projecting `hidingImplCountAll` to one salt counter
recovers `hidingImpl₁ s`. -/
theorem hidingImplCountAll_proj_eq_hidingImpl₁
    (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) :
    Prod.map id (fun st => (st.1, st.2 s)) <$>
        (hidingImplCountAll (M := M) (S := S) (C := C) ms).run st =
      (hidingImpl₁ (M := M) (S := S) (C := C) s ms).run (st.1, st.2 s) := by
  obtain ⟨cache, counts⟩ := st
  cases hcache : cache ms with
  | some u =>
      simp [hidingImplCountAll, hidingImpl₁, hcache, StateT.run_bind, StateT.run_get,
        pure_bind]
  | none =>
      simp only [hidingImplCountAll, bind_pure_comp, StateT.run_bind, StateT.run_get,
        pure_bind, hcache, StateT.run_monadLift, StateT.run_map, StateT.run_set, map_pure,
        Functor.map_map, Prod.map, id_eq, Function.update, eq_rec_constant, dite_eq_ite,
        hidingImpl₁, beq_iff_eq]
      congr
      funext a
      by_cases h : ms.2 = s
      · simp [h]
      · have hs : ¬ s = ms.2 := by simpa [eq_comm] using h
        simp [h, hs]

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
theorem hidingImplCountAll_proj_eq_cachingOracle
    (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) :
    Prod.map id Prod.fst <$>
        (hidingImplCountAll (M := M) (S := S) (C := C) ms).run st =
      (cachingOracle (spec := CMOracle M S C) ms).run st.1 := by
  rcases st with ⟨cache, counts⟩
  cases hcache : cache ms with
  | some u =>
      simp [hidingImplCountAll, cachingOracle, QueryImpl.withCaching_apply, hcache,
        StateT.run_bind, StateT.run_get, pure_bind]
  | none =>
      simp [hidingImplCountAll, cachingOracle, QueryImpl.withCaching_apply, hcache,
        StateT.run_bind, StateT.run_get, pure_bind, StateT.run_set,
        StateT.run_modifyGet, Prod.map]

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
theorem run_hidingImplCountAll_proj_eq_cachingOracle
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) :
    Prod.map id Prod.fst <$> (simulateQ hidingImplCountAll oa).run st =
      (simulateQ cachingOracle oa).run st.1 := by
  simpa using
    (OracleComp.ProgramLogic.Relational.map_run_simulateQ_eq_of_query_map_eq'
      hidingImplCountAll cachingOracle (fun st => st.1)
      (fun ms st => by
        simpa [Prod.map] using
          hidingImplCountAll_proj_eq_cachingOracle
            (M := M) (S := S) (C := C) ms st)
      oa st)

/-- Intermediate oracle implementation for the hiding game.
Same as `hidingImpl₁`, except when `cnt ≥ 2` (bad) and cache miss with salt `s`,
queries the underlying oracle at `(default, default)` instead. -/
def hidingImpl₂ (s : S) :
    QueryImpl (CMOracle M S C)
      (StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C))) :=
  fun (ms : M × S) => do
    let (cache, cnt) ← get
    match cache ms with
    | some u => return u
    | none => do
      -- When bad (cnt ≥ 2) and salt matches, redirect query
      let queryPoint := if (decide (cnt ≥ 2)) && (ms.2 == s) then (default, default) else ms
      let u ← (liftM (query (spec := CMOracle M S C) queryPoint) :
        StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C)) C)
      let cnt' := if ms.2 == s then cnt + 1 else cnt
      set (cache.cacheQuery ms u, cnt')
      return u

/-- Simulator oracle implementation for the hiding game.
Same as `hidingImpl₁` EXCEPT that ALL salt-`s` cache misses are redirected to
`(default, default)`. The result is still cached at the original query point `ms`,
and the counter still increments. Since the underlying oracle is memoryless
(each `query` returns fresh uniform regardless of point), the redirect doesn't
change the marginal distribution of the returned value.

The key difference from `hidingImpl₂` (which only redirects when `cnt ≥ 2`):
`hidingImplSim` redirects ALL salt-s cache misses, including the very first one
(the challenge query). This makes `hidingImplSim` match the simulator's behavior. -/
def hidingImplSim (s : S) :
    QueryImpl (CMOracle M S C)
      (StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C))) :=
  fun (ms : M × S) => do
    let (cache, cnt) ← get
    match cache ms with
    | some u => return u
    | none => do
      -- Redirect ALL salt-s cache misses to (default, default)
      let queryPoint := if ms.2 == s then (default, default) else ms
      let u ← (liftM (query (spec := CMOracle M S C) queryPoint) :
        StateT (QueryCache (CMOracle M S C) × ℕ) (OracleComp (CMOracle M S C)) C)
      let cnt' := if ms.2 == s then cnt + 1 else cnt
      set (cache.cacheQuery ms u, cnt')
      return u

/-- The shared adversary computation for the hiding game.
Both `hidingReal` and the intermediate game use this computation. -/
def hidingOa {AUX : Type} {t : ℕ} (A : HidingAdversary M S C AUX t) (s : S) :
    OracleComp (CMOracle M S C) Bool := do
  let (m, aux) ← A.choose
  let cm ← query (spec := CMOracle M S C) (m, s)
  A.distinguish aux cm

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
/-- Total query bound for the full two-phase hiding computation, matching the
textbook's bounded-query setting: `t` adversary queries plus one challenge
query. -/
lemma hidingOa_totalBound_current {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    IsTotalQueryBound (hidingOa A s) (t + 1) := by
  simpa [hidingOa] using A.totalBound s

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] in
lemma hiding_choose_totalBound {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    IsTotalQueryBound A.choose t := by
  simpa [hidingOa] using
    (OracleComp.IsTotalQueryBound.of_bind_query_prefix
      (spec := CMOracle M S C)
      (oa := A.choose)
      (next := fun x : M × AUX => (x.1, default))
      (ob := fun x cm => A.distinguish x.2 cm)
      (n := t)
      (A.totalBound default))

omit [DecidableEq C] [Fintype C] [Inhabited M] [Inhabited S] [Inhabited C] in
lemma hiding_distinguish_totalBound_of_choose_support
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {x : (M × AUX) × QueryCount (M × S)}
    (hx : x ∈ support (countingOracle.simulate A.choose 0)) :
    ∀ cm : C, IsTotalQueryBound (A.distinguish x.1.2 cm) (t - ∑ ms, x.2 ms) := by
  have hres :
      IsTotalQueryBound
        ((liftM (query (spec := CMOracle M S C) (x.1.1, s))) >>= fun cm =>
          A.distinguish x.1.2 cm)
        ((t + 1) - ∑ ms, x.2 ms) := by
    simpa [hidingOa] using
      (IsTotalQueryBound.residual_of_mem_support_counting
        (spec := CMOracle M S C)
        (oa := A.choose)
        (ob := fun a =>
          (liftM (query (spec := CMOracle M S C) (a.1, s))) >>= fun cm =>
            A.distinguish a.2 cm)
        (n := t + 1)
        (h := A.totalBound s)
        hx)
  rw [isTotalQueryBound_query_bind_iff] at hres
  intro cm
  have hcm : IsTotalQueryBound (A.distinguish x.1.2 cm) (((t + 1) - ∑ ms, x.2 ms) - 1) := by
    simpa using hres.2 cm
  have hbudget : (((t + 1) - ∑ ms, x.2 ms) - 1) = t - ∑ ms, x.2 ms := by
    omega
  simpa [hbudget] using hcm

omit [DecidableEq C] [Fintype M] [Fintype S] [Fintype C] [Inhabited M] [Inhabited S]
  [Inhabited C] in
lemma hidingImpl₁_run_totalBound_current {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    IsTotalQueryBound
      ((simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0))
      (t + 1) := by
  exact (hidingOa_totalBound_current A s).simulateQ_run_of_step
    (fun ms st => hidingImpl₁_step_totalBound s ms st) (∅, 0)

