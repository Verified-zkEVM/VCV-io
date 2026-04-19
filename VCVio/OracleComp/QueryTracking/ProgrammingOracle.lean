/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Programmable Oracles

This file defines combinators for **programming** an oracle: forcing chosen query points to
return chosen pre-decided values, with a bookkeeping flag tracking whether the programming has
been used (the canonical "bad event" of the identical-until-bad pattern).

## Main definitions

- `OracleSpec.ProgrammingPolicy spec` — partial function `t ↦ Option (programmed answer)`.
- `OracleSpec.ProgrammingPolicy.empty` — the all-`none` policy (no programming).
- `QueryImpl.withRedirect so redirect` — replace every query with a user-supplied callback.
- `QueryImpl.withProgramming so policy` — wrap `so` in `StateT (QueryCache × Bool)` so that
  policy hits override the underlying impl, set the bad flag, and are cached for consistency.

## Design notes

The state of `withProgramming` is `(QueryCache × Bool)`:

* The `QueryCache` ensures *consistent answering*: re-querying a programmed point returns the
  same value (so the adversary cannot detect programming via repeat queries).
* The `Bool` flag is set the **first time** the policy fires on an uncached query — i.e. when
  the programming would be observable relative to standard caching semantics. This is the
  canonical bad event for the identical-until-bad bound coming in a follow-up PR.

The flag is monotone (`bad_monotone`): once set, it stays set throughout execution. With the
empty policy, the flag stays `false` and the impl is structurally an `extendState`-lift of
`withCaching` (`withProgramming_empty_run_proj_eq`).

## TODO

- `tvDist_withCaching_withProgramming_le_probEvent_bad`: TV-distance between `withCaching` and
  `withProgramming` is bounded by the probability of the bad flag firing. Requires a refined
  "identical-until-bad-at-output" lemma (the existing `tvDist_simulateQ_le_probEvent_bad` needs
  per-step agreement under `¬bad` *input*, which fails on policy-hit steps where the two impls
  diverge in the same step the flag fires).
- `programming_collision_bound`: concrete probability bound on the bad flag in terms of the
  policy size, query budget, and per-point predictability of the policy distribution. Requires
  introducing a `HasUnpredictableSample` typeclass.
-/

universe u v

open OracleComp OracleSpec

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}

namespace OracleSpec

/-- A programming policy: a partial assignment of programmed answers to oracle inputs.

`policy t = some v` means "force the oracle to return `v` when queried at `t`".
`policy t = none` means "leave the oracle unchanged at `t`". -/
def ProgrammingPolicy (spec : OracleSpec ι) : Type _ :=
  (t : spec.Domain) → Option (spec.Range t)

namespace ProgrammingPolicy

instance : Inhabited (ProgrammingPolicy spec) := ⟨fun _ => none⟩

/-- The empty programming policy: no point is programmed. Specializing `withProgramming` to
this policy recovers `withCaching` (modulo the auxiliary `Bool` flag). -/
@[reducible] def empty : ProgrammingPolicy spec := fun _ => none

omit [DecidableEq ι] in
@[simp] lemma empty_apply (t : spec.Domain) :
    (empty : ProgrammingPolicy spec) t = none := rfl

end ProgrammingPolicy

end OracleSpec

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-! ## Redirect -/

/-- Redirect every oracle query to a user-supplied callback. The base impl `so` is **discarded**
on every query, and `redirect t : m (spec.Range t)` is consulted instead.

`withRedirect so redirect = redirect` definitionally; the named wrapper exists to expose intent
at call sites and to compose with `withProgramming` (which uses `withRedirect` internally for the
"programmed branch" of each query). -/
def withRedirect (_so : QueryImpl spec m)
    (redirect : (t : spec.Domain) → m (spec.Range t)) :
    QueryImpl spec m :=
  redirect

omit [DecidableEq ι] [Monad m] in
@[simp] lemma withRedirect_apply (so : QueryImpl spec m)
    (redirect : (t : spec.Domain) → m (spec.Range t)) (t : spec.Domain) :
    so.withRedirect redirect t = redirect t := rfl

/-! ## Programming -/

/-- Wrap a query implementation `so` to honor a programming `policy`.

State: `StateT (spec.QueryCache × Bool) m`.

* The `QueryCache` is consulted first; cache hits return the cached value (consistent answers
  on repeated queries).
* On a cache miss:
  * `policy t = some v` → return `v`, cache it, **set the bad flag**.
  * `policy t = none` → fall through to `so t`, cache the result, leave the flag untouched.

Specialising to `policy = ProgrammingPolicy.empty` recovers `withCaching` lifted via
`extendState`; see `withProgramming_empty_run_proj_eq`. -/
def withProgramming
    (so : QueryImpl spec m) (policy : ProgrammingPolicy spec) :
    QueryImpl spec (StateT (spec.QueryCache × Bool) m) :=
  fun t => do
    let (cache, bad) ← get
    match cache t with
    | some v => pure v
    | none =>
      match policy t with
      | some v => modifyGet fun _ => (v, (cache.cacheQuery t v, true))
      | none => do
        let u ← liftM (so t)
        modifyGet fun _ => (u, (cache.cacheQuery t u, bad))

@[simp] lemma withProgramming_apply (so : QueryImpl spec m) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) :
    so.withProgramming policy t = (do
      let (cache, bad) ← get
      match cache t with
      | some v => pure v
      | none =>
        match policy t with
        | some v => modifyGet fun _ => (v, (cache.cacheQuery t v, true))
        | none => do
          let u ← liftM (so t)
          modifyGet fun _ => (u, (cache.cacheQuery t u, bad))) := rfl

/-! ## Bad-flag monotonicity -/

variable [LawfulMonad m] [HasEvalSet m]

/-- The bad flag of `withProgramming` is monotone: once set, every query keeps it set. -/
lemma withProgramming_bad_monotone
    (so : QueryImpl spec m) (policy : ProgrammingPolicy spec)
    (t : spec.Domain) (cache : spec.QueryCache)
    (z) (hz : z ∈ support ((so.withProgramming policy t).run (cache, true))) :
    z.2.2 = true := by
  simp only [withProgramming_apply, StateT.run_bind] at hz
  have hget : (get : StateT (spec.QueryCache × Bool) m _).run (cache, true) =
      pure ((cache, true), (cache, true)) := rfl
  rw [hget, pure_bind] at hz
  cases hcache : cache t with
  | some v =>
    simp only [hcache] at hz
    have : (pure v : StateT (spec.QueryCache × Bool) m (spec.Range t)).run (cache, true) =
        pure (v, (cache, true)) := rfl
    rw [this, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | none =>
    simp only [hcache] at hz
    cases hpol : policy t with
    | some v =>
      simp only [hpol] at hz
      have hmod : (modifyGet (fun _ : spec.QueryCache × Bool =>
          (v, (cache.cacheQuery t v, true))) :
          StateT (spec.QueryCache × Bool) m (spec.Range t)).run (cache, true) =
          pure (v, (cache.cacheQuery t v, true)) := rfl
      rw [hmod, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    | none =>
      simp only [hpol, StateT.run_bind] at hz
      have hlift : (liftM (so t) :
          StateT (spec.QueryCache × Bool) m (spec.Range t)).run (cache, true) =
          so t >>= fun u => pure (u, (cache, true)) := rfl
      rw [hlift, bind_assoc] at hz
      simp only [pure_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨u, _, hmod⟩
      have : (modifyGet (fun _ : spec.QueryCache × Bool =>
          (u, (cache.cacheQuery t u, true))) :
          StateT (spec.QueryCache × Bool) m (spec.Range t)).run (cache, true) =
          pure (u, (cache.cacheQuery t u, true)) := rfl
      rw [this, support_pure, Set.mem_singleton_iff] at hmod
      rw [hmod]

/-- `PreservesInv` packaging of `withProgramming_bad_monotone` for `ProbComp`. -/
lemma PreservesInv.withProgramming_bad
    {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    (so : QueryImpl spec₀ ProbComp) (policy : ProgrammingPolicy spec₀) :
    QueryImpl.PreservesInv (so.withProgramming policy)
      (fun (s : spec₀.QueryCache × Bool) => s.2 = true) := by
  intro t ⟨cache, bad⟩ hbad z hz
  cases hbad
  exact withProgramming_bad_monotone so policy t cache z hz

end QueryImpl

/-! ## `withProgramming empty` ≡ `withCaching` (cache-side projection) -/

namespace OracleComp.ProgramLogic.Relational

variable {α : Type}

/-- Per-query equation: with the empty policy and bad flag at value `bad`, projecting away the
bad flag from a single `withProgramming` step gives the corresponding `withCaching` step. -/
private lemma withProgramming_empty_query_proj_eq
    {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    (so : QueryImpl spec ProbComp)
    (t : spec.Domain) (cache : spec.QueryCache) (bad : Bool) :
    Prod.map id Prod.fst <$>
        (so.withProgramming ProgrammingPolicy.empty t).run (cache, bad) =
      (so.withCaching t).run cache := by
  simp only [QueryImpl.withProgramming_apply, QueryImpl.withCaching_apply,
    StateT.run_bind, StateT.run_get, pure_bind]
  cases hcache : cache t with
  | some v =>
    have h1 : (pure v : StateT (spec.QueryCache × Bool) ProbComp (spec.Range t)).run (cache, bad) =
        pure (v, (cache, bad)) := rfl
    have h2 : (pure v : StateT spec.QueryCache ProbComp (spec.Range t)).run cache =
        pure (v, cache) := rfl
    rw [h1, h2, map_pure]
    rfl
  | none =>
    simp only [StateT.run_bind]
    have hlift1 : (liftM (so t) :
        StateT (spec.QueryCache × Bool) ProbComp (spec.Range t)).run (cache, bad) =
        so t >>= fun u => pure (u, (cache, bad)) := rfl
    have hlift2 : (liftM (so t) :
        StateT spec.QueryCache ProbComp (spec.Range t)).run cache =
        so t >>= fun u => pure (u, cache) := rfl
    rw [hlift1, hlift2, bind_assoc, bind_assoc]
    simp only [pure_bind, map_bind]
    refine bind_congr fun u => ?_
    have hmod1 : (modifyGet (fun _ : spec.QueryCache × Bool =>
        (u, (cache.cacheQuery t u, bad))) :
        StateT (spec.QueryCache × Bool) ProbComp (spec.Range t)).run (cache, bad) =
        pure (u, (cache.cacheQuery t u, bad)) := rfl
    have hmod2 : (modifyGet (fun cache : spec.QueryCache =>
        (u, cache.cacheQuery t u)) :
        StateT spec.QueryCache ProbComp (spec.Range t)).run cache =
        pure (u, cache.cacheQuery t u) := rfl
    rw [hmod1, hmod2, map_pure]
    rfl

/-- Cache-side projection: running `withProgramming so empty` and projecting away the bad flag
gives the same distribution as running `so.withCaching` directly.

This is the "specializes to caching" sanity check for `withProgramming`, witnessing that the
empty policy adds no observable behavior beyond `withCaching` plus a trivial bookkeeping flag. -/
theorem withProgramming_empty_run_proj_eq
    {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    (so : QueryImpl spec ProbComp)
    (oa : OracleComp spec α) (cache : spec.QueryCache) (bad : Bool) :
    Prod.map id Prod.fst <$>
        (simulateQ (so.withProgramming ProgrammingPolicy.empty) oa).run (cache, bad) =
      (simulateQ so.withCaching oa).run cache := by
  refine map_run_simulateQ_eq_of_query_map_eq
    (impl₁ := so.withProgramming ProgrammingPolicy.empty)
    (impl₂ := so.withCaching)
    (proj := Prod.fst) ?_ oa (cache, bad)
  intro t ⟨cache', bad'⟩
  exact withProgramming_empty_query_proj_eq so t cache' bad'

/-- `run'` projection corollary of `withProgramming_empty_run_proj_eq`. -/
theorem withProgramming_empty_run'_eq
    {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    (so : QueryImpl spec ProbComp)
    (oa : OracleComp spec α) (cache : spec.QueryCache) (bad : Bool) :
    (simulateQ (so.withProgramming ProgrammingPolicy.empty) oa).run' (cache, bad) =
      (simulateQ so.withCaching oa).run' cache := by
  have h := withProgramming_empty_run_proj_eq so oa cache bad
  have hmap := congrArg (fun p => Prod.fst <$> p) h
  simpa [StateT.run'] using hmap

end OracleComp.ProgramLogic.Relational
