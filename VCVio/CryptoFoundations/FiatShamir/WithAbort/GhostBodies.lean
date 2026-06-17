/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort

/-!
# Hybrid signing bodies and ghost-layer machinery for Fiat-Shamir with aborts

Cache-level signing bodies of the CMA-to-NMA hybrid chain for the
Fiat-Shamir-with-aborts transform (`realSignBody`, `progSignBody`,
`transSignBody`, `simSignBody`), together with the run-level hybrid handlers
(`hybridBaseImpl`, `hybridSignImpl`) and the ghost-layer presentation of the
reprogramming bodies used by the Prog → Trans hop:

* `ghostSignBody` acts on a two-layer cache, writing accepted transcripts to
  the real layer and rejected-attempt programmings to the ghost layer; the
  projections `run_ghostSignBody_overlay` and `run_ghostSignBody_fst` recover
  `progSignBody` and the accepted-only programming loop of `transSignBody`.
* `ghostHybridImpl` instruments the adversary's oracles over the layered cache
  with a monotone bad flag firing on adversarial reads of the ghost layer,
  with per-step projections onto both hybrid games
  (`ghostHybridImpl_proj_prog`, `ghostHybridImpl_proj_trans`) and the
  ghost-domain invariant `ghostHybridImpl_preserves_signed_inv`.

The hybrid experiment itself and the hop lemmas live in
`FiatShamir.WithAbort.Security`.
-/

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)
variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))

/-! ## First-success retry loops

The real, reprogrammed, and simulated signing oracles of the hybrid chain all share the
same restart structure: iterate an optional sampler until the first non-`none` result,
up to a fixed attempt budget. `firstSome` abstracts that loop so the zero-knowledge hop
can be reduced to a single distributional lemma about retry loops. -/

/-- Iterate an optional sampler up to `n` times, returning the first non-`none` result
(or `none` when every attempt fails). -/
def firstSome {α : Type} (attempt : ProbComp (Option α)) : ℕ → ProbComp (Option α)
  | 0 => pure none
  | n + 1 => do
    match ← attempt with
    | some a => pure (some a)
    | none => firstSome attempt n

lemma firstSome_succ {α : Type} (attempt : ProbComp (Option α)) (n : ℕ) :
    firstSome attempt (n + 1) =
      attempt >>= fun r =>
        match r with
        | some a => pure (some a)
        | none => firstSome attempt n := rfl

/-- Gluing per-attempt simulation across a first-success retry loop: if two optional
samplers are within total-variation distance `ζ` and the second aborts with probability
at most `q`, then the `n`-attempt retry loops are within `ζ * (1 + q + ⋯ + q^(n-1))`.
In particular, with `q < 1` the loop simulation error is at most `ζ / (1 - q)`,
independently of the attempt budget.

This is the distributional core of the `transSignBody`-to-`simSignBody` hop: each
hybrid step couples one more attempt, and attempt `j` is only reached when the first
`j` attempts of the second loop all abort. -/
lemma tvDist_firstSome_le_geometric {α : Type} (a₁ a₂ : ProbComp (Option α))
    {ζ q : ℝ} (hζ : tvDist a₁ a₂ ≤ ζ) (hq : Pr[= none | a₂].toReal ≤ q) (hq0 : 0 ≤ q) :
    ∀ n : ℕ, tvDist (firstSome a₁ n) (firstSome a₂ n) ≤ ζ * ∑ j ∈ Finset.range n, q ^ j
  | 0 => by simp [firstSome]
  | (n + 1) => by
    have hζ0 : 0 ≤ ζ := le_trans (tvDist_nonneg a₁ a₂) hζ
    have ih := tvDist_firstSome_le_geometric a₁ a₂ hζ hq hq0 n
    have hGeomNonneg : (0 : ℝ) ≤ ∑ j ∈ Finset.range n, q ^ j :=
      Finset.sum_nonneg fun j _ => pow_nonneg hq0 j
    set k₁ : Option α → ProbComp (Option α) := fun r =>
      match r with
      | some a => pure (some a)
      | none => firstSome a₁ n with hk₁
    set k₂ : Option α → ProbComp (Option α) := fun r =>
      match r with
      | some a => pure (some a)
      | none => firstSome a₂ n with hk₂
    have hterm : ∀ b : Option α, b ≠ (none : Option α) →
        Pr[= b | a₂].toReal * tvDist (k₁ b) (k₂ b) = 0 := by
      intro b hb
      match b, hb with
      | some a, _ => simp [hk₁, hk₂]
    have hStep : tvDist (a₂ >>= k₁) (a₂ >>= k₂) ≤
        Pr[= none | a₂].toReal * tvDist (firstSome a₁ n) (firstSome a₂ n) := by
      refine le_trans (tvDist_bind_left_le a₂ k₁ k₂) (le_of_eq ?_)
      rw [tsum_eq_single (none : Option α) hterm]
    calc
      tvDist (firstSome a₁ (n + 1)) (firstSome a₂ (n + 1))
          = tvDist (a₁ >>= k₁) (a₂ >>= k₂) := by
            rw [firstSome_succ, firstSome_succ]
      _ ≤ tvDist (a₁ >>= k₁) (a₂ >>= k₁) + tvDist (a₂ >>= k₁) (a₂ >>= k₂) :=
            tvDist_triangle _ _ _
      _ ≤ ζ + Pr[= none | a₂].toReal * tvDist (firstSome a₁ n) (firstSome a₂ n) :=
            add_le_add (le_trans (tvDist_bind_right_le k₁ a₁ a₂) hζ) hStep
      _ ≤ ζ + q * (ζ * ∑ j ∈ Finset.range n, q ^ j) :=
            add_le_add le_rfl (mul_le_mul hq ih (tvDist_nonneg _ _) hq0)
      _ = ζ * ∑ j ∈ Finset.range (n + 1), q ^ j := by
            have hsum : ∑ j ∈ Finset.range (n + 1), q ^ j =
                q * (∑ j ∈ Finset.range n, q ^ j) + 1 := by
              rw [Finset.sum_range_succ', Finset.mul_sum]
              simp [pow_succ']
            rw [hsum]
            ring

/-! ## The hybrid signing bodies

All four hybrid games run the adversary against the same uniform-sampling and
random-oracle handlers, differing only in the signing-oracle body. Each body is a
cache-level state transformer on the random-oracle cache. Following Fig. 2 of the
paper (adapted to the bounded restart loop):

- `realSignBody` (Sign): the real signing loop, hashing each attempt's commitment
  through the caching random oracle. Aborted attempts also populate the cache.
- `progSignBody` (Prog): every attempt **overwrites** the cache at `(msg, w)` with a
  fresh uniform challenge, for rejected and accepted attempts alike, removing the
  dependency between the cached challenge and the accept event.
- `transSignBody` (Trans): the loop runs privately on `ids.honestExecution` (no cache
  interaction), and only the accepted transcript is programmed into the cache.
- `simSignBody` (Sim): as `transSignBody` with the per-attempt HVZK simulator in place
  of the honest execution; the secret key is no longer used. -/

/-- Real signing-oracle body: the cache-level semantics of `fsAbortSignLoop` under the
caching random oracle. Each attempt queries the random oracle at `(msg, w)`, so aborted
attempts leave their challenge in the cache exactly as in the real experiment. -/
noncomputable def realSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp)) :=
  simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
    (fsAbortSignLoop ids M pk sk msg maxAttempts)

/-- One signing attempt of the all-attempts-reprogramming hybrid: commit honestly, then
overwrite the cache at `(msg, w)` with a fresh uniform challenge before responding. -/
noncomputable def progSignAttempt (pk : Stmt) (sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Commit × Option Resp) := do
  let (w, st) ← liftM (ids.commit pk sk)
  let c ← (liftM (uniformSample Chal) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp Chal)
  modify fun cache => cache.cacheQuery (msg, w) c
  let oz ← liftM (ids.respond pk sk st c)
  pure (w, oz)

/-- Signing-oracle body of the all-attempts-reprogramming hybrid (Prog): run the restart
loop with `progSignAttempt`, so every attempt (accepted or rejected) reprograms the
random-oracle cache with a fresh challenge. -/
noncomputable def progSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    ℕ → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp))
  | 0 => pure none
  | n + 1 => do
    let (w, oz) ← progSignAttempt ids M pk sk msg
    match oz with
    | some z => pure (some (w, z))
    | none => progSignBody pk sk msg n

/-- Shared cache-programming continuation of `transSignBody` and `simSignBody`: program
the accepted transcript's challenge into the cache at `(msg, w)` and return the
signature `(w, z)`; an all-abort loop outcome produces no signature and no programming.

The continuation is a deterministic function of the loop outcome, so the gap between
the two hybrids reduces entirely to the gap between their private loops (see
`tvDist_run_transSignBody_simSignBody_le`). -/
noncomputable def signProgramCont (msg : M) :
    Option (Commit × Chal × Resp) →
      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp))
  | some (w, c, z) => do
    modify fun cache => cache.cacheQuery (msg, w) c
    pure (some (w, z))
  | none => pure none

/-- Signing-oracle body of the accepted-only-reprogramming hybrid (Trans): the restart
loop runs privately on honest executions (`ids.honestExecution`, which samples its own
uniform challenge and never touches the cache); only the accepted transcript is
programmed into the cache. Rejected attempts leave no trace. -/
noncomputable def transSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp)) :=
  liftM (firstSome (ids.honestExecution pk sk) maxAttempts) >>= signProgramCont M msg

/-- Signing-oracle body of the simulated hybrid (Sim): as `transSignBody`, with the
per-attempt HVZK simulator replacing the honest execution. The secret key is unused, so
this body can be run by the NMA reduction. -/
noncomputable def simSignBody (pk : Stmt) (_sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp)) :=
  liftM (firstSome (sim pk) maxAttempts) >>= signProgramCont M msg

/-! ## Ghost-layer presentation of the reprogramming bodies

The Prog → Trans hop (`probOutput_hybridExpAtKey_prog_le_trans`) compares two signing
bodies whose caches genuinely differ throughout the run: `progSignBody` programs every
attempt, while `transSignBody` programs only the accepted transcript. The bridge is a
two-layer presentation of the cache: a *real* layer holding the entries both games agree
on, and a *ghost* layer holding the rejected-attempt programmings that only
`progSignBody` performs. `ghostSignBody` acts on the layered state, writing the accepted
transcript to the real layer and each rejected attempt to the ghost layer.

Two projection lemmas make the deferred-sampling step of the hop precise:

* overlaying the ghost layer onto the real layer recovers `progSignBody`
  (`run_ghostSignBody_overlay`), and
* forgetting the ghost layer recovers the accepted-only programming loop of
  `transSignBody` (`run_ghostSignBody_fst`) — a programmed point that is never
  subsequently read is distributionally removable. -/

/-- Overlay a ghost cache onto a real cache; ghost entries shadow real ones. -/
def overlayCache (re gh : (M × Commit →ₒ Chal).QueryCache) :
    (M × Commit →ₒ Chal).QueryCache :=
  fun q => (gh q).or (re q)

/-- Remove a single point from a query cache. -/
def uncacheQuery (cache : (M × Commit →ₒ Chal).QueryCache) (q : M × Commit) :
    (M × Commit →ₒ Chal).QueryCache :=
  fun q' => if q' = q then none else cache q'

omit [SampleableType Chal] in
lemma overlayCache_cacheQuery_uncacheQuery
    (re gh : (M × Commit →ₒ Chal).QueryCache) (q : M × Commit) (c : Chal) :
    overlayCache M (re.cacheQuery q c) (uncacheQuery M gh q) =
      (overlayCache M re gh).cacheQuery q c := by
  funext q'
  by_cases hq : q' = q
  · subst hq
    simp [overlayCache, uncacheQuery]
  · simp [overlayCache, uncacheQuery, hq]

omit [SampleableType Chal] in
/-- Removing a point from a cache does not increase its live-entry count: the support set
of `uncacheQuery cache q` is a subset of that of `cache`. -/
lemma toSet_uncacheQuery_subset (cache : (M × Commit →ₒ Chal).QueryCache) (q : M × Commit) :
    (uncacheQuery M cache q).toSet ⊆ cache.toSet := by
  rintro ⟨t', u'⟩ hmem
  rw [QueryCache.mem_toSet] at hmem ⊢
  by_cases ht : t' = q
  · subst ht; simp only [uncacheQuery, if_true] at hmem; exact absurd hmem (by simp)
  · rwa [uncacheQuery, if_neg ht] at hmem

omit [SampleableType Chal] in
/-- `uncacheQuery` does not increase the `enncard` resource. -/
lemma enncard_uncacheQuery_le (cache : (M × Commit →ₒ Chal).QueryCache) (q : M × Commit) :
    QueryCache.enncard (uncacheQuery M cache q) ≤ QueryCache.enncard cache :=
  ENat.toENNReal_mono (Set.encard_le_encard (toSet_uncacheQuery_subset M cache q))

omit [SampleableType Chal] in
lemma overlayCache_cacheQuery_ghost
    (re gh : (M × Commit →ₒ Chal).QueryCache) (q : M × Commit) (c : Chal) :
    overlayCache M re (gh.cacheQuery q c) = (overlayCache M re gh).cacheQuery q c := by
  funext q'
  by_cases hq : q' = q
  · subst hq
    simp [overlayCache]
  · simp [overlayCache, hq]

omit [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma overlayCache_apply_ghost_some
    {gh : (M × Commit →ₒ Chal).QueryCache} {q : M × Commit} {v : Chal}
    (re : (M × Commit →ₒ Chal).QueryCache) (h : gh q = some v) :
    overlayCache M re gh q = some v := by
  simp [overlayCache, h]

omit [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma overlayCache_apply_ghost_none
    {gh : (M × Commit →ₒ Chal).QueryCache} {q : M × Commit}
    (re : (M × Commit →ₒ Chal).QueryCache) (h : gh q = none) :
    overlayCache M re gh q = re q := by
  simp [overlayCache, h]

omit [SampleableType Chal] in
lemma overlayCache_cacheQuery_real_of_ghost_none
    (re : (M × Commit →ₒ Chal).QueryCache) {gh : (M × Commit →ₒ Chal).QueryCache}
    {q : M × Commit} (h : gh q = none) (c : Chal) :
    overlayCache M (re.cacheQuery q c) gh = (overlayCache M re gh).cacheQuery q c := by
  funext q'
  by_cases hq : q' = q
  · subst hq
    simp [overlayCache, h]
  · simp [overlayCache, hq]

/-- Signing body on the layered cache: run the abort loop privately, recording each
rejected attempt's would-be programming in the ghost layer and programming the accepted
transcript into the real layer (clearing any stale ghost entry at that point). -/
noncomputable def ghostSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    ℕ → StateT ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache)
      ProbComp (Option (Commit × Resp))
  | 0 => pure none
  | n + 1 => do
    let (w, st) ← liftM (ids.commit pk sk)
    let c ← (liftM (uniformSample Chal) :
      StateT ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache)
        ProbComp Chal)
    let oz ← liftM (ids.respond pk sk st c)
    match oz with
    | some z =>
        modify fun s => (s.1.cacheQuery (msg, w) c, uncacheQuery M s.2 (msg, w))
        pure (some (w, z))
    | none =>
        modify fun s => (s.1, s.2.cacheQuery (msg, w) c)
        ghostSignBody pk sk msg n

omit [SampleableType Stmt] in
/-- Overlay projection: `ghostSignBody` with the ghost layer overlaid onto the real
layer is exactly `progSignBody` on the overlaid cache. Rejected-attempt programmings
(ghost writes) and accepted programmings (real writes) both surface as ordinary cache
programmings under the overlay. -/
lemma run_ghostSignBody_overlay (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache),
      (fun zs : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
          (zs.1, overlayCache M zs.2.1 zs.2.2)) <$>
        (ghostSignBody ids M pk sk msg n).run (re, gh) =
      (progSignBody ids M pk sk msg n).run (overlayCache M re gh)
  | 0, re, gh => by
    simp [ghostSignBody, progSignBody]
  | (n + 1), re, gh => by
    simp only [ghostSignBody, progSignBody, progSignAttempt, bind_assoc, StateT.run_bind,
      OracleComp.liftM_run_StateT, map_bind, pure_bind, StateT.run_modify]
    refine congrArg (ids.commit pk sk >>= ·) (funext fun wst => ?_)
    obtain ⟨w, st⟩ := wst
    refine congrArg (uniformSample Chal >>= ·) (funext fun c => ?_)
    refine congrArg (ids.respond pk sk st c >>= ·) (funext fun oz => ?_)
    cases oz with
    | some z =>
        simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
          map_pure, overlayCache_cacheQuery_uncacheQuery]
    | none =>
        simp only [StateT.run_bind, StateT.run_modify, pure_bind,
          run_ghostSignBody_overlay pk sk msg n re (gh.cacheQuery (msg, w) c),
          overlayCache_cacheQuery_ghost]

omit [SampleableType Stmt] in
/-- Ghost-forgetting projection (deferred sampling): dropping the ghost layer from
`ghostSignBody` yields the accepted-only programming loop of `transSignBody`. The
programming of a rejected attempt lives only in the ghost layer, so removing it does not
change the joint distribution of the signing output and the real cache. -/
lemma run_ghostSignBody_fst (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache),
      (fun zs : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) => (zs.1, zs.2.1)) <$>
        (ghostSignBody ids M pk sk msg n).run (re, gh) =
      (liftM (firstSome (ids.honestExecution pk sk) n) >>= signProgramCont M msg).run re
  | 0, re, gh => by
    simp [ghostSignBody, firstSome, signProgramCont]
  | (n + 1), re, gh => by
    simp only [ghostSignBody, firstSome_succ, IdenSchemeWithAbort.honestExecution,
      bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT, map_bind, pure_bind]
    refine congrArg (ids.commit pk sk >>= ·) (funext fun wst => ?_)
    obtain ⟨w, st⟩ := wst
    refine congrArg (uniformSample Chal >>= ·) (funext fun c => ?_)
    refine congrArg (ids.respond pk sk st c >>= ·) (funext fun oz => ?_)
    cases oz with
    | some z =>
        simp only [Option.map_some, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, map_pure, signProgramCont]
    | none =>
        simp only [Option.map_none, StateT.run_bind, StateT.run_modify, pure_bind]
        rw [run_ghostSignBody_fst pk sk msg n re (gh.cacheQuery (msg, w) c)]
        simp only [IdenSchemeWithAbort.honestExecution, StateT.run_bind,
          OracleComp.liftM_run_StateT, bind_assoc, pure_bind]

omit [SampleableType Stmt] in
/-- `run_ghostSignBody_fst` at the attempt budget of the scheme: forgetting the ghost
layer of `ghostSignBody` recovers `transSignBody` on the real layer. -/
lemma run_ghostSignBody_fst_eq_transSignBody (pk : Stmt) (sk : Wit) (msg : M)
    (re gh : (M × Commit →ₒ Chal).QueryCache) :
    (fun zs : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) => (zs.1, zs.2.1)) <$>
        (ghostSignBody ids M pk sk msg maxAttempts).run (re, gh) =
      (transSignBody ids M maxAttempts pk sk msg).run re :=
  run_ghostSignBody_fst ids M pk sk msg maxAttempts re gh

omit [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma overlayCache_empty (re : (M × Commit →ₒ Chal).QueryCache) :
    overlayCache M re ∅ = re := by
  funext q
  simp [overlayCache]

/-! ## Ghost-instrumented hybrid handlers

Run-level counterpart of the ghost-layer presentation: handlers for the adversary's
oracles over the layered cache, a signed-message list, and a monotone bad flag that
fires exactly when the adversary's random-oracle query hits a point of the ghost layer.
The Prog-side handler (`ghostHybridImpl … true`) answers such a query from the ghost
layer (matching `progSignBody`'s overlaid cache), while the Trans-side handler
(`ghostHybridImpl … false`) answers it from the real layer (matching `transSignBody`'s
cache). On every other query the two handlers are literally identical, which is the
identical-until-bad shape of `tvDist_simulateQ_run_le_probEvent_output_bad`. -/

/-- One caching random-oracle step on a bare cache, as a `ProbComp`. Agrees with
`(randomOracle mc).run re` (see `randomOracle_run_eq_roStep`). -/
noncomputable def roStep (re : (M × Commit →ₒ Chal).QueryCache) (mc : M × Commit) :
    ProbComp (Chal × (M × Commit →ₒ Chal).QueryCache) :=
  match re mc with
  | some v => pure (v, re)
  | none => do
    let c ← uniformSample Chal
    pure (c, re.cacheQuery mc c)

omit [SampleableType Stmt] in
lemma randomOracle_run_eq_roStep (re : (M × Commit →ₒ Chal).QueryCache) (mc : M × Commit) :
    ((randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) mc).run re =
      roStep M re mc := by
  rw [randomOracle.apply_eq]
  cases hre : re mc with
  | some v => simp [roStep, hre]
  | none => simp [roStep, hre, StateT.run_bind]

/-- The state of the ghost-instrumented hybrid run: layered cache, signed-message list,
and the bad flag for adversarial reads of the ghost layer. -/
abbrev GhostState (M Commit Chal : Type) : Type :=
  (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) × Bool

/-- Instrumented handler for the adversary's oracles over the layered cache.
`progSide` selects the answer at a ghost hit: the ghost value (Prog side) or a fresh
caching read of the real layer (Trans side). The bad flag fires on ghost hits and is
otherwise preserved; signing queries run `ghostSignBody` on the cache layers. -/
noncomputable def ghostHybridImpl (progSide : Bool) (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (GhostState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      match s.1.1.2 mc with
      | some v =>
          if progSide then pure (v, (s.1, true))
          else (fun cu => (cu.1, (((cu.2, s.1.1.2), s.1.2), true))) <$> roStep M s.1.1.1 mc
      | none =>
          (fun cu => (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2))) <$> roStep M s.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1, ((alc.2, msg :: s.1.2), s.2))) <$>
        (ghostSignBody ids M pk sk msg maxAttempts).run s.1.1

omit [SampleableType Stmt] in
/-- The two ghost-instrumented handlers agree on all transitions that leave the bad flag
unset: they differ only in the answer at a ghost hit, which fires the flag on both
sides. -/
lemma ghostHybridImpl_agree_good (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M)
    (u : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t)
    (s' : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) :
    Pr[= (u, (s', false)) |
        (ghostHybridImpl ids M maxAttempts true pk sk t).run (s, false)] =
      Pr[= (u, (s', false)) |
        (ghostHybridImpl ids M maxAttempts false pk sk t).run (s, false)] := by
  rcases t with (n | mc) | msg
  · rfl
  · simp only [ghostHybridImpl, StateT.run_mk]
    cases hgh : s.1.2 mc with
    | some v =>
        simp only [↓reduceIte]
        rw [probOutput_eq_zero_of_not_mem_support (by
            intro h
            rw [support_pure] at h
            simpa using congrArg (fun z : _ × GhostState M Commit Chal => z.2.2) h),
          probOutput_eq_zero_of_not_mem_support (by
            intro h
            rw [if_neg Bool.false_ne_true, support_map] at h
            obtain ⟨cu, -, hcu⟩ := h
            simpa using congrArg (fun z : _ × GhostState M Commit Chal => z.2.2) hcu)]
    | none => rfl
  · rfl

omit [SampleableType Stmt] in
/-- The ghost-instrumented handlers never unset the bad flag. -/
lemma ghostHybridImpl_bad_mono (progSide : Bool) (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (p : GhostState M Commit Chal) (hp : p.2 = true) :
    ∀ z ∈ support ((ghostHybridImpl ids M maxAttempts progSide pk sk t).run p),
      z.2.2 = true := by
  intro z hz
  rcases t with (n | mc) | msg
  · simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hp
  · simp only [ghostHybridImpl, StateT.run_mk] at hz
    rcases hgh : p.1.1.2 mc with _ | v
    · simp only [hgh, support_map] at hz
      obtain ⟨_, _, rfl⟩ := hz
      exact hp
    · simp only [hgh] at hz
      cases progSide with
      | true =>
          simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          rfl
      | false =>
          rw [if_neg Bool.false_ne_true, support_map] at hz
          obtain ⟨_, _, rfl⟩ := hz
          rfl
  · simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact hp

/-! ## Hybrid run-level handlers -/

/-- Run a cache-level action inside the hybrid state (random-oracle cache plus the list
of signed messages), acting on the cache component. -/
def onCache {α : Type}
    (action : StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp α) :
    StateT ((M × Commit →ₒ Chal).QueryCache × List M) ProbComp α :=
  fun s => (fun (a, c) => (a, (c, s.2))) <$> action.run s.1

/-- Handler for the adversary's base oracles in the hybrid games: uniform queries are
forwarded and random-oracle queries go through the caching random oracle on the cache
component of the hybrid state. -/
noncomputable def hybridBaseImpl :
    QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache × List M) ProbComp) :=
  let base : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))
  fun t => onCache M (base t)

/-- Handler for the adversary's signing oracle in the hybrid games: record the signed
message (for the freshness check) and run the given signing body on the cache. -/
noncomputable def hybridSignImpl
    (signBody : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp))) :
    QueryImpl (M →ₒ Option (Commit × Resp))
      (StateT ((M × Commit →ₒ Chal).QueryCache × List M) ProbComp) :=
  fun msg => do
    modify fun s => (s.1, msg :: s.2)
    onCache M (signBody msg)

/-! ## Projections of the ghost-instrumented run

The ghost-instrumented run projects onto the Prog hybrid by overlaying the ghost layer
onto the real one, and onto the Trans hybrid by forgetting the ghost layer. Both are
per-step state projections in the sense of `OracleComp.map_run_simulateQ_eq_of_query_map_eq`. -/

omit [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma onCache_run {α : Type}
    (action : StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp α)
    (s : (M × Commit →ₒ Chal).QueryCache × List M) :
    (onCache M action).run s = (fun ac : α × (M × Commit →ₒ Chal).QueryCache =>
      (ac.1, (ac.2, s.2))) <$> action.run s.1 := rfl

omit [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma hybridSignImpl_run
    (signBody : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp)))
    (msg : M) (c : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (hybridSignImpl M signBody msg).run (c, l) =
      (fun ac : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
        (ac.1, (ac.2, msg :: l))) <$> (signBody msg).run c := rfl

omit [SampleableType Stmt] in
lemma roStep_of_some {re : (M × Commit →ₒ Chal).QueryCache} {mc : M × Commit} {v : Chal}
    (h : re mc = some v) : roStep M re mc = pure (v, re) := by
  unfold roStep
  rw [h]

omit [SampleableType Stmt] in
lemma roStep_of_none {re : (M × Commit →ₒ Chal).QueryCache} {mc : M × Commit}
    (h : re mc = none) :
    roStep M re mc = uniformSample Chal >>= fun c => pure (c, re.cacheQuery mc c) := by
  unfold roStep
  rw [h]

omit [SampleableType Stmt] in
lemma hybridBaseImpl_run_ro (mc : M × Commit)
    (c : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (hybridBaseImpl (Commit := Commit) (Chal := Chal) M (.inr mc)).run (c, l) =
      (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (cu.2, l))) <$> roStep M c mc := by
  have h : (onCache M ((unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))) (.inr mc))).run (c, l) =
        (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (cu.2, l))) <$> roStep M c mc := by
    rw [QueryImpl.add_apply_inr, onCache_run]
    exact congrArg (fun x => (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
      (cu.1, (cu.2, l))) <$> x) (randomOracle_run_eq_roStep M c mc)
  exact h

omit [SampleableType Stmt] in
lemma ghostHybridImpl_run_ro_ghost_some (progSide : Bool) (pk : Stmt) (sk : Wit)
    {mc : M × Commit} {s : GhostState M Commit Chal} {v : Chal}
    (h : s.1.1.2 mc = some v) :
    (ghostHybridImpl ids M maxAttempts progSide pk sk (.inl (.inr mc))).run s =
      if progSide then pure (v, (s.1, true))
      else (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((cu.2, s.1.1.2), s.1.2), true))) <$> roStep M s.1.1.1 mc := by
  change (match s.1.1.2 mc with
    | some v => if progSide then pure (v, (s.1, true))
        else (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, s.1.1.2), s.1.2), true))) <$> roStep M s.1.1.1 mc
    | none => (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2))) <$> roStep M s.1.1.1 mc) = _
  rw [h]

omit [SampleableType Stmt] in
lemma ghostHybridImpl_run_ro_ghost_none (progSide : Bool) (pk : Stmt) (sk : Wit)
    {mc : M × Commit} {s : GhostState M Commit Chal}
    (h : s.1.1.2 mc = none) :
    (ghostHybridImpl ids M maxAttempts progSide pk sk (.inl (.inr mc))).run s =
      (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2))) <$> roStep M s.1.1.1 mc := by
  change (match s.1.1.2 mc with
    | some v => if progSide then pure (v, (s.1, true))
        else (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, s.1.1.2), s.1.2), true))) <$> roStep M s.1.1.1 mc
    | none => (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2))) <$> roStep M s.1.1.1 mc) = _
  rw [h]

omit [SampleableType Stmt] in
lemma ghostHybridImpl_run_sign (progSide : Bool) (pk : Stmt) (sk : Wit)
    (msg : M) (s : GhostState M Commit Chal) :
    (ghostHybridImpl ids M maxAttempts progSide pk sk (.inr msg)).run s =
      (fun alc : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (alc.1, ((alc.2, msg :: s.1.2), s.2))) <$>
        (ghostSignBody ids M pk sk msg maxAttempts).run s.1.1 := rfl

omit [SampleableType Stmt] in
/-- Per-step overlay projection: each step of the Prog-side ghost-instrumented handler
projects onto the corresponding step of the Prog hybrid handler. -/
lemma ghostHybridImpl_proj_prog (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : GhostState M Commit Chal) :
    Prod.map id (fun g : GhostState M Commit Chal =>
        (overlayCache M g.1.1.1 g.1.1.2, g.1.2)) <$>
        (ghostHybridImpl ids M maxAttempts true pk sk t).run s =
      ((hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (progSignBody ids M pk sk · maxAttempts)) t).run
        (overlayCache M s.1.1.1 s.1.1.2, s.1.2) := by
  rcases t with (n | mc) | msg
  · simp only [ghostHybridImpl, StateT.run_mk, QueryImpl.add_apply_inl, hybridBaseImpl,
      unifFwdImpl, QueryImpl.liftTarget_apply, Functor.map_map]
    rfl
  · refine Eq.trans ?_
      (hybridBaseImpl_run_ro M mc (overlayCache M s.1.1.1 s.1.1.2) s.1.2).symm
    cases hgh : s.1.1.2 mc with
    | some v =>
        rw [ghostHybridImpl_run_ro_ghost_some ids M maxAttempts true pk sk hgh,
          if_pos rfl,
          roStep_of_some M (overlayCache_apply_ghost_some (M := M) s.1.1.1 hgh)]
        simp
    | none =>
        rw [ghostHybridImpl_run_ro_ghost_none ids M maxAttempts true pk sk hgh]
        cases hre : s.1.1.1 mc with
        | some v =>
            rw [roStep_of_some M hre, roStep_of_some M (show overlayCache M
              s.1.1.1 s.1.1.2 mc = some v by
                rw [overlayCache_apply_ghost_none (M := M) s.1.1.1 hgh, hre])]
            simp
        | none =>
            rw [roStep_of_none M hre, roStep_of_none M (show overlayCache M
              s.1.1.1 s.1.1.2 mc = none by
                rw [overlayCache_apply_ghost_none (M := M) s.1.1.1 hgh, hre])]
            simp [overlayCache_cacheQuery_real_of_ghost_none (M := M) s.1.1.1 hgh]
  · refine Eq.trans (b := (fun ac : Option (Commit × Resp) ×
        (M × Commit →ₒ Chal).QueryCache => (ac.1, (ac.2, msg :: s.1.2))) <$>
        (progSignBody ids M pk sk msg maxAttempts).run
          (overlayCache M s.1.1.1 s.1.1.2)) ?_ ?_
    · rw [ghostHybridImpl_run_sign ids M maxAttempts true pk sk msg s,
        ← run_ghostSignBody_overlay ids M pk sk msg maxAttempts s.1.1.1 s.1.1.2]
      refine (Functor.map_map _ _ _).trans (Eq.symm ?_)
      exact (Functor.map_map _ _ _).trans rfl
    · exact (hybridSignImpl_run M (progSignBody ids M pk sk · maxAttempts) msg
        (overlayCache M s.1.1.1 s.1.1.2) s.1.2).symm

omit [SampleableType Stmt] in
/-- Per-step ghost-forgetting projection: each step of the Trans-side ghost-instrumented
handler projects onto the corresponding step of the Trans hybrid handler. -/
lemma ghostHybridImpl_proj_trans (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : GhostState M Commit Chal) :
    Prod.map id (fun g : GhostState M Commit Chal => (g.1.1.1, g.1.2)) <$>
        (ghostHybridImpl ids M maxAttempts false pk sk t).run s =
      ((hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (transSignBody ids M maxAttempts pk sk)) t).run
        (s.1.1.1, s.1.2) := by
  rcases t with (n | mc) | msg
  · simp only [ghostHybridImpl, StateT.run_mk, QueryImpl.add_apply_inl, hybridBaseImpl,
      unifFwdImpl, QueryImpl.liftTarget_apply, Functor.map_map]
    rfl
  · refine Eq.trans ?_ (hybridBaseImpl_run_ro M mc s.1.1.1 s.1.2).symm
    cases hgh : s.1.1.2 mc with
    | some v =>
        rw [ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk hgh,
          if_neg Bool.false_ne_true]
        exact (Functor.map_map _ _ _).trans rfl
    | none =>
        rw [ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk hgh]
        exact (Functor.map_map _ _ _).trans rfl
  · refine Eq.trans (b := (fun ac : Option (Commit × Resp) ×
        (M × Commit →ₒ Chal).QueryCache => (ac.1, (ac.2, msg :: s.1.2))) <$>
        (transSignBody ids M maxAttempts pk sk msg).run s.1.1.1) ?_ ?_
    · rw [ghostHybridImpl_run_sign ids M maxAttempts false pk sk msg s,
        ← run_ghostSignBody_fst_eq_transSignBody ids M maxAttempts pk sk msg
          s.1.1.1 s.1.1.2]
      refine (Functor.map_map _ _ _).trans (Eq.symm ?_)
      exact (Functor.map_map _ _ _).trans rfl
    · exact (hybridSignImpl_run M (transSignBody ids M maxAttempts pk sk) msg
        s.1.1.1 s.1.2).symm

/-! ## Ghost-domain invariant -/

omit [SampleableType Stmt] in
/-- Support bound for the ghost writes of `ghostSignBody`: every ghost entry of an
output state was either already present or lies at the signed message `msg`. -/
lemma ghostSignBody_support_ghost (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache)
      (z : Option (Commit × Resp) ×
        ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache)),
      z ∈ support ((ghostSignBody ids M pk sk msg n).run (re, gh)) →
      ∀ q : M × Commit, z.2.2 q ≠ none → gh q ≠ none ∨ q.1 = msg
  | 0, re, gh, z, hz, q, hq => by
    simp only [ghostSignBody, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hq
  | (n + 1), re, gh, z, hz, q, hq => by
    simp only [ghostSignBody, StateT.run_bind, OracleComp.liftM_run_StateT, bind_assoc,
      pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨⟨w, st⟩, -, hz⟩ := hz
    obtain ⟨c, -, hz⟩ := hz
    obtain ⟨oz, -, hz⟩ := hz
    rcases oz with - | zr
    · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hz
      rcases ghostSignBody_support_ghost pk sk msg n re (gh.cacheQuery (msg, w) c)
          z hz q hq with hgh | hmsg
      · by_cases hqw : q = (msg, w)
        · exact Or.inr (by simp [hqw])
        · exact Or.inl (by rwa [QueryCache.cacheQuery_of_ne _ _ hqw] at hgh)
      · exact Or.inr hmsg
    · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp only [uncacheQuery, ne_eq, ite_eq_left_iff, not_forall] at hq
      exact Or.inl hq.2

omit [SampleableType Stmt] in
/-- Ghost-domain invariant: along any run of the ghost-instrumented handlers, every
ghost entry's message component has been recorded in the signed list. -/
lemma ghostHybridImpl_preserves_signed_inv (progSide : Bool) (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : GhostState M Commit Chal)
    (hs : ∀ q : M × Commit, s.1.1.2 q ≠ none → q.1 ∈ s.1.2) :
    ∀ z ∈ support ((ghostHybridImpl ids M maxAttempts progSide pk sk t).run s),
      ∀ q : M × Commit, z.2.1.1.2 q ≠ none → q.1 ∈ z.2.1.2 := by
  intro z hz
  rcases t with (n | mc) | msg
  · simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · simp only [ghostHybridImpl, StateT.run_mk] at hz
    rcases hgh : s.1.1.2 mc with - | v
    · simp only [hgh, support_map] at hz
      obtain ⟨cu, -, rfl⟩ := hz
      exact hs
    · simp only [hgh] at hz
      cases progSide with
      | true =>
          simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact hs
      | false =>
          rw [if_neg Bool.false_ne_true, support_map] at hz
          obtain ⟨cu, -, rfl⟩ := hz
          exact hs
  · simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨alc, halc, rfl⟩ := hz
    intro q hq
    rcases ghostSignBody_support_ghost ids M pk sk msg maxAttempts s.1.1.1 s.1.1.2
        alc halc q hq with hgh | hmsg
    · exact List.mem_cons_of_mem _ (hs q hgh)
    · exact hmsg ▸ List.mem_cons_self

/-! ## Real-versus-reprogrammed signing-body bounds

Quantitative body-level core of the Sign → Prog hop
(`probOutput_hybridExpAtKey_real_le_prog`): run equations unfolding one attempt of the
real signing loop (`fsAbortSignLoop` under the caching random oracle) and of the
reprogramming loop (`progSignBody`), the per-attempt commitment-collision and abort
bounds, the within-signing-query total-variation induction
(`ofReal_tvDist_run_fsAbortSignLoop_progSignBody_le`), and the expected cache-growth
bound for the reprogramming loop (`tsum_probOutput_run_progSignBody_mul_enncard_le`). -/

/-- Expectation of a nonnegative functional under a `pure` computation. -/
lemma tsum_probOutput_pure_mul {β : Type} (y : β) (f : β → ℝ≥0∞) :
    ∑' z, Pr[= z | (pure y : ProbComp β)] * f z = f y := by
  rw [tsum_eq_single y fun z hz => by
    rw [probOutput_eq_zero_of_not_mem_support (by simp [hz]), zero_mul]]
  rw [probOutput_pure_self, one_mul]

/-- Tonelli-style rearrangement: the expectation of a nonnegative functional under a
bind is the outer expectation of the inner expectations. -/
lemma tsum_probOutput_bind_mul {α β : Type} (oa : ProbComp α)
    (g : α → ProbComp β) (f : β → ℝ≥0∞) :
    ∑' z, Pr[= z | oa >>= g] * f z =
      ∑' x, Pr[= x | oa] * ∑' z, Pr[= z | g x] * f z := by
  simp_rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]

/-- Push a constant out of a pointwise expectation bound: a (sub)probability average of
`f ≤ C + g` is at most `C` plus the average of `g`. -/
lemma tsum_probOutput_mul_le_add_of_le {α : Type} (oa : ProbComp α)
    {f g : α → ℝ≥0∞} {C : ℝ≥0∞} (h : ∀ a, f a ≤ C + g a) :
    ∑' a, Pr[= a | oa] * f a ≤ C + ∑' a, Pr[= a | oa] * g a := by
  calc ∑' a, Pr[= a | oa] * f a
      ≤ ∑' a, (Pr[= a | oa] * C + Pr[= a | oa] * g a) :=
        ENNReal.tsum_le_tsum fun a => by rw [← mul_add]; exact mul_le_mul_right (h a) _
    _ = (∑' a, Pr[= a | oa]) * C + ∑' a, Pr[= a | oa] * g a := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ 1 * C + ∑' a, Pr[= a | oa] * g a := by
        gcongr
        exact tsum_probOutput_le_one
    _ = C + ∑' a, Pr[= a | oa] * g a := by rw [one_mul]

/-- `ENNReal` form of `tvDist_bind_left_le`: the lifted TV distance of a bind over a
shared base is at most the base-averaged lifted TV distance of the continuations. -/
lemma ofReal_tvDist_bind_le_tsum {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β) :
    ENNReal.ofReal (tvDist (oa >>= f) (oa >>= g)) ≤
      ∑' x, Pr[= x | oa] * ENNReal.ofReal (tvDist (f x) (g x)) := by
  refine le_trans (ENNReal.ofReal_le_ofReal (tvDist_bind_left_le oa f g)) ?_
  have h_sum_ne_top : (∑' x : α, Pr[= x | oa]) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsum_probOutput_le_one
  have h_summable : Summable fun x : α => Pr[= x | oa].toReal * tvDist (f x) (g x) :=
    Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
      (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _))
      (ENNReal.summable_toReal h_sum_ne_top)
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun x => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)) h_summable]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal probOutput_ne_top]

omit [SampleableType Stmt] in
/-- One-attempt unfolding of the reprogramming loop's cache-level run. -/
lemma run_progSignBody_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (c : (M × Commit →ₒ Chal).QueryCache) :
    (progSignBody ids M pk sk msg (n + 1)).run c =
      ids.commit pk sk >>= fun ws =>
        uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
            | none => (progSignBody ids M pk sk msg n).run (c.cacheQuery (msg, ws.1) ch) := by
  simp only [progSignBody, progSignAttempt, bind_assoc, StateT.run_bind,
    OracleComp.liftM_run_StateT, pure_bind, StateT.run_modify]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => rfl
  | none => rfl

omit [SampleableType Stmt] in
/-- One-attempt unfolding of the real signing loop's cache-level run under the caching
random oracle: commit, take one `roStep` at the commitment point, respond against the
returned challenge, and either return or recurse on the post-step cache. -/
lemma run_simulateQ_fsAbortSignLoop_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (c : (M × Commit →ₒ Chal).QueryCache) :
    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
      (fsAbortSignLoop ids M pk sk msg (n + 1))).run c =
      ids.commit pk sk >>= fun ws =>
        roStep M c (msg, ws.1) >>= fun chc =>
          ids.respond pk sk ws.2 chc.1 >>= fun oz =>
            match oz with
            | some z => pure (some (ws.1, z), chc.2)
            | none =>
                (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
                    (randomOracle : QueryImpl (M × Commit →ₒ Chal)
                      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
                  (fsAbortSignLoop ids M pk sk msg n)).run chc.2 := by
  simp only [fsAbortSignLoop, fsAbortSignAttempt, simulateQ_bind,
    roSim.simulateQ_HasQuery_query, bind_assoc, StateT.run_bind]
  rw [roSim.run_liftM, bind_map_left]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  rw [randomOracle_run_eq_roStep]
  refine congrArg (roStep M c (msg, w) >>= ·) (funext fun chc => ?_)
  rw [roSim.run_liftM, bind_map_left]
  refine congrArg (ids.respond pk sk st chc.1 >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => rfl
  | none => rfl

/-! ### The within-signing-query collision budget -/

/-- Collision budget of one signing query of the Sign → Prog hop, as a function of the
attempt budget `n` and the starting cache size `N`: attempt `a` is reached with
probability at most `p ^ a` and collides with a cached point with probability at most
`(N + a) · ε`. -/
noncomputable def signCollisionBound (ε p : ℝ) (n : ℕ) (N : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal ε * ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ a * (N + a)

@[simp]
lemma signCollisionBound_zero (ε p : ℝ) (N : ℝ≥0∞) :
    signCollisionBound ε p 0 N = 0 := by
  simp [signCollisionBound]

lemma signCollisionBound_succ (ε p : ℝ) (n : ℕ) (N : ℝ≥0∞) :
    signCollisionBound ε p (n + 1) N =
      N * ENNReal.ofReal ε +
        ENNReal.ofReal p * signCollisionBound ε p n (N + 1) := by
  have h : ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ (a + 1) * (N + ↑(a + 1)) =
      ENNReal.ofReal p * ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ a * (N + 1 + ↑a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    push_cast
    ring
  rw [signCollisionBound, signCollisionBound, Finset.sum_range_succ', h]
  push_cast
  ring

lemma signCollisionBound_mono (ε p : ℝ) (n : ℕ) {N N' : ℝ≥0∞} (h : N ≤ N') :
    signCollisionBound ε p n N ≤ signCollisionBound ε p n N' := by
  unfold signCollisionBound
  gcongr

/-- Splitting of the collision budget into a state-free part and a part linear in the
starting cache size, matching the `ζ + R s · β` query-slack shape of
`OracleComp.ProgramLogic.Relational.expectedQuerySlack_expected_resource_le`. -/
lemma signCollisionBound_eq (ε p : ℝ) (n : ℕ) (N : ℝ≥0∞) :
    signCollisionBound ε p n N =
      ENNReal.ofReal ε * ∑ a ∈ Finset.range n, (a : ℝ≥0∞) * ENNReal.ofReal p ^ a +
        N * (ENNReal.ofReal ε * ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ a) := by
  rw [signCollisionBound]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ### Per-attempt collision and abort bounds -/

omit [SampleableType Stmt] in
/-- Aggregate per-attempt abort bound: the commit-averaged probability that a fresh
uniform challenge is refused equals the abort probability of one honest execution. -/
lemma tsum_probOutput_commit_mul_abort_le (pk : Stmt) (sk : Wit) {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
        Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch]
      ≤ ENNReal.ofReal p_abort := by
  classical
  refine le_trans (le_of_eq ?_) hAbort
  rw [IdenSchemeWithAbort.honestExecution, probOutput_bind_eq_tsum]
  refine tsum_congr fun ws => ?_
  obtain ⟨cm, st⟩ := ws
  congr 1
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun ch => ?_
  congr 1
  rw [probOutput_bind_eq_tsum, tsum_eq_single (none : Option Resp) ?_]
  · simp [probOutput_pure]
  · rintro (_ | z) hb
    · exact absurd rfl hb
    · simp [probOutput_pure]

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq M] in
/-- Commitment-guessing bound for cache hits: under a pointwise commitment-guessing
bound `ε`, one commit lands on a cached point of `c` at message `msg` with probability
at most `enncard c · ε`. -/
lemma probEvent_commit_hit_le (pk : Stmt) (sk : Wit) {ε : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (msg : M) (c : (M × Commit →ₒ Chal).QueryCache) :
    Pr[fun ws : Commit × PrvState => c (msg, ws.1) ≠ none | ids.commit pk sk]
      ≤ QueryCache.enncard c * ENNReal.ofReal ε := by
  classical
  let commitDist : ProbComp Commit := Prod.fst <$> ids.commit pk sk
  let hit : Commit → Prop := fun w => c (msg, w) ≠ none
  let S : Finset Commit := (finSupport commitDist).filter hit
  have h_event :
      Pr[fun ws : Commit × PrvState => c (msg, ws.1) ≠ none | ids.commit pk sk]
        = Pr[hit | commitDist] := by
    simp [commitDist, hit]
  have h_sum : Pr[hit | commitDist] = ∑ w ∈ S, Pr[= w | commitDist] := by
    simp [S, probEvent_eq_sum_filter_finSupport]
  have h_sum_le : ∑ w ∈ S, Pr[= w | commitDist] ≤ ∑ w ∈ S, ENNReal.ofReal ε :=
    Finset.sum_le_sum fun w _ => hGuess w
  have h_card_le : (S.card : ℝ≥0∞) ≤ QueryCache.enncard c := by
    have hex : ∀ w : ↑(S : Set Commit), ∃ v : Chal, c (msg, w.1) = some v := fun w =>
      Option.ne_none_iff_exists'.mp ((Finset.mem_filter.mp w.2).2)
    let cacheEntryOfHit : ↑(S : Set Commit) → c.toSet := fun w =>
      ⟨⟨(msg, w.1), Classical.choose (hex w)⟩, Classical.choose_spec (hex w)⟩
    have h_inj : Function.Injective cacheEntryOfHit := by
      intro w₁ w₂ h
      apply Subtype.ext
      have hdomain : ((msg, w₁.1) : M × Commit) = (msg, w₂.1) :=
        congrArg (fun x : c.toSet => x.1.1) h
      exact congrArg Prod.snd hdomain
    have henc : (S : Set Commit).encard ≤ c.toSet.encard := by
      simpa using Function.Embedding.encard_le ⟨cacheEntryOfHit, h_inj⟩
    have henc_nat : (S.card : ℕ∞) ≤ c.toSet.encard := by simpa using henc
    exact ENat.toENNReal_mono henc_nat
  calc Pr[fun ws : Commit × PrvState => c (msg, ws.1) ≠ none | ids.commit pk sk]
      = Pr[hit | commitDist] := h_event
    _ = ∑ w ∈ S, Pr[= w | commitDist] := h_sum
    _ ≤ ∑ w ∈ S, ENNReal.ofReal ε := h_sum_le
    _ = (S.card : ℝ≥0∞) * ENNReal.ofReal ε := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ QueryCache.enncard c * ENNReal.ofReal ε := mul_le_mul' h_card_le le_rfl

/-! ### Deferred-sampling read step (lazy ghost firing)

The eager ghost handler `ghostHybridImpl … true` pre-populates the ghost cache during
signing and reads it deterministically, so an adversarial read at a ghost point flips the
bad flag with mass `1`. That deterministic flip is *not* amortized by `enncard · ε`, which
is why the charged-step premise of `probEvent_bad_simulateQ_run_le_expectedQuerySlack`
fails for the eager run.

The fix is deferred sampling: postpone each rejected attempt's commitment draw to read
time. A read at point `(msg, w')` then redraws the `pending` deferred commitments and fires
iff one of them equals `w'`. Under the pointwise guessing bound `hGuess`, each redraw lands
on `w'` with probability `≤ ε`, so the union bound over `pending` redraws gives the per-read
charge `pending · ε` — exactly the `R s · ε` shape the accumulator's charged-step premise
demands, with `R s := enncard (ghost cache) = pending`. `lazyGhostFire` is that read step
and `probOutput_lazyGhostFire_true_le` is its charge bound. -/

/-- Deferred-sampling ghost read: draw `pending` fresh commitments and fire iff some draw
equals the adversary's read point `w'`. The lazy counterpart of the eager ghost-domain
membership test in `ghostHybridImpl … true`, with the rejected attempts' commitment draws
postponed to read time. -/
noncomputable def lazyGhostFire (pk : Stmt) (sk : Wit) (w' : Commit) :
    ℕ → ProbComp Bool
  | 0 => pure false
  | n + 1 => do
    let w ← Prod.fst <$> ids.commit pk sk
    let b ← lazyGhostFire pk sk w' n
    pure (decide (w = w') || b)

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] in
/-- Boolean-or read shape: appending one fresh `decide (w = w')` flag to a Boolean draw
raises the firing probability by at most `1` (when the fresh flag is set) over the residual
draw. The per-summand step of `probOutput_lazyGhostFire_true_le`. -/
lemma probOutput_bind_or_pure_le (q : Bool) (mb : ProbComp Bool) :
    Pr[= true | mb >>= fun b => pure (q || b)] ≤ (if q then 1 else 0) + Pr[= true | mb] := by
  cases q with
  | true => simp
  | false => simp

omit [SampleableType Stmt] [SampleableType Chal] in
/-- **Charged-step bound for the lazy ghost read.** Under the pointwise commitment-guessing
bound `ε`, the deferred-sampling read `lazyGhostFire … pending` fires with probability at
most `pending · ε`. This is the `R s · ε` charge that makes the charged-step premise of
`probEvent_bad_simulateQ_run_le_expectedQuerySlack` *true* for the lazy run (with
`R s := enncard (ghost cache) = pending`), in contrast to the eager run's deterministic
flip. Proved by a union bound over the `pending` redraws, each bounded by `hGuess`. -/
lemma probOutput_lazyGhostFire_true_le (pk : Stmt) (sk : Wit) {ε : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (w' : Commit) :
    ∀ n : ℕ, Pr[= true | lazyGhostFire ids pk sk w' n] ≤ (n : ℝ≥0∞) * ENNReal.ofReal ε := by
  intro n
  induction n with
  | zero => simp [lazyGhostFire]
  | succ n ih =>
      have hbody : Pr[= true | lazyGhostFire ids pk sk w' (n + 1)] ≤
          Pr[= w' | Prod.fst <$> ids.commit pk sk] +
            Pr[= true | lazyGhostFire ids pk sk w' n] := by
        change Pr[= true | (Prod.fst <$> ids.commit pk sk) >>= fun w =>
            lazyGhostFire ids pk sk w' n >>= fun b => pure (decide (w = w') || b)] ≤ _
        rw [probOutput_bind_eq_tsum]
        calc (∑' w : Commit, Pr[= w | Prod.fst <$> ids.commit pk sk] *
              Pr[= true | lazyGhostFire ids pk sk w' n >>=
                fun b => pure (decide (w = w') || b)])
            ≤ ∑' w : Commit, Pr[= w | Prod.fst <$> ids.commit pk sk] *
                ((if w = w' then 1 else 0) +
                  Pr[= true | lazyGhostFire ids pk sk w' n]) := by
              refine ENNReal.tsum_le_tsum fun w => ?_
              gcongr
              have h := probOutput_bind_or_pure_le (decide (w = w'))
                (lazyGhostFire ids pk sk w' n)
              simp only [decide_eq_true_eq] at h
              exact h
          _ = (∑' w : Commit, Pr[= w | Prod.fst <$> ids.commit pk sk] *
                  (if w = w' then 1 else 0)) +
                (∑' w : Commit, Pr[= w | Prod.fst <$> ids.commit pk sk]) *
                  Pr[= true | lazyGhostFire ids pk sk w' n] := by
              rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
              exact tsum_congr fun w => by ring
          _ ≤ Pr[= w' | Prod.fst <$> ids.commit pk sk] +
                Pr[= true | lazyGhostFire ids pk sk w' n] := by
              gcongr
              · rw [tsum_eq_single w' (by intro b hb; simp [hb]), if_pos rfl, mul_one]
              · exact mul_le_of_le_one_left (zero_le') tsum_probOutput_le_one
      refine hbody.trans ?_
      push_cast
      rw [add_mul, one_mul, add_comm]
      gcongr
      exact hGuess w'

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq M] in
/-- The lazy ghost read fires with probability at most `enncard gh · ε`, where the deferred
attempt count is the ghost cache size. The `R s · ε` charge in the shape consumed by the
accumulator's charged-step premise (`R s := QueryCache.enncard`). -/
lemma probOutput_lazyGhostFire_true_le_enncard (pk : Stmt) (sk : Wit) {ε : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (w' : Commit) (gh : (M × Commit →ₒ Chal).QueryCache)
    (hpending : (gh.toSet.encard.toNat : ℝ≥0∞) ≤ QueryCache.enncard gh) :
    Pr[= true | lazyGhostFire ids pk sk w' gh.toSet.encard.toNat]
      ≤ QueryCache.enncard gh * ENNReal.ofReal ε := by
  refine (probOutput_lazyGhostFire_true_le ids pk sk hGuess w' _).trans ?_
  gcongr

/-! ### Deferred-sampling (lazy) ghost-instrumented hybrid handler

`lazyGhostHybridImpl` is the deferred-sampling counterpart of `ghostHybridImpl … true`.
It carries the *same* layered-cache-plus-flag state `GhostState`, and signs with the same
`ghostSignBody` (so the ghost layer records the same per-attempt programmings and grows by
the same amount). The only change is the adversarial random-oracle read step: instead of
the eager deterministic ghost lookup that flips the bad flag with mass `1`, the read draws
`lazyGhostFire` over the *pending count* `enncard (ghost cache)` and fires the bad flag with
probability `≤ enncard (ghost cache) · ε` (the deferred-sampling charge
`probOutput_lazyGhostFire_true_le_enncard`). The answer to the adversary is taken from the
real layer via `roStep`, independently of the fire draw. This is the handler for which the
charged-step premise of `probEvent_bad_simulateQ_run_le_expectedQuerySlack` holds. -/

/-- Deferred-sampling ghost-instrumented hybrid handler: signs with `ghostSignBody`, answers
uniform queries by forwarding, and answers adversarial random-oracle reads from the real
layer while firing the bad flag lazily (`lazyGhostFire` over the pending ghost count). -/
noncomputable def lazyGhostHybridImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (GhostState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      lazyGhostFire ids pk sk mc.2 s.1.1.2.toSet.encard.toNat >>= fun fired =>
        (fun cu => (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || fired))) <$> roStep M s.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1, ((alc.2, msg :: s.1.2), s.2))) <$>
        (ghostSignBody ids M pk sk msg maxAttempts).run s.1.1

/-! ### The two body-level cores of the Sign → Prog hop -/

omit [SampleableType Stmt] in
/-- **Within-signing-query TV induction for the Sign → Prog hop.** From a shared
starting cache, the real signing loop (live caching random oracle) and the
all-attempts-reprogramming loop are within total-variation distance
`ε · ∑_{a<n} p ^ a · (|c| + a)`: the two loops agree until an attempt commits to an
already-cached point, attempt `a` is reached only after `a` fresh-challenge rejections
(probability at most `p ^ a` each, by `hAbort`), and at that point the cache holds at
most `|c| + a` entries, each guessed with probability at most `ε` (`hGuess`). -/
lemma ofReal_tvDist_run_fsAbortSignLoop_progSignBody_le (pk : Stmt) (sk : Wit) (msg : M)
    {ε p_abort : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (c : (M × Commit →ₒ Chal).QueryCache),
      ENNReal.ofReal (tvDist
        ((simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          (fsAbortSignLoop ids M pk sk msg n)).run c)
        ((progSignBody ids M pk sk msg n).run c))
        ≤ signCollisionBound ε p_abort n (QueryCache.enncard c) := by
  intro n
  induction n with
  | zero =>
      intro c
      simp [fsAbortSignLoop, progSignBody]
  | succ n ih =>
      intro c
      classical
      rw [run_simulateQ_fsAbortSignLoop_succ, run_progSignBody_succ]
      refine le_trans (ofReal_tvDist_bind_le_tsum _ _ _) ?_
      set B' := signCollisionBound ε p_abort n (QueryCache.enncard c + 1) with hB'
      have key : ∀ ws : Commit × PrvState,
          ENNReal.ofReal (tvDist
            (roStep M c (msg, ws.1) >>= fun chc =>
              ids.respond pk sk ws.2 chc.1 >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), chc.2)
                | none =>
                    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
                        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
                          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
                      (fsAbortSignLoop ids M pk sk msg n)).run chc.2)
            (uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                | none =>
                    (progSignBody ids M pk sk msg n).run (c.cacheQuery (msg, ws.1) ch)))
          ≤ (if c (msg, ws.1) = none then 0 else 1) +
              Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                B' := by
        intro ws
        cases hc : c (msg, ws.1) with
        | some v =>
            rw [if_neg (by simp)]
            exact le_add_right (ENNReal.ofReal_le_one.mpr (tvDist_le_one _ _))
        | none =>
            rw [if_pos rfl, zero_add, roStep_of_none M hc]
            simp only [bind_assoc, pure_bind]
            refine le_trans (ofReal_tvDist_bind_le_tsum _ _ _) ?_
            have hch : ∀ ch : Chal,
                ENNReal.ofReal (tvDist
                  (ids.respond pk sk ws.2 ch >>= fun oz =>
                    match oz with
                    | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                    | none =>
                        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
                            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
                              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
                          (fsAbortSignLoop ids M pk sk msg n)).run
                            (c.cacheQuery (msg, ws.1) ch))
                  (ids.respond pk sk ws.2 ch >>= fun oz =>
                    match oz with
                    | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                    | none =>
                        (progSignBody ids M pk sk msg n).run
                          (c.cacheQuery (msg, ws.1) ch)))
                ≤ Pr[= none | ids.respond pk sk ws.2 ch] * B' := by
              intro ch
              refine le_trans (ofReal_tvDist_bind_le_tsum _ _ _) ?_
              calc ∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
                    ENNReal.ofReal (tvDist _ _)
                  ≤ ∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
                      (if oz = none then B' else 0) := by
                    refine ENNReal.tsum_le_tsum fun oz => mul_le_mul_right ?_ _
                    cases oz with
                    | some z => simp
                    | none =>
                        rw [if_pos rfl]
                        exact le_trans (ih (c.cacheQuery (msg, ws.1) ch))
                          (signCollisionBound_mono ε p_abort n
                            (QueryCache.enncard_cacheQuery_le c (msg, ws.1) ch))
                _ = Pr[= none | ids.respond pk sk ws.2 ch] * B' := by
                    rw [tsum_eq_single (none : Option Resp)
                      fun oz hoz => by simp [hoz]]
                    simp
            calc ∑' ch : Chal, Pr[= ch | uniformSample Chal] *
                  ENNReal.ofReal (tvDist _ _)
                ≤ ∑' ch : Chal, Pr[= ch | uniformSample Chal] *
                    (Pr[= none | ids.respond pk sk ws.2 ch] * B') :=
                  ENNReal.tsum_le_tsum fun ch => mul_le_mul_right (hch ch) _
              _ = Pr[= none | uniformSample Chal >>= fun ch =>
                    ids.respond pk sk ws.2 ch] * B' := by
                  rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
                  exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ENNReal.ofReal (tvDist _ _)
          ≤ ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              ((if c (msg, ws.1) = none then 0 else 1) +
                Pr[= none | uniformSample Chal >>= fun ch =>
                  ids.respond pk sk ws.2 ch] * B') :=
            ENNReal.tsum_le_tsum fun ws => mul_le_mul_right (key ws) _
        _ = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (if c (msg, ws.1) = none then 0 else 1)) +
            ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * B') := by
            simp_rw [mul_add]
            exact ENNReal.tsum_add
        _ ≤ QueryCache.enncard c * ENNReal.ofReal ε + ENNReal.ofReal p_abort * B' := by
            refine add_le_add ?_ ?_
            · refine le_trans (le_of_eq ?_)
                (probEvent_commit_hit_le ids M pk sk hGuess msg c)
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun ws => ?_
              by_cases h : c (msg, ws.1) = none <;> simp [h]
            · calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                    (Pr[= none | uniformSample Chal >>= fun ch =>
                      ids.respond pk sk ws.2 ch] * B')
                  = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                      Pr[= none | uniformSample Chal >>= fun ch =>
                        ids.respond pk sk ws.2 ch]) * B' := by
                    rw [← ENNReal.tsum_mul_right]
                    exact tsum_congr fun ws => (mul_assoc _ _ _).symm
                _ ≤ ENNReal.ofReal p_abort * B' :=
                    mul_le_mul_left
                      (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _
        _ = signCollisionBound ε p_abort (n + 1) (QueryCache.enncard c) :=
            (signCollisionBound_succ ε p_abort n (QueryCache.enncard c)).symm

omit [SampleableType Stmt] in
/-- **Expected cache growth of the reprogramming loop.** Each attempt of `progSignBody`
programs at most one new cache point and the loop continues only on a fresh-challenge
rejection, so the expected size of the final cache is at most `|c| + ∑_{a<n} p ^ a`. -/
lemma tsum_probOutput_run_progSignBody_mul_enncard_le (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (c : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= z | (progSignBody ids M pk sk msg n).run c] * QueryCache.enncard z.2
        ≤ QueryCache.enncard c + ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a := by
  intro n
  induction n with
  | zero =>
      intro c
      simp only [progSignBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro c
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a with hS
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ a =
          1 + ENNReal.ofReal p_abort * S := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => pow_succ' _ _
      rw [run_progSignBody_succ, tsum_probOutput_bind_mul]
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                | none =>
                    (progSignBody ids M pk sk msg n).run (c.cacheQuery (msg, ws.1) ch)] *
              QueryCache.enncard z.2)
          ≤ (QueryCache.enncard c + 1) +
              Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                S := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                | none =>
                    (progSignBody ids M pk sk msg n).run
                      (c.cacheQuery (msg, ws.1) ch)] *
                QueryCache.enncard z.2)
            ≤ (QueryCache.enncard c + 1) +
                Pr[= none | ids.respond pk sk ws.2 ch] * S := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          have h_oz : ∀ oz : Option Resp,
              (∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= z | (match oz with
                  | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                  | none =>
                      (progSignBody ids M pk sk msg n).run
                        (c.cacheQuery (msg, ws.1) ch) :
                  ProbComp (Option (Commit × Resp) ×
                    (M × Commit →ₒ Chal).QueryCache))] *
                  QueryCache.enncard z.2)
              ≤ (QueryCache.enncard c + 1) + (if oz = none then S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), add_zero, tsum_probOutput_pure_mul]
                exact QueryCache.enncard_cacheQuery_le c (msg, ws.1) ch
            | none =>
                rw [if_pos rfl]
                refine le_trans (ih (c.cacheQuery (msg, ws.1) ch)) ?_
                exact add_le_add_left
                  (QueryCache.enncard_cacheQuery_le c (msg, ws.1) ch) S
          refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_oz) ?_
          refine add_le_add_right (le_of_eq ?_) _
          rw [tsum_eq_single (none : Option Resp) fun oz hoz => by simp [hoz]]
          simp [mul_comm]
        refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ch) ?_
        refine add_le_add_right (le_of_eq ?_) _
        rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ws) ?_
      rw [hSucc]
      have : ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
          (Pr[= none | uniformSample Chal >>= fun ch =>
            ids.respond pk sk ws.2 ch] * S)
          ≤ ENNReal.ofReal p_abort * S := by
        calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * S)
            = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                Pr[= none | uniformSample Chal >>= fun ch =>
                  ids.respond pk sk ws.2 ch]) * S := by
              rw [← ENNReal.tsum_mul_right]
              exact tsum_congr fun ws => (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal p_abort * S :=
              mul_le_mul_left
                (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _
      calc QueryCache.enncard c + 1 +
            ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * S)
          ≤ QueryCache.enncard c + 1 + ENNReal.ofReal p_abort * S :=
            add_le_add_right this _
        _ = QueryCache.enncard c + (1 + ENNReal.ofReal p_abort * S) := by
            rw [add_assoc]

omit [SampleableType Stmt] in
/-- One-attempt unfolding of the ghost reprogramming loop's layered-cache run. -/
lemma run_ghostSignBody_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (re gh : (M × Commit →ₒ Chal).QueryCache) :
    (ghostSignBody ids M pk sk msg (n + 1)).run (re, gh) =
      ids.commit pk sk >>= fun ws =>
        uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z =>
                pure (some (ws.1, z),
                  (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
            | none =>
                (ghostSignBody ids M pk sk msg n).run (re, gh.cacheQuery (msg, ws.1) ch) := by
  simp only [ghostSignBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
    pure_bind]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => rfl
  | none => rfl

omit [SampleableType Stmt] in
/-- **Expected ghost-layer growth of the reprogramming loop.** Each rejected attempt of
`ghostSignBody` programs at most one new ghost-cache point; an accepted attempt only
*removes* a point from the ghost layer (`uncacheQuery`). The loop continues only on a
fresh-challenge rejection, so the expected size of the final ghost cache is at most
`|gh| + ∑_{a<n} p ^ a` — the deferred-attempt count that bounds the lazy ghost read. -/
lemma tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
        Pr[= z | (ghostSignBody ids M pk sk msg n).run (re, gh)] * QueryCache.enncard z.2.2
        ≤ QueryCache.enncard gh + ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a := by
  intro n
  induction n with
  | zero =>
      intro re gh
      simp only [ghostSignBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro re gh
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a with hS
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ a =
          1 + ENNReal.ofReal p_abort * S := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => pow_succ' _ _
      rw [run_ghostSignBody_succ, tsum_probOutput_bind_mul]
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : Option (Commit × Resp) ×
              ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z =>
                    pure (some (ws.1, z),
                      (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
                | none =>
                    (ghostSignBody ids M pk sk msg n).run
                      (re, gh.cacheQuery (msg, ws.1) ch)] *
              QueryCache.enncard z.2.2)
          ≤ (QueryCache.enncard gh + 1) +
              Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                S := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : Option (Commit × Resp) ×
                ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z =>
                    pure (some (ws.1, z),
                      (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
                | none =>
                    (ghostSignBody ids M pk sk msg n).run
                      (re, gh.cacheQuery (msg, ws.1) ch)] *
                QueryCache.enncard z.2.2)
            ≤ (QueryCache.enncard gh + 1) +
                Pr[= none | ids.respond pk sk ws.2 ch] * S := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          have h_oz : ∀ oz : Option Resp,
              (∑' z : Option (Commit × Resp) ×
                  ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
                Pr[= z | (match oz with
                  | some z =>
                      pure (some (ws.1, z),
                        (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
                  | none =>
                      (ghostSignBody ids M pk sk msg n).run
                        (re, gh.cacheQuery (msg, ws.1) ch) :
                  ProbComp (Option (Commit × Resp) ×
                    ((M × Commit →ₒ Chal).QueryCache ×
                      (M × Commit →ₒ Chal).QueryCache)))] *
                  QueryCache.enncard z.2.2)
              ≤ (QueryCache.enncard gh + 1) + (if oz = none then S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), add_zero, tsum_probOutput_pure_mul]
                exact le_trans (enncard_uncacheQuery_le M gh (msg, ws.1)) le_self_add
            | none =>
                rw [if_pos rfl]
                refine le_trans (ih re (gh.cacheQuery (msg, ws.1) ch)) ?_
                exact add_le_add_left
                  (QueryCache.enncard_cacheQuery_le gh (msg, ws.1) ch) S
          refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_oz) ?_
          refine add_le_add_right (le_of_eq ?_) _
          rw [tsum_eq_single (none : Option Resp) fun oz hoz => by simp [hoz]]
          simp [mul_comm]
        refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ch) ?_
        refine add_le_add_right (le_of_eq ?_) _
        rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ws) ?_
      rw [hSucc]
      have : ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
          (Pr[= none | uniformSample Chal >>= fun ch =>
            ids.respond pk sk ws.2 ch] * S)
          ≤ ENNReal.ofReal p_abort * S := by
        calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * S)
            = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                Pr[= none | uniformSample Chal >>= fun ch =>
                  ids.respond pk sk ws.2 ch]) * S := by
              rw [← ENNReal.tsum_mul_right]
              exact tsum_congr fun ws => (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal p_abort * S :=
              mul_le_mul_left
                (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _
      calc QueryCache.enncard gh + 1 +
            ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * S)
          ≤ QueryCache.enncard gh + 1 + ENNReal.ofReal p_abort * S :=
            add_le_add_right this _
        _ = QueryCache.enncard gh + (1 + ENNReal.ofReal p_abort * S) := by
            rw [add_assoc]

/-! ## Layered ghost-tagged NMA handler

The NMA bridge (`hybridSimRun_le_managedRun_verify`) couples the single-cache simulated
hybrid against the linked managed run.  The obstruction recorded there is that the single
hybrid cache does not, on its own, record whether a point entered by a *live RO read* or by
the *signing simulation's programming* (`signProgramCont`).  We resolve this exactly as in
the Prog → Trans hop: run the hybrid on an enriched, layered cache state
`((baseCache, ghostCache), signed)` that tags each entry as live-read (base) vs
signing-programmed (ghost).  The base oracles write live RO reads to `baseCache`; the
signing body's `signProgramCont` writes the accepted-transcript programming to `ghostCache`.

On that layered state the partition *is* a function of the state, so the overlay projection
`((base, ghost), signed) ↦ (overlayCache base ghost, signed)` back to the plain single-cache
hybrid is a per-step state projection in the sense of
`OracleComp.map_run_simulateQ_eq_of_query_map_eq`.  This section builds the layered handler
and proves that overlay projection (sub-lemma (a) of the bridge). -/

/-- Ghost-layer programming continuation: like `signProgramCont`, but the accepted
transcript's challenge is written to the *ghost* layer of a `(base, ghost)` cache pair.
An all-abort loop outcome produces no signature and no programming. -/
noncomputable def ghostSignProgramCont (msg : M) :
    Option (Commit × Chal × Resp) →
      StateT ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache)
        ProbComp (Option (Commit × Resp))
  | some (w, c, z) => do
    modify fun s => (s.1, s.2.cacheQuery (msg, w) c)
    pure (some (w, z))
  | none => pure none

/-- Signing body of the simulated hybrid on the layered cache: run the simulator loop
privately, programming the accepted transcript into the *ghost* layer (`ghostSignProgramCont`).
The base layer is untouched. -/
noncomputable def simGhostSignBody (pk : Stmt) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache)
      ProbComp (Option (Commit × Resp)) :=
  liftM (firstSome (sim pk) maxAttempts) >>= ghostSignProgramCont M msg

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Overlay projection of `ghostSignProgramCont`: overlaying the ghost layer onto the base
layer turns the ghost-layer programming into an ordinary cache programming, recovering
`signProgramCont` on the overlaid cache. -/
lemma run_ghostSignProgramCont_overlay (msg : M)
    (oz : Option (Commit × Chal × Resp))
    (re gh : (M × Commit →ₒ Chal).QueryCache) :
    (fun zs : Option (Commit × Resp) ×
        ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (zs.1, overlayCache M zs.2.1 zs.2.2)) <$>
      (ghostSignProgramCont M msg oz).run (re, gh) =
    (signProgramCont M msg oz).run (overlayCache M re gh) := by
  cases oz with
  | none => simp [ghostSignProgramCont, signProgramCont]
  | some wcz =>
      obtain ⟨w, c, z⟩ := wcz
      simp only [ghostSignProgramCont, signProgramCont, StateT.run_bind, StateT.run_modify,
        pure_bind, StateT.run_pure, map_pure, overlayCache_cacheQuery_ghost]

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Overlay projection of `simGhostSignBody`: overlaying the ghost layer onto the base layer
recovers `simSignBody` on the overlaid cache. The simulator loop is run identically; only
the destination layer of the accepted programming differs, which the overlay erases. -/
lemma run_simGhostSignBody_overlay (pk : Stmt) (sk : Wit) (msg : M)
    (re gh : (M × Commit →ₒ Chal).QueryCache) :
    (fun zs : Option (Commit × Resp) ×
        ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (zs.1, overlayCache M zs.2.1 zs.2.2)) <$>
      (simGhostSignBody M maxAttempts sim pk msg).run (re, gh) =
    (simSignBody M maxAttempts sim pk sk msg).run (overlayCache M re gh) := by
  simp only [simGhostSignBody, simSignBody, StateT.run_bind, OracleComp.liftM_run_StateT,
    bind_assoc, pure_bind, map_bind]
  refine congrArg (firstSome (sim pk) maxAttempts >>= ·) (funext fun oz => ?_)
  exact run_ghostSignProgramCont_overlay M msg oz re gh

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Ghost-domain support fact for `simGhostSignBody`: every ghost-layer entry of an output
state is either an entry already present in the input ghost layer, or sits at a point whose
message component equals the signed message `msg`.  The base layer is never touched. -/
lemma simGhostSignBody_support_ghost (pk : Stmt) (msg : M)
    (re gh : (M × Commit →ₒ Chal).QueryCache)
    (z : Option (Commit × Resp) ×
      ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache))
    (hz : z ∈ support ((simGhostSignBody M maxAttempts sim pk msg).run (re, gh)))
    (q : M × Commit) (hq : z.2.2 q ≠ none) : gh q ≠ none ∨ q.1 = msg := by
  simp only [simGhostSignBody, StateT.run_bind, OracleComp.liftM_run_StateT, bind_assoc,
    pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
  obtain ⟨oz, -, hz⟩ := hz
  cases oz with
  | none =>
      simp only [ghostSignProgramCont, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl hq
  | some wcz =>
      obtain ⟨w, c, z'⟩ := wcz
      simp only [ghostSignProgramCont, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp only at hq
      by_cases hqw : q = (msg, w)
      · exact Or.inr (by simp [hqw])
      · exact Or.inl (by rwa [QueryCache.cacheQuery_of_ne _ _ hqw] at hq)

/-- State of the layered ghost-tagged NMA run: a base/ghost cache pair together with the
signed-message list. (No bad flag is needed for the NMA bridge: the coupling is exact, not
identical-until-bad.) -/
abbrev NmaGhostState (M Commit Chal : Type) : Type :=
  ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M

/-- Embed a base random-oracle cache (keyed by `M × Commit`) into the outer runtime cache of
the linked managed run, which is keyed by the sum spec `unifSpec + (M × Commit →ₒ Chal)`. The
uniform-query slots are empty (the runtime forwards uniform queries through `unifFwdImpl`
without caching), and the random-oracle slots carry the base entries. This is the left
component of the linked-run projection `proj₂` for sub-lemma (b). -/
def baseEmbed (base : (M × Commit →ₒ Chal).QueryCache) :
    (unifSpec + (M × Commit →ₒ Chal)).QueryCache
  | .inl _ => none
  | .inr mc => base mc

omit [SampleableType Stmt] [DecidableEq Commit] [DecidableEq M] [SampleableType Chal] in
@[simp] lemma baseEmbed_inr (base : (M × Commit →ₒ Chal).QueryCache) (mc : M × Commit) :
    baseEmbed M base (.inr mc) = base mc := rfl

omit [SampleableType Stmt] [DecidableEq Commit] [DecidableEq M] [SampleableType Chal] in
@[simp] lemma baseEmbed_inl (base : (M × Commit →ₒ Chal).QueryCache)
    (n : unifSpec.Domain) : baseEmbed M base (.inl n) = none := rfl

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Embedding commutes with caching a random-oracle point: `baseEmbed` of a base cache
extended at `mc` equals the outer cache extended at the `.inr mc` slot. -/
lemma baseEmbed_cacheQuery (base : (M × Commit →ₒ Chal).QueryCache)
    (mc : M × Commit) (v : Chal) :
    baseEmbed M (base.cacheQuery mc v) =
      (baseEmbed M base).cacheQuery (.inr mc) v := by
  funext t
  cases t with
  | inl n =>
      rw [QueryCache.cacheQuery_of_ne _ _ (show (Sum.inl n : (unifSpec +
        (M × Commit →ₒ Chal)).Domain) ≠ Sum.inr mc by simp), baseEmbed_inl, baseEmbed_inl]
  | inr mc' =>
      by_cases h : mc' = mc
      · subst h; simp [baseEmbed, QueryCache.cacheQuery_self]
      · rw [baseEmbed_inr, QueryCache.cacheQuery_of_ne _ _ h,
          QueryCache.cacheQuery_of_ne _ _ (show (Sum.inr mc' : (unifSpec +
            (M × Commit →ₒ Chal)).Domain) ≠ Sum.inr mc by simp [h]), baseEmbed_inr]

/-- Layered ghost-tagged handler for the simulated hybrid.  Base oracles (uniform and the
caching random oracle) write live RO reads to the *base* layer, reading through the overlay
so that signing-programmed (ghost) points are visible to the adversary; the signing oracle
records the signed message and runs `simGhostSignBody`, writing the accepted-transcript
programming to the *ghost* layer. -/
noncomputable def ghostNmaImpl (pk : Stmt) (_sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (NmaGhostState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      match s.1.2 mc with
      | some v => pure (v, s)
      | none =>
          (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((cu.2, s.1.2), s.2))) <$> roStep M s.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (alc.1, (alc.2, msg :: s.2))) <$>
        (simGhostSignBody M maxAttempts sim pk msg).run s.1

omit [SampleableType Stmt] in
lemma ghostNmaImpl_run_unif (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : NmaGhostState M Commit Chal) :
    (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl

omit [SampleableType Stmt] in
lemma ghostNmaImpl_run_ro (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : NmaGhostState M Commit Chal) :
    (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inr mc))).run s =
      match s.1.2 mc with
      | some v => pure (v, s)
      | none =>
          (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((cu.2, s.1.2), s.2))) <$> roStep M s.1.1 mc := rfl

omit [SampleableType Stmt] in
lemma ghostNmaImpl_run_sign (pk : Stmt) (sk : Wit) (msg : M)
    (s : NmaGhostState M Commit Chal) :
    (ghostNmaImpl M maxAttempts sim pk sk (.inr msg)).run s =
      (fun alc : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (alc.1, (alc.2, msg :: s.2))) <$>
        (simGhostSignBody M maxAttempts sim pk msg).run s.1 := rfl

omit [SampleableType Stmt] in
/-- **Ghost-domain invariant for `ghostNmaImpl`.** Along any run of the layered NMA handler,
every ghost-layer entry's message component has been recorded in the signed list. This is the
NMA analogue of `ghostHybridImpl_preserves_signed_inv`: the base oracles never write the ghost
layer, and the signing oracle records the signed message before programming the ghost layer at
a point whose message component equals that signed message (`simGhostSignBody_support_ghost`).
This invariant is the gate for the linked-run coupling (sub-lemma (b)): it certifies that on a
random-oracle step a live read hits the base/outer layer, while the ghost layer only carries
signing-programmed points. -/
lemma ghostNmaImpl_preserves_signed_inv (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : NmaGhostState M Commit Chal)
    (hs : ∀ q : M × Commit, s.1.2 q ≠ none → q.1 ∈ s.2) :
    ∀ z ∈ support ((ghostNmaImpl M maxAttempts sim pk sk t).run s),
      ∀ q : M × Commit, z.2.1.2 q ≠ none → q.1 ∈ z.2.2 := by
  intro z hz
  rcases t with (n | mc) | msg
  · simp only [ghostNmaImpl, StateT.run_mk, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · simp only [ghostNmaImpl, StateT.run_mk] at hz
    cases hgh : s.1.2 mc with
    | some v =>
        simp only [hgh, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hs
    | none =>
        simp only [hgh, support_map] at hz
        obtain ⟨cu, -, rfl⟩ := hz
        exact hs
  · simp only [ghostNmaImpl, StateT.run_mk, support_map] at hz
    obtain ⟨alc, halc, rfl⟩ := hz
    intro q hq
    rcases simGhostSignBody_support_ghost M maxAttempts sim pk msg s.1.1 s.1.2 alc halc q hq
      with hgh | hmsg
    · exact List.mem_cons_of_mem _ (hs q hgh)
    · exact hmsg ▸ List.mem_cons_self

omit [SampleableType Stmt] in
/-- **Sub-lemma (a): overlay projection of the layered NMA handler.** Each step of the
layered ghost-tagged handler `ghostNmaImpl`, projected by overlaying the ghost layer onto the
base layer, equals the corresponding step of the plain single-cache hybrid handler
`hybridBaseImpl + hybridSignImpl simSignBody`. -/
lemma ghostNmaImpl_proj_hybrid (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : NmaGhostState M Commit Chal) :
    Prod.map id (fun g : NmaGhostState M Commit Chal =>
        (overlayCache M g.1.1 g.1.2, g.2)) <$>
        (ghostNmaImpl M maxAttempts sim pk sk t).run s =
      ((hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (simSignBody M maxAttempts sim pk sk)) t).run
        (overlayCache M s.1.1 s.1.2, s.2) := by
  rcases t with (n | mc) | msg
  · simp only [ghostNmaImpl, StateT.run_mk, QueryImpl.add_apply_inl, hybridBaseImpl,
      unifFwdImpl, QueryImpl.liftTarget_apply, Functor.map_map]
    rfl
  · refine Eq.trans ?_
      (hybridBaseImpl_run_ro M mc (overlayCache M s.1.1 s.1.2) s.2).symm
    rw [ghostNmaImpl_run_ro]
    cases hgh : s.1.2 mc with
    | some v =>
        rw [roStep_of_some M (overlayCache_apply_ghost_some (M := M) s.1.1 hgh)]
        simp
    | none =>
        cases hre : s.1.1 mc with
        | some v =>
            rw [roStep_of_some M hre, roStep_of_some M (show overlayCache M
              s.1.1 s.1.2 mc = some v by
                rw [overlayCache_apply_ghost_none (M := M) s.1.1 hgh, hre])]
            simp
        | none =>
            rw [roStep_of_none M hre, roStep_of_none M (show overlayCache M
              s.1.1 s.1.2 mc = none by
                rw [overlayCache_apply_ghost_none (M := M) s.1.1 hgh, hre])]
            simp [overlayCache_cacheQuery_real_of_ghost_none (M := M) s.1.1 hgh]
  · refine Eq.trans (b := (fun ac : Option (Commit × Resp) ×
        (M × Commit →ₒ Chal).QueryCache => (ac.1, (ac.2, msg :: s.2))) <$>
        (simSignBody M maxAttempts sim pk sk msg).run
          (overlayCache M s.1.1 s.1.2)) ?_ ?_
    · rw [ghostNmaImpl_run_sign,
        ← run_simGhostSignBody_overlay M maxAttempts sim pk sk msg s.1.1 s.1.2]
      refine (Functor.map_map _ _ _).trans (Eq.symm ?_)
      exact (Functor.map_map _ _ _).trans rfl
    · exact (hybridSignImpl_run M (simSignBody M maxAttempts sim pk sk) msg
        (overlayCache M s.1.1 s.1.2) s.2).symm

omit [SampleableType Stmt] in
/-- **Sub-lemma (a), full-run form.** The full simulated run of the layered ghost-tagged NMA
handler `ghostNmaImpl`, projected by overlaying the ghost layer onto the base layer, equals
the plain single-cache simulated hybrid run.  This lifts the per-step projection
`ghostNmaImpl_proj_hybrid` through `OracleComp.map_run_simulateQ_eq_of_query_map_eq`. -/
lemma map_run_simulateQ_ghostNmaImpl_overlay {β : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
      (M →ₒ Option (Commit × Resp))) β)
    (s : NmaGhostState M Commit Chal) :
    Prod.map id (fun g : NmaGhostState M Commit Chal =>
        (overlayCache M g.1.1 g.1.2, g.2)) <$>
        (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) oa).run s =
      (simulateQ (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (simSignBody M maxAttempts sim pk sk)) oa).run
        (overlayCache M s.1.1 s.1.2, s.2) :=
  map_run_simulateQ_eq_of_query_map_eq
    (ghostNmaImpl M maxAttempts sim pk sk)
    (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
      hybridSignImpl M (simSignBody M maxAttempts sim pk sk))
    (fun g => (overlayCache M g.1.1 g.1.2, g.2))
    (ghostNmaImpl_proj_hybrid M maxAttempts sim pk sk) oa s

omit [SampleableType Stmt] in
/-- **Sub-lemma (a) at the initial empty layered state.** Starting from the empty layered
cache `((∅, ∅), [])`, the overlay-projected layered run equals the plain single-cache hybrid
run started from `(∅, [])` (using `overlayCache _ ∅ = id` to simplify the projected initial
state). -/
lemma map_run_simulateQ_ghostNmaImpl_overlay_empty {β : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
      (M →ₒ Option (Commit × Resp))) β) :
    Prod.map id (fun g : NmaGhostState M Commit Chal =>
        (overlayCache M g.1.1 g.1.2, g.2)) <$>
        (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) oa).run ((∅, ∅), []) =
      (simulateQ (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (simSignBody M maxAttempts sim pk sk)) oa).run (∅, []) := by
  rw [map_run_simulateQ_ghostNmaImpl_overlay M maxAttempts sim pk sk oa ((∅, ∅), [])]
  simp only [overlayCache_empty]

end FiatShamirWithAbort
