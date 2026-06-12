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
open scoped BigOperators

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

end FiatShamirWithAbort
