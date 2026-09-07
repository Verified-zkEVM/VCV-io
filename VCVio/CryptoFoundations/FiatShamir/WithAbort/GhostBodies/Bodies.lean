/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort

/-!
# Ghost-layer machinery for Fiat-Shamir with aborts: Bodies

The first-success retry loops (`firstSome` and its distribution laws) and
the cache-level signing bodies of the CMA-to-NMA hybrid chain (`realSignBody`,
`progSignBody`, `transSignBody`, `simSignBody`). This module opens the hybrid
signing-body development and holds its overview.

## Overview

The development provides the cache-level signing bodies of the CMA-to-NMA
hybrid chain for the Fiat-Shamir-with-aborts transform, together with the
run-level hybrid handlers (`hybridBaseImpl`, `hybridSignImpl`) and the
ghost-layer presentation of the reprogramming bodies used by the Prog → Trans
hop:

* `ghostSignBody` acts on a two-layer cache, writing accepted transcripts to
  the real layer and rejected-attempt programmings to the ghost layer; the
  projections `run_ghostSignBody_overlay` and `run_ghostSignBody_fst` recover
  `progSignBody` and the accepted-only programming loop of `transSignBody`.
* `ghostHybridImpl` instruments the adversary's oracles over the layered cache
  with a monotone bad flag firing on adversarial reads of the ghost layer,
  with per-step projections onto both hybrid games
  (`ghostHybridImpl_proj_prog`, `ghostHybridImpl_proj_trans`) and the
  ghost-domain invariant `ghostHybridImpl_preserves_signed_inv`.

The hybrid experiment itself and the hop lemmas live in the
`FiatShamir.WithAbort.Security` modules.

## Module layout

The development is split along its phases, each module publicly importing its
predecessor: `Bodies` (retry loops and the four signing bodies), `GhostLayer`
(the two-layer cache presentation and the ghost-instrumented handlers),
`Projections` (projections onto both hybrid games and the ghost-domain
invariant), `BodyBounds` (the body-level collision and deferred-sampling
bounds), and `NMAHandler` (the layered ghost-tagged NMA handler).
-/

public section

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
@[expose] def firstSome {α : Type} (attempt : ProbComp (Option α)) : ℕ → ProbComp (Option α)
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
@[expose] noncomputable def realSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp)) :=
  simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
    (fsAbortSignLoop ids M pk sk msg maxAttempts)

/-- One signing attempt of the all-attempts-reprogramming hybrid: commit honestly, then
overwrite the cache at `(msg, w)` with a fresh uniform challenge before responding. -/
@[expose] noncomputable def progSignAttempt (pk : Stmt) (sk : Wit) (msg : M) :
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
@[expose] noncomputable def progSignBody (pk : Stmt) (sk : Wit) (msg : M) :
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
@[expose] noncomputable def signProgramCont (msg : M) :
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
@[expose] noncomputable def transSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp)) :=
  liftM (firstSome (ids.honestExecution pk sk) maxAttempts) >>= signProgramCont M msg

/-- Signing-oracle body of the simulated hybrid (Sim): as `transSignBody`, with the
per-attempt HVZK simulator replacing the honest execution. The secret key is unused, so
this body can be run by the NMA reduction. -/
@[expose] noncomputable def simSignBody (pk : Stmt) (_sk : Wit) (msg : M) :
    StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Option (Commit × Resp)) :=
  liftM (firstSome (sim pk) maxAttempts) >>= signProgramCont M msg

end FiatShamirWithAbort
