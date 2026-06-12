/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# EUF-CMA security of Fiat-Shamir with aborts

Statistical CMA-to-NMA reduction for the Fiat-Shamir-with-aborts transform,
following Theorem 3 of Barbosa et al. (CRYPTO 2023, ePrint 2023/246).
Instantiates `FiatShamir.signHashQueryBound` at the with-aborts signature type
and exposes `cmaToNmaLoss` plus `euf_cma_bound` / `euf_cma_bound_perfectHVZK`,
together with the hybrid game chain (`hybridExpAtKey` over the signing bodies
`realSignBody`, `progSignBody`, `transSignBody`, `simSignBody`) that structures
the proof.

The quantitative parameters `ε` (per-key commitment-guessing probability),
`p_abort` (per-attempt abort probability), and `δ` (key-regularity failure
probability) are tied to the identification scheme by explicit hypotheses on a
"good key" event, mirroring the event `Γ` of the paper's Lemma 1: `δ` bounds
the probability that key generation falls outside the event, and `ε`/`p_abort`
bound the per-key quantities pointwise on it.

The scheme-specific NMA-to-hard-problem reduction lives with each concrete
scheme (e.g. `MLDSA.nma_security`).
-/

universe u v

open OracleComp OracleSpec
open scoped BigOperators

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

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

section EUF_CMA

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

/-- The classical ROM statistical loss of the Fiat-Shamir-with-aborts CMA-to-NMA
reduction (after Theorem 3, CRYPTO 2023), for a per-attempt HVZK simulator:

`L = 2·qS·(qH+1)·ε/(1-p) + qS·ε·(qS+1)/(2·(1-p)²) + qS·ζ_zk/(1-p) + δ`

where:
- `qS` / `qH`: signing-oracle / adversarial random-oracle query bounds;
- `ε`: per-key commitment-guessing probability bound (on good keys);
- `p`: per-key, per-attempt abort probability bound (on good keys), for both the honest
  prover and the simulator;
- `ζ_zk`: total-variation error of the HVZK simulator for one signing **attempt**, over
  optional transcripts (`none` = abort), as in `IdenSchemeWithAbort.HVZK`;
- `δ`: probability that key generation falls outside the good-key event.

The first term pays for reprogramming collisions with adversarial hash queries (both in
the all-attempts-reprogram hybrid and in the accepted-only-reprogram hybrid, hence the
factor 2; the `qH + 1` accounts for the final verification query). The second term pays
for collisions among the signing oracle's own commitments. The third term glues the
per-attempt simulator across the restart loop, whose expected length is at most
`1/(1-p)` (see `tvDist_firstSome_le_geometric`); a simulator for the accepted-transcript
distribution itself (the paper's acHVZK notion) would shave this `1/(1-p)` factor. -/
noncomputable def cmaToNmaLoss (qS qH : ℕ) (ε p ζ_zk δ : ℝ) (_hp : p < 1) : ℝ :=
  2 * qS * (qH + 1) * ε / (1 - p) +
  qS * ε * (qS + 1) / (2 * (1 - p) ^ 2) +
  qS * ζ_zk / (1 - p) +
  δ

/-- The per-key part of `cmaToNmaLoss`: the statistical loss of the three signing-oracle
hybrid hops at a fixed good key pair. `cmaToNmaLoss` is this quantity plus the
key-regularity failure probability `δ`. -/
noncomputable def perKeyLoss (qS qH : ℕ) (ε p ζ_zk : ℝ) : ℝ :=
  2 * qS * (qH + 1) * ε / (1 - p) +
  qS * ε * (qS + 1) / (2 * (1 - p) ^ 2) +
  qS * ζ_zk / (1 - p)

lemma cmaToNmaLoss_eq_perKeyLoss_add (qS qH : ℕ) (ε p ζ_zk δ : ℝ) (hp : p < 1) :
    cmaToNmaLoss qS qH ε p ζ_zk δ hp = perKeyLoss qS qH ε p ζ_zk + δ := rfl

section scaffold

variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
variable (adv : SignatureAlg.unforgeableAdv
  (FiatShamirWithAbort
    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))

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

omit [SampleableType Stmt] in
/-- **Per-signing-query core of the Trans → Sim hop.** From any shared starting cache,
the accepted-only-reprogramming body and the simulated body are within total-variation
distance `ζ_zk · (1 + q + ⋯ + q^(maxAttempts-1)) ≤ ζ_zk / (1 - q)` on their joint
output-and-cache distribution, where `ζ_zk` bounds the per-attempt HVZK error and `q`
the simulator's per-attempt abort probability.

The cache programming is the same deterministic continuation on both sides
(`signProgramCont`), so the bound reduces to `tvDist_firstSome_le_geometric` on the
private restart loops. -/
lemma tvDist_run_transSignBody_simSignBody_le
    (pk : Stmt) (sk : Wit) (hrel : rel pk sk = true) (msg : M)
    {ζ_zk : ℝ} (hhvzk : ids.HVZK sim ζ_zk)
    {q : ℝ} (hq : Pr[= none | sim pk].toReal ≤ q) (hq0 : 0 ≤ q)
    (s : (M × Commit →ₒ Chal).QueryCache) :
    tvDist (StateT.run (transSignBody ids M maxAttempts pk sk msg) s)
        (StateT.run (simSignBody M maxAttempts sim pk sk msg) s) ≤
      ζ_zk * ∑ j ∈ Finset.range maxAttempts, q ^ j := by
  have hcore : tvDist (firstSome (ids.honestExecution pk sk) maxAttempts)
      (firstSome (sim pk) maxAttempts) ≤
        ζ_zk * ∑ j ∈ Finset.range maxAttempts, q ^ j :=
    tvDist_firstSome_le_geometric (ids.honestExecution pk sk) (sim pk)
      (hhvzk pk sk hrel) hq hq0 maxAttempts
  have hrw : ∀ (loop : ProbComp (Option (Commit × Chal × Resp))),
      StateT.run (liftM loop >>= signProgramCont M msg) s =
        loop >>= fun r => StateT.run (signProgramCont M msg r) s := by
    intro loop
    simp [StateT.run_bind]
  rw [transSignBody, simSignBody, hrw, hrw]
  exact le_trans (tvDist_bind_right_le _ _ _) hcore

/-! ## The hybrid experiment -/

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

/-- The hybrid unforgeability experiment at a fixed key pair: run the adversary with the
base handlers and the given signing body, then verify the forgery under the final cache
and apply the freshness check. Instantiating `signBody` with `realSignBody`,
`progSignBody`, `transSignBody`, and `simSignBody` yields the games G₀ — G₃ of the
CMA-to-NMA hybrid chain. -/
noncomputable def hybridExpAtKey
    (signBody : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp)))
    (pk : Stmt) : ProbComp Bool := do
  let ((msg, σ), (cache, signed)) ← StateT.run
    (simulateQ
      (hybridBaseImpl (Commit := Commit) (Chal := Chal) M + hybridSignImpl M signBody)
      (adv.main pk)) (∅, [])
  let ok ← StateT.run'
    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
      ((FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts).verify pk msg σ)) cache
  pure (decide (msg ∉ signed) && ok)

/-! ## Hop lemmas

Each hop is stated per key pair, under pointwise hypotheses at that key; the good-key
event and `δ` enter only once, in the final averaging over `hr.gen`. -/

/-- G₀ bridge: at every key pair produced by key generation, the real-signing hybrid
experiment reproduces the success probability of the standard unforgeability experiment
`SignatureAlg.unforgeableExp` under `runtime M`.

Distributional content: the runtime's `withStateOracle randomOracle` semantics of the
experiment (with its `WriterT` signing log) coincides with the single-cache-layer
presentation, with the `WriterT` log projected to the signed-message list. The proof is
a `simulateQ` commutation argument in the style of `roSim.run'_liftM_bind` and the
correctness proof in `FiatShamirWithAbort.correct`. -/
lemma probOutput_unforgeableExp_eq_hybridExpAtKey_real :
    Pr[= true | SignatureAlg.unforgeableExp (runtime M) adv] =
      Pr[= true | do
        let (pk, sk) ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (realSignBody ids M maxAttempts pk sk) pk] := by
  sorry

/-- Hop G₀ → G₁ (Sign → Prog) at a fixed key: replacing the caching hash of each signing
attempt by overwrite-reprogramming with a fresh challenge costs at most

`qS·ε·((qS+1)/(2·(1-p)²) + (qH+1)/(1-p))`.

Distributional content (identical-until-bad): the two games agree unless some signing
attempt commits to a point `(msg, w)` already present in the cache. Conditioned on good
keys, each attempt's commitment is `ε`-guessable (`hGuess`), the cache holds at most
`qH + 1` adversarial entries plus the entries of previous signing attempts, and the
expected number of attempts per signing query is at most `1/(1-p)` (`hAbort`, via
`sign_expectedQueries_le_geometric`). Intended vehicle:
`tvDist_simulateQ_le_probEvent_bad` (the fundamental lemma in
`ProgramLogic/Relational/SimulateQ.lean`) with the bad event tracked on the hybrid
state, plus the expected-attempt-count machinery of `WithAbort/ExpectedCost.lean`. -/
lemma probOutput_hybridExpAtKey_real_le_prog
    (qS qH : ℕ) (ε p_abort : ℝ) (hp : p_abort < 1)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (realSignBody ids M maxAttempts pk sk) pk] ≤
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (progSignBody ids M pk sk · maxAttempts) pk] +
        ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
          qS * (qH + 1) * ε / (1 - p_abort)) := by
  sorry

/-- Hop G₁ → G₂ (Prog → Trans) at a fixed key: dropping the reprogramming of rejected
attempts (keeping only the accepted transcript's programming) costs at most
`qS·(qH+1)·ε/(1-p)`.

Distributional content (identical-until-bad): the games differ only on cache points
`(msg, w)` of rejected attempts, which in G₁ hold fresh uniform values and in G₂ are
absent (so a later adversary query samples them fresh — same distribution). The bad
event is the adversary querying such a point that an earlier of its `qH + 1` hash
queries had already fixed; each rejected attempt's commitment is `ε`-guessable, and the
expected number of rejected attempts per query is at most `1/(1-p)`. The deferred-
sampling step ("a never-again-touched programmed point is distributionally equal to an
unprogrammed point") is the part that needs a new framework lemma; see the lazy-vs-eager
sampling analysis in `OracleComp/QueryTracking/RandomOracle/`. -/
lemma probOutput_hybridExpAtKey_prog_le_trans
    (qS qH : ℕ) (ε p_abort : ℝ) (hp : p_abort < 1)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (progSignBody ids M pk sk · maxAttempts) pk] ≤
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (transSignBody ids M maxAttempts pk sk) pk] +
        ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
  sorry

omit [SampleableType Stmt] in
/-- Hop G₂ → G₃ (Trans → Sim) at a fixed key: replacing the private honest-execution
loop by the per-attempt HVZK simulator loop costs at most `qS·ζ_zk/(1-p)`.

Distributional content: per signing query, `transSignBody` and `simSignBody` differ only
in the optional sampler driving `firstSome`; `tvDist_firstSome_le_geometric` bounds the
per-query gap by `ζ_zk · (1 + p + ⋯) ≤ ζ_zk/(1-p)` using `ids.HVZK sim ζ_zk` (`hhvzk`)
and the simulator abort bound (`hAbortSim`), uniformly in the shared starting cache
(`tvDist_run_transSignBody_simSignBody_le`). The per-query total-variation budget is
accumulated across the at-most-`qS` signing queries of the adversary run by
`tvDist_simulateQ_run_le_queryBoundP_mul`, the two hybrid handlers agreeing exactly on
the base (uniform and random-oracle) component. -/
lemma probOutput_hybridExpAtKey_trans_le_sim
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk) (hhvzk : ids.HVZK sim ζ_zk)
    (qS qH : ℕ) (p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit) (hrel : rel pk sk = true)
    (hAbortSim : Pr[= none | sim pk] ≤ ENNReal.ofReal p_abort) :
    Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (transSignBody ids M maxAttempts pk sk) pk] ≤
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (simSignBody M maxAttempts sim pk sk) pk] +
        ENNReal.ofReal (qS * ζ_zk / (1 - p_abort)) := by
  set ε : ℝ := ζ_zk * ∑ j ∈ Finset.range maxAttempts, p_abort ^ j with hε_def
  have hε_nonneg : 0 ≤ ε :=
    mul_nonneg hζ (Finset.sum_nonneg fun j _ => pow_nonneg hp₀ j)
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  -- The simulator abort bound, in real form.
  have hq_toReal : Pr[= none | sim pk].toReal ≤ p_abort := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hAbortSim
    rwa [ENNReal.toReal_ofReal hp₀] at h
  -- Per-signing-query step bound, uniform over the hybrid state.
  have h_step : ∀ (msg : M) (s : (M × Commit →ₒ Chal).QueryCache × List M),
      tvDist ((hybridSignImpl M (transSignBody ids M maxAttempts pk sk) msg).run s)
        ((hybridSignImpl M (simSignBody M maxAttempts sim pk sk) msg).run s) ≤ ε := by
    intro msg s
    have hrun : ∀ (body : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
        (Option (Commit × Resp))),
        (hybridSignImpl M body msg).run s =
          (fun (ac : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache) =>
            (ac.1, (ac.2, msg :: s.2))) <$> (body msg).run s.1 := by
      intro body
      rfl
    rw [hrun, hrun]
    exact le_trans (tvDist_map_le _ _ _)
      (tvDist_run_transSignBody_simSignBody_le ids M maxAttempts sim pk sk hrel msg
        hhvzk hq_toReal hp₀ s.1)
  -- Accumulate the per-query budget across the `qS` signing queries of the run.
  have h_run : tvDist
      (StateT.run (simulateQ
        (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (transSignBody ids M maxAttempts pk sk)) (adv.main pk)) (∅, []))
      (StateT.run (simulateQ
        (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (simSignBody M maxAttempts sim pk sk)) (adv.main pk)) (∅, []))
        ≤ qS * ε := by
    refine OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_queryBoundP_mul
      _ _ hε_nonneg
      (· matches .inr _) ?_ ?_ (adv.main pk) (hQ pk).1 (∅, [])
    · rintro (t | msg) hSt s
      · simp at hSt
      · simpa only [QueryImpl.add_apply_inr] using h_step msg s
    · rintro (t | msg) hSt s
      · simp only [QueryImpl.add_apply_inl]
      · simp at hSt
  -- The verification continuation is shared, so the games inherit the run-level bound.
  have h_tv_games : tvDist
      (hybridExpAtKey ids hr M maxAttempts adv (transSignBody ids M maxAttempts pk sk) pk)
      (hybridExpAtKey ids hr M maxAttempts adv (simSignBody M maxAttempts sim pk sk) pk)
        ≤ qS * ε := by
    refine le_trans ?_ h_run
    simp only [hybridExpAtKey]
    exact tvDist_bind_right_le _ _ _
  -- Close the finite geometric sum: `∑_{j<n} p^j ≤ 1/(1-p)`.
  have hsum_le : ∑ j ∈ Finset.range maxAttempts, p_abort ^ j ≤ 1 / (1 - p_abort) := by
    rw [le_div_iff₀ h1p]
    have hmul := geom_sum_mul p_abort maxAttempts
    nlinarith [pow_nonneg hp₀ maxAttempts]
  have h_bound : (qS : ℝ) * ε ≤ qS * ζ_zk / (1 - p_abort) := by
    rw [hε_def, div_eq_mul_inv, ← one_div]
    calc (qS : ℝ) * (ζ_zk * ∑ j ∈ Finset.range maxAttempts, p_abort ^ j)
        ≤ (qS : ℝ) * (ζ_zk * (1 / (1 - p_abort))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left hsum_le hζ
      _ = (qS : ℝ) * ζ_zk * (1 / (1 - p_abort)) := by ring
  have h_loss_nonneg : (0 : ℝ) ≤ qS * ζ_zk / (1 - p_abort) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hζ) h1p.le
  -- Convert the real TV bound into the `ℝ≥0∞` output-probability bound.
  have h_real : Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (transSignBody ids M maxAttempts pk sk) pk].toReal ≤
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (simSignBody M maxAttempts sim pk sk) pk].toReal +
        qS * ζ_zk / (1 - p_abort) := by
    have habs := abs_probOutput_toReal_sub_le_tvDist
      (hybridExpAtKey ids hr M maxAttempts adv (transSignBody ids M maxAttempts pk sk) pk)
      (hybridExpAtKey ids hr M maxAttempts adv (simSignBody M maxAttempts sim pk sk) pk)
    have h_le := (abs_le.mp habs).2
    linarith [h_tv_games, h_bound]
  calc Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (transSignBody ids M maxAttempts pk sk) pk]
      = ENNReal.ofReal (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (transSignBody ids M maxAttempts pk sk) pk].toReal) :=
        (ENNReal.ofReal_toReal probOutput_ne_top).symm
    _ ≤ ENNReal.ofReal (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (simSignBody M maxAttempts sim pk sk) pk].toReal +
          qS * ζ_zk / (1 - p_abort)) := ENNReal.ofReal_le_ofReal h_real
    _ = Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (simSignBody M maxAttempts sim pk sk) pk] +
          ENNReal.ofReal (qS * ζ_zk / (1 - p_abort)) := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg h_loss_nonneg,
          ENNReal.ofReal_toReal probOutput_ne_top]

/-! ## The NMA reduction -/

/-- The managed-RO NMA reduction for Fiat-Shamir with aborts: run the CMA adversary,
forwarding uniform queries, answering live hash queries through a managed cache, and
answering signing queries with the simulator loop of `simSignBody` (programming the
accepted transcript's challenge into the managed cache). Returns the forgery together
with the managed cache, in the interface of `SignatureAlg.managedRoNmaAdv`. -/
noncomputable def simulatedNmaAdv :
    SignatureAlg.managedRoNmaAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts) where
  main pk :=
    let spec := unifSpec + (M × Commit →ₒ Chal)
    let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
    let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
      fun n => fwd (.inl n)
    let roSim : QueryImpl (M × Commit →ₒ Chal)
        (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
      let cache ← get
      match cache (.inr mc) with
      | some v => pure v
      | none => do
          let v ← fwd (.inr mc)
          modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
    let sigSim : QueryImpl (M →ₒ Option (Commit × Resp))
        (StateT spec.QueryCache (OracleComp spec)) := fun msg => do
      let r ← simulateQ unifSim (firstSome (sim pk) maxAttempts)
      match r with
      | some (w, c, z) =>
          modifyGet fun cache => (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
      | none => pure none
    (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅

/-- NMA bridge: the success probability of the simulated hybrid (averaged over key
generation, with the freshness check) is at most the success probability of
`simulatedNmaAdv` in the managed-RO NMA experiment.

Distributional content: (i) the single-cache-layer hybrid run coincides with the
managed-cache run of `simulatedNmaAdv` followed by overlay verification
(`withCacheOverlay`), and (ii) by a cache invariant in the style of
`fsAbortSignLoop_cache_invariant`, every entry programmed by the signing simulation has
its message recorded in the signed list, so on fresh forgeries the overlay agrees with
the live oracle at the verification point and the freshness conjunct can only decrease
the left-hand side. A hash-query-bound transfer in the style of
`FiatShamir.simulatedNmaAdv_hashQueryBound` (the loop issues no live hash queries)
should accompany this lemma when the downstream consumer needs NMA query bounds. -/
lemma probOutput_hybridExp_sim_le_managedRoNmaExp :
    Pr[= true | do
        let (pk, sk) ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (simSignBody M maxAttempts sim pk sk) pk] ≤
      Pr[= true | SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv)] := by
  sorry

/-! ## Assembly -/

/-- **CMA-to-NMA reduction for Fiat-Shamir with aborts** (after Theorem 3, CRYPTO 2023),
at the managed-RO NMA interface: for any EUF-CMA adversary making at most `qS` signing
and `qH` hash queries, the CMA advantage is bounded by the managed-RO NMA success
probability of `simulatedNmaAdv` plus the statistical loss `cmaToNmaLoss`.

The good-key event `Good` plays the role of the event `Γ` in the paper's Lemma 1: `δ`
bounds its complement under key generation, while `ε` and `p_abort` bound the per-key
commitment-guessing and per-attempt abort probabilities pointwise on it. -/
theorem euf_cma_to_nma
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk) (hhvzk : ids.HVZK sim ζ_zk)
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : Stmt → Wit → Prop)
    (hGood : Pr[ fun xw : Stmt × Wit => ¬ Good xw.1 xw.2 | hr.gen] ≤ ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (hAbortSim : ∀ pk sk, Good pk sk →
      Pr[= none | sim pk] ≤ ENNReal.ofReal p_abort)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    adv.advantage (runtime M) ≤
      Pr[= true | SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv)] +
      ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  -- Chain: advantage = Pr[G₀] (per-key bridge), then average the per-key chain
  -- G₀ ≤ G₃ + perKeyLoss over `hr.gen`, paying `δ` for keys outside `Good`
  -- (the keys where `gen_sound` holds but the pointwise bounds may fail),
  -- then apply the NMA bridge. The averaging step uses `probOutput_bind_eq_tsum`
  -- and splits the key sum on `Good`, in the style of
  -- `SignatureAlg.probOutput_bind_ge_of_forall_support`.
  sorry

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Cache-invariant companion to `simulatedNmaAdv`: the reduction issues at most `qH`
live hash queries (the signing simulation samples transcripts using only uniform
queries and programs the managed cache). Mirrors
`FiatShamir.simulatedNmaAdv_hashQueryBound` from the Σ-protocol track. -/
lemma simulatedNmaAdv_nmaHashQueryBound
    [Finite Chal] [Inhabited Chal]
    (qS qH : ℕ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    ∀ pk, FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulatedNmaAdv ids hr M maxAttempts sim adv).main pk) qH := by
  haveI : Fintype Chal := Fintype.ofFinite Chal
  letI : IsUniformSpec ((M × Commit →ₒ Chal) : OracleSpec _) :=
    IsUniformSpec.ofFintypeInhabited _
  intro pk
  let spec := unifSpec + (M × Commit →ₒ Chal)
  let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
    fun n => fwd (.inl n)
  let roSim : QueryImpl (M × Commit →ₒ Chal)
      (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none => do
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  let sigSim : QueryImpl (M →ₒ Option (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun msg => do
    let r ← simulateQ unifSim (firstSome (sim pk) maxAttempts)
    match r with
    | some (w, c, z) =>
        modifyGet fun cache => (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
    | none => pure none
  -- Step bound for `fwd`: 0 live hash queries on `.inl`, exactly 1 on `.inr`.
  have hfwd :
      ∀ (t : spec.Domain) (s : spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (fwd t).run s) (match t with
            | .inl _ => 0
            | .inr _ => 1) := by
    intro t s
    cases t with
    | inl n =>
        simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
          OracleComp.liftM_run_StateT] using
          (FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
            (show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (oa := liftM (spec.query (.inl n))) 0 by
                exact (FiatShamir.nmaHashQueryBound_query_iff (M := M) (Commit := Commit)
                  (Chal := Chal) (.inl n) 0).2 trivial)
            (fun u =>
              show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := pure (u, s)) 0 by
                  trivial))
    | inr mc =>
        simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
          OracleComp.liftM_run_StateT] using
          (FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
            (show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (oa := liftM (spec.query (.inr mc))) 1 by
                exact (FiatShamir.nmaHashQueryBound_query_iff (M := M) (Commit := Commit)
                  (Chal := Chal) (.inr mc) 1).2 (Nat.succ_pos 0))
            (fun u =>
              show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := pure (u, s)) 0 by
                  trivial))
  -- Step bound for `roSim`: a cache hit issues no live query, a miss issues exactly one.
  have hro :
      ∀ (mc : M × Commit) (s : spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (roSim mc).run s) 1 := by
    intro mc s
    cases hs : s (.inr mc) with
    | some v =>
        simp [roSim, hs, FiatShamir.nmaHashQueryBound]
    | none =>
        simp only [FiatShamir.nmaHashQueryBound, Sum.forall, Prod.forall, StateT.run_bind,
          StateT.run_get, pure_bind, hs, StateT.run_modifyGet, bind_pure_comp,
          isQueryBoundP_map_iff, roSim] at ⊢ hfwd
        exact hfwd.2 mc.1 mc.2 s
  -- Step bound for `sigSim`: the simulator loop samples under `unifSim` (uniform-only)
  -- and then programs the managed cache, issuing no live hash query.
  have hsig :
      ∀ (msg : M) (s : spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (sigSim msg).run s) 0 := by
    intro msg s
    have htranscript :
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (simulateQ unifSim (firstSome (sim pk) maxAttempts)).run s) 0 := by
      unfold FiatShamir.nmaHashQueryBound
      refine OracleComp.IsQueryBoundP.simulateQ_run_of_step
        (p := fun _ : ℕ => False) (impl := unifSim)
        (oa := firstSome (sim pk) maxAttempts)
        (OracleComp.isQueryBoundP_false _ _)
        (fun _ h _ => h.elim)
        ?_ s
      intro n _ s'
      have h := hfwd (.inl n) s'
      simpa [unifSim, FiatShamir.nmaHashQueryBound] using h
    have hcont : ∀ (rs : Option (Commit × Chal × Resp) × spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := StateT.run
            (match rs.1 with
              | some (w, c, z) => modifyGet fun cache =>
                  (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
              | none =>
                  (pure none : StateT spec.QueryCache (OracleComp spec)
                    (Option (Commit × Resp)))) rs.2) 0 := by
      rintro ⟨(_ | ⟨w, c, z⟩), cache⟩ <;>
        simp [FiatShamir.nmaHashQueryBound, StateT.run_modifyGet]
    have hbind := FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit)
      (Chal := Chal) htranscript (fun rs => hcont rs)
    simpa [sigSim, StateT.run_bind] using hbind
  change FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
    (oa := (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅) qH
  unfold FiatShamir.nmaHashQueryBound
  refine OracleComp.IsQueryBoundP.simulateQ_run_of_step (hQ pk).2 ?_ ?_ ∅
  · rintro ((n | mc) | msg) hp s'
    · simp at hp
    · simpa only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] using hro mc s'
    · simp at hp
  · rintro ((n | mc) | msg) hnp s'
    · have h := hfwd (.inl n) s'
      simpa only [QueryImpl.add_apply_inl, FiatShamir.nmaHashQueryBound] using h
    · simp at hnp
    · simpa only [QueryImpl.add_apply_inr] using hsig msg s'

end scaffold

/-- **CMA-to-NMA security bound for Fiat-Shamir with aborts (Theorem 3, CRYPTO 2023).**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists a witness-finding reduction whose success
probability in `hardRelationExp` absorbs the computational part of the bound:

  `Adv^{EUF-CMA}(A) ≤ Pr[hardRelationExp hr reduction] + L`

with `L = cmaToNmaLoss qS qH ε p_abort ζ_zk δ`. The quantitative hypotheses tie each
loss parameter to the identification scheme on a good-key event `Good` (the event `Γ`
of the paper's Lemma 1):

- `hGood`: key generation leaves `Good` with probability at most `δ`;
- `hGuess`: on good keys, every fixed commitment is hit by `ids.commit` with
  probability at most `ε` (commitment-guessing / min-entropy bound);
- `hAbort` / `hAbortSim`: on good keys, a single honest signing attempt
  (resp. simulator attempt) aborts with probability at most `p_abort`;
- `hhvzk`: the simulator is within total-variation distance `ζ_zk` of one honest
  attempt, over optional transcripts (`IdenSchemeWithAbort.HVZK`).

The reduction uses the HVZK simulator to answer signing queries without the secret key
and commitment recoverability `recover` to convert between the standard and
commitment-recoverable signature formats; see `euf_cma_to_nma` for the hybrid chain and
the managed-RO NMA interface, and `MLDSA.nma_security` / `MLDSA.euf_cma_security` for
the scheme-specific computational step. -/
theorem euf_cma_bound
    (hc : ids.Complete)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
    (ζ_zk : ℝ)
    (hζ : 0 ≤ ζ_zk)
    (hhvzk : ids.HVZK sim ζ_zk)
    (recover : Stmt → Chal → Resp → Commit)
    (hcr : ids.CommitmentRecoverable recover)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : Stmt → Wit → Prop)
    (hGood : Pr[ fun xw : Stmt × Wit => ¬ Good xw.1 xw.2 | hr.gen] ≤ ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (hAbortSim : ∀ pk sk, Good pk sk →
      Pr[= none | sim pk] ≤ ENNReal.ofReal p_abort)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      adv.advantage (runtime M) ≤
        Pr[= true | hardRelationExp hr reduction] +
          ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  let _ := hc
  let _ := hcr
  -- From `euf_cma_to_nma`, the advantage is bounded by the managed-RO NMA success
  -- probability of `simulatedNmaAdv` plus the loss. The remaining step relates the
  -- NMA success probability to `hardRelationExp`. NOTE (statement-level): in this
  -- non-asymptotic formulation `hardRelationExp` admits an unbounded witness-search
  -- reduction, so this conclusion is strictly weaker than the NMA-advantage form of
  -- `euf_cma_to_nma`; downstream consumers (e.g. `MLDSA.euf_cma_security`) should
  -- compose with `euf_cma_to_nma` and the scheme-specific NMA theorem instead.
  sorry

/-- Perfect-HVZK special case of `euf_cma_bound`, where the simulator contributes no
zero-knowledge loss term. The simulator abort hypothesis `hAbortSim` is retained: even a
perfect per-attempt simulator participates in the restart loop, whose length governs the
reprogramming terms. -/
theorem euf_cma_bound_perfectHVZK
    (hc : ids.Complete)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
    (hhvzk : ids.PerfectHVZK sim)
    (recover : Stmt → Chal → Resp → Commit)
    (hcr : ids.CommitmentRecoverable recover)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : Stmt → Wit → Prop)
    (hGood : Pr[ fun xw : Stmt × Wit => ¬ Good xw.1 xw.2 | hr.gen] ≤ ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (hAbortSim : ∀ pk sk, Good pk sk →
      Pr[= none | sim pk] ≤ ENNReal.ofReal p_abort)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      adv.advantage (runtime M) ≤
        Pr[= true | hardRelationExp hr reduction] +
          ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort 0 δ hp) := by
  simpa using
    (euf_cma_bound (ids := ids) (M := M) (maxAttempts := maxAttempts)
      (hc := hc) (sim := sim) (ζ_zk := 0) (hζ := le_rfl)
      (hhvzk := (IdenSchemeWithAbort.perfectHVZK_iff_hvzk_zero ids sim).mp hhvzk)
      (recover := recover) (hcr := hcr) (adv := adv)
      (qS := qS) (qH := qH) (ε := ε) (p_abort := p_abort) (δ := δ)
      (hε := hε) (hδ := hδ) (hp₀ := hp₀) (hp := hp)
      (Good := Good) (hGood := hGood) (hGuess := hGuess)
      (hAbort := hAbort) (hAbortSim := hAbortSim)
      (hQ := hQ))

end EUF_CMA

end FiatShamirWithAbort
