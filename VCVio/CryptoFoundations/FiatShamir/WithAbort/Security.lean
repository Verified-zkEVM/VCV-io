/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating

/-!
# EUF-CMA security of Fiat-Shamir with aborts

Statistical CMA-to-NMA reduction for the Fiat-Shamir-with-aborts transform,
following Theorem 3 of Barbosa et al. (CRYPTO 2023, ePrint 2023/246).
Instantiates `FiatShamir.signHashQueryBound` at the with-aborts signature type
and exposes `cmaToNmaLoss` plus `euf_cma_to_nma` (the managed-RO NMA interface),
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
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

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

/-! ## Verification tail -/

/-- Verification-and-freshness continuation of `hybridExpAtKey`, as a function of the
adversary's forgery and the final hybrid state. -/
noncomputable def hybridVerifyCont (pk : Stmt)
    (z : (M × Option (Commit × Resp)) × ((M × Commit →ₒ Chal).QueryCache × List M)) :
    ProbComp Bool := do
  let ok ← StateT.run'
    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
      ((FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts).verify pk z.1.1 z.1.2)) z.2.1
  pure (decide (z.1.1 ∉ z.2.2) && ok)

omit [SampleableType Stmt] in
lemma hybridExpAtKey_eq_run_bind
    (signBody : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp)))
    (pk : Stmt) :
    hybridExpAtKey ids hr M maxAttempts adv signBody pk =
      (simulateQ
          (hybridBaseImpl (Commit := Commit) (Chal := Chal) M + hybridSignImpl M signBody)
          (adv.main pk)).run (∅, []) >>=
        hybridVerifyCont ids hr M maxAttempts pk := by
  refine bind_congr fun z => ?_
  rcases z with ⟨⟨msg, σ⟩, cache, signed⟩
  rfl

omit [SampleableType Stmt] in
/-- The verification continuation only reads the cache at the forged message's points,
so it is insensitive to cache changes away from them. -/
lemma hybridVerifyCont_cache_congr (pk : Stmt) (ms : M × Option (Commit × Resp))
    (c₁ c₂ : (M × Commit →ₒ Chal).QueryCache) (l : List M)
    (h : ∀ w : Commit, c₁ (ms.1, w) = c₂ (ms.1, w)) :
    hybridVerifyCont ids hr M maxAttempts pk (ms, (c₁, l)) =
      hybridVerifyCont ids hr M maxAttempts pk (ms, (c₂, l)) := by
  rcases ms with ⟨msg, _ | ⟨w, zr⟩⟩
  · rfl
  · refine congrArg (· >>= fun ok => pure (decide (msg ∉ l) && ok)) ?_
    have hside : ∀ c : (M × Commit →ₒ Chal).QueryCache,
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          ((FiatShamirWithAbort
            (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
            ids hr M maxAttempts).verify pk msg (some (w, zr)))).run' c =
          (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            ids.verify pk w cu.1 zr) <$> roStep M c (msg, w) := by
      intro c
      simp only [FiatShamirWithAbort, simulateQ_bind, roSim.simulateQ_HasQuery_query,
        simulateQ_pure]
      change Prod.fst <$> (((randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) (msg, w) >>=
            fun cc => pure (ids.verify pk w cc zr)).run c) = _
      rw [StateT.run_bind]
      rw [show ((randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) (msg, w)).run c =
        roStep M c (msg, w) from randomOracle_run_eq_roStep M c (msg, w)]
      simp
    rw [hside c₁, hside c₂]
    cases hc : c₁ (msg, w) with
    | some v =>
        rw [roStep_of_some M hc,
          roStep_of_some M (show c₂ (msg, w) = some v from (h w).symm.trans hc)]
        simp
    | none =>
        rw [roStep_of_none M hc,
          roStep_of_none M (show c₂ (msg, w) = none from (h w).symm.trans hc)]
        simp

omit [SampleableType Stmt] in
/-- When the forged message has already been signed, the freshness conjunct forces the
game output to `false`, so the success probability vanishes regardless of the cache. -/
lemma probOutput_true_hybridVerifyCont_of_mem (pk : Stmt)
    (ms : M × Option (Commit × Resp))
    (c : (M × Commit →ₒ Chal).QueryCache) (l : List M) (hmem : ms.1 ∈ l) :
    Pr[= true | hybridVerifyCont ids hr M maxAttempts pk (ms, (c, l))] = 0 := by
  rw [hybridVerifyCont, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr fun ok => ?_
  rw [probOutput_pure, if_neg (by simp [hmem]), mul_zero]

/-! ## The lazy-side ghost-read charge -/

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- Transport a predicate-targeted query bound across a (propositionally equal) choice of
predicate and `DecidablePred` instance. The decidability instance is a subsingleton up to
the propositional content; this lets a query bound built with one instance feed a lemma
expecting another (e.g. the accumulator's synthesised instance). -/
lemma isQueryBoundP_cast_pred' {ι₀ : Type} {spec₀ : OracleSpec ι₀} {α₀ : Type}
    {oa : OracleComp spec₀ α₀} {p₁ p₂ : spec₀.Domain → Prop}
    {i₁ : DecidablePred p₁} {i₂ : DecidablePred p₂} {n : ℕ} (hp : p₁ = p₂)
    (h : @OracleComp.IsQueryBoundP _ spec₀ α₀ oa p₁ i₁ n) :
    @OracleComp.IsQueryBoundP _ spec₀ α₀ oa p₂ i₂ n := by
  subst hp
  rwa [Subsingleton.elim i₂ i₁]

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- **Bad-flag pass-through for a bad-free run.** If every output of `oa` carries bad bit
`false`, then the bad probability of `oa >>= k` is carried entirely by `oa`'s (good)
outputs: it equals the resource-weighted sum the accumulator's free/charged step premises
require, with no extra bad mass introduced by `oa` itself. -/
lemma probEvent_bad_bind_eq_tsum_false {γ' σ' δ' τ' : Type}
    (oa : ProbComp (γ' × σ' × Bool))
    (k : γ' × σ' × Bool → ProbComp (δ' × τ' × Bool))
    (hbf : ∀ z ∈ support oa, z.2.2 = false) :
    Pr[fun w => w.2.2 = true | oa >>= k]
      = ∑' z : γ' × σ',
          Pr[= (z.1, z.2, false) | oa] * Pr[fun w => w.2.2 = true | k (z.1, z.2, false)] := by
  classical
  rw [probEvent_bind_eq_tsum,
    ← (Equiv.prodAssoc γ' σ' Bool).tsum_eq
      (fun w => Pr[= w | oa] * Pr[fun y => y.2.2 = true | k w]),
    ENNReal.tsum_prod']
  refine tsum_congr fun z => ?_
  rw [tsum_bool]
  simp only [Equiv.prodAssoc_apply]
  have htrue : Pr[= (z.1, z.2, true) | oa] = 0 := by
    refine probOutput_eq_zero_of_not_mem_support fun hz => ?_
    exact absurd (hbf _ hz) (by simp)
  rw [htrue, zero_mul, add_zero]

omit [SampleableType Stmt] in
/-- **Charged-step premise for the lazy ghost read.** For the deferred-sampling handler
`lazyGhostHybridImpl`, an adversarial random-oracle read at `(.inl (.inr mc))` from a
non-bad state pays the amortizable flip charge `enncard (ghost cache) · ofReal ε` and
routes any residual bad mass through its `fired = false` (good) outputs. This is exactly
the `h_charged_step` hypothesis required by
`probEvent_bad_simulateQ_run_le_expectedQuerySlack`, made true (in contrast to the eager
handler's deterministic mass-`1` flip) by the lazy fire draw whose `true` mass is bounded
by `probOutput_lazyGhostFire_true_le_enncard`. -/
lemma probEvent_lazyGhostHybridImpl_charged_step (pk : Stmt) (sk : Wit) {ε : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (mc : M × Commit)
    (s : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M)
    (k : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
          (.inl (.inr mc))) ×
        (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) ×
          Bool →
        ProbComp ((M × Option (Commit × Resp)) ×
          (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) ×
            Bool)) :
    Pr[fun z => z.2.2 = true |
        ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inr mc))).run (s, false)) >>= k]
      ≤ QueryCache.enncard s.1.2 * ENNReal.ofReal ε +
        ∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (.inl (.inr mc))) ×
          (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
          Pr[= (z.1, z.2, false) |
            (lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inr mc))).run (s, false)] *
            Pr[fun w => w.2.2 = true | k (z.1, z.2, false)] := by
  classical
  obtain ⟨⟨re, gh⟩, list⟩ := s
  set fire := lazyGhostFire ids pk sk mc.2 gh.toSet.encard.toNat with hfire
  set ro := roStep M re mc with hro
  -- The lazy-fire `true`-mass is the amortizable flip charge `enncard gh · ofReal ε`.
  have h_fire_true : Pr[= true | fire] ≤ QueryCache.enncard gh * ENNReal.ofReal ε := by
    rw [hfire]
    refine (probOutput_lazyGhostFire_true_le ids pk sk hGuess mc.2 _).trans ?_
    gcongr
    -- `(encard.toNat : ℝ≥0∞) ≤ (encard : ℝ≥0∞) = enncard gh`.
    change ((gh.toSet.encard.toNat : ℕ) : ℝ≥0∞) ≤ (gh.toSet.encard : ℝ≥0∞)
    calc ((gh.toSet.encard.toNat : ℕ) : ℝ≥0∞)
        = ((gh.toSet.encard.toNat : ℕ∞) : ℝ≥0∞) := by push_cast; rfl
      _ ≤ (gh.toSet.encard : ℝ≥0∞) := ENat.toENNReal_mono (ENat.coe_toNat_le_self _)
  -- The run, with its bad bit reduced (`false || b = b`): a fire draw whose Boolean result
  -- becomes the output bad bit, composed with the real-layer caching read `ro`.
  have h_run : (lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inr mc))).run
        (((re, gh), list), false) =
      fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro := by
    simp only [hfire, hro]
    rfl
  -- Rewrite both the run-bind and the good-continuation sum into the reduced form, then
  -- expand the bad probability over each run output (`Chal × σ × Bool`).
  rw [h_run, probEvent_bind_eq_tsum]
  -- Unfold the `GhostState` abbreviation so the product structure is explicit.
  simp only [GhostState] at *
  -- Split each output sum over its Boolean (bad) coordinate.
  rw [← (Equiv.prodAssoc
      (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
        (Sum.inl (Sum.inr mc)))
      (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M)
      Bool).tsum_eq,
    ENNReal.tsum_prod']
  -- The `bad = false` summand is the accumulator's good-continuation term; the `bad = true`
  -- summand sums to the run's bad-output mass, bounded by `enncard gh · ofReal ε`.
  have h_split : ∀ z : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) ×
        (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
      (∑' b : Bool,
        Pr[= (z.1, z.2, b) |
          fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
          Pr[fun y => y.2.2 = true | k (z.1, z.2, b)])
      = Pr[= (z.1, z.2, false) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
          Pr[fun y => y.2.2 = true | k (z.1, z.2, false)]
        + Pr[= (z.1, z.2, true) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
          Pr[fun y => y.2.2 = true | k (z.1, z.2, true)] := by
    intro z
    rw [tsum_bool, add_comm]
  simp only [Equiv.prodAssoc_apply]
  -- Split each per-output Boolean sum into its `false` (good continuation) and `true`
  -- (bad output) parts, then separate the two sums.
  have hsplit_sum :
      (∑' a : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) ×
          (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
        ∑' b : Bool,
          Pr[= (a.1, a.2, b) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
            Pr[fun z => z.2.2 = true | k (a.1, a.2, b)])
      = (∑' a : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) ×
            (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
          Pr[= (a.1, a.2, false) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
            Pr[fun z => z.2.2 = true | k (a.1, a.2, false)])
        + (∑' a : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) ×
            (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
          Pr[= (a.1, a.2, true) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
            Pr[fun z => z.2.2 = true | k (a.1, a.2, true)]) := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun a => h_split a
  refine le_trans (le_of_eq hsplit_sum) ?_
  rw [add_comm]
  refine add_le_add ?_ le_rfl
  -- The bad-output (`b = true`) mass is at most the fire `true`-mass: each output's bad bit
  -- is the fire result, and the continuation contributes at most `1`.
  calc (∑' z : Chal ×
          (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
        Pr[= (z.1, z.2, true) |
          fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
          Pr[fun y => y.2.2 = true | k (z.1, z.2, true)])
      ≤ ∑' z : Chal ×
          (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
          Pr[= (z.1, z.2, true) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        exact mul_le_of_le_one_right (zero_le') probEvent_le_one
    _ ≤ Pr[= true | fire] := by
        -- Each output's bad bit equals the fire draw, so the `b = true` outputs carry
        -- at most the fire `true`-mass. Expand each summand over the fire draw, swap the
        -- sums, and use that `g_fired <$> ro` outputs bad bit `fired`.
        have h_per_z : ∀ z : Chal ×
            (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
            Pr[= (z.1, z.2, true) |
              fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro]
            = ∑' fired : Bool, Pr[= fired | fire] *
                Pr[= (z.1, z.2, true) |
                  (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] :=
          fun z => probOutput_bind_eq_tsum fire _ _
        rw [tsum_congr h_per_z, ENNReal.tsum_comm]
        -- The inner sum over outputs is `0` for `fired = false` (its outputs carry bad bit
        -- `false`) and `≤ 1` for `fired = true`, giving the bound `≤ Pr[= true | fire]`.
        have h_inner : ∀ fired : Bool,
            (∑' z : Chal ×
              (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
              Pr[= fired | fire] *
                Pr[= (z.1, z.2, true) |
                  (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro])
              ≤ Pr[= fired | fire] * (if fired then 1 else 0) := by
          intro fired
          rw [ENNReal.tsum_mul_left]
          gcongr ?_ * ?_
          cases fired with
          | false =>
              rw [if_neg (by decide)]
              refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun z => ?_)
              refine probOutput_eq_zero_of_not_mem_support ?_
              rw [support_map]
              rintro ⟨cu, _, heq⟩
              simp only [Prod.mk.injEq] at heq
              exact absurd heq.2.2 (by decide)
          | true =>
              rw [if_pos rfl]
              -- The bad-output mass is a sub-sum of the total mass `≤ 1`, via the injection
              -- `z ↦ (z.1, z.2, true)`.
              refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective ?_
                (fun w => Pr[= w | (fun cu => (cu.1, (((cu.2, gh), list), true))) <$> ro]))
                tsum_probOutput_le_one
              rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ heq
              simp only [Prod.mk.injEq] at heq
              exact Prod.ext heq.1 heq.2.1
        refine le_trans (ENNReal.tsum_le_tsum h_inner) ?_
        rw [tsum_bool]
        simp
    _ ≤ QueryCache.enncard gh * ENNReal.ofReal ε := h_fire_true

omit [SampleableType Stmt] in
/-- A uniform-sampling read of the lazy ghost handler preserves the bad flag: started from a
non-bad state, every output is non-bad. -/
lemma lazyGhostHybridImpl_run_unif_bad_false (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : GhostState M Commit Chal) (hs : s.2 = false) :
    ∀ z ∈ support ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inl n))).run s),
      z.2.2 = false := by
  intro z hz
  rw [show (lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n from rfl]
    at hz
  obtain ⟨u, _, heq⟩ :=
    (support_map (fun u => (u, s)) ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n)
      ▸ hz)
  rw [← heq, hs]

omit [SampleableType Stmt] in
/-- A signing query of the lazy ghost handler preserves the bad flag: started from a non-bad
state, every output is non-bad. -/
lemma lazyGhostHybridImpl_run_sign_bad_false (pk : Stmt) (sk : Wit) (msg : M)
    (s : GhostState M Commit Chal) (hs : s.2 = false) :
    ∀ z ∈ support ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inr msg)).run s),
      z.2.2 = false := by
  intro z hz
  rw [show (lazyGhostHybridImpl ids M maxAttempts pk sk (.inr msg)).run s =
      (fun alc => (alc.1, ((alc.2, msg :: s.1.2), s.2))) <$>
        (ghostSignBody ids M pk sk msg maxAttempts).run s.1.1 from rfl] at hz
  obtain ⟨alc, _, heq⟩ :=
    (support_map (fun alc : Option (Commit × Resp) ×
        ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (alc.1, ((alc.2, msg :: s.1.2), s.2)))
      ((ghostSignBody ids M pk sk msg maxAttempts).run s.1.1) ▸ hz)
  rw [← heq, hs]

omit [SampleableType Stmt] in
/-- **Deliverable A: the lazy-side ghost-read bound.** For the deferred-sampling handler
`lazyGhostHybridImpl`, the probability that the adversary's run ever flips the bad flag is
at most `qS·(qH+1)·ε/(1-p)`.

Assembled from the single-world resource-charged accumulator
`probEvent_bad_simulateQ_run_le_expectedQuerySlack` (charged step =
`probEvent_lazyGhostHybridImpl_charged_step`, free step = the bad-flag pass-through of
non-read queries) chained with the charged-read / expected-growth fold
`expectedQuerySlack_charged_read_expected_growth_le` (resource `R s := enncard (ghost
cache)`, per-read charge `ofReal ε`, expected growth `g := ∑_{a<maxAttempts} ofReal p^a` per
signing query via `tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le`), with the
charged-read budget `qH+1` and the growth-query budget `qS` from `hQ`, the empty starting
ghost cache contributing `R = 0`, and `g ≤ 1/(1-p)`. -/
lemma probEvent_lazyGhostHybridImpl_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (lazyGhostHybridImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
  classical
  -- ASSEMBLY RECIPE (all ingredients PROVEN; blocked only by elaboration performance).
  --
  -- (1) Single-world accumulator
  --     `OracleComp.ProgramLogic.Relational.probEvent_bad_simulateQ_run_le_expectedQuerySlack`
  --     at `impl := lazyGhostHybridImpl ids M maxAttempts pk sk`,
  --     `charged := (· matches Sum.inl (Sum.inr _))` (random-oracle reads),
  --     `R s := QueryCache.enncard s.1.2` (the ghost cache size), `ε := ofReal ε`, with
  --       * `h_charged_step := probEvent_lazyGhostHybridImpl_charged_step …` (PROVEN above);
  --       * `h_free_step` from the bad-flag pass-through `probEvent_bad_bind_eq_tsum_false`
  --         combined with `lazyGhostHybridImpl_run_unif_bad_false` /
  --         `lazyGhostHybridImpl_run_sign_bad_false` (all PROVEN above);
  --       * charged-read budget `qH + 1` from `(hQ pk).2.mono` transported across the
  --         `DecidablePred` instance by `isQueryBoundP_cast_pred'` (PROVEN above).
  --     This yields
  --       `Pr[bad | run] ≤ expectedQuerySlack lazyGhostHybridImpl charged
  --                          (fun s => R s * ofReal ε) (adv.main pk) (qH+1) (init, false)`.
  --
  -- (2) The charged-read / expected-growth fold
  --     `OracleComp.ProgramLogic.Relational.expectedQuerySlack_charged_read_expected_growth_le`
  --     with `chargedQuery := reads`, `growthQuery := (· matches Sum.inr _)` (signings),
  --     `R`, `β := ofReal ε`, `g := ∑_{a<maxAttempts} ofReal p_abort ^ a`, where
  --       * `h_charged` / `h_free`: a read / uniform query leaves the ghost cache `R`
  --         unchanged (output ghost cache `= s.1.2`), so `R z.2.1 ≤ R p.1` (in fact `=`);
  --       * `h_growth`: the ghost-layer growth law
  --         `tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le ids … hAbort` gives
  --         `∑ Pr[=z|signing.run]·enncard z.2.2 ≤ enncard gh + ∑_{a} ofReal p^a = R p.1 + g`;
  --       * growth budget `qS` from `(hQ pk).1`.
  --     This yields `expectedQuerySlack … (qH+1) (init,false) ≤ (qH+1)·(R init + qS·g)·ofReal ε`.
  --
  -- (3) Arithmetic: `R init = enncard ∅ = 0`, and `g = ∑_{a<maxAttempts} ofReal p^a ≤
  --     1/(1-p_abort)` (geometric bound `geom_sum_mul`, cf. `hSgeo` in
  --     `probEvent_charge_signCollision_le`), giving
  --       `(qH+1)·(0 + qS·g)·ofReal ε ≤ ofReal (qS·(qH+1)·ε/(1-p_abort))`
  --     via `ENNReal.ofReal` push-through (cf. the closing block of
  --     `probEvent_charge_signCollision_le`).
  --
  refine (OracleComp.ProgramLogic.Relational.probEvent_bad_simulateQ_run_le_expectedQuerySlack
    (impl := lazyGhostHybridImpl ids M maxAttempts pk sk)
    (charged := fun t => t matches Sum.inl (Sum.inr _))
    (R := fun s => QueryCache.enncard s.1.2) (ε := ENNReal.ofReal ε)
    ?_ ?_ (adv.main pk) (qS := qH + 1) ?_ (((∅, ∅), []))).trans ?_
  · -- h_charged_step: a charged random-oracle read pays `enncard · ofReal ε`.
    rintro t s ht k
    obtain ⟨mc, rfl⟩ : ∃ mc, t = Sum.inl (Sum.inr mc) := by
      revert ht; rcases t with (n | mc) | msg <;> simp
    exact probEvent_lazyGhostHybridImpl_charged_step ids M maxAttempts pk sk hGuess mc s k
  · -- h_free_step: a non-charged (uniform or signing) query introduces no bad mass.
    rintro t s ht k
    rcases t with (n | mc) | msg
    · exact le_of_eq (probEvent_bad_bind_eq_tsum_false
        (oa := (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run (s, false))
        (k := k)
        (lazyGhostHybridImpl_run_unif_bad_false ids M maxAttempts pk sk n (s, false) rfl))
    · exact absurd rfl ht
    · exact le_of_eq (probEvent_bad_bind_eq_tsum_false
        (oa := (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inr msg)).run (s, false))
        (k := k)
        (lazyGhostHybridImpl_run_sign_bad_false ids M maxAttempts pk sk msg (s, false) rfl))
  · -- charged-read budget `qH + 1`: from the RO-read bound `qH`, weakened by `+1`.
    have h := (hQ pk).2.mono (Nat.le_succ qH)
    convert h using 3 with x
    rcases x with (_ | _) | _ <;> rfl
  · -- (2)+(3): the charged-read / expected-growth fold, then arithmetic.
    set g : ℝ≥0∞ := ∑ a ∈ Finset.range maxAttempts, ENNReal.ofReal p_abort ^ a with hg
    -- The fold bound: `expectedQuerySlack ≤ (qH+1)·(R init + qS·g)·ofReal ε`.
    have h_fold :
        OracleComp.ProgramLogic.Relational.expectedQuerySlack
            (lazyGhostHybridImpl ids M maxAttempts pk sk)
            (fun t => t matches Sum.inl (Sum.inr _))
            (fun s => QueryCache.enncard s.1.2 * ENNReal.ofReal ε) (adv.main pk) (qH + 1)
            ((((∅, ∅), []) :
              ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
                false)
          ≤ ((qH + 1 : ℕ) : ℝ≥0∞) *
              (QueryCache.enncard (∅ : (M × Commit →ₒ Chal).QueryCache) + (qS : ℝ≥0∞) * g) *
              ENNReal.ofReal ε := by
      refine OracleComp.ProgramLogic.Relational.expectedQuerySlack_charged_read_expected_growth_le
        (lazyGhostHybridImpl ids M maxAttempts pk sk)
        (chargedQuery := fun t => t matches Sum.inl (Sum.inr _))
        (growthQuery := fun t => t matches Sum.inr _)
        (R := fun s => QueryCache.enncard s.1.2) (β := ENNReal.ofReal ε) (g := g)
        ?_ ?_ ?_ (adv.main pk) ?_ ?_ _
      · -- h_charged: a charged RO read leaves the ghost cache (`R`) unchanged.
        rintro t p hp ht z hz
        rcases t with (n | mc) | msg
        · exact absurd ht (by simp)
        · rw [show (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run p =
              lazyGhostFire ids pk sk mc.2 p.1.1.2.toSet.encard.toNat >>= fun fired =>
                (fun cu => (cu.1, (((cu.2, p.1.1.2), p.1.2), p.2 || fired))) <$>
                  roStep M p.1.1.1 mc from rfl] at hz
          obtain ⟨fired, _, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
          obtain ⟨cu, _, heq⟩ :=
            (support_map (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
                (cu.1, (((cu.2, p.1.1.2), p.1.2), p.2 || fired)))
              (roStep M p.1.1.1 mc) ▸ hz)
          rw [← heq]
        · exact absurd ht (by simp)
      · -- h_growth: the ghost-layer growth law for a signing query.
        rintro t p hp ht ht2
        rcases t with (n | mc) | msg
        · exact absurd ht2 (by simp)
        · exact absurd ht2 (by simp)
        · obtain ⟨⟨⟨re, gh⟩, list⟩, b⟩ := p
          rw [show b = false from hp]
          change ∑' z : (Option (Commit × Resp)) ×
              (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) × Bool,
              Pr[= z | (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inr msg)).run
                (((re, gh), list), false)] * QueryCache.enncard z.2.1.1.2
            ≤ QueryCache.enncard gh + g
          rw [show (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inr msg)).run
                (((re, gh), list), false) =
              (ghostSignBody ids M pk sk msg maxAttempts).run (re, gh) >>= fun alc =>
                pure (alc.1, ((alc.2, msg :: list), false)) from rfl]
          have heq := tsum_probOutput_bind_mul
            ((ghostSignBody ids M pk sk msg maxAttempts).run (re, gh))
            (fun alc => (pure (alc.1, ((alc.2, msg :: list), false)) : ProbComp _))
            (fun z => QueryCache.enncard z.2.1.1.2)
          refine le_trans (le_of_eq heq) ?_
          refine le_trans (ENNReal.tsum_le_tsum fun alc => ?_)
            (tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le ids M pk sk msg hAbort
              maxAttempts re gh)
          rw [tsum_probOutput_pure_mul]
      · -- h_free: a uniform query leaves the ghost cache (`R`) unchanged.
        rintro t p hp ht ht2 z hz
        rcases t with (n | mc) | msg
        · rw [show (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run p =
              (fun u => (u, p)) <$>
                (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n from rfl] at hz
          obtain ⟨u, _, heq⟩ :=
            (support_map (fun u => (u, p))
              ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) ▸ hz)
          rw [← heq]
        · exact absurd ht (by simp)
        · exact absurd ht2 (by simp)
      · -- charged budget `qH + 1`.
        have h := (hQ pk).2.mono (Nat.le_succ qH)
        convert h using 3 with x
        rcases x with (_ | _) | _ <;> rfl
      · -- growth budget `qS`.
        have h := (hQ pk).1
        convert h using 3 with x
        rcases x with (_ | _) | _ <;> rfl
    refine h_fold.trans ?_
    -- (3) Arithmetic: `enncard ∅ = 0`, `g = ofReal S` with `S = ∑ pᵃ ≤ 1/(1-p)`.
    have h1p : (0 : ℝ) < 1 - p_abort := by linarith
    set S : ℝ := ∑ a ∈ Finset.range maxAttempts, p_abort ^ a with hSdef
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun a _ => pow_nonneg hp₀ a
    have hg_eq : g = ENNReal.ofReal S := by
      rw [hg, hSdef, ENNReal.ofReal_sum_of_nonneg (fun a _ => pow_nonneg hp₀ a)]
      exact Finset.sum_congr rfl fun a _ => by rw [← ENNReal.ofReal_pow hp₀]
    have hSgeo : S ≤ 1 / (1 - p_abort) := by
      rw [hSdef, le_div_iff₀ h1p]
      have hmul := geom_sum_mul p_abort maxAttempts
      nlinarith [pow_nonneg hp₀ maxAttempts]
    rw [QueryCache.enncard_empty, zero_add, hg_eq,
      show ((qH + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((qH : ℝ) + 1) from by
        rw [← ENNReal.ofReal_natCast (qH + 1)]; push_cast; ring_nf,
      show (qS : ℝ≥0∞) = ENNReal.ofReal qS from (ENNReal.ofReal_natCast qS).symm]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hqS : (0 : ℝ) ≤ qS := Nat.cast_nonneg qS
    have hqH1 : (0 : ℝ) ≤ (qH : ℝ) + 1 := by positivity
    calc ((qH : ℝ) + 1) * (qS * S) * ε
        ≤ ((qH : ℝ) + 1) * (qS * (1 / (1 - p_abort))) * ε := by
          gcongr
      _ = qS * ((qH : ℝ) + 1) * ε / (1 - p_abort) := by ring

/-! ## Deferred-sampling eager↔lazy coupling (ghost-read leaf) -/

omit [SampleableType Stmt] in
/-- **Uniform-branch per-query coupling for the eager↔lazy ghost handlers** (banked). On a
uniform query both `ghostHybridImpl … true` and `lazyGhostHybridImpl` forward the draw and
leave the state untouched (`lazyGhostHybridImpl_run_unif_eq`), so they are coupled by the
identity coupling on the shared uniform sample with *equal outputs* and the bad-flag
implication preserved verbatim. This is the divergence-free branch of `h_step`. -/
theorem relTriple_ghostHybrid_lazyGhost_unif (pk : Stmt) (sk : Wit)
    (n : unifSpec.Domain) (e l : GhostState M Commit Chal) (hRel : e.2 = true → l.2 = true) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inl n))).run e)
      ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inl n))).run l)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ (p₁.2.2 = true → p₂.2.2 = true)) := by
  classical
  rw [lazyGhostHybridImpl_run_unif_eq ids M maxAttempts pk sk n l]
  simp only [ghostHybridImpl, StateT.run_mk]
  refine OracleComp.ProgramLogic.Relational.relTriple_bind
    (OracleComp.ProgramLogic.Relational.relTriple_refl
      ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n)) ?_
  rintro u u' rfl
  exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, hRel⟩

omit [SampleableType Stmt] in
/-- **Signing-branch per-query coupling for the eager↔lazy ghost handlers** (banked). On a
signing query both handlers run the *same* `ghostSignBody` over the layered cache, prepend
`msg` to the signed-message list, and leave the bad flag untouched
(`lazyGhostHybridImpl_run_sign_eq`); they are therefore identical, so coupled by the
identity coupling with equal outputs and the bad-flag implication preserved. This is the
second divergence-free branch of `h_step`. -/
theorem relTriple_ghostHybrid_lazyGhost_sign (pk : Stmt) (sk : Wit)
    (msg : M) (e l : GhostState M Commit Chal) (hRel : e.2 = true → l.2 = true) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((ghostHybridImpl ids M maxAttempts true pk sk (.inr msg)).run e)
      ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inr msg)).run l)
      (fun p₁ p₂ => p₁.2.2 = true → p₂.2.2 = true) := by
  classical
  -- The signing handlers copy the input bad flag to the output (`alc ↦ (…, s.2)`), so the
  -- output bad flag is the *constant* `e.2` on the left and `l.2` on the right, independent of
  -- the `ghostSignBody` draw. Couple the two (possibly differently-cached) `ghostSignBody`
  -- runs by *any* coupling (the product coupling from `relTriple_true`), then map both to
  -- `pure`s whose bad flags are `e.2` / `l.2`; the post is then exactly `hRel`.
  rw [lazyGhostHybridImpl_run_sign_eq ids M maxAttempts pk sk msg l]
  simp only [ghostHybridImpl, StateT.run_mk]
  refine OracleComp.ProgramLogic.Relational.relTriple_bind
    (OracleComp.ProgramLogic.Relational.relTriple_true
      ((ghostSignBody ids M pk sk msg maxAttempts).run e.1.1)
      ((ghostSignBody ids M pk sk msg maxAttempts).run l.1.1)) ?_
  rintro a b -
  exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure hRel

/-! ## The ghost-read collision charge (open) -/

omit [SampleableType Stmt] in
/-- **Ghost-read collision bound** for the Prog → Trans hop: the probability that the
adversary ever queries the random oracle at a ghost point (a rejected signing attempt's
programmed point) is at most `qS·(qH+1)·ε/(1-p)`.

Probabilistic content (deferred sampling): a rejected attempt's commitment `w` enters
the ghost layer with the joint law of `(w, c)` conditioned on rejection, and influences
the run only through the ghost-domain membership tests of later adversarial queries.
Per (rejected attempt `j`, adversarial query `k`) pair, the conditional independence of
the post-rejection run from `w` given the rejection event yields
`Pr[query k hits attempt j] ≤ Pr[attempt j runs] · ε` (the `1/Pr[reject]` skew of the
conditioned commitment law cancels against the rejection probability of the attempt).
Summing the expected number of attempts (`≤ 1/(1-p)` per signing query by `hAbort`)
against the `qH` adversarial queries (`hQ`) gives the bound; the budget `qH + 1` leaves
one unit of slack for a verification read, which the freshness check already rules out
(see `ghostHybridImpl_preserves_signed_inv`). Note that for `p_abort < 0` the
hypothesis `hAbort` forces rejection-free signing, so the ghost layer stays empty and
the left-hand side vanishes. -/
lemma probEvent_ghostRead_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
  classical
  -- (A) is PROVEN: the deferred-sampling (lazy) handler's bad-flag probability is bounded.
  have h_lazy :
      Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
          (simulateQ (lazyGhostHybridImpl ids M maxAttempts pk sk) (adv.main pk)).run
            ((((∅, ∅), []) :
              ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
                List M), false)]
        ≤ ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) :=
    probEvent_lazyGhostHybridImpl_bad_le ids hr M maxAttempts adv qS qH ε p_abort
      hp₀ hp hε hQ pk sk hGuess hAbort
  -- (B) RESIDUAL: the eager↔lazy bad-flag equivalence. The eager handler
  -- `ghostHybridImpl … true` and the deferred-sampling handler `lazyGhostHybridImpl` are
  -- definitionally identical on uniform queries (`lazyGhostHybridImpl_run_unif_eq`) and on
  -- signing queries (`lazyGhostHybridImpl_run_sign_eq`); the *entire* distributional gap is
  -- the adversarial random-oracle read step `.inl (.inr mc)`:
  --   * eager: a ghost hit `s.1.1.2 mc = some v` runs `pure (v, (s.1, true))` — the bad flag
  --     flips DETERMINISTICALLY (mass 1) on the structural cache match, the cache key `w` of
  --     which was sampled `w ← ids.commit` during a rejected signing attempt;
  --   * lazy: the read draws `lazyGhostFire (enncard ghost)` and fires with prob `≤ enncard·ε`,
  --     answering from the real layer via `roStep`.
  -- These two read steps have the SAME bad-flag marginal under the never-read-before-write
  -- deferred-sampling commutation: a programmed ghost point `(msg, w)` is only ever READ
  -- (never re-keyed/overwritten — see `ghostHybridImpl_preserves_signed_inv`), so postponing
  -- its draw `w ← ids.commit` from signing time to read time preserves the joint law of the
  -- bad flag. Closing this requires a global induction on `adv.main pk` carrying a deferred-
  -- sampling invariant relating the eager ghost cache (concrete sampled keys) to the lazy
  -- pending count, in the term-equality style of `run_ghostSignBody_overlay` /
  -- `run_ghostSignBody_fst`. It is NOT reducible to a per-state handler equality
  -- (`probOutput_simulateQ_run_eq_of_impl_eq_preservesInv`) — the read handlers genuinely
  -- diverge on the bad-flag marginal at every reachable non-empty-ghost state — nor to a
  -- per-query state coupling (`relTriple_simulateQ_run`), since the eager world has already
  -- committed the sampled keys into the state; the commutation moves the *sampling site*,
  -- changing the structure of the computation, not merely the state relation. This is the
  -- single remaining blocker, the genuine multi-week probabilistic content. Bounding the
  -- eager probability by the lazy one suffices to close the leaf via `h_lazy`.
  have h_eager_le_lazy :
      Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
          (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
            ((((∅, ∅), []) :
              ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
                List M), false)]
        ≤ Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
            (simulateQ (lazyGhostHybridImpl ids M maxAttempts pk sk) (adv.main pk)).run
              ((((∅, ∅), []) :
                ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
                  List M), false)] := by
    -- DEFERRED-SAMPLING COMMUTATION (the eager↔lazy bad-flag dominance). The bookkeeping is
    -- now handled by two banked, general-purpose relational rules:
    --   * `relTriple_simulateQ_run_mono` runs the global free-monad induction on `adv.main pk`,
    --     carrying a coupling invariant `R_couple` between the eager state
    --     `((reCache, ghostEager), signed)` and the lazy state
    --     `((reCache, ghostLazy), signed)`. Unlike `relTriple_simulateQ_run` it permits the two
    --     handlers to return *different* answers at the random-oracle read step, recoupling the
    --     diverged continuations rather than demanding output equality;
    --   * `probEvent_le_of_relTriple_imp` reads the bad-flag marginal inequality off the
    --     resulting coupling, using the post-implication `eager.bad → lazy.bad`.
    -- The uniform and signing steps preserve `R_couple` by the banked definitional handler
    -- equalities (`lazyGhostHybridImpl_run_unif_eq`, `lazyGhostHybridImpl_run_sign_eq`).
    --
    -- ISOLATED RESIDUAL (`h_step`): the per-query divergent-branch coupling. At the read step
    -- the eager handler flips the bad flag with mass 1 on a structural ghost hit, while the lazy
    -- handler fires `lazyGhostFire` with sub-unit mass; pointwise bad-dominance therefore fails
    -- on a single step, and the coupling must instead *resample* the deferred commitment draw
    -- `w ← ids.commit` at read time to match the eager sample-consistent ghost cache. This moves
    -- the sampling site inside the handler body, so it is genuinely a body-level deferred-
    -- sampling commutation, not a state relation — the single remaining multi-week obligation.
    set R_couple : GhostState M Commit Chal → GhostState M Commit Chal → Prop :=
      fun e l => (e.2 = true → l.2 = true) with hR_couple
    -- The per-query divergent-branch coupling required by `relTriple_simulateQ_run_mono`. The
    -- uniform and signing branches are *fully banked* as
    -- `relTriple_ghostHybrid_lazyGhost_unif` / `relTriple_ghostHybrid_lazyGhost_sign`; on those
    -- branches the two handlers return equal outputs (uniform) or are definitionally identical
    -- (signing).
    --
    -- REFUTATION OF THE relTriple ROUTE AT THE READ BRANCH. The state-coupling conjunct
    -- `R_couple p₁.2 p₂.2` (= `eager.bad → lazy.bad`) must hold *pointwise on the support of the
    -- per-step coupling*. At a ghost-hit read state the eager read step is the point mass
    -- `δ_{bad = true}`, while the lazy read step (`lazyGhostFire … >>= roStep`) puts mass
    -- `1 - Pr[fire] > 0` on `bad = false`. Any coupling's left marginal is `δ_{bad = true}`, so
    -- its support is contained in `{true} × _`; for `eager.bad → lazy.bad` to hold there, every
    -- support point must have right component `bad = true`, forcing the right marginal to put no
    -- mass on `bad = false` — contradicting the lazy read's positive `bad = false` mass.
    -- Therefore NO coupling discharges this branch: `h_step` is *false*, not merely hard, and the
    -- `relTriple_simulateQ_run_mono` route below cannot close the leaf. (A direct collision bound
    -- on the eager run is likewise refuted: the ghost keys are pre-drawn at signing time, so each
    -- adversarial read is a deterministic `0/1` hit, never an `ε`-mass event.)
    --
    -- THE ACTUAL ROUTE (marginal / Fubini, not a coupling). Bound the eager bad-flag *marginal*
    -- by the lazy one through a bespoke global induction on `adv.main pk` that tracks the bad-flag
    -- marginal as a `tsum` over the deferred commitment draw, NOT a per-state relation. At the
    -- read step both sides reduce to the SAME `tsum` over the `ids.commit` measure — the eager run
    -- summed over its earlier signing-time draw of `w`, the lazy run summed over its read-time
    -- draw — *before* the divergent continuation is applied, which sidesteps the refutation above.
    -- The single-pending read-time marginal of that `tsum` is now banked as
    -- `lazyGhostFire_one_eq` / `probOutput_lazyGhostFire_one` (GhostBodies.lean): the lazy read
    -- fires with probability exactly `Pr[= w' | Prod.fst <$> ids.commit pk sk]`, which is the same
    -- quantity as the marginal of the eager handler's signing-time draw of `w` over the structural
    -- ghost hit `w = w'`. Lifting this single-pending draw-commutation through the full run is the
    -- remaining multi-week obligation (a `probEvent_marginal_simulateQ_mono` over deferred draws,
    -- which the framework does not yet provide). The dead-end relTriple scaffolding is retained
    -- below only so the leaf still elaborates; the `sorry` discharges the *false* `h_step` and
    -- must be replaced by the marginal induction, NOT by a coupling.
    have h_step : ∀ (t : ((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Domain)
        (e l : GhostState M Commit Chal), R_couple e l →
        OracleComp.ProgramLogic.Relational.RelTriple
          ((ghostHybridImpl ids M maxAttempts true pk sk t).run e)
          ((lazyGhostHybridImpl ids M maxAttempts pk sk t).run l)
          (fun p₁ p₂ => R_couple p₁.2 p₂.2 ∧
            ∀ (ob : _ → OracleComp _
                (M × Option (Commit × Resp))),
              OracleComp.ProgramLogic.Relational.RelTriple
                ((simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (ob p₁.1)).run p₁.2)
                ((simulateQ (lazyGhostHybridImpl ids M maxAttempts pk sk) (ob p₂.1)).run p₂.2)
                (fun q₁ q₂ => R_couple q₁.2 q₂.2)) := by
      sorry
    refine OracleComp.ProgramLogic.Relational.probEvent_le_of_relTriple_imp
      (R := fun p₁ p₂ => R_couple p₁.2 p₂.2) ?_ ?_
    · exact OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run_mono
        (ghostHybridImpl ids M maxAttempts true pk sk)
        (lazyGhostHybridImpl ids M maxAttempts pk sk) R_couple (adv.main pk) h_step
        _ _ (by simp [hR_couple])
    · intro a b hab hbad
      exact hab hbad
  exact h_eager_le_lazy.trans h_lazy

/-! ## Hop lemmas

Each hop is stated per key pair, under pointwise hypotheses at that key; the good-key
event and `δ` enter only once, in the final averaging over `hr.gen`. -/

omit [SampleableType Stmt] in
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
  classical
  set base : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) with hbase
  -- `base` matches the runtime's `withStateOracle` interpreter: both lift `unifSpec` by
  -- `liftTarget` (`unifFwdImpl` is exactly that) and use the caching `randomOracle`.
  have hrt : ∀ {α : Type} (oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α),
      (runtime M).evalDist oa = 𝒟[(simulateQ base oa).run' ∅] := fun {α} oa => by
    rw [hbase]
    rfl
  unfold SignatureAlg.unforgeableExp
  rw [hrt]
  rw [show (FiatShamirWithAbort ids hr M maxAttempts).keygen =
    (liftM hr.gen : OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Stmt × Wit)) from rfl]
  rw [simulateQ_bind, roSim.run'_liftM_bind]
  refine probOutput_congr rfl ?_
  refine congrArg _ (bind_congr fun pksk => ?_)
  obtain ⟨pk, sk⟩ := pksk
  simp only []
  rw [hybridExpAtKey_eq_run_bind]
  -- Fuse the inner WriterT-logging `simulateQ` pass with the outer cache simulation
  -- `simulateQ base` via `writerTMapBase`, so the whole left-hand experiment becomes a
  -- single `simulateQ` over the run-normal-form cache base, still carrying the WriterT log.
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    QueryImpl.simulateQ_writerTMapBase_run]
  -- Remaining: reconcile the fused WriterT-log-over-`StateT cache` run with the hybrid's
  -- flat `StateT (cache × List M)` run. The bridge follows the Sigma-side recipe in
  -- `FiatShamir/Sigma/Stateful/Compatibility.lean`:
  --   1. `base.writerTMapBase implW = (toQueryImpl _).liftTarget _ + (realSignBody …).withLogging`
  --      (a per-query handler equality; the signing handler is `simulateQ base (sign …) =
  --      realSignBody`);
  --   2. `QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog` rewrites the WriterT log
  --      into a `StateT (List M)` input log carrying `[] ++ log.map fst`;
  --   3. `OracleComp.simulateQ_flattenStateT_run` flattens the nested `StateT (List M)
  --      (StateT cache ProbComp)` into the hybrid's flat `StateT (cache × List M) ProbComp`;
  --   4. a state-projection (`map_run_simulateQ_eq_of_query_map_eq`) matches the flattened
  --      handler against `hybridBaseImpl + hybridSignImpl realSignBody` (the lists differ only
  --      by append-vs-prepend ordering, which is invisible to the freshness check);
  --   5. the verify tail matches `hybridVerifyCont` with `wasQueried msg ↔ msg ∈ signed`
  --      via `QueryLog.wasQueried_eq_decide_mem_map_fst`.
  have hHandler : base.writerTMapBase
      ((HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))).liftTarget
          (WriterT (QueryLog (M →ₒ Option (Commit × Resp)))
            (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) +
        (FiatShamirWithAbort (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
          ids hr M maxAttempts).signingOracle pk sk) =
      base.liftTarget
          (WriterT (QueryLog (M →ₒ Option (Commit × Resp)))
            (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) +
        QueryImpl.withLogging
          (fun msg => realSignBody ids M maxAttempts pk sk msg :
            QueryImpl (M →ₒ Option (Commit × Resp))
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) := by
    funext t
    rcases t with bq | sq
    · ext s
      simp [QueryImpl.writerTMapBase, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        HasQuery.toQueryImpl_apply, base, unifFwdImpl]
    · ext s
      simp [QueryImpl.writerTMapBase, QueryImpl.add_apply_inr, SignatureAlg.signingOracle,
        QueryImpl.withLogging_apply, FiatShamirWithAbort, realSignBody, base]
  rw [hHandler]
  -- Provide the cache base as a `HasQuery` instance so the WriterT-log → input-list replay
  -- lemma `QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog` matches
  -- `base.liftTarget _` (it equals `(HasQuery.toQueryImpl).liftTarget _` for this instance).
  letI hq : HasQuery (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := base.toHasQuery
  -- Replay the WriterT log into a `StateT (List M)` input log, flatten the nested
  -- `StateT (List M) (StateT cache ProbComp)` to `StateT (List M × cache) ProbComp`, and
  -- match the flattened handler against `hybridBaseImpl + hybridSignImpl realSignBody` under
  -- the state swap `(List M × cache) → (cache × List M)`.
  set so : QueryImpl (M →ₒ Option (Commit × Resp))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    (fun msg => realSignBody ids M maxAttempts pk sk msg) with hso
  -- (a) the WriterT-log run, mapped to `(out, log.map fst)`, equals the `appendInputLog` run.
  have hreplay := QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
    (spec₀ := unifSpec + (M × Commit →ₒ Chal)) (loggedSpec := M →ₒ Option (Commit × Resp))
    (m₀ := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)
    so (adv.main pk) ([] : List M)
  simp only [] at hreplay
  -- The flattened `appendInputLog` handler.
  set implAppend : QueryImpl
      ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (List M) (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
    (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
      (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)).liftTarget
        (StateT (List M) (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) +
      QueryImpl.appendInputLog so with himplAppend
  -- (c) the flattened handler equals `hybridBaseImpl + hybridSignImpl realSignBody` after
  -- swapping the joint state `(List M × cache) → (cache × List M)`.
  -- `proj` swaps the components and reverses the list: the hybrid prepends each signed
  -- message (`msg :: l`) while `appendInputLog` appends it (`l ++ [msg]`), and reversing
  -- reconciles the two orderings step by step.
  set proj : List M × (M × Commit →ₒ Chal).QueryCache →
      (M × Commit →ₒ Chal).QueryCache × List M := fun s => (s.2, s.1.reverse) with hproj
  have hmatch : ∀ (t : ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Domain)
      (s : List M × (M × Commit →ₒ Chal).QueryCache),
      Prod.map id proj <$> (implAppend.flattenStateT t).run s =
        ((hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M so) t).run (proj s) := by
    rintro ((tu | tro) | tsign) ⟨l, c⟩
    · simp only [hproj, himplAppend, QueryImpl.flattenStateT, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply, hybridBaseImpl, unifFwdImpl]
      rfl
    · have hlhs : (implAppend.flattenStateT (Sum.inl (Sum.inr tro))).run (l, c) =
          roStep M c tro >>= fun a => pure (a.1, (l, a.2)) := by
        rw [himplAppend]
        simp only [QueryImpl.flattenStateT, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          StateT.run_mk]
        erw [StateT.run_monadLift]
        have hbq : (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
            (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) (Sum.inr tro)).run c
            = roStep M c tro := randomOracle_run_eq_roStep M c tro
        rw [StateT.run_bind]
        erw [hbq]
        simp [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp, monad_norm]
      rw [hlhs, hproj]
      simp only [QueryImpl.add_apply_inl]
      erw [hybridBaseImpl_run_ro]
      simp [map_eq_bind_pure_comp, bind_assoc, Function.comp]
    · have hlhs : (implAppend.flattenStateT (Sum.inr tsign)).run (l, c) =
          (so tsign).run c >>= fun a => pure (a.1, (l ++ [tsign], a.2)) := by
        simp [himplAppend, QueryImpl.flattenStateT, QueryImpl.add_apply_inr,
          QueryImpl.appendInputLog_apply, StateT.run_mk, StateT.run_bind, StateT.run_monadLift,
          StateT.run_modifyGet, modify, map_eq_bind_pure_comp, bind_assoc, Function.comp,
          monad_norm]
      rw [hlhs, hproj]
      simp only [QueryImpl.add_apply_inr]
      erw [hybridSignImpl_run]
      simp [map_eq_bind_pure_comp, bind_assoc, Function.comp, List.reverse_append]
  have hflat := fun {β : Type}
      (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))) β) (s : List M × (M × Commit →ₒ Chal).QueryCache) =>
    OracleComp.map_run_simulateQ_eq_of_query_map_eq implAppend.flattenStateT
      (hybridBaseImpl (Commit := Commit) (Chal := Chal) M + hybridSignImpl M so)
      proj hmatch oa s
  -- Final assembly (steps b/d): chain `hreplay` (WriterT-log → `appendInputLog`),
  -- `OracleComp.simulateQ_flattenStateT_run` (flatten the nested `StateT (List M) (StateT cache)`
  -- to `StateT (List M × cache)`), and `hflat` (the `proj`-projection to the hybrid run on
  -- `(cache × List M)`), then identify the verify tail with `hybridVerifyCont` using
  -- `QueryLog.wasQueried_eq_decide_mem_map_fst` (`wasQueried msg ↔ msg ∈ log.map fst ↔
  -- msg ∈ (final signed list).reverse`, membership-invariant under the `proj` list reversal).
  -- (b) Apply `.run ∅` to `hreplay` (a `StateT cache` identity) to obtain a `ProbComp`
  -- identity for the cache-run of the WriterT log, with the log already projected to its
  -- list of queried messages.
  have hreplay' := congrArg
    (fun (g : StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp _) => g.run ∅) hreplay
  simp only [StateT.run_map] at hreplay'
  -- (c) Flatten the nested `StateT (List M) (StateT cache)` run into the joint-state run.
  have hflatten := OracleComp.simulateQ_flattenStateT_run implAppend (adv.main pk) ([] : List M)
    (∅ : (M × Commit →ₒ Chal).QueryCache)
  -- (d) Project the joint-state run onto the hybrid run via `proj`.
  have hflatHybrid := hflat (adv.main pk) (([], ∅) : List M × (M × Commit →ₒ Chal).QueryCache)
  rw [hproj] at hflatHybrid
  simp only [List.reverse_nil] at hflatHybrid
  -- Rewrite the hybrid run on the right as a pure relabelling of the cache-run of the
  -- WriterT-logged adversary, sending `(((msg, σ), log), cache)` to
  -- `((msg, σ), (cache, (log.map fst).reverse))`.
  rw [← hflatHybrid, hflatten, ← hreplay']
  simp only [map_bind, bind_assoc, map_pure, pure_bind, Prod.map, id]
  -- The cache base appearing in the left generator is exactly the `HasQuery.toQueryImpl`
  -- instance used by the replayed run (`hq := base.toHasQuery`).
  rw [show (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
      (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) = base from rfl]
  -- Push the relabelling map into the bind so both sides bind over the same generator.
  rw [bind_map_left]
  refine bind_congr fun p => ?_
  -- For each WriterT-run outcome `p = (((msg, σ), log), cache)`, the left verify tail equals
  -- `hybridVerifyCont` at the relabelled state `((msg, σ), (cache, (log.map fst).reverse))`.
  obtain ⟨⟨⟨msg, σ⟩, log⟩, cache⟩ := p
  simp only [hybridVerifyCont]
  rw [simulateQ_bind]
  simp only [simulateQ_pure, StateT.run_bind, StateT.run', map_bind, bind_map_left]
  refine bind_congr fun verified => ?_
  obtain ⟨ok, c⟩ := verified
  simp only [StateT.run_pure, map_pure, List.nil_append, List.mem_reverse,
    QueryLog.wasQueried_eq_decide_mem_map_fst, decide_not]
  -- Both sides are `!decide (msg ∈ log.map fst) && ok`; they differ only in the choice of
  -- `Decidable` instance for the membership test, which is a subsingleton, so `decide`
  -- agrees on the nose after normalising.
  norm_num [Bool.and_left_comm]

/-- Lift a cache-level hybrid handler to one carrying a never-touched bad flag in its
state, so the `expectedQuerySlack` bridge of `ProgramLogic/Relational/SimulateQ.lean`
applies. The flag is preserved on every step, hence stays `false` along any run started
from `false`. -/
noncomputable def flagLift {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl spec (StateT (σ × Bool) ProbComp) :=
  fun t => StateT.mk fun p =>
    (fun us : spec.Range t × σ => (us.1, (us.2, p.2))) <$> (impl t).run p.1

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma flagLift_run {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (t : spec.Domain) (s : σ) (b : Bool) :
    ((flagLift impl t).run (s, b)) =
      (fun us : spec.Range t × σ => (us.1, (us.2, b))) <$> (impl t).run s := rfl

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- Transport a predicate-targeted query bound across a (propositionally equal) choice of
predicate and `DecidablePred` instance. The predicate is allowed to differ by its match
auxiliary (which arises when the same matches-notation is elaborated in different
modules), and the decidability instance is a subsingleton. -/
lemma isQueryBoundP_cast_pred {ι : Type} {spec : OracleSpec ι} {α : Type}
    {oa : OracleComp spec α} {p₁ p₂ : spec.Domain → Prop}
    {i₁ : DecidablePred p₁} {i₂ : DecidablePred p₂} {n : ℕ} (hp : p₁ = p₂)
    (h : @OracleComp.IsQueryBoundP _ spec α oa p₁ i₁ n) :
    @OracleComp.IsQueryBoundP _ spec α oa p₂ i₂ n := by
  subst hp
  convert h using 2

/-- Arithmetic kernel of the Sign → Prog charge: the discrete first moment of a truncated
geometric series is dominated by the square of its zeroth moment, `∑_{a<m} a·pᵃ ≤
(∑_{a<m} pᵃ)²`. The right-hand convolution `(∑ pᵃ)² = ∑_{i,j} p^{i+j}` collects, for each
`k`, the `k+1` ordered pairs summing to `k`; injecting `(i, j) ↦ (i-j-1, j+1)` exhibits the
left sum as a subset of those nonnegative contributions. -/
lemma sum_natCast_mul_pow_le_sq_sum_pow (p : ℝ) (hp0 : 0 ≤ p) (m : ℕ) :
    ∑ a ∈ Finset.range m, (a : ℝ) * p ^ a ≤ (∑ a ∈ Finset.range m, p ^ a) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  set P := Finset.range m ×ˢ Finset.range m with hP
  set Q := (Finset.range m).sigma (fun i => Finset.range i) with hQ
  have hLHS : ∑ a ∈ Finset.range m, (a : ℝ) * p ^ a = ∑ q ∈ Q, p ^ q.1 := by
    rw [hQ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hLHS, show (∑ a ∈ P, p ^ a.1 * p ^ a.2) = ∑ a ∈ P, p ^ (a.1 + a.2) from
    Finset.sum_congr rfl fun a _ => by rw [pow_add]]
  have himg : ∑ q ∈ Q, p ^ q.1
      = ∑ r ∈ Q.image (fun q => (q.1 - (q.2 + 1), q.2 + 1)), p ^ (r.1 + r.2) := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [hQ, Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hq
      congr 1
      omega
    · intro a ha b hb hab
      rw [Finset.mem_coe, hQ, Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at ha hb
      simp only [Prod.mk.injEq] at hab
      obtain ⟨h1, h2⟩ := hab
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only at *
      have hsnd : a2 = b2 := by omega
      subst hsnd
      have hfst : a1 = b1 := by omega
      subst hfst
      rfl
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun r _ _ => by positivity)
  intro r hr
  rw [Finset.mem_image] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  rw [hQ, Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hq
  rw [hP, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  omega

omit [SampleableType Stmt] in
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
state, plus the expected-attempt-count machinery of `WithAbort/ExpectedCost.lean`.

The nonnegativity hypothesis `hp₀` is necessary: for `p_abort < 0` the claimed loss
shrinks below the genuine adversarial-collision gap `qS·qH·ε` of an abort-free scheme
(the `1/(1-p)` factors fall below `1`), so the statement would be false. The
corresponding bound is available at every call site from the good-key event. -/
lemma probOutput_hybridExpAtKey_real_le_prog
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
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
  classical
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  set σ := (M × Commit →ₒ Chal).QueryCache × List M with hσ
  -- The combined cache-level handlers for the two games.
  set implReal : QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT σ ProbComp) :=
    hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
      hybridSignImpl M (realSignBody ids M maxAttempts pk sk) with himplReal
  set implProg : QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT σ ProbComp) :=
    hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
      hybridSignImpl M (progSignBody ids M pk sk · maxAttempts) with himplProg
  set R : σ → ℝ≥0∞ := fun s => QueryCache.enncard s.1 with hR
  set ζ : ℝ≥0∞ := ENNReal.ofReal ε *
    ∑ a ∈ Finset.range maxAttempts, (a : ℝ≥0∞) * ENNReal.ofReal p_abort ^ a with hζ
  set β : ℝ≥0∞ := ENNReal.ofReal ε *
    ∑ a ∈ Finset.range maxAttempts, ENNReal.ofReal p_abort ^ a with hβ
  set g : ℝ≥0∞ := ∑ a ∈ Finset.range maxAttempts, ENNReal.ofReal p_abort ^ a with hg
  set querySlack : σ → ℝ≥0∞ := fun s => ζ + R s * β with hquerySlack
  -- The per-charged-query TV slack: real-vs-prog within a single signing query.
  have h_step_tv_charged : ∀ (t : _), (· matches .inr _) t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((flagLift implProg t).run (s, false))
          ((flagLift implReal t).run (s, false))) ≤ querySlack s := by
    rintro (t' | msg) hc s
    · exact absurd hc (by simp)
    rcases s with ⟨c, l⟩
    -- Both flag-lifted signing runs are a single (shared, injective) map over the
    -- corresponding cache-level signing body; the map drops out of the TV distance,
    -- and the body-level TV is the proven `signCollisionBound`.
    have hrunProg : (flagLift implProg (Sum.inr msg)).run ((c, l), false) =
        (fun x : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
          (x.1, ((x.2, msg :: l), false))) <$>
            (progSignBody ids M pk sk msg maxAttempts).run c := by
      rw [flagLift_run, himplProg, QueryImpl.add_apply_inr]
      change (fun us => (us.1, us.2, false)) <$>
          ((fun ac : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
            (ac.1, (ac.2, msg :: l))) <$> (progSignBody ids M pk sk msg maxAttempts).run c) = _
      rw [Functor.map_map]
    have hrunReal : (flagLift implReal (Sum.inr msg)).run ((c, l), false) =
        (fun x : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
          (x.1, ((x.2, msg :: l), false))) <$>
            (realSignBody ids M maxAttempts pk sk msg).run c := by
      rw [flagLift_run, himplReal, QueryImpl.add_apply_inr]
      change (fun us => (us.1, us.2, false)) <$>
          ((fun ac : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
            (ac.1, (ac.2, msg :: l))) <$> (realSignBody ids M maxAttempts pk sk msg).run c) = _
      rw [Functor.map_map]
    rw [hrunProg, hrunReal]
    refine le_trans (ENNReal.ofReal_le_ofReal
      (le_trans (tvDist_map_le _ _ _) (le_of_eq (tvDist_comm _ _)))) ?_
    refine le_trans (ofReal_tvDist_run_fsAbortSignLoop_progSignBody_le
      ids M pk sk msg hGuess hAbort maxAttempts c) ?_
    rw [signCollisionBound_eq, hquerySlack, hζ, hβ, hR]
  -- Uncharged (base) queries: the two handlers coincide.
  have h_step_eq_uncharged : ∀ (t : _), ¬ (· matches .inr _) t → ∀ (p : σ × Bool),
      (flagLift implProg t).run p = (flagLift implReal t).run p := by
    rintro (t' | msg) hnc p
    · rw [flagLift_run, flagLift_run, himplProg, himplReal,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inl]
    · exact absurd rfl hnc
  -- The flag is never set: monotonicity is vacuous-by-preservation.
  have h_mono₁ : ∀ (t : _) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((flagLift implProg t).run p), z.2.2 = true := by
    intro t p hp2 z hz
    rw [flagLift_run, support_map] at hz
    obtain ⟨us, -, rfl⟩ := hz
    exact hp2
  -- Expected-resource hypotheses for `expectedQuerySlack_expected_resource_le`.
  have h_charged : ∀ (t : _) (p : σ × Bool), p.2 = false → (· matches .inr _) t →
      ∑' z : _ × σ × Bool, Pr[= z | (flagLift implProg t).run p] * R z.2.1 ≤ R p.1 + g := by
    rintro (t' | msg) p - hc
    · exact absurd hc (by simp)
    rcases p with ⟨⟨c, l⟩, b⟩
    -- Reduce the flag-lifted signing run to the `progSignBody` cache-growth tsum.
    -- The combined-spec `Range (Sum.inr msg)` index of the tsum is only defeq (not
    -- syntactically equal) to `Option (Commit × Resp)`, so we `change` into the
    -- explicit type and rewrite the run as a single map over `progSignBody`.
    have hrun : (flagLift implProg (Sum.inr msg)).run ((c, l), b) =
        (fun x : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
          (x.1, ((x.2, msg :: l), b))) <$>
            (progSignBody ids M pk sk msg maxAttempts).run c := by
      rw [flagLift_run, himplProg, QueryImpl.add_apply_inr]
      change (fun us => (us.1, us.2, b)) <$>
          ((fun ac : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
            (ac.1, (ac.2, msg :: l))) <$> (progSignBody ids M pk sk msg maxAttempts).run c) = _
      rw [Functor.map_map]
    rw [hrun]
    change (∑' z : Option (Commit × Resp) × σ × Bool,
      Pr[= z | (fun x : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
        (x.1, ((x.2, msg :: l), b))) <$>
          (progSignBody ids M pk sk msg maxAttempts).run c] * R z.2.1) ≤ _
    rw [map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
    simp only [Function.comp, tsum_probOutput_pure_mul]
    exact tsum_probOutput_run_progSignBody_mul_enncard_le ids M pk sk msg hAbort maxAttempts c
  have h_growth : ∀ (t : _) (p : σ × Bool), p.2 = false →
      ¬ (· matches .inr _) t → (· matches .inl (.inr _)) t →
      ∀ z ∈ support ((flagLift implProg t).run p), R z.2.1 ≤ R p.1 + 1 := by
    rintro ((n | mc) | msg) p - hnc hg z hz
    · exact absurd hg (by simp)
    · rcases p with ⟨⟨c, l⟩, b⟩
      rw [flagLift_run, himplProg, QueryImpl.add_apply_inl] at hz
      replace hz : z ∈ support ((fun us : Chal × σ => (us.1, (us.2, b))) <$>
          ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache => (cu.1, (cu.2, l))) <$>
            roStep M c mc)) := by
        rw [← hybridBaseImpl_run_ro]; exact hz
      simp only [support_map] at hz
      obtain ⟨cu', ⟨cu'', hcu'', rfl⟩, rfl⟩ := hz
      -- The random-oracle step grows the cache by at most one entry.
      simp only [hR]
      rcases hmc : c mc with _ | v
      · rw [roStep_of_none M hmc] at hcu''
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hcu''
        obtain ⟨ch, -, rfl⟩ := hcu''
        exact QueryCache.enncard_cacheQuery_le c mc ch
      · rw [roStep_of_some M hmc] at hcu''
        rw [(by simpa using hcu'' : cu'' = (v, c))]
        exact le_self_add
    · exact absurd hg (by simp)
  have h_free : ∀ (t : _) (p : σ × Bool), p.2 = false →
      ¬ (· matches .inr _) t → ¬ (· matches .inl (.inr _)) t →
      ∀ z ∈ support ((flagLift implProg t).run p), R z.2.1 ≤ R p.1 := by
    rintro ((n | mc) | msg) p - hnc hng z hz
    · -- Uniform query: forwarded without touching the cache.
      rcases p with ⟨⟨c, l⟩, b⟩
      have hrun : (hybridBaseImpl (Commit := Commit) (Chal := Chal) M (.inl n)).run
          (c, l) = (fun x => (x, (c, l))) <$>
            (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) := by
        simp only [hybridBaseImpl, QueryImpl.add_apply_inl]
        rfl
      rw [flagLift_run, himplProg, QueryImpl.add_apply_inl] at hz
      replace hz : z ∈ support ((fun us : unifSpec.Range n × σ => (us.1, (us.2, b))) <$>
          ((fun x : unifSpec.Range n => (x, ((c, l) : σ))) <$>
            (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)))) := by
        rw [← hrun]; exact hz
      simp only [support_map] at hz
      obtain ⟨x, ⟨y, -, rfl⟩, rfl⟩ := hz
      exact le_rfl
    · exact absurd rfl hng
    · exact absurd rfl hnc
  -- The bridge: run-level TV ≤ accumulated slack + Pr[bad].
  open OracleComp.ProgramLogic.Relational in
  have h_bridge :
      ENNReal.ofReal (tvDist
          ((simulateQ (flagLift implProg) (adv.main pk)).run ((∅, []), false))
          ((simulateQ (flagLift implReal) (adv.main pk)).run ((∅, []), false)))
        ≤ expectedQuerySlack (flagLift implProg)
            (· matches .inr _) querySlack (adv.main pk) qS (((∅, []) : σ), false)
          + Pr[fun z : _ × σ × Bool => z.2.2 = true |
              (simulateQ (flagLift implProg) (adv.main pk)).run (((∅, []) : σ), false)] := by
    refine ofReal_tvDist_simulateQ_run_le_expectedQuerySlack_plus_probEvent_output_bad
      (flagLift implProg) (flagLift implReal) (· matches .inr _) querySlack
      h_step_tv_charged h_step_eq_uncharged h_mono₁ (adv.main pk)
      (queryBudget := qS) ?_ (((∅, []) : σ), false)
    exact isQueryBoundP_cast_pred (by funext x; rcases x with (_ | _) | _ <;> rfl) (hQ pk).1
  -- The bad-flag probability vanishes: the flag is preserved from `false`.
  have h_bad_zero : Pr[fun z : _ × σ × Bool => z.2.2 = true |
      (simulateQ (flagLift implProg) (adv.main pk)).run (((∅, []) : σ), false)] = 0 := by
    refine probEvent_eq_zero fun z hz hbad => ?_
    have hinv : ∀ y ∈ support ((simulateQ (flagLift implProg) (adv.main pk)).run
        (((∅, []) : σ), false)), y.2.2 = false := by
      refine OracleComp.simulateQ_run_preserves_inv_of_query (flagLift implProg)
        (fun s : σ × Bool => s.2 = false) (fun t s hs y hy => ?_) (adv.main pk)
        (((∅, []) : σ), false) rfl
      rw [flagLift_run, support_map] at hy
      obtain ⟨us, -, rfl⟩ := hy
      exact hs
    rw [hinv z hz] at hbad
    exact absurd hbad (by decide)
  -- The accumulated slack is bounded by the resource estimate.
  have h_slack_le : OracleComp.ProgramLogic.Relational.expectedQuerySlack (flagLift implProg)
        (· matches .inr _) querySlack (adv.main pk) qS (((∅, []) : σ), false)
      ≤ (qS : ℝ≥0∞) * ζ +
          ((qS : ℝ≥0∞) * R ((∅, []) : σ) + (qS : ℝ≥0∞) * (qH : ℝ≥0∞)
            + (qS.choose 2 : ℝ≥0∞) * g) * β := by
    refine OracleComp.ProgramLogic.Relational.expectedQuerySlack_expected_resource_le
      (flagLift implProg) (· matches .inr _) (· matches .inl (.inr _)) R ζ β g
      h_charged h_growth h_free (adv.main pk) (qS := qS) (qH := qH) ?_ ?_ ((∅, []) : σ)
    · exact isQueryBoundP_cast_pred (by funext x; rcases x with (_ | _) | _ <;> rfl) (hQ pk).1
    · exact isQueryBoundP_cast_pred (by funext x; rcases x with (_ | _) | _ <;> rfl) (hQ pk).2
  -- The flag-lifted run TV is bounded by the accumulated slack (the bad term vanishes).
  set slack : ℝ≥0∞ := (qS : ℝ≥0∞) * ζ +
      ((qS : ℝ≥0∞) * R ((∅, []) : σ) + (qS : ℝ≥0∞) * (qH : ℝ≥0∞)
        + (qS.choose 2 : ℝ≥0∞) * g) * β with hslack
  have h_flag_tv : ENNReal.ofReal (tvDist
      ((simulateQ (flagLift implProg) (adv.main pk)).run ((∅, []), false))
      ((simulateQ (flagLift implReal) (adv.main pk)).run ((∅, []), false))) ≤ slack := by
    refine le_trans h_bridge ?_
    rw [h_bad_zero, add_zero]
    exact h_slack_le
  -- Project the flag away: the flag-lifted runs map onto the (unflagged) hybrid runs.
  have hprojP : ∀ (t : _) (sb : σ × Bool),
      Prod.map id (Prod.fst : σ × Bool → σ) <$> (flagLift implProg t).run sb =
        (implProg t).run sb.1 := by
    intro t sb
    rw [flagLift_run, Functor.map_map]
    simp only [Prod.map, id_eq, Prod.mk.eta, id_map']
  have hprojR : ∀ (t : _) (sb : σ × Bool),
      Prod.map id (Prod.fst : σ × Bool → σ) <$> (flagLift implReal t).run sb =
        (implReal t).run sb.1 := by
    intro t sb
    rw [flagLift_run, Functor.map_map]
    simp only [Prod.map, id_eq, Prod.mk.eta, id_map']
  have hrunProj_P : (simulateQ implProg (adv.main pk)).run (∅, []) =
      Prod.map id (Prod.fst : σ × Bool → σ) <$>
        (simulateQ (flagLift implProg) (adv.main pk)).run ((∅, []), false) :=
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq (flagLift implProg) implProg
      (Prod.fst : σ × Bool → σ) hprojP (adv.main pk) ((∅, []), false)).symm
  have hrunProj_R : (simulateQ implReal (adv.main pk)).run (∅, []) =
      Prod.map id (Prod.fst : σ × Bool → σ) <$>
        (simulateQ (flagLift implReal) (adv.main pk)).run ((∅, []), false) :=
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq (flagLift implReal) implReal
      (Prod.fst : σ × Bool → σ) hprojR (adv.main pk) ((∅, []), false)).symm
  -- Hence the unflagged run TV is also bounded by the slack.
  have h_run_tv : ENNReal.ofReal (tvDist
      ((simulateQ implProg (adv.main pk)).run (∅, []))
      ((simulateQ implReal (adv.main pk)).run (∅, []))) ≤ slack := by
    rw [hrunProj_P, hrunProj_R]
    exact le_trans (ENNReal.ofReal_le_ofReal (tvDist_map_le _ _ _)) h_flag_tv
  -- Lift the run-level bound to the games through the shared verification continuation.
  have h_games_tv : ENNReal.ofReal (tvDist
      (hybridExpAtKey ids hr M maxAttempts adv (realSignBody ids M maxAttempts pk sk) pk)
      (hybridExpAtKey ids hr M maxAttempts adv
        (progSignBody ids M pk sk · maxAttempts) pk)) ≤ slack := by
    rw [hybridExpAtKey_eq_run_bind, hybridExpAtKey_eq_run_bind, tvDist_comm]
    refine le_trans (ENNReal.ofReal_le_ofReal (tvDist_bind_right_le _ _ _)) ?_
    rw [← himplProg, ← himplReal]
    exact h_run_tv
  -- Convert the game-level TV bound into the probability-output inequality.
  have h_prob : Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (realSignBody ids M maxAttempts pk sk) pk] ≤
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (progSignBody ids M pk sk · maxAttempts) pk] + slack := by
    have habs := abs_probOutput_toReal_sub_le_tvDist
      (hybridExpAtKey ids hr M maxAttempts adv (realSignBody ids M maxAttempts pk sk) pk)
      (hybridExpAtKey ids hr M maxAttempts adv (progSignBody ids M pk sk · maxAttempts) pk)
    have h2 := (abs_le.mp habs).2
    calc Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (realSignBody ids M maxAttempts pk sk) pk]
        = ENNReal.ofReal (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts pk sk) pk].toReal) :=
          (ENNReal.ofReal_toReal probOutput_ne_top).symm
      _ ≤ ENNReal.ofReal (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (progSignBody ids M pk sk · maxAttempts) pk].toReal +
          tvDist (hybridExpAtKey ids hr M maxAttempts adv
              (realSignBody ids M maxAttempts pk sk) pk)
            (hybridExpAtKey ids hr M maxAttempts adv
              (progSignBody ids M pk sk · maxAttempts) pk)) := by
            refine ENNReal.ofReal_le_ofReal ?_; linarith [h2]
      _ = Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (progSignBody ids M pk sk · maxAttempts) pk] +
          ENNReal.ofReal (tvDist _ _) := by
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (tvDist_nonneg _ _),
              ENNReal.ofReal_toReal probOutput_ne_top]
      _ ≤ Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (progSignBody ids M pk sk · maxAttempts) pk] + slack :=
          add_le_add le_rfl h_games_tv
  -- Close: `slack ≤ ofReal(target)` via the `ℝ≥0∞` arithmetic.
  refine le_trans h_prob (add_le_add le_rfl ?_)
  rw [hslack]
  -- The starting cache is empty, so the resource base `R ∅` vanishes.
  have hR0 : R ((∅, []) : σ) = 0 := by rw [hR]; exact QueryCache.enncard_empty
  rw [hR0]
  rcases lt_or_ge ε 0 with hε | hε
  · -- `ε < 0`: the `ofReal ε` factors collapse `ζ` and `β` to `0`.
    have h0 : ENNReal.ofReal ε = 0 := ENNReal.ofReal_eq_zero.mpr hε.le
    have hζ0 : ζ = 0 := by rw [hζ, h0, zero_mul]
    have hβ0 : β = 0 := by rw [hβ, h0, zero_mul]
    rw [hζ0, hβ0, mul_zero, mul_zero, zero_add]
    exact bot_le
  · -- Main case: convert the `ℝ≥0∞` slack into `ofReal` of a real expression.
    set S : ℝ := ∑ a ∈ Finset.range maxAttempts, p_abort ^ a with hSdef
    set Tm : ℝ := ∑ a ∈ Finset.range maxAttempts, (a : ℝ) * p_abort ^ a with hTdef
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun a _ => pow_nonneg hp₀ a
    have hTnn : 0 ≤ Tm :=
      Finset.sum_nonneg fun a _ => mul_nonneg (Nat.cast_nonneg a) (pow_nonneg hp₀ a)
    have hg_eq : g = ENNReal.ofReal S := by
      rw [hg, hSdef, ENNReal.ofReal_sum_of_nonneg (fun a _ => pow_nonneg hp₀ a)]
      exact Finset.sum_congr rfl fun a _ => by rw [← ENNReal.ofReal_pow hp₀]
    have hTsum : (∑ a ∈ Finset.range maxAttempts, (a : ℝ≥0∞) * ENNReal.ofReal p_abort ^ a)
        = ENNReal.ofReal Tm := by
      rw [hTdef, ENNReal.ofReal_sum_of_nonneg
        (fun a _ => mul_nonneg (Nat.cast_nonneg a) (pow_nonneg hp₀ a))]
      exact Finset.sum_congr rfl fun a _ => by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg a), ← ENNReal.ofReal_pow hp₀,
          ENNReal.ofReal_natCast]
    have hζ_eq : ζ = ENNReal.ofReal (ε * Tm) := by
      rw [hζ, hTsum, ← ENNReal.ofReal_mul hε]
    have hβ_eq : β = ENNReal.ofReal (ε * S) := by
      rw [hβ, hg_eq, ← ENNReal.ofReal_mul hε]
    -- The convolution bound `∑ a·pᵃ ≤ (∑ pᵃ)²` and the geometric bound `∑ pᵃ ≤ 1/(1-p)`.
    have hTS : Tm ≤ S ^ 2 := by
      rw [hTdef, hSdef]; exact sum_natCast_mul_pow_le_sq_sum_pow p_abort hp₀ maxAttempts
    have hSgeo : S ≤ 1 / (1 - p_abort) := by
      rw [hSdef, le_div_iff₀ h1p]
      have hmul := geom_sum_mul p_abort maxAttempts
      nlinarith [pow_nonneg hp₀ maxAttempts]
    rw [hζ_eq, hβ_eq, hg_eq, mul_zero, zero_add,
      show (qS : ℝ≥0∞) = ENNReal.ofReal qS from (ENNReal.ofReal_natCast qS).symm,
      show (qH : ℝ≥0∞) = ENNReal.ofReal qH from (ENNReal.ofReal_natCast qH).symm,
      show (qS.choose 2 : ℝ≥0∞) = ENNReal.ofReal (qS.choose 2) from
        (ENNReal.ofReal_natCast _).symm]
    rw [← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    -- Pure real inequality.
    have hchoose : (qS.choose 2 : ℝ) = qS * (qS - 1) / 2 := Nat.cast_choose_two ℝ qS
    have hqS : (0 : ℝ) ≤ qS := Nat.cast_nonneg qS
    have hqH : (0 : ℝ) ≤ qH := Nat.cast_nonneg qH
    have hS2 : S ^ 2 ≤ 1 / (1 - p_abort) ^ 2 := by
      have hsq : S ^ 2 ≤ (1 / (1 - p_abort)) ^ 2 := by gcongr
      rwa [div_pow, one_pow] at hsq
    have hTle : Tm ≤ 1 / (1 - p_abort) ^ 2 := le_trans hTS hS2
    have ht1 : ↑qS * (ε * Tm) ≤ qS * ε / (1 - p_abort) ^ 2 := by
      rw [show (qS : ℝ) * (ε * Tm) = (qS * ε) * Tm by ring,
        show (qS : ℝ) * ε / (1 - p_abort) ^ 2 = (qS * ε) * (1 / (1 - p_abort) ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left hTle (by positivity)
    have ht2 : ↑qS * ↑qH * (ε * S) ≤ qS * qH * ε / (1 - p_abort) := by
      rw [show (qS : ℝ) * qH * (ε * S) = (qS * qH * ε) * S by ring,
        show (qS : ℝ) * qH * ε / (1 - p_abort) = (qS * qH * ε) * (1 / (1 - p_abort)) by ring]
      exact mul_le_mul_of_nonneg_left hSgeo (by positivity)
    have ht3 : (qS.choose 2 : ℝ) * (ε * S ^ 2) ≤ (qS.choose 2 : ℝ) * ε / (1 - p_abort) ^ 2 := by
      rw [show (qS.choose 2 : ℝ) * (ε * S ^ 2) = ((qS.choose 2 : ℝ) * ε) * S ^ 2 by ring,
        show (qS.choose 2 : ℝ) * ε / (1 - p_abort) ^ 2
          = ((qS.choose 2 : ℝ) * ε) * (1 / (1 - p_abort) ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left hS2 (by positivity)
    have hcomb : ↑qS * (ε * Tm) + (↑qS * ↑qH + ↑(qS.choose 2) * S) * (ε * S)
        ≤ qS * ε / (1 - p_abort) ^ 2 + qS * qH * ε / (1 - p_abort)
          + (qS.choose 2 : ℝ) * ε / (1 - p_abort) ^ 2 := by
      rw [show (↑qS * ↑qH + ↑(qS.choose 2) * S) * (ε * S)
          = ↑qS * ↑qH * (ε * S) + (qS.choose 2 : ℝ) * (ε * S ^ 2) by ring]
      linarith [ht1, ht2, ht3]
    refine le_trans hcomb ?_
    rw [hchoose]
    have hne : (1 - p_abort) ^ 2 ≠ 0 := by positivity
    have hkey : (qS : ℝ) * ε / (1 - p_abort) ^ 2 + (qS * (qS - 1) / 2) * ε / (1 - p_abort) ^ 2
        = ↑qS * ε * (↑qS + 1) / (2 * (1 - p_abort) ^ 2) := by
      field_simp
      ring
    rw [show (qS : ℝ) * ε / (1 - p_abort) ^ 2 + qS * qH * ε / (1 - p_abort)
        + (qS * (qS - 1) / 2) * ε / (1 - p_abort) ^ 2
        = ((qS : ℝ) * ε / (1 - p_abort) ^ 2 + (qS * (qS - 1) / 2) * ε / (1 - p_abort) ^ 2)
          + qS * qH * ε / (1 - p_abort) by ring, hkey]
    have hextra : (qS : ℝ) * qH * ε / (1 - p_abort) ≤ qS * (qH + 1) * ε / (1 - p_abort) := by
      gcongr (?_ / (1 - p_abort))
      nlinarith [mul_nonneg hqS hε, hqS, hqH, hε]
    linarith [hextra]

omit [SampleableType Stmt] in
/-- Hop G₁ → G₂ (Prog → Trans) at a fixed key: dropping the reprogramming of rejected
attempts (keeping only the accepted transcript's programming) costs at most
`qS·(qH+1)·ε/(1-p)`.

Proof structure: both games are presented as projections of a single ghost-instrumented
run (`ghostHybridImpl`) over the two-layer cache, with rejected-attempt programmings
routed to the ghost layer. Overlaying the ghost layer recovers the Prog game
(`ghostHybridImpl_proj_prog`) and forgetting it recovers the Trans game
(`ghostHybridImpl_proj_trans`) — the deferred-sampling step. The two instrumented
handlers agree until the adversary reads a ghost point
(`tvDist_simulateQ_run_le_probEvent_output_bad`), the verification tail agrees by the
freshness check and the ghost-domain invariant
(`ghostHybridImpl_preserves_signed_inv`), and the firing probability is bounded by the
ghost-read collision charge `probEvent_ghostRead_bad_le`. -/
lemma probOutput_hybridExpAtKey_prog_le_trans
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
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
  classical
  set s₀ : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
      List M := ((∅, ∅), []) with hs₀
  set runP := (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk)
    (adv.main pk)).run (s₀, false) with hrunP
  set runT := (simulateQ (ghostHybridImpl ids M maxAttempts false pk sk)
    (adv.main pk)).run (s₀, false) with hrunT
  set gP : (M × Option (Commit × Resp)) × GhostState M Commit Chal → ProbComp Bool :=
    fun z => hybridVerifyCont ids hr M maxAttempts pk
      (z.1, (overlayCache M z.2.1.1.1 z.2.1.1.2, z.2.1.2)) with hgP
  set gT : (M × Option (Commit × Resp)) × GhostState M Commit Chal → ProbComp Bool :=
    fun z => hybridVerifyCont ids hr M maxAttempts pk
      (z.1, (z.2.1.1.1, z.2.1.2)) with hgT
  -- Overlay projection of the instrumented run gives the Prog game.
  have hGP : hybridExpAtKey ids hr M maxAttempts adv
      (progSignBody ids M pk sk · maxAttempts) pk = runP >>= gP := by
    rw [hybridExpAtKey_eq_run_bind]
    have hproj := OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (ghostHybridImpl ids M maxAttempts true pk sk)
      (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
        hybridSignImpl M (progSignBody ids M pk sk · maxAttempts))
      (fun g : GhostState M Commit Chal => (overlayCache M g.1.1.1 g.1.1.2, g.1.2))
      (ghostHybridImpl_proj_prog ids M maxAttempts pk sk)
      (adv.main pk) (s₀, false)
    have hinit : (overlayCache M ((s₀, false) : GhostState M Commit Chal).1.1.1
          (s₀, false).1.1.2, ((s₀, false) : GhostState M Commit Chal).1.2) =
        ((∅, []) : (M × Commit →ₒ Chal).QueryCache × List M) := by
      simp [hs₀, overlayCache_empty]
    rw [hinit] at hproj
    rw [← hproj, bind_map_left]
    exact bind_congr fun z => rfl
  -- Ghost-forgetting projection of the instrumented run gives the Trans game.
  have hGT : hybridExpAtKey ids hr M maxAttempts adv
      (transSignBody ids M maxAttempts pk sk) pk = runT >>= gT := by
    rw [hybridExpAtKey_eq_run_bind]
    have hproj := OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (ghostHybridImpl ids M maxAttempts false pk sk)
      (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
        hybridSignImpl M (transSignBody ids M maxAttempts pk sk))
      (fun g : GhostState M Commit Chal => (g.1.1.1, g.1.2))
      (ghostHybridImpl_proj_trans ids M maxAttempts pk sk)
      (adv.main pk) (s₀, false)
    have hinit : ((((s₀, false) : GhostState M Commit Chal).1.1.1,
          ((s₀, false) : GhostState M Commit Chal).1.2)) =
        ((∅, []) : (M × Commit →ₒ Chal).QueryCache × List M) := by
      simp [hs₀]
    rw [hinit] at hproj
    rw [← hproj, bind_map_left]
    exact bind_congr fun z => rfl
  -- Identical-until-bad on the instrumented runs.
  have h_bad :=
    OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
      (ghostHybridImpl ids M maxAttempts true pk sk)
      (ghostHybridImpl ids M maxAttempts false pk sk)
      (adv.main pk) s₀
      (ghostHybridImpl_agree_good ids M maxAttempts pk sk)
      (ghostHybridImpl_bad_mono ids M maxAttempts true pk sk)
      (ghostHybridImpl_bad_mono ids M maxAttempts false pk sk)
  set Pbad := Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal =>
    z.2.2 = true | runP] with hPbad
  -- Ghost-domain invariant along the Trans-side run.
  have h_inv : ∀ z ∈ support runT,
      ∀ q : M × Commit, z.2.1.1.2 q ≠ none → q.1 ∈ z.2.1.2 := by
    intro z hz
    exact OracleComp.simulateQ_run_preserves_inv_of_query
      (ghostHybridImpl ids M maxAttempts false pk sk)
      (fun g : GhostState M Commit Chal =>
        ∀ q : M × Commit, g.1.1.2 q ≠ none → q.1 ∈ g.1.2)
      (fun t s hs =>
        ghostHybridImpl_preserves_signed_inv ids M maxAttempts false pk sk t s hs)
      (adv.main pk) (s₀, false) (fun q hq => by simp [hs₀] at hq)
      z hz
  -- The two verification continuations agree on the Trans-side support.
  have h_eqT : Pr[= true | runT >>= gP] = Pr[= true | runT >>= gT] := by
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support runT
    · congr 1
      by_cases hmem : z.1.1 ∈ z.2.1.2
      · rw [hgP, hgT]
        rw [probOutput_true_hybridVerifyCont_of_mem ids hr M maxAttempts pk
            z.1 _ z.2.1.2 hmem,
          probOutput_true_hybridVerifyCont_of_mem ids hr M maxAttempts pk
            z.1 _ z.2.1.2 hmem]
      · have hagree : ∀ w : Commit,
            overlayCache M z.2.1.1.1 z.2.1.1.2 (z.1.1, w) = z.2.1.1.1 (z.1.1, w) := by
          intro w
          refine overlayCache_apply_ghost_none (M := M) _ ?_
          by_contra hne
          exact hmem (h_inv z hz (z.1.1, w) hne)
        rw [hgP, hgT]
        exact congrArg (fun x => Pr[= true | x])
          (hybridVerifyCont_cache_congr ids hr M maxAttempts pk z.1 _ _ z.2.1.2 hagree)
    · simp [probOutput_eq_zero_of_not_mem_support hz]
  -- Combine: TV budget plus the (open) collision charge.
  have h_tv : tvDist (runP >>= gP) (runT >>= gP) ≤ Pbad.toReal :=
    le_trans (tvDist_bind_right_le gP runP runT) h_bad
  have h_badBound : Pbad ≤ ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) :=
    probEvent_ghostRead_bad_le ids hr M maxAttempts adv qS qH ε p_abort hp₀ hp hε hQ pk sk
      hGuess hAbort
  have h_real : Pr[= true | runP >>= gP].toReal ≤
      Pr[= true | runT >>= gT].toReal + Pbad.toReal := by
    have habs := abs_probOutput_toReal_sub_le_tvDist (runP >>= gP) (runT >>= gP)
    have h2 := (abs_le.mp habs).2
    rw [h_eqT] at h2
    linarith [h_tv]
  have hPbad_ne_top : Pbad ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one
  calc Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (progSignBody ids M pk sk · maxAttempts) pk]
      = Pr[= true | runP >>= gP] := by rw [hGP]
    _ = ENNReal.ofReal (Pr[= true | runP >>= gP].toReal) :=
        (ENNReal.ofReal_toReal probOutput_ne_top).symm
    _ ≤ ENNReal.ofReal (Pr[= true | runT >>= gT].toReal + Pbad.toReal) :=
        ENNReal.ofReal_le_ofReal h_real
    _ = Pr[= true | runT >>= gT] + Pbad := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal probOutput_ne_top, ENNReal.ofReal_toReal hPbad_ne_top]
    _ ≤ Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (transSignBody ids M maxAttempts pk sk) pk] +
        ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
        rw [hGT]
        exact add_le_add le_rfl h_badBound

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

/-! ## The NMA reduction

### Named managed/runtime handlers for the linked-run coupling

The managed NMA run is a two-layer nested simulation: an *inner managed* handler
`nmaOuterImpl pk` (forward uniform, managed-cache RO reads, simulator-loop signing) threads
the inner cache, and an *outer runtime* handler `nmaInnerImpl` (`unifFwdImpl + randomOracle`)
re-simulates the residual live queries. Their `link`, `nmaLinkImpl pk`, is the single
combined simulation over the product cache that the per-step state-coupling projects onto.
These were previously inline `letI` bindings inside `simulatedNmaAdv` and
`managedRun_eq_link_run`; promoting them to top level makes `nmaLinkImpl pk` a nameable
handler so the coupling can be stated and proved one query step at a time. -/

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- **Uniform-only nested-simulation collapse (sub-lemma (b), part (i) — PROVEN, axiom-clean).**
The simulator loop inside `sigSim`/`nmaOuterImpl` is run under the inner managed handler's
uniform branch `unifSim n = fwd (.inl n)`, which forwards each uniform draw transparently into
the sum spec without touching the managed cache. Hence simulating any `unifSpec`-only
computation `oa` under `unifSim` and running the resulting `StateT` at a cache `cache` returns
`oa` lifted into the sum spec with the cache threaded *unchanged*: `(simulateQ unifSim oa).run
cache = (·, cache) <$> liftComp oa _`. This collapses the `simulateQ unifSim (firstSome (sim
pk) maxAttempts)` nested simulation in the sign step back to the bare lifted `firstSome` loop —
the part of `hproj2_sign` that is independent of the live-read/sign collision. -/
lemma simulateQ_unifSim_run {α : Type}
    (oa : OracleComp unifSpec α)
    (cache : (unifSpec + (M × Commit →ₒ Chal)).QueryCache) :
    let spec := unifSpec + (M × Commit →ₒ Chal)
    let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
    let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
      fun n => fwd (.inl n)
    (simulateQ unifSim oa).run cache =
      (fun r => (r, cache)) <$> (liftComp oa (unifSpec + (M × Commit →ₒ Chal))) := by
  intro spec fwd unifSim
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x => simp [unifSim, fwd]
  | query_bind t k ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_query]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
      -- `unifSim t` forwards the uniform query `t` straight through into the sum spec, leaving
      -- the cache untouched.
      have hstep : (unifSim t).run cache
          = (liftComp (query t : OracleComp unifSpec _) spec) >>= fun u => pure (u, cache) := by
        simp only [unifSim, fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
        change ((liftM (query (Sum.inl t)) :
            StateT (unifSpec + (M × Commit →ₒ Chal)).QueryCache
              (OracleComp (unifSpec + (M × Commit →ₒ Chal))) _)).run cache = _
        rw [OracleComp.liftM_run_StateT]
        refine congrArg (· >>= fun u => pure (u, cache)) ?_
        rfl
      rw [hstep, liftComp_bind, map_bind, bind_assoc]
      simp only [pure_bind]
      exact bind_congr (fun u => ih u cache)

/-- The inner *managed* handler of the NMA reduction: forward uniform queries to the live
spec (`unifSim`), answer hash queries through the managed cache (`roSim`, forwarding misses
to the live oracle), and answer signing queries with the simulator loop (`sigSim`), programming
the accepted transcript's challenge into the managed cache. This is the
`(unifSim + roSim) + sigSim` handler used inside `simulatedNmaAdv`. -/
noncomputable def nmaOuterImpl (pk : Stmt) :
    QueryImpl.Stateful (unifSpec + (M × Commit →ₒ Chal))
      ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (unifSpec + (M × Commit →ₒ Chal)).QueryCache :=
  letI spec := unifSpec + (M × Commit →ₒ Chal)
  letI fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  letI unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
    fun n => fwd (.inl n)
  letI roSim : QueryImpl (M × Commit →ₒ Chal)
      (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none => do
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  letI sigSim : QueryImpl (M →ₒ Option (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun msg => do
    let r ← simulateQ unifSim (firstSome (sim pk) maxAttempts)
    match r with
    | some (w, c, z) =>
        modifyGet fun cache => (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
    | none => pure none
  (unifSim + roSim) + sigSim

/-- The outer *runtime* handler of the NMA reduction: forward uniform queries (`unifFwdImpl`)
and answer the residual live random-oracle reads through the runtime's own random oracle
(`randomOracle`), threading the outer cache. This is the
`unifFwdImpl + randomOracle` handler that re-simulates the `.run ∅` boundary in
`simulatedNmaAdv`. -/
noncomputable def nmaInnerImpl :
    QueryImpl.Stateful unifSpec (unifSpec + (M × Commit →ₒ Chal))
      ((M × Commit →ₒ Chal).QueryCache) :=
  unifFwdImpl (M × Commit →ₒ Chal) +
    (randomOracle : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))

/-- The single *linked* handler `nmaOuterImpl pk |>.link nmaInnerImpl` that collapses the
two-layer managed/runtime nesting into one simulation over the product cache
`((unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache)`.
The per-step state-coupling for the NMA bridge is stated against this handler. -/
noncomputable def nmaLinkImpl (pk : Stmt) :
    QueryImpl.Stateful unifSpec
      ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      ((unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache) :=
  (nmaOuterImpl M maxAttempts sim pk).link (nmaInnerImpl M)

/-- The linked-run projection of sub-lemma (b): map the layered ghost-tagged NMA state
`((base, ghost), signed)` onto the linked managed handler's product cache pair. The left
component is the inner managed cache, recovered as `baseEmbed base` (the live-read base layer
embedded into the sum-keyed inner cache, with no signing-programmed points: those live in the
ghost layer); the right component is the outer runtime cache, recovered as the full overlay
`overlayCache base ghost` (live reads plus signing-programmed points). The signed-message list
is forgotten — the linked handler carries no such list. -/
def proj2 (s : NmaGhostState M Commit Chal) :
    (unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache :=
  (baseEmbed M s.1.1, overlayCache M s.1.1 s.1.2)

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), uniform-query step.** On a uniform query the layered ghost-tagged
handler `ghostNmaImpl`, projected by `proj2`, matches the linked managed handler `nmaLinkImpl`
applied to the projected state. The uniform query forwards straight through both handlers
(`unifSim`/`unifFwdImpl`) without touching either cache layer, so the coupling is the
straightforward forward pass. -/
lemma hproj2_unif (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : NmaGhostState M Commit Chal) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inl n))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inl n))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_unif, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
    HasQuery.toQueryImpl_apply, nmaInnerImpl, unifFwdImpl, proj2]
  rfl

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), random-oracle step — cached-read sub-case.** On a random-oracle query at a
point `mc` whose ghost layer misses (`hgm`) and whose base layer already holds a value `v`
(`hbh : s.1.1 mc = some v`), the layered ghost-tagged handler `ghostNmaImpl`, projected by
`proj2`, matches the linked managed handler `nmaLinkImpl` applied to the projected state. Both
sides read the cached value: `ghostNmaImpl` returns `roStep`'s cached branch (base hit), while
the linked `roSim` finds the same value in the inner managed cache (`baseEmbed base`, which holds
the base entry at `.inr mc`) and short-circuits, so neither cache layer is written.

The two RO sub-cases left open (gated by the reachable-state invariant, see `hproj2_sign`'s
docstring and the residual in `hybridSimRun_le_managedRun_verify`) are:

* **fresh live read** (`s.1.1 mc = none`, ghost miss): the read resamples; both sides write the
  sampled value to base/inner (`baseEmbed_cacheQuery`) and to overlay/outer
  (`overlayCache_cacheQuery_real_of_ghost_none`, via the `randomOracle_run_eq_roStep` round-trip).
  This is true and reduces to a `roStep`-on-`overlayCache` match, but the inner-`roSim` /
  outer-`randomOracle` nested-simulation `.run` plumbing is part of the deferred coupling.
* **ghost hit** (`s.1.2 mc ≠ none`): genuinely *not* a per-step state projection — `ghostNmaImpl`
  returns the ghost value leaving its state untouched, whereas the linked `roSim` re-reads through
  the runtime `randomOracle` (recovering the same value from `overlayCache base ghost`) but
  *writes it back* into the inner managed cache's `.inr mc` slot, so the two final inner caches
  differ by exactly that re-cached point. Reconciling it needs the reachable-state invariant "a
  ghost point is never separately live-read" rather than a pointwise projection. -/
lemma hproj2_ro (pk : Stmt) (sk : Wit) (mc : M × Commit) (v : Chal)
    (s : NmaGhostState M Commit Chal) (hgm : s.1.2 mc = none) (hbh : s.1.1 mc = some v) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inr mc))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inr mc))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_ro, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, proj2]
  rw [hgm]
  erw [StateT.run_bind, StateT.run_get]
  simp only [pure_bind, baseEmbed_inr, hbh, roStep_of_some M hbh, map_pure, nmaInnerImpl]
  erw [StateT.run_pure]
  simp only [map_pure, QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst, PFunctor.Lens.State.snd, Prod.map, id_eq, proj2]
  rfl

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), random-oracle step — fresh-live-read sub-case.** On a random-oracle
query at a point `mc` whose ghost layer misses (`hgm`) and whose base layer also misses
(`hbm : s.1.1 mc = none`), the layered ghost-tagged handler `ghostNmaImpl`, projected by
`proj2`, matches the linked managed handler `nmaLinkImpl` applied to the projected state.
Both sides resample a fresh value `c`; `ghostNmaImpl` writes it to the base layer (`roStep`'s
miss branch), while the linked `roSim` misses the inner managed cache (`baseEmbed base`,
which has no entry at `.inr mc` since `base mc = none`) and forwards to the runtime
`randomOracle` (the `randomOracle_run_eq_roStep` round-trip), caching the result both in the
inner managed cache and the outer runtime cache. Under `proj2`, the inner write matches
`baseEmbed_cacheQuery` and the outer write matches `overlayCache_cacheQuery_real_of_ghost_none`. -/
lemma hproj2_ro_fresh (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : NmaGhostState M Commit Chal) (hgm : s.1.2 mc = none) (hbm : s.1.1 mc = none) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inr mc))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inr mc))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_ro, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, proj2]
  rw [hgm]
  erw [StateT.run_bind, StateT.run_get]
  simp only [pure_bind, baseEmbed_inr, hbm]
  rw [QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
  -- Reduce the inner `roSim` body run to a single `query` followed by a base-cache write,
  -- then push `simulateQ nmaInnerImpl` through it: the `.inr mc` query is answered by the
  -- runtime `randomOracle`, whose run is `roStep` on the outer cache.
  conv_rhs =>
    enter [2, 1, 2]
    change (query (Sum.inr mc) : OracleComp (unifSpec + (M × Commit →ₒ Chal)) _) >>=
      fun v => pure (v, (baseEmbed M s.1.1).cacheQuery (Sum.inr mc) v)
  rw [simulateQ_bind]
  simp only [simulateQ_pure]
  conv_rhs =>
    enter [2, 1, 1]
    rw [show (query (Sum.inr mc) : OracleComp (unifSpec + (M × Commit →ₒ Chal)) _) =
        liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inr mc)) from rfl,
      simulateQ_spec_query]
    simp only [nmaInnerImpl, QueryImpl.add_apply_inr]
  rw [StateT.run_bind]
  conv_rhs => enter [2, 1]; erw [randomOracle_run_eq_roStep]
  -- Both sides resample, since the base layer and the overlay both miss at `mc`.
  have hov : overlayCache M s.1.1 s.1.2 mc = none := by simp [overlayCache, hgm, hbm]
  rw [roStep_of_none M hbm, roStep_of_none M hov]
  -- Normalise both sides to a single resample, mapping `c` to a `(c, inner, outer)` triple.
  simp only [bind_pure_comp, StateT.run_pure]
  conv_lhs => erw [Functor.map_map, Functor.map_map]
  conv_rhs => erw [Functor.map_map, Functor.map_map]
  refine map_congr fun c => ?_
  -- Reconcile the cache writes on the two layers: the inner write matches `baseEmbed`'s
  -- `cacheQuery`, the outer write matches the overlay's `cacheQuery` (ghost misses at `mc`).
  simp only [Prod.map, id_eq, proj2, QueryImpl.Stateful.Frame.linkReshape,
    QueryImpl.Stateful.Frame.prod, PFunctor.Lens.State.fst, PFunctor.Lens.State.snd,
    PFunctor.Lens.State.put, PFunctor.Lens.State.mk]
  rw [baseEmbed_cacheQuery, overlayCache_cacheQuery_real_of_ghost_none (M := M) s.1.1 hgm]

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), signing-query step.**

PROVEN IMPOSSIBLE AS A PER-STEP EQUALITY. This unconditional projection equality is *false* at
reachable states: a sign-programmed transcript point `(msg, w)` can coincide with a point
already live in the base layer from a prior adversary random-oracle read, and the projection
`proj₂ ((base, ghost), signed) = (baseEmbed base, overlayCache base ghost)` cannot then recover
the linked managed handler's separate inner/outer cache split from `(base, ghost)` alone (see
`signLiveCollision` in `GhostBodies.lean`). The statement is kept for the documented
nested-simulation reduction it carries and as the pivot point for the collision-accounting
reframe (`hybridSimRun_le_managedRun_verify`); it is NOT used to close the leaf.

BANKED MECHANICAL REDUCTION (the proof body below, sorry-terminated). `link_impl_apply_run`
exposes the linked RHS as the *nested* simulation
`simulateQ nmaInnerImpl ((nmaOuterImpl pk (.inr msg)).run outerCache)`, and `simp [nmaOuterImpl]`
reduces the outer step to the `sigSim` body: a nested `simulateQ unifSim (firstSome (sim pk)
maxAttempts)` followed by the inner-cache programming `cacheQuery (.inr (msg, w)) c`. The LHS is
already `simGhostSignBody` (`liftM (firstSome (sim pk) maxAttempts)` then ghost-layer
`cacheQuery (msg, w) c`). The exposed residual goal is therefore precisely:

  (i)  the uniform-only nested-simulation collapse
       `(simulateQ unifSim (firstSome (sim pk) maxAttempts)).run cache
          = (·, cache) <$> liftM (firstSome (sim pk) maxAttempts)`
       (the simulator loop touches no cache layer; `unifSim n = fwd (.inl n)` forwards each
       uniform draw transparently), then
  (ii) matching the accepted-transcript programming: ghost-layer `cacheQuery (msg, w) c` against
       inner-cache `cacheQuery (.inr (msg, w)) c` under `proj₂`, which is exact *iff*
       `¬ signLiveCollision base msg w` (off the collision event), and otherwise diverges by the
       collision charge.

The reframe routes around the unconditional version via `relTriple_simulateQ_run_mono` +
`probEvent_le_of_relTriple_imp` (the GHOST-leaf machinery), paying (ii)'s collision on the bad
side. The remaining open content is the uniform-only collapse (i), independent of the
collision. -/
lemma hproj2_sign (pk : Stmt) (sk : Wit) (msg : M)
    (s : NmaGhostState M Commit Chal)
    (hs : ∀ q : M × Commit, s.1.2 q ≠ none → q.1 ∈ s.2) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inr msg)).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inr msg)).run (proj2 M s) := by
  rw [ghostNmaImpl_run_sign, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  -- Reduce the linked RHS's outer step `nmaOuterImpl pk (.inr msg)` to the simulator body
  -- `sigSim msg`: a nested simulation `simulateQ unifSim (firstSome (sim pk) maxAttempts)`
  -- followed by inner-cache programming of the accepted transcript. After this the residual is
  -- the uniform-only nested-simulation collapse (i) above; the per-step equality then fails
  -- exactly on `signLiveCollision`, which the leaf's collision-accounting reframe pays on the
  -- bad side rather than discharging here.
  simp only [nmaOuterImpl, QueryImpl.add_apply_inr]
  sorry

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
    -- Run the inner CMA adversary under the managed simulation, then erase the
    -- forgery's own verification point from the returned cache (Option B). The
    -- with-aborts `verify pk msg (some (w', z))` issues exactly one hash query, at
    -- `(msg, w')`; clearing that entry makes `withCacheOverlay advCache verify` miss
    -- there and fall through to the live oracle, so the managed-RO experiment agrees
    -- with the plain EUF-NMA verification on *every* forgery. In particular a replayed
    -- signed `(msg, w')` no longer wins through the programmed challenge, which is what
    -- makes the bridge to `eufNmaAdv.advantage` sound. Other programmed entries sit at
    -- different points and are never read by `verify`.
    (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅ >>= fun result =>
      let ((msg, σ), cache) := result
      let advCache : spec.QueryCache :=
        match σ with
        | some (w', _) => Function.update cache (Sum.inr (msg, w')) none
        | none => cache
      pure ((msg, σ), advCache)

omit [SampleableType Stmt] in
/-- **Nested-simulation fusion for the managed NMA run.** The managed reduction runs the
common adversary `adv.main pk` under the inner managed handler `nmaOuterImpl pk` threading the
inner cache (`StateT spec.QueryCache (OracleComp spec)`), then `.run ∅` re-simulates the
residual live queries under the outer runtime handler `nmaInnerImpl` (`unifFwdImpl +
randomOracle`) threading the outer cache. By `QueryImpl.Stateful.simulateQ_link_run` this
two-layer nesting is a single simulation of the *linked* handler `nmaLinkImpl pk =
(nmaOuterImpl pk).link nmaInnerImpl` over the product cache, up to the canonical `linkReshape`
regrouping of the final state. This collapses the explicit `.run ∅` boundary into a single
`simulateQ` whose state is the genuine `(inner managed cache, outer runtime cache)` pair the
per-step coupling projects onto. -/
lemma managedRun_eq_link_run (pk : Stmt) :
    letI spec := unifSpec + (M × Commit →ₒ Chal)
    (simulateQ (nmaLinkImpl M maxAttempts sim pk) (adv.main pk)).run (∅, ∅) =
      (QueryImpl.Stateful.Frame.prod spec.QueryCache
          ((M × Commit →ₒ Chal).QueryCache)).linkReshape (∅, ∅) <$>
        (simulateQ (nmaInnerImpl M)
          ((simulateQ (nmaOuterImpl M maxAttempts sim pk)
            (adv.main pk)).run ∅)).run ∅ := by
  exact (QueryImpl.Stateful.simulateQ_link_run _ _ (adv.main pk) ∅ ∅)

/-- **State-coupling for the NMA bridge** (genuine two-layer content). At a fixed key pair
the single-cache hybrid run of `hybridExpAtKey`, *followed by its verification-and-freshness
tail* `hybridVerifyCont`, is bounded by the run-normal-form of the managed-RO NMA
experiment: the managed-cache run of `simulatedNmaAdv` (re-simulated under the runtime's
outer `randomOracle`), followed by overlay verification.

The two presentations run the *same* adversary `adv.main pk` but thread the random-oracle
cache through genuinely different layers:

* the **hybrid** (`impl₁ := hybridBaseImpl + hybridSignImpl simSignBody`) keeps a *single*
  cache `(cache, signed)`, into which both live RO reads (`randomOracle`) and the signing
  simulation's accepted-transcript programming (`simSignBody` via `signProgramCont`) write;
* the **managed reduction** (`simulatedNmaAdv.main`) keeps an *inner managed* cache threaded
  by `roSim`/`sigSim`, whose live `fwd` reads are resolved by the runtime's *separate outer*
  `randomOracle` cache. `simulateQ_compose` (`∘ₛ`) does not collapse these two layers because
  the inner `.run ∅` boundary turns `roSim`/`fwd` misses into live queries answered by the
  outer oracle.

The coupling claim is that the *overlay* of the inner managed cache onto the outer runtime
cache reproduces the single hybrid cache throughout the run (a state-projection in the sense
of `OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'`), and that the signed-message list
matches the set of points the managed simulation programmed (a cache invariant in the style
of `fsAbortSignLoop_cache_invariant`). On `msg ∈ signed` the freshness conjunct kills the
left side (`probOutput_true_hybridVerifyCont_of_mem`); on fresh forgeries the
`withCacheOverlay` verification agrees with the live verification at the verification point
(`withCacheOverlay_verify_eq_of_miss`, since the managed point at `(msg, w')` carries the
programmed challenge that equals the hybrid's cached value, while the freshness check rules
out a stale read). Hence the per-forgery success of the hybrid tail is at most that of the
overlay verification, and the bound follows. -/
lemma hybridSimRun_le_managedRun_verify (pk : Stmt) (sk : Wit) :
    Pr[= true | (simulateQ
          (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
            hybridSignImpl M (simSignBody M maxAttempts sim pk sk))
          (adv.main pk)).run (∅, []) >>= hybridVerifyCont ids hr M maxAttempts pk] ≤
      Pr[= true | (fun x : Bool × _ => x.1) <$> do
        let p ← (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pk)).run ∅
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          (withCacheOverlay p.1.2 ((FiatShamirWithAbort ids hr M maxAttempts).verify
            pk p.1.1.1 p.1.1.2))).run p.2] := by
  -- Step 1 (banked, axiom-clean): collapse the explicit `.run ∅` re-simulation boundary on
  -- the RHS. Distributing the outer `simulateQ` over `simulatedNmaAdv`'s post-processing bind
  -- (`simulateQ_bind`/`StateT.run_bind`) exposes the nested managed run
  --   `(simulateQ (unifFwd+ro) ((simulateQ ((unifSim+roSim)+sigSim) (adv.main pk)).run ∅)).run ∅`,
  -- which `managedRun_eq_link_run` rewrites to the canonical `linkReshape` of a *single*
  -- linked simulation `(simulateQ (outer.link inner) (adv.main pk)).run (∅, ∅)` over the
  -- product cache `(inner managed cache, outer runtime cache)`. After this rewrite the RHS is
  -- a single `simulateQ` whose state is genuinely the inner/outer cache pair, so the coupling
  -- to the hybrid is a plain `map_run_simulateQ_eq_of_query_map_eq_inv'` state-projection (no
  -- nesting). The fusion lemma `managedRun_eq_link_run` is proven and axiom-clean.
  --
  -- RESIDUAL SUBGOAL (the genuinely hard, still-open content): the state-projection coupling
  -- of `impl₁ := hybridBaseImpl + hybridSignImpl simSignBody` (single state `(reCache, signed)
  -- : (M × Commit →ₒ Chal).QueryCache × List M`) against `impl₂ := outer.link inner` (state
  -- `(innerCache, outerCache) : spec.QueryCache × (M × Commit →ₒ Chal).QueryCache`), followed
  -- by the verify-tail split.
  --
  -- DESIGN OBSTRUCTION FOUND (corrects the original `proj` recipe). A per-step replay of both
  -- handlers shows the linked caches evolve as:
  --   * `outerCache` accumulates *only live RO reads* (`roSim` forwards inner misses to `fwd`,
  --     re-simulated by `inner`'s `randomOracle`, which writes the outer layer); signing's
  --     `sigSim` programs the *inner* layer only and never forwards to the outer oracle;
  --   * `innerCache` accumulates *both* live RO reads *and* the signing-programmed points.
  -- Hence `reCache = innerCache` and `overlayCache outerCache innerCache = reCache`
  -- throughout — matching the docstring's overlay claim. The problem is that the verifying
  -- direction of `map_run_simulateQ_eq_of_query_map_eq_inv'` requires `proj` to be a *total
  -- function of the hybrid state* `(reCache, signed)` whose value reproduces the linked state
  -- pair *exactly* (not just up to overlay): `(impl₂ t).run (proj s) = Prod.map id proj <$>
  -- (impl₁ t).run s`. But `outerCache = reCache ∖ {signing-only-programmed points}` is **not a
  -- function of `(reCache, signed)`**: a point `(msg, w)` with `msg ∈ signed` may have entered
  -- `reCache` either by a live RO read (then it is in `outerCache`) or by `signProgramCont`
  -- (then it is *absent* from `outerCache`), and the current hybrid state records no flag
  -- distinguishing the two. Defining `proj.outerCache := reCache` fails on the signing step
  -- (hybrid writes the programmed point to `reCache`, so `proj.outerCache` would gain it, but
  -- the linked `outerCache` does not), and the restricted-by-`signed` choice fails on live
  -- reads at signed messages (those *are* in the linked `outerCache`). The split therefore
  -- depends on per-query programming history that neither the hybrid `(reCache, signed)` nor
  -- the linked cache pair records on its own — so the coupling is *not* a single
  -- `map_run_simulateQ_eq_of_query_map_eq_inv'` over the existing states.
  --
  -- RESOLUTION (not yet built; ~150–250 lines of new infrastructure). Run the hybrid (or the
  -- linked managed handler) on an *enriched, layered* cache state that explicitly tags each
  -- entry as live-read vs signing-programmed — the same `overlayCache`/ghost-layer device
  -- already used for the Prog→Trans hop in `GhostBodies` (`ghostHybridImpl`, `GhostState`,
  -- `run_ghostSignBody_overlay`/`_fst`). On that layered state the partition *is* a function
  -- of the state, both projection directions (`overlay`-to-hybrid and `forget`-to-managed) are
  -- per-step state projections, and `map_run_simulateQ_eq_of_query_map_eq_inv'` applies. The
  -- verify-tail then splits on `result.1.1 ∈ signed` exactly as in the original recipe:
  -- `probOutput_true_hybridVerifyCont_of_mem` zeroes the LHS on `msg ∈ signed`, while on fresh
  -- forgeries `withCacheOverlay_verify_eq_of_miss` + `hybridVerifyCont_cache_congr` align the
  -- overlay verification with the live verification. The fusion (Step 1) and the verify-tail
  -- toolkit are in place; the open content is the layered-state projection.
  --
  -- STEP 1 (executed below, axiom-clean): the mechanical link-fusion plumbing. Distributing
  -- `simulateQ_bind`/`StateT.run_bind` over `simulatedNmaAdv.main`'s Option-B post-processing
  -- bind exposes the bare nested managed run, and `managedRun_eq_link_run` rewrites it to the
  -- single linked simulation `(simulateQ (outer.link inner) (adv.main pk)).run (∅, ∅)`.
  simp only [simulatedNmaAdv, simulateQ_bind, StateT.run_bind, bind_assoc]
  -- The RHS is now `(fun x => x.1) <$> do let p ← (simulateQ (unifFwd+ro)
  --   ((simulateQ ((unifSim+roSim)+sigSim) (adv.main pk)).run ∅)).run ∅; (Option-B post)…`,
  -- with the bare nested managed run exposed. `managedRun_eq_link_run` equates this nested
  -- run (modulo the canonical `linkReshape <$> _` regrouping of the final state) with the
  -- single linked simulation `(simulateQ (outer.link inner) (adv.main pk)).run (∅, ∅)`.
  --
  -- REMAINING SUBGOAL (the genuine still-open content). With the nested boundary exposed, the
  -- bound is the state-projection coupling described above: a layered ghost-tagged handler that
  -- partitions each cache point as live-read (base layer) vs signing-programmed (ghost layer),
  -- projecting (a) by `overlayCache` to the single hybrid cache and (b) by the
  -- `randomOracle_run_eq_roStep` round-trip to the linked (inner,outer) pair under the invariant
  -- "every ghost-tagged point's msg ∈ signed", then (c) the verify-tail split on `msg ∈ signed`
  -- (`probOutput_true_hybridVerifyCont_of_mem`, `withCacheOverlay_verify_eq_of_miss`,
  -- `hybridVerifyCont_cache_congr`). The fusion `simp only` above is the executed, axiom-clean
  -- Step 1; the layered-state projection is the open content.
  --
  -- BANKED (sub-lemma (a), axiom-clean, `GhostBodies.lean`). The layered ghost-tagged handler
  -- is now built: `ghostNmaImpl` over the state `((baseCache, ghostCache), signed)` (abbrev
  -- `NmaGhostState`), with `simGhostSignBody`/`ghostSignProgramCont` writing the accepted
  -- transcript to the ghost layer and the base oracles writing live RO reads to the base layer.
  -- The overlay projection back to the plain single-cache hybrid is proven:
  --   `ghostNmaImpl_proj_hybrid` (per step) and
  --   `map_run_simulateQ_ghostNmaImpl_overlay`/`_empty` (full run), via
  --   `OracleComp.map_run_simulateQ_eq_of_query_map_eq` with
  --   `proj ((base, ghost), signed) = (overlayCache base ghost, signed)`.
  -- Hence the hybrid LHS equals `Pr[= true | (overlay-projected ghostNmaImpl run) >>= …]`.
  --
  -- EXACT OPEN RESIDUAL (sub-lemma (b), not landed; ~2-3 weeks). Couple the *same* layered run
  -- `(simulateQ (ghostNmaImpl …) (adv.main pk)).run ((∅,∅), [])` to the linked managed run
  -- `(simulateQ (outer.link inner) (adv.main pk)).run (∅, ∅)` (from `managedRun_eq_link_run`)
  -- under the projection `proj₂ ((base, ghost), signed) = (baseEmbed base, overlayCache base
  -- ghost)` onto the linked `(outerCache : spec.QueryCache, innerCache : (M×Commit→ₒChal).
  -- QueryCache)` pair (outer = live-read layer = base, inner = full hybrid cache = overlay).
  -- The per-step `hproj` linchpin is NOT a primitive-query projection against `outer.link inner`:
  -- by `linkWith_apply_run`, each `(outer.link inner) t` step is itself a *nested*
  -- `simulateQ inner ((outer t).run …)`, where `outer t` (roSim/sigSim) is a multi-query
  -- composite — roSim does an inner cache lookup then forwards a miss to `fwd` (re-simulated by
  -- `inner`'s `randomOracle`, the `randomOracle_run_eq_roStep` round-trip), and sigSim runs a
  -- whole `simulateQ unifSim (firstSome (sim pk) maxAttempts)`. So (b) requires coupling
  -- `ghostNmaImpl` against the *nested-simulation* form of the managed handler step-by-step,
  -- under the ghost-domain invariant "every ghost point's msg ∈ signed" (cf.
  -- `ghostHybridImpl_preserves_signed_inv` for the sibling hop), so that on the RO step the
  -- live read writes the base layer and outer cache identically, while the signing step's ghost
  -- write matches the inner cache's `cacheQuery (.inr (msg, w)) c` and never touches the outer.
  -- This is the genuine multi-week content; (a) and the verify-tail toolkit (c) are in place.
  --
  -- BANKED toward (b) (axiom-clean, `GhostBodies.lean`). The ghost-domain *gate* and the left
  -- component of `proj₂` are now built and proven:
  --   * `ghostNmaImpl_preserves_signed_inv` — the invariant "every ghost-layer point's msg ∈
  --     signed" is preserved by every `ghostNmaImpl` step (NMA analogue of
  --     `ghostHybridImpl_preserves_signed_inv`), backed by the new support fact
  --     `simGhostSignBody_support_ghost` (the signing body only writes ghost points whose msg is
  --     the signed message). This is exactly the `inv` to feed
  --     `map_run_simulateQ_eq_of_query_map_eq_inv'`.
  --   * `baseEmbed` (+ `baseEmbed_inr`/`baseEmbed_inl`/`baseEmbed_cacheQuery`) — the embedding
  --     of a base RO cache (keyed by `M × Commit`) into the outer runtime cache (keyed by the
  --     sum spec), i.e. the left component of `proj₂ ((base,ghost),signed) = (baseEmbed base,
  --     overlayCache base ghost)`; `baseEmbed_cacheQuery` provides the RO-step algebra
  --     `baseEmbed (base.cacheQuery mc v) = (baseEmbed base).cacheQuery (.inr mc) v`.
  -- DONE: the local `outer`/`inner`/`roSim`/`sigSim`/`unifSim` lets of
  -- `simulatedNmaAdv`/`managedRun_eq_link_run` are now top-level handlers `nmaOuterImpl`,
  -- `nmaInnerImpl`, and `nmaLinkImpl := (nmaOuterImpl …).link (nmaInnerImpl …)`, so the linked
  -- handler is nameable; `managedRun_eq_link_run` is re-expressed in terms of them and stays
  -- axiom-clean. The per-step coupling is stated as
  --   `hproj₂ : Prod.map id proj₂ <$> (ghostNmaImpl t).run s
  --              = (nmaLinkImpl M maxAttempts sim pk t).run (proj₂ s)`
  -- with `proj₂ ((base, ghost), signed) = (baseEmbed base, overlayCache base ghost)`, split into
  -- `hproj2_unif`, `hproj2_ro`, `hproj2_ro_fresh` (all PROVEN, axiom-clean) and `hproj2_sign`.
  --
  -- R19 REFRAME (collision-accounting; the per-step sign equality is PROVEN IMPOSSIBLE). The
  -- unconditional sign-step equality `hproj2_sign` is *false*: a sign-programmed `(msg, w)` can
  -- coincide with a base-layer live read (the `signLiveCollision` event, `GhostBodies.lean`),
  -- and `proj₂` cannot recover the linked inner/outer split from `(base, ghost)` at such a point.
  -- Since this leaf is an *inequality* (`≤`), the route is the GHOST-leaf machinery
  -- (`relTriple_simulateQ_run_mono` + `probEvent_le_of_relTriple_imp`): an *exact coupling off
  -- the collision event* (where `proj₂` IS a state function, so the per-step coupling is an
  -- equality) PLUS the collision probability paid on the bad side via the commit-guessing charge
  -- `probEvent_commit_hit_le` (live-read count · ε) — the SAME charge class as the ghost-read
  -- collision `probEvent_ghostRead_bad_le`.
  --
  -- BANKED THIS ROUND (axiom-clean):
  --   * `signLiveCollision` / `not_signLiveCollision_iff` (`GhostBodies.lean`) — the exact
  --     state-level collision event distinguishing the two runs, and its no-collision negation
  --     `base (msg, w) = none` under which the sign-step projection is exact.
  --   * `simulateQ_unifSim_run` (above) — sub-lemma (b) PART (i), the uniform-only
  --     nested-simulation collapse `(simulateQ unifSim oa).run cache = (·, cache) <$> liftComp oa`
  --     for any `unifSpec`-only `oa`. This collapses the `simulateQ unifSim (firstSome (sim pk)
  --     maxAttempts)` loop inside `sigSim`/`nmaOuterImpl` back to the bare lifted `firstSome`
  --     loop, exactly the collision-independent half of `hproj2_sign`. `hproj2_sign`'s proof body
  --     now executes the `link_impl_apply_run` + `nmaOuterImpl` reduction exposing this
  --     nested loop as its residual goal.
  --
  -- EXACT REMAINING RESIDUAL. (1) Finish `hproj2_sign` *conditioned on no collision*
  -- (`¬ signLiveCollision base msg w`): push `simulateQ nmaInnerImpl` through the collapsed
  -- `firstSome` loop (via `simulateQ_unifSim_run`) and match the ghost-layer `cacheQuery (msg, w)
  -- c` against the inner-cache `cacheQuery (.inr (msg, w)) c` under `proj₂` (exact off-collision).
  -- (2) Assemble the off-collision per-step couplings (`hproj2_unif`/`_ro`/`_ro_fresh` plus the
  -- conditional sign step) into a global `relTriple_simulateQ_run_mono` coupling whose
  -- post-implication pays the collision mass through `probEvent_commit_hit_le`, then split the
  -- verify tail on `msg ∈ signed` (`probOutput_true_hybridVerifyCont_of_mem`,
  -- `withCacheOverlay_verify_eq_of_miss`, `hybridVerifyCont_cache_congr`). The fusion (Step 1),
  -- sub-lemma (a), the invariant gate, the `baseEmbed` algebra, part (i), the collision predicate,
  -- and the verify-tail toolkit are all in place.
  sorry

/-- **Per-key cache-overlay invariant** (core of the NMA bridge): at a fixed key pair the
simulated single-cache hybrid (with the freshness check) is bounded by the run-normal-form
of the managed-RO NMA experiment — the managed-cache run of `simulatedNmaAdv` followed by
overlay verification, all under the runtime's `randomOracle` layer.

This is the genuine distributional content of `probOutput_hybridExp_sim_le_managedRoNmaExp`:
the inner managed cache threaded by `roSim`/`sigSim` together with the runtime's outer
`randomOracle` layer reproduces the single-cache hybrid run of `hybridExpAtKey`, and on
fresh forgeries the `withCacheOverlay` verification agrees with the live oracle at the
verification point (a cache invariant in the style of `fsAbortSignLoop_cache_invariant`:
every entry programmed by the signing simulation has its message recorded in the signed
list, so the freshness conjunct can only decrease the left-hand side). -/
lemma hybridExp_sim_le_managedRun_perKey
    (ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))
    (hro : ro = randomOracle) (pk : Stmt) (sk : Wit) :
    Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (simSignBody M maxAttempts sim pk sk) pk] ≤
      Pr[= true | (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
        ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pk >>= fun result =>
          withCacheOverlay result.2
            ((FiatShamirWithAbort ids hr M maxAttempts).verify
              pk result.1.1 result.1.2))).run' ∅] := by
  subst hro
  -- Put the hybrid LHS into run-normal-form (`run` of the hybrid handler on `adv.main pk`
  -- followed by the verify-and-freshness tail `hybridVerifyCont`).
  rw [hybridExpAtKey_eq_run_bind]
  -- Put the managed RHS into run-normal-form: `simulateQ_bind` distributes the outer RO
  -- simulation over the managed run and the overlay verification, and `StateT.run'`/`run`
  -- exposes the `(forgery, runtimeCache)` bind as a `ProbComp` bind whose final value is the
  -- forgery's verification bit (`pure p.1`).
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  exact hybridSimRun_le_managedRun_verify ids hr M maxAttempts sim adv pk sk

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
  classical
  -- Abbreviation for the runtime random-oracle simulator.
  set ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := randomOracle with hro
  -- Normal form of the managed-RO NMA experiment: the runtime's `withStateOracle`
  -- semantics unfolds to a single `simulateQ … |>.run' ∅`, and the lifted key
  -- generation pulls out as an ordinary `ProbComp` bind via `roSim.run'_liftM_bind`.
  have hRHS : Pr[= true | SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv)] =
      Pr[= true | hr.gen >>= fun pksk =>
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
          ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pksk.1 >>= fun result =>
            withCacheOverlay result.2
              ((FiatShamirWithAbort ids hr M maxAttempts).verify
                pksk.1 result.1.1 result.1.2))).run' ∅] := by
    unfold SignatureAlg.managedRoNmaExp
    -- Expose the bundled `withStateOracle` semantics as a run-normal-form ProbComp.
    change Pr[= true | 𝒟[(simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
        (do
          let (pk, _) ← (FiatShamirWithAbort ids hr M maxAttempts).keygen
          let result ← (simulatedNmaAdv ids hr M maxAttempts sim adv).main pk
          withCacheOverlay result.2
            ((FiatShamirWithAbort ids hr M maxAttempts).verify
              pk result.1.1 result.1.2))).run' ∅]] = _
    -- `keygen = monadLift hr.gen`; pull it out of the simulation.
    rw [show (FiatShamirWithAbort ids hr M maxAttempts).keygen =
      (liftM hr.gen : OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Stmt × Wit)) from rfl]
    rw [simulateQ_bind, roSim.run'_liftM_bind]
    rfl
  rw [hRHS]
  -- Reduce to a per-key statement under the shared `hr.gen` prefix.
  refine probOutput_bind_mono fun pksk _ => ?_
  -- Per-key core: the simulated hybrid (with the freshness check) is bounded by the
  -- managed-cache run of `simulatedNmaAdv` followed by overlay verification. This is the
  -- cache-overlay invariant: the inner managed cache `roSim` plus the runtime's outer
  -- `randomOracle` layer reproduces the single-cache hybrid, and on fresh forgeries the
  -- overlay agrees with the live oracle at the verification point.
  obtain ⟨pk, sk⟩ := pksk
  exact hybridExp_sim_le_managedRun_perKey ids hr M maxAttempts sim adv ro hro pk sk

/-! ## Bridge to the plain EUF-NMA interface

Option B makes `simulatedNmaAdv` discard the forgery's own verification point from the
returned managed cache. The single hash query issued by `FiatShamirWithAbort.verify`
therefore always *misses* in the overlay and falls through to the live oracle, so the
overlay verification coincides — as an `OracleComp` — with the plain verification. This
collapses the managed-RO NMA experiment onto the plain EUF-NMA experiment of the
cache-forgetting adversary `simulatedEufNmaAdv`, making the bound
`Pr[managedRoNmaExp simulatedNmaAdv] ≤ simulatedEufNmaAdv.advantage` sound. -/

omit [SampleableType Stmt] [SampleableType Chal] in
/-- If a cache misses at the forgery's verification point `Sum.inr (msg, w')`, the overlay
verification of `FiatShamirWithAbort.verify pk msg (some (w', z))` agrees with the plain
live verification: the single query at `Sum.inr (msg, w')` misses and is forwarded live.
The `none` case is verification-free, so it is trivially overlay-insensitive. -/
lemma withCacheOverlay_verify_eq_of_miss
    (cache : (unifSpec + (M × Commit →ₒ Chal)).QueryCache) (pk : Stmt)
    (msg : M) (σ : Option (Commit × Resp))
    (hmiss : ∀ w' z, σ = some (w', z) → cache (Sum.inr (msg, w')) = none) :
    withCacheOverlay cache
        ((FiatShamirWithAbort (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
          ids hr M maxAttempts).verify pk msg σ) =
      (FiatShamirWithAbort (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts).verify pk msg σ := by
  cases σ with
  | none => simp only [FiatShamirWithAbort, withCacheOverlay_pure]
  | some wz =>
      obtain ⟨w', z⟩ := wz
      have hm : cache (Sum.inr (msg, w')) = none := hmiss w' z rfl
      change withCacheOverlay _
          ((query (Sum.inr (msg, w')) :
            OracleComp (unifSpec + (M × Commit →ₒ Chal))
              ((unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inr (msg, w')))) >>=
            fun c => pure (ids.verify pk w' c z)) =
        (query (Sum.inr (msg, w')) :
            OracleComp (unifSpec + (M × Commit →ₒ Chal))
              ((unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inr (msg, w')))) >>=
            fun c => pure (ids.verify pk w' c z)
      rw [withCacheOverlay_bind_pure, bind_pure_comp]
      congr 1
      exact withCacheOverlay_query_miss _ (Sum.inr (msg, w')) hm

/-- The plain EUF-NMA adversary underlying `simulatedNmaAdv`: run the same managed
simulation of the CMA adversary, but forget the returned cache and verify in the plain
random-oracle model. By Option B (`withCacheOverlay_verify_eq_of_miss`) the managed-RO NMA
experiment of `simulatedNmaAdv` coincides with the plain EUF-NMA experiment of this
adversary. -/
noncomputable def simulatedEufNmaAdv :
    SignatureAlg.eufNmaAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts) where
  main pk := Prod.fst <$> (simulatedNmaAdv ids hr M maxAttempts sim adv).main pk

omit [SampleableType Stmt] in
/-- **Soundness of the managed-RO → plain EUF-NMA bridge** (Option B). The managed-RO NMA
success probability of `simulatedNmaAdv` equals the plain EUF-NMA success probability of
`simulatedEufNmaAdv`. The Option B post-processing erases the forgery's own verification
point from the returned cache, so `withCacheOverlay` agrees with the plain live verifier
on every forgery (`withCacheOverlay_verify_eq_of_miss`); in particular a replayed signed
forgery no longer wins through a programmed challenge. -/
lemma managedRoNmaExp_simulatedNmaAdv_eq_eufNmaExp :
    SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv) =
      SignatureAlg.eufNmaExp (runtime M)
        (simulatedEufNmaAdv ids hr M maxAttempts sim adv) := by
  unfold SignatureAlg.managedRoNmaExp SignatureAlg.eufNmaExp
  refine congrArg (runtime M).evalDist ?_
  refine bind_congr fun pksk => ?_
  -- Reduce the eufNma side `Prod.fst <$> _` to a bind, so both sides bind over
  -- `simulatedNmaAdv.main`, then compare the verification wrappers pointwise.
  change ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pksk.1 >>= fun result =>
      withCacheOverlay result.2
        ((FiatShamirWithAbort ids hr M maxAttempts).verify
          pksk.1 result.1.1 result.1.2)) =
    (Prod.fst <$> (simulatedNmaAdv ids hr M maxAttempts sim adv).main pksk.1) >>= fun ms =>
      (FiatShamirWithAbort ids hr M maxAttempts).verify pksk.1 ms.1 ms.2
  rw [map_eq_bind_pure_comp, bind_assoc]
  -- Unfold `.main` to expose the inner managed run followed by the Option-B
  -- post-processing, then `bind_congr` over the inner run.
  simp only [simulatedNmaAdv, bind_assoc, pure_bind, Function.comp_apply]
  refine bind_congr fun r => ?_
  -- `r.1.2` is the inner forgery's signature; the post-processed cache erases its own
  -- verification point, so the overlay verification agrees with the plain verification.
  refine withCacheOverlay_verify_eq_of_miss ids hr M maxAttempts _ pksk.1 r.1.1 r.1.2 ?_
  intro w' z hσ
  simp only [hσ, Function.update_self]

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
  classical
  -- `advantage = Pr[G₀]` via the per-key bridge `G₀`.
  rw [SignatureAlg.unforgeableAdv.advantage,
    probOutput_unforgeableExp_eq_hybridExpAtKey_real ids hr M maxAttempts adv]
  -- Nonnegativity of the three per-hop slack pieces.
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  have hA : 0 ≤ qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) + qS * (qH + 1) * ε / (1 - p_abort) :=
    add_nonneg
      (div_nonneg (by positivity) (by positivity))
      (div_nonneg (by positivity) (le_of_lt h1p))
  have hB : 0 ≤ qS * (qH + 1) * ε / (1 - p_abort) := div_nonneg (by positivity) (le_of_lt h1p)
  have hC : 0 ≤ qS * ζ_zk / (1 - p_abort) := div_nonneg (by positivity) (le_of_lt h1p)
  have hPK : 0 ≤ perKeyLoss qS qH ε p_abort ζ_zk := by unfold perKeyLoss; positivity
  -- Per-key chain on good keys: `real ≤ sim + ofReal (perKeyLoss)`.
  have hperkey : ∀ x ∈ support hr.gen, Good x.1 x.2 →
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
        Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (simSignBody M maxAttempts sim x.1 x.2) x.1] +
        ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) := by
    rintro ⟨pk, sk⟩ hmem hgood
    have hrel : rel pk sk = true := hr.gen_sound pk sk hmem
    have step1 := probOutput_hybridExpAtKey_real_le_prog ids hr M maxAttempts adv qS qH ε p_abort
      hp₀ hp hQ pk sk (hGuess pk sk hgood) (hAbort pk sk hgood)
    have step2 := probOutput_hybridExpAtKey_prog_le_trans ids hr M maxAttempts adv qS qH ε p_abort
      hp₀ hp hε hQ pk sk (hGuess pk sk hgood) (hAbort pk sk hgood)
    have step3 := probOutput_hybridExpAtKey_trans_le_sim ids hr M maxAttempts sim adv ζ_zk hζ hhvzk
      qS qH p_abort hp₀ hp hQ pk sk hrel (hAbortSim pk sk hgood)
    -- Chain the three hops and collapse the `ofReal` sums (slack pieces nonneg).
    calc Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts pk sk) pk]
        ≤ Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (fun x ↦ progSignBody ids M pk sk x maxAttempts) pk] +
            ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
              qS * (qH + 1) * ε / (1 - p_abort)) := step1
      _ ≤ (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (transSignBody ids M maxAttempts pk sk) pk] +
            ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort))) +
            ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
              qS * (qH + 1) * ε / (1 - p_abort)) := by gcongr
      _ ≤ ((Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim pk sk) pk] +
            ENNReal.ofReal (qS * ζ_zk / (1 - p_abort))) +
            ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort))) +
            ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
              qS * (qH + 1) * ε / (1 - p_abort)) := by gcongr
      _ = Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim pk sk) pk] +
            ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) := by
          have hcollapse :
              ENNReal.ofReal (qS * ζ_zk / (1 - p_abort)) +
                ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) +
                ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
                  qS * (qH + 1) * ε / (1 - p_abort)) =
                ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) := by
            rw [← ENNReal.ofReal_add hC hB, ← ENNReal.ofReal_add (add_nonneg hC hB) hA]
            congr 1
            unfold perKeyLoss
            ring
          rw [add_assoc, add_assoc, ← add_assoc (ENNReal.ofReal (qS * ζ_zk / (1 - p_abort))),
            hcollapse]
  -- Average the per-key bound over `hr.gen`, paying `δ` on the complement of `Good`.
  have hbound : Pr[= true | do
        let x ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
      Pr[= true | do
        let x ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (simSignBody M maxAttempts sim x.1 x.2) x.1] +
        ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) + ENNReal.ofReal δ := by
    simp only [probOutput_bind_eq_tsum]
    -- Pointwise: split on `Good`. On `Good` use `hperkey`; off `Good` charge the `δ` slot.
    have hpt : ∀ x : Stmt × Wit,
        Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
          Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (simSignBody M maxAttempts sim x.1 x.2) x.1] +
          Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) +
          Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0) := by
      intro x
      by_cases hx : x ∈ support hr.gen
      · by_cases hg : Good x.1 x.2
        · have := mul_le_mul' (le_refl (Pr[= x | hr.gen])) (hperkey x hx hg)
          calc Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                  (realSignBody ids M maxAttempts x.1 x.2) x.1]
              ≤ Pr[= x | hr.gen] *
                  (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                    (simSignBody M maxAttempts sim x.1 x.2) x.1] +
                  ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk)) := this
            _ = Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                  (simSignBody M maxAttempts sim x.1 x.2) x.1] +
                Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) :=
                mul_add ..
            _ ≤ _ := by simp [hg]
        · -- Off `Good`: real ≤ 1, charged to the indicator slot.
          have : Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                  (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
              Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0) := by
            simp only [hg, not_false_eq_true, if_true]
            exact mul_le_mul' le_rfl probOutput_le_one
          exact le_trans this le_add_self
      · simp [probOutput_eq_zero_of_not_mem_support hx]
    calc ∑' x, Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts x.1 x.2) x.1]
        ≤ ∑' x, (Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim x.1 x.2) x.1] +
            Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) +
            Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0)) :=
          ENNReal.tsum_le_tsum hpt
      _ = (∑' x, Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim x.1 x.2) x.1]) +
            (∑' x, Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk)) +
            (∑' x, Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0)) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_add]
      _ ≤ (∑' x, Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim x.1 x.2) x.1]) +
            ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) + ENNReal.ofReal δ := by
          gcongr
          · rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
          · calc ∑' x, Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0)
                = ∑' x, if ¬ Good x.1 x.2 then Pr[= x | hr.gen] else 0 := by
                  refine tsum_congr fun x => ?_; by_cases hg : Good x.1 x.2 <;> simp [hg]
              _ = Pr[fun xw : Stmt × Wit => ¬ Good xw.1 xw.2 | hr.gen] := by
                  rw [probEvent_eq_tsum_ite]
              _ ≤ ENNReal.ofReal δ := hGood
  -- Final: glue with the NMA bridge and reassociate the loss.
  refine le_trans hbound ?_
  rw [cmaToNmaLoss_eq_perKeyLoss_add, ENNReal.ofReal_add hPK hδ, add_assoc]
  gcongr
  exact probOutput_hybridExp_sim_le_managedRoNmaExp ids hr M maxAttempts sim adv

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
  -- The run-level managed simulation issues at most `qH` live hash queries; the final
  -- pure post-processing (erasing the forgery's own verification point from the returned
  -- cache, Option B) issues none, so the total bound is `qH + 0 = qH`.
  have hrun : FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅) qH := by
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
  have hpost : ∀ result : (M × Option (Commit × Resp)) × spec.QueryCache,
      FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := (pure ((result.1.1, result.1.2),
          match result.1.2 with
          | some (w', _) => Function.update result.2 (Sum.inr (result.1.1, w')) none
          | none => result.2) :
          OracleComp spec ((M × Option (Commit × Resp)) × spec.QueryCache))) 0 := by
    intro result
    simp [FiatShamir.nmaHashQueryBound]
  have hbind := FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit)
    (Chal := Chal) hrun (fun result => hpost result)
  change FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
    (oa := (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅ >>= fun result =>
      pure ((result.1.1, result.1.2),
        match result.1.2 with
        | some (w', _) => Function.update result.2 (Sum.inr (result.1.1, w')) none
        | none => result.2)) qH
  simpa only [Nat.add_zero] using hbind

end scaffold


end EUF_CMA

end FiatShamirWithAbort
