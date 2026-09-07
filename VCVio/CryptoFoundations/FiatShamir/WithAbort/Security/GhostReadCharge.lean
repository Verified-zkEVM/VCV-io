/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.BodyHops
public import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.BodyBounds

/-!
# EUF-CMA for Fiat-Shamir with aborts: GhostReadCharge

The lazy-side ghost-read charge: query-bound transport across decidability
instances and the lazy ghost handler's per-read charge accounting.

Part of the CMA-to-NMA security development for the Fiat-Shamir-with-aborts
transform; `VCVio.CryptoFoundations.FiatShamir.WithAbort.Security` assembles
the headline `euf_cma_to_nma` and holds the overview docstring.
-/

public section

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

section scaffold

variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
variable (adv : SignatureAlg.unforgeableAdv
  (FiatShamirWithAbort
    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))

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
      _ ≤ (gh.toSet.encard : ℝ≥0∞) := ENat.toENNReal_mono (ENat.natCast_toNat_le_self _)
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
        exact mul_le_of_le_one_right (zero_le) probEvent_le_one
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
          · exact le_rfl
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
  -- The assembly, in three stages, executed below.
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
                pure (alc.1, ((alc.2, msg :: list), false)) from by rw [bind_pure_comp]; rfl]
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

end scaffold

end EUF_CMA

end FiatShamirWithAbort
