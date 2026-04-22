/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.SSP.Games
import VCVio.SSP.IdenticalUntilBad
import VCVio.CryptoFoundations.SigmaProtocol

/-!
# Game-hops for the SSP-style Fiat-Shamir EUF-CMA proof

This file contributes hops H3, H4, H5 of the SSP plan in
`.ignore/fs-ssp-plan.md` §5:

* **H3** (`cmaReal` ↔ `cmaSim`, the tight HVZK + programming-collision hop):
  `| Pr[cmaReal accepts] - Pr[cmaSim accepts] | ≤ qS · ζ_zk + qS · (qS + qH) · β`,
  obtained from `Package.advantage_le_expectedSCost_plus_probEvent_bad` in
  `VCVio/SSP/IdenticalUntilBad.lean` instantiated at
  `G₀ = cmaReal`, `G₁ = cmaSim`. The bad-probability term vanishes since
  `cmaReal`'s bad flag is vacuously `false` (real signing never programs
  the RO); the single factor of `β` in the conclusion is a consequence of
  this one-sided choice of `G₀` (see §5 of the plan).
* **H4** (`cmaSim = cmaToNma.shiftLeft nma`): mechanical program-equivalence.
* **H5** (`nma ≤ Fork`): bridge to `Fork.replayForkingBound`.

Current content:

* `IsCostlyQuery` — the predicate picking out `signSpec` queries inside
  `cmaSpec`, matching the `S` predicate consumed by
  `Package.advantage_le_expectedSCost_plus_probEvent_bad`.
* `cmaReal_impl_eq_cmaSim_impl_of_not_isCostlyQuery` — non-sign queries
  are pointwise identical between `cmaReal` and `cmaSim`. This is the
  `h_step_eq_nS` hypothesis of the SSP bridge.
* `cmaReal_impl_bad_preserved` / `cmaSim_impl_bad_monotone` — strict
  preservation of the bad flag on the `cmaReal` side and monotonicity on
  the `cmaSim` side. Together they supply the `h_mono₀` hypothesis of
  the SSP bridge (at either choice of `G₀`) and drive the
  `Pr[bad | G₀ = cmaReal] = 0` corollary below.
* `cmaReal_simulateQ_bad_preserved` /
  `cmaReal_simulateQ_probEvent_bad_eq_zero` — lift bad-preservation
  through the whole program by induction on `oa`, discharging the
  `Pr[bad fires in G₀]` term of the SSP bridge.
* `cmaSignEps` / `cacheCount` — the per-state ε function
  `ε s = ζ_zk + cacheCount s.1 · β` used by the bridge's `expectedSCost`.
* `cmaReal_cmaSim_tv_costly_le_cmaSignEps` — the `h_step_tv_S`
  hypothesis, dispatched into the costly vs. non-costly branches and
  delegating the sign case to `cmaReal_cmaSim_tv_sign_le_cmaSignEps`
  (the mathematical heart of the H3 hop).
* `cmaReal_cmaSim_advantage_le_H3_bound` — top-level H3 statement,
  threading all of the above through
  `Package.advantage_le_expectedSCost_plus_probEvent_bad`.

Remaining work (isolated to two `sorry`s):

* `cmaReal_cmaSim_tv_sign_le_cmaSignEps` — the HVZK + cache-collision
  coupling proof on a single sign query.
* `cmaSignEps_expectedSCost_le` — the cache-growth invariant closing the
  `expectedSCost` term to the headline `qS · ζ_zk + qS · (qS + qH) · β`.
-/

universe u

open ENNReal OracleSpec OracleComp ProbComp ProgramLogic.Relational VCVio.SSP

namespace FiatShamir.SSP

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]

/-! ### Costly-query predicate for H3 -/

/-- The "costly" query predicate for the H3 identical-until-bad hop.

A query into `cmaSpec` is costly iff it targets the `signSpec` summand —
this is the only branch on which `cmaReal` and `cmaSim` disagree. The
SSP bridge `Package.advantage_le_expectedSCost_plus_probEvent_bad`
charges a per-step `ε s` on costly queries and requires pointwise
equality on free queries, so the predicate must line up exactly with
the "sign vs. the rest" split of `cmaSpec`. -/
def IsCostlyQuery : (cmaSpec M Commit Chal Resp Stmt).Domain → Prop
  | Sum.inl (Sum.inr _) => True
  | _ => False

instance : DecidablePred (IsCostlyQuery (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt)) := fun t =>
  match t with
  | Sum.inl (Sum.inl (Sum.inl _)) => isFalse fun h => h
  | Sum.inl (Sum.inl (Sum.inr _)) => isFalse fun h => h
  | Sum.inl (Sum.inr _) => isTrue trivial
  | Sum.inr _ => isFalse fun h => h

/-! ### `h_step_eq_nS`: non-sign queries coincide -/

/-- The handler components of `cmaReal.impl` and `cmaSim.impl` are
pointwise identical on every non-sign query (uniform sampling, hash
queries, public-key queries). This is the `h_step_eq_nS` hypothesis of
the SSP identical-until-bad bridge. -/
theorem cmaReal_impl_eq_cmaSim_impl_of_not_isCostlyQuery
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (ht : ¬ IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) t)
    (p : cmaGameState M Commit Chal Stmt Wit) :
    ((cmaReal M Commit Chal σ hr).impl t).run p =
      ((cmaSim M Commit Chal hr simT).impl t).run p := by
  rcases t with ((_ | _) | _) | _
  · rfl
  · rfl
  · exact (ht True.intro).elim
  · rfl

/-! ### `h_mono₀`: bad-flag monotonicity for `cmaReal` and `cmaSim`

The SSP bridge `Package.advantage_le_expectedSCost_plus_probEvent_bad`
takes a monotonicity hypothesis for `G₀`'s impl: once the bad flag
fires, every continuation preserves it. For the H3 hop we choose
`G₀ = cmaReal`, which makes monotonicity trivial — `cmaReal` never
touches the bad flag at all. We also prove the analogous fact for
`cmaSim`; it is the only direction that genuinely uses the "sign
programs the RO cache" branch, and is kept here as reusable
infrastructure for bridging to other SSP hops (e.g. H4 and the
runtime bound). -/

/-- `cmaReal.impl` propagates the input bad flag through unchanged: on
every query, the output state's bad flag equals the input state's bad
flag. This is strictly stronger than monotonicity. -/
theorem cmaReal_impl_bad_preserved
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (p : cmaGameState M Commit Chal Stmt Wit)
    (z) (hz : z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run p)) :
    z.2.2 = p.2 := by
  obtain ⟨⟨cache, kp, log⟩, bad⟩ := p
  rcases t with ((_ | mc) | m) | ⟨⟩
  · -- unif query: output form (a, (cache, kp, log), bad), bad preserved
    rename_i n
    have hz' : z ∈ support
        ((unifSpec.query n : OracleComp unifSpec _) >>= fun r =>
          (pure (r, (cache, kp, log), bad) :
            OracleComp unifSpec
              (_ × cmaGameState M Commit Chal Stmt Wit))) := hz
    rw [support_bind] at hz'
    obtain ⟨_, _, hz'⟩ := Set.mem_iUnion₂.mp hz'
    rw [support_pure] at hz'
    cases Set.eq_of_mem_singleton hz'
    rfl
  · -- hash query: cache hit/miss both preserve bad
    rcases hmc : cache mc with _ | r
    · have hz' : z ∈ support
          ((($ᵗ Chal) : OracleComp unifSpec _) >>= fun r =>
            (pure (r, (cache.cacheQuery mc r, kp, log), bad) :
              OracleComp unifSpec
                (_ × cmaGameState M Commit Chal Stmt Wit))) := by
        simpa [cmaRealSubImpl, cmaRealUnifRoImpl, StateT.run, hmc] using hz
      rw [support_bind] at hz'
      obtain ⟨_, _, hz'⟩ := Set.mem_iUnion₂.mp hz'
      rw [support_pure] at hz'
      cases Set.eq_of_mem_singleton hz'
      rfl
    · have hz' : z = (r, (cache, kp, log), bad) := by
        simpa [cmaRealSubImpl, cmaRealUnifRoImpl, StateT.run, hmc] using hz
      rw [hz']
  · -- sign query: every branch of `cmaRealSignImpl` ends with
    -- `pure (…, …, bad)`, so the output's bad field is always `bad`.
    -- Shared inner lemma: for any (pk, sk) and any commitment output (c, prvSt),
    -- the cache-match-then-respond subcomputation preserves `bad`.
    rcases hkp : kp with _ | ⟨pk', sk'⟩
    · -- fresh keypair: hr.gen ≫= σ.commit ≫= (cache-match ch) ≫= σ.respond
      simp only [add_apply_inl, add_apply_inr, StateT.run, cmaRealSubImpl, hkp,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, cmaRealSignImpl,
        Prod.mk.eta, monadLift_self, bind_pure_comp, pure_bind,
        support_bind] at hz
      obtain ⟨pksk, _, hz⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨c, _, hz⟩ := Set.mem_iUnion₂.mp hz
      rcases hmc : cache (m, c.1) with _ | r
      · rw [hmc] at hz
        simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image,
          exists_prop] at hz
        obtain ⟨_, _, _, _, rfl⟩ := hz
        rfl
      · rw [hmc] at hz
        simp only [support_map, Set.mem_image] at hz
        obtain ⟨_, _, rfl⟩ := hz
        rfl
    · -- cached keypair: σ.commit ≫= (cache-match ch) ≫= σ.respond
      simp only [add_apply_inl, add_apply_inr, StateT.run, cmaRealSubImpl, hkp,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, cmaRealSignImpl,
        monadLift_self, bind_pure_comp, pure_bind,
        support_bind] at hz
      obtain ⟨c, _, hz⟩ := Set.mem_iUnion₂.mp hz
      rcases hmc : cache (m, c.1) with _ | r
      · rw [hmc] at hz
        simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image,
          exists_prop] at hz
        obtain ⟨_, _, _, _, rfl⟩ := hz
        rfl
      · rw [hmc] at hz
        simp only [support_map, Set.mem_image] at hz
        obtain ⟨_, _, rfl⟩ := hz
        rfl
  · -- pk query
    rcases hkp : kp with _ | ⟨pk', sk'⟩
    · simp only [add_apply_inr, StateT.run, cmaRealPkImpl, hkp,
        QueryImpl.add_apply_inr, bind_pure_comp, support_map] at hz
      obtain ⟨_, _, rfl⟩ := hz
      rfl
    · have hz' : z = (pk', (cache, some (pk', sk'), log), bad) := by
        simpa [cmaRealPkImpl, StateT.run, hkp] using hz
      rw [hz']

/-- `cmaReal`'s bad flag is monotonic: once set, it stays set. Immediate
corollary of `cmaReal_impl_bad_preserved`. This is the `h_mono₀`
hypothesis of the SSP bridge when instantiated with `G₀ = cmaReal`. -/
theorem cmaReal_impl_bad_monotone
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (p : cmaGameState M Commit Chal Stmt Wit) (hp : p.2 = true)
    (z) (hz : z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run p)) :
    z.2.2 = true := by
  rw [cmaReal_impl_bad_preserved (M := M) σ hr t p z hz]; exact hp

/-- Once `cmaSim`'s bad flag is `true`, every continuation of `cmaSim.impl`
preserves it. This is not directly used by the H3 hop (which instantiates
`G₀ = cmaReal`), but is reusable infrastructure for other SSP hops that
expose `cmaSim` as the "low-adversary-advantage" side. -/
theorem cmaSim_impl_bad_monotone
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (p : cmaGameState M Commit Chal Stmt Wit) (hp : p.2 = true)
    (z) (hz : z ∈ support (((cmaSim M Commit Chal hr simT).impl t).run p)) :
    z.2.2 = true := by
  obtain ⟨⟨cache, kp, log⟩, bad⟩ := p
  cases (show bad = true from hp)
  rcases t with ((_ | mc) | m) | ⟨⟩
  · -- unif query: output form (r, state, true), state unchanged
    simp only [StateT.run, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff, exists_prop] at hz
    obtain ⟨_, _, rfl⟩ := hz
    rfl
  · -- hash query: cache hit/miss both preserve bad
    rcases hmc : cache mc with _ | r
    · -- miss
      simp only [StateT.run, hmc, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨_, _, rfl⟩ := hz
      rfl
    · -- hit
      simp only [StateT.run, hmc, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
  · -- sign query: bad' ∈ {bad, true}, so bad = true ⇒ bad' = true
    rcases hkp : kp with _ | ⟨pk', sk'⟩
    · -- fresh keypair
      simp only [StateT.run, hkp, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨_, _, _, _, _, _, rfl⟩ := hz
      split <;> rfl
    · -- cached keypair
      simp only [StateT.run, hkp, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨_, rfl, _, _, rfl⟩ := hz
      split <;> rfl
  · -- pk query: both branches preserve bad
    rcases hkp : kp with _ | ⟨pk', sk'⟩
    · simp only [StateT.run, hkp, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨_, _, rfl⟩ := hz
      rfl
    · simp only [StateT.run, hkp, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]

/-! ### `h_step_tv_S`: per-step TV bound on costly queries

For a sign query from a no-bad input state `(s, false)`, the real and
simulated CMA impls are `ε(s)`-close in total variation, where

  `ε(s) := ζ_zk + cacheCount s.1 · β`

with `ζ_zk` the HVZK statistical distance, `β` the simulator commit-
marginal predictability bound, and `cacheCount` the number of cached
`(m', c')` entries in the RO cache. The `ζ_zk` summand comes from
running `σ.realTranscript` versus `simT` on the current keypair
(HVZK); the `cacheCount · β` summand comes from the programming
collision gap (`simCommitPredictability` bounds each cache hit by `β`
and we union-bound over the at most `cacheCount s.1` cached keys).

The proof is the joint-coupling argument from §A.4.2 of the SSP plan
(`.ignore/fs-ssp-plan.md`). It is intentionally stated as a standalone
lemma so the caller can either use it directly with the state-dep ε
bridge, or specialize to a constant ε via `(qS + qH) · β + ζ_zk`. -/

/-- Number of cached entries in a random-oracle cache, as an `ℕ`.
Computed via `Set.ncard` on the cache's graph. For the H3 hop this
bounds the cache-hit probability `Pr[(m, sim.commit) ∈ cache] ≤
cacheCount · β` via `simCommitPredictability β`. -/
noncomputable def cacheCount {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal : Type}
    (cache : (roSpec M Commit Chal).QueryCache) : ℕ :=
  cache.toSet.ncard

/-- Per-state ε for the H3 hop: HVZK gap `ζ_zk` plus cache-hit gap
`cacheCount · β`. Used as the `ε` argument of the state-dep SSP
identical-until-bad bridge `advantage_le_expectedSCost_plus_probEvent_bad`
at the H3 instantiation `G₀ = cmaReal`, `G₁ = cmaSim`. -/
noncomputable def cmaSignEps {M : Type} [DecidableEq M]
    {Commit : Type} [DecidableEq Commit] {Chal Stmt Wit : Type}
    (ζ_zk β : ℝ≥0∞) (s : cmaInnerState M Commit Chal Stmt Wit) : ℝ≥0∞ :=
  ζ_zk + cacheCount s.1 * β

/-- **Per-step TV bound for H3 on a sign query.** On a single sign
query from a `(s, false)` input, the real and simulated CMA impls
are `cmaSignEps ζ_zk β s`-close in total variation. This is the core
HVZK + cache-collision coupling used in the H3 hop.

Proof strategy (§A.4.2 of the SSP plan):
1. Fetch the keypair (`kp` cache hit or `hr.gen` fresh) — no TV gap.
2. On the remaining `(pk, sk) ↦ …` continuation, use the triangle
   inequality through an intermediate "use real transcript, apply
   sim's post-processing" computation:
   * Real vs. intermediate: bounded by the cache-hit probability at
     `simT`'s commit marginal (`cacheCount · β` by union bound via
     `simCommitPredictability`).
   * Intermediate vs. simulated: bounded by `ζ_zk` via HVZK on the
     full transcript. -/
theorem cmaReal_cmaSim_tv_sign_le_cmaSignEps
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (m : M) (s : cmaInnerState M Commit Chal Stmt Wit) :
    ENNReal.ofReal (tvDist
      (((cmaReal M Commit Chal σ hr).impl
        (Sum.inl (Sum.inr m) : (cmaSpec M Commit Chal Resp Stmt).Domain)).run
          (s, false))
      (((cmaSim M Commit Chal hr simT).impl
        (Sum.inl (Sum.inr m))).run (s, false)))
      ≤ cmaSignEps ζ_zk β s := by
  sorry

/-- The `h_step_tv_S` hypothesis of
`Package.advantage_le_expectedSCost_plus_probEvent_bad` instantiated at
`G₀ = cmaReal`, `G₁ = cmaSim`, `S = IsCostlyQuery`, and
`ε = cmaSignEps ζ_zk β`. Only the sign-query branch has content; the
other branches are vacuous (`¬ IsCostlyQuery t`).

This is the canonical interface between the FS-specific HVZK coupling
(in `cmaReal_cmaSim_tv_sign_le_cmaSignEps`) and the generic SSP bridge
in `VCVio/SSP/IdenticalUntilBad.lean`. -/
theorem cmaReal_cmaSim_tv_costly_le_cmaSignEps
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (ht : IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) t)
    (s : cmaInnerState M Commit Chal Stmt Wit) :
    ENNReal.ofReal (tvDist
      (((cmaReal M Commit Chal σ hr).impl t).run (s, false))
      (((cmaSim M Commit Chal hr simT).impl t).run (s, false)))
      ≤ cmaSignEps ζ_zk β s := by
  rcases t with ((_ | _) | m) | ⟨⟩
  · exact (ht).elim
  · exact (ht).elim
  · exact cmaReal_cmaSim_tv_sign_le_cmaSignEps σ hr (M := M) simT ζ_zk β hζ_zk
      hHVZK hCommit m s
  · exact (ht).elim

/-! ### Bad-event probability: zero on the `cmaReal` side

The state-dep SSP bridge `advantage_le_expectedSCost_plus_probEvent_bad`
charges a `Pr[bad fires in G₀]` term on top of the cumulative per-step ε.
For H3 we instantiate `G₀ = cmaReal`, whose bad flag is *preserved* (not
merely monotone): every step leaves it unchanged. Starting from the
no-bad init state `(s_init, false)`, every reachable simulation output
therefore has `z.2.2 = false`, so the bad event has probability zero.

The lemma `cmaReal_simulateQ_bad_preserved` lifts
`cmaReal_impl_bad_preserved` over the whole simulation by induction
on the program. Its corollary `cmaReal_simulateQ_probEvent_bad_eq_zero`
discharges the bad-event term of the SSP bridge. -/

/-- Lift per-step bad-preservation through the whole simulation: if
`cmaReal.impl` preserves the bad flag on every query, then so does
`simulateQ cmaReal.impl oa` (by induction on `oa`).

This is the simulation-level analogue of `cmaReal_impl_bad_preserved`
and is the key ingredient of `cmaReal_simulateQ_probEvent_bad_eq_zero`. -/
theorem cmaReal_simulateQ_bad_preserved
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) {α : Type}
    (oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (p : cmaGameState M Commit Chal Stmt Wit)
    (z) (hz : z ∈ support ((simulateQ (cmaReal M Commit Chal σ hr).impl oa).run p)) :
    z.2.2 = p.2 := by
  induction oa using OracleComp.inductionOn generalizing p z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      rfl
  | query_bind t cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, support_bind,
        Set.mem_iUnion, exists_prop] at hz
      obtain ⟨⟨u, p'⟩, h_mem, h_z⟩ := hz
      have hp' : p'.2 = p.2 :=
        cmaReal_impl_bad_preserved (M := M) σ hr t p (u, p') h_mem
      have hz' : z.2.2 = p'.2 := ih u p' z h_z
      exact hz'.trans hp'

/-- The bad-event probability of any `cmaReal` simulation started from
`(s, false)` is zero: every reachable output has `z.2.2 = false`.

This discharges the `Pr[bad | G₀]` term of
`Package.advantage_le_expectedSCost_plus_probEvent_bad` when
instantiated at `G₀ = cmaReal`, leaving the advantage bounded purely
by the per-step expected ε cost. -/
theorem cmaReal_simulateQ_probEvent_bad_eq_zero
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) {α : Type}
    (oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (s : cmaInnerState M Commit Chal Stmt Wit) :
    Pr[fun z : α × cmaInnerState M Commit Chal Stmt Wit × Bool => z.2.2 = true |
        (simulateQ (cmaReal M Commit Chal σ hr).impl oa).run (s, false)] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro z hz
  have : z.2.2 = false :=
    cmaReal_simulateQ_bad_preserved (M := M) σ hr oa (s, false) z hz
  simp [this]

/-! ### Expected cumulative ε cost

The `expectedSCost` term in the state-dep SSP bridge integrates
`ε s = cmaSignEps ζ_zk β s = ζ_zk + cacheCount s.1 · β` over the
reachable states of the simulation. At the i-th costly (sign) query,
the cache contains at most `qH + (i - 1)` entries (the adversary has
made at most `qH` hash queries and `i - 1` previous sign queries, each
adding at most one cache entry). Summing `ζ_zk + (qH + i - 1) · β`
from `i = 1` to `qS` yields `qS · ζ_zk + (qS · qH + qS · (qS - 1)/2) · β`,
which is upper-bounded by the headline `qS · ζ_zk + qS · (qS + qH) · β`.

The cache-growth invariant is specific to Fiat-Shamir; the bound
itself is scheduled for Phase E3'. -/

/-- Upper bound on the expected cumulative ε cost for the H3 hop.
Integrates `cmaSignEps ζ_zk β` over the reachable states of
`simulateQ cmaReal.impl A` from `(s_init, false)`, using the
cache-growth invariant "at step `i`, `cacheCount ≤ qH + (i - 1)`".

The headline bound `qS · ζ_zk + qS · (qS + qH) · β` matches the target
H3 bound from §5 of the SSP plan. -/
theorem cmaSignEps_expectedSCost_le
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (ζ_zk β : ℝ≥0∞) {α : Type}
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)
    (qS qH : ℕ)
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b))
    (_h_qH : True) -- placeholder; real E3' bound also needs a hash-query budget
    (s : cmaInnerState M Commit Chal Stmt Wit) :
    expectedSCost (cmaReal M Commit Chal σ hr).impl
        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        (cmaSignEps ζ_zk β) A qS (s, false)
      ≤ (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β := by
  sorry

/-! ### Top-level H3 hop

The advantage between `cmaReal` and `cmaSim` is bounded by the cumulative
ε cost (dominated by `qS · ζ_zk + qS · (qS + qH) · β`) plus the
`cmaReal`-side bad-event probability (zero since bad is preserved).
This is precisely the H3 bound from §5 of the SSP plan. -/

/-- **H3 hop** via the SSP state-dep identical-until-bad bridge.

`cmaReal` and `cmaSim` are ε(s)-close on sign queries and pointwise
identical on all other queries; `cmaReal`'s bad flag is preserved.
Threading this through the state-dep SSP bridge and bounding
`expectedSCost` by `qS · ζ_zk + qS · (qS + qH) · β` yields the tight H3
bound of the FS-on-Σ rewrite. -/
theorem cmaReal_cmaSim_advantage_le_H3_bound
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)
    (qS qH : ℕ)
    (h_qb : OracleComp.IsQueryBound A qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b)) :
    ENNReal.ofReal ((cmaReal M Commit Chal σ hr).advantage
        (cmaSim M Commit Chal hr simT) A)
      ≤ (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β := by
  have h_init : (cmaReal M Commit Chal σ hr).init = pure ((∅, none, []), false) := rfl
  have h_init' : (cmaSim M Commit Chal hr simT).init = pure ((∅, none, []), false) := rfl
  have h_mono₀ : ∀ (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
      (p : cmaGameState M Commit Chal Stmt Wit), p.2 = true →
      ∀ z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run p), z.2.2 = true := by
    intro t p hp z hz
    exact cmaReal_impl_bad_monotone (M := M) σ hr t p hp z hz
  have h_bridge := Package.advantage_le_expectedSCost_plus_probEvent_bad
    (cmaReal M Commit Chal σ hr) (cmaSim M Commit Chal hr simT)
    ((∅ : (roSpec M Commit Chal).QueryCache), (none : Option (Stmt × Wit)), ([] : List M))
    h_init h_init'
    (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (cmaSignEps ζ_zk β)
    (fun t ht s => cmaReal_cmaSim_tv_costly_le_cmaSignEps (M := M) σ hr simT ζ_zk β hζ_zk
      hHVZK hCommit t ht s)
    (fun t ht p => cmaReal_impl_eq_cmaSim_impl_of_not_isCostlyQuery (M := M) σ hr simT t ht p)
    h_mono₀
    A h_qb
  have h_bad_zero :
      Pr[fun z : Bool × cmaInnerState M Commit Chal Stmt Wit × Bool => z.2.2 = true |
          (simulateQ (cmaReal M Commit Chal σ hr).impl A).run
            ((∅, none, []), false)] = 0 :=
    cmaReal_simulateQ_probEvent_bad_eq_zero (M := M) σ hr A _
  have h_cost_le :
      expectedSCost (cmaReal M Commit Chal σ hr).impl
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEps ζ_zk β) A qS (((∅, none, []) :
            cmaInnerState M Commit Chal Stmt Wit), false)
        ≤ (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β :=
    cmaSignEps_expectedSCost_le (M := M) σ hr ζ_zk β A qS qH h_qb trivial _
  calc ENNReal.ofReal ((cmaReal M Commit Chal σ hr).advantage
          (cmaSim M Commit Chal hr simT) A)
      ≤ expectedSCost (cmaReal M Commit Chal σ hr).impl
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEps ζ_zk β) A qS (((∅, none, []) :
            cmaInnerState M Commit Chal Stmt Wit), false)
        + Pr[fun z : Bool × cmaInnerState M Commit Chal Stmt Wit × Bool => z.2.2 = true |
            (simulateQ (cmaReal M Commit Chal σ hr).impl A).run
              ((∅, none, []), false)] := h_bridge
    _ = expectedSCost (cmaReal M Commit Chal σ hr).impl
          (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt))
          (cmaSignEps ζ_zk β) A qS ((∅, none, []), false) := by
        rw [h_bad_zero, add_zero]
    _ ≤ (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * (qS + qH) * β := h_cost_le

end FiatShamir.SSP
