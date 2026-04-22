/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.SSP.Games
import VCVio.SSP.IdenticalUntilBad
import VCVio.SSP.Composition
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

* `cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma` — the H4 program
  equivalence, routed through the SSP `run_link_eq_run_shiftLeft` +
  a `Package`-level structural identity `cmaSim = cmaToNma.link nma`
  (up to state reshuffling by `simulateQ_StateT_evalDist_congr`).

Remaining work (isolated to `sorry`s):

* `cmaReal_cmaSim_tv_sign_le_cmaSignEps` — the HVZK + cache-collision
  coupling proof on a single sign query (H3 heart).
* `cmaSignEps_expectedSCost_le` — the cache-growth invariant closing the
  `expectedSCost` term to the headline `qS · ζ_zk + qS · (qS + qH) · β`
  (H3 cost bookkeeping).
* `cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma` — the H4 program-
  equivalence distribution identity. The statement sits here so that the
  full chain H1+H2 → H3 → H4 → H5 is visible in one view; the proof is
  deferred to Phase F (see `.ignore/fs-ssp-plan.md`).

The dual to this file (H5 + the top-level chain producing the EUF-CMA
`Fork.advantage + qS·ζ_zk + qS·(qS+qH)·β + δ_verify` bound) lives in
`Sigma/SSP/Chain.lean`.
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
flag. This is strictly stronger than monotonicity.

Since `cmaReal.impl` is built entirely from `QueryImpl.withBadFlag`
(one instance per atomic handler), each branch reduces via
`withBadFlag_apply_run` to the shape
`(fun vs => (vs.1, vs.2, b)) <$> (innerImpl t').run s`, whence every
element of the support has third component equal to the input bad `b`. -/
theorem cmaReal_impl_bad_preserved
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (p : cmaGameState M Commit Chal Stmt Wit)
    (z) (hz : z ∈ support (((cmaReal M Commit Chal σ hr).impl t).run p)) :
    z.2.2 = p.2 := by
  obtain ⟨s, b⟩ := p
  rw [cmaReal_impl_apply_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨_, _, rfl⟩ := hz
  rfl

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
expose `cmaSim` as the "low-adversary-advantage" side.

All non-sign branches of `cmaSim.impl` are `*.withBadFlag`-lifts (bad
preserved); the sign branch is a `*.withBadUpdate progCollision` lift
(bad OR'd with a predicate), monotone by `Bool.or`. -/
theorem cmaSim_impl_bad_monotone
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (t : (cmaSpec M Commit Chal Resp Stmt).Domain)
    (p : cmaGameState M Commit Chal Stmt Wit) (hp : p.2 = true)
    (z) (hz : z ∈ support (((cmaSim M Commit Chal hr simT).impl t).run p)) :
    z.2.2 = true := by
  obtain ⟨s, b⟩ := p
  rcases t with ((u | h) | m) | ⟨⟩
  · rw [cmaSim_impl_unifRo_apply_run] at hz
    have hz' := support_map (m := OracleComp unifSpec)
        (fun (vs : (unifSpec + roSpec M Commit Chal).Range (Sum.inl u) ×
            cmaInnerState M Commit Chal Stmt Wit) => (vs.1, vs.2, b))
        ((unifRoInnerImpl M Commit Chal Stmt Wit (Sum.inl u)).run s) ▸ hz
    obtain ⟨_, _, rfl⟩ := hz'; exact hp
  · rw [cmaSim_impl_unifRo_apply_run] at hz
    have hz' := support_map (m := OracleComp unifSpec)
        (fun (vs : (unifSpec + roSpec M Commit Chal).Range (Sum.inr h) ×
            cmaInnerState M Commit Chal Stmt Wit) => (vs.1, vs.2, b))
        ((unifRoInnerImpl M Commit Chal Stmt Wit (Sum.inr h)).run s) ▸ hz
    obtain ⟨_, _, rfl⟩ := hz'; exact hp
  · rw [cmaSim_impl_sign_apply_run] at hz
    have hz' := support_map (m := OracleComp unifSpec)
        (fun (vs : (signSpec M Commit Resp).Range m ×
            cmaInnerState M Commit Chal Stmt Wit) =>
          (vs.1, vs.2, b || progCollision m s vs.1))
        ((signSimInnerImpl M Commit Chal hr simT m).run s) ▸ hz
    obtain ⟨_, _, rfl⟩ := hz'
    change (b || _) = true
    simp [show b = true from hp]
  · rw [cmaSim_impl_pk_apply_run] at hz
    have hz' := support_map (m := OracleComp unifSpec)
        (fun (vs : (pkSpec Stmt).Range () ×
            cmaInnerState M Commit Chal Stmt Wit) => (vs.1, vs.2, b))
        ((pkInnerImpl M Commit Chal hr ()).run s) ▸ hz
    obtain ⟨_, _, rfl⟩ := hz'; exact hp

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

/-! ### H4 hop: `cmaSim` equals `nma · cmaToNma` as a package

Hop H4 of the SSP plan states that running `cmaSim` against an adversary
`A` is program-equivalent to first running the CMA-to-NMA reduction
`cmaToNma` against `A` (absorbing the reduction's `signSpec` translation
into the adversary) and then running the `nma` game:

  `cmaSim.runProb A  =  nma.runProb (cmaToNma.shiftLeft A)`.

This is a pure program-equivalence hop (zero advantage gap) whose proof
relies on:

* `Package.run_link_eq_run_shiftLeft` — the SSP-level identity
  `(P.link Q).run A = Q.run (P.shiftLeft A)` from
  `VCVio/SSP/Composition.lean`, which collapses the composition at
  `P = cmaToNma`, `Q = nma`.
* A structural `Package`-level identity
  `cmaSim = cmaToNma.link nma` up to state reshuffling. The state shapes
  differ (`cmaSim`'s state is `cmaInnerState × Bool`; the link's state
  is `List M × (cache × Bool × Option (Stmt × Wit))`) but the output
  distributions coincide; the equality is at the level of `evalDist`
  via `Package.simulateQ_StateT_evalDist_congr`
  (`VCVio/SSP/Advantage.lean`).

The proof is Phase F of the plan (estimated ~80 LoC: mostly mechanical
`simulateQ`-congruence normalization). -/

/-- State bijection between `cmaSim`'s `cmaGameState` and the nested link
state `List M × nmaState` of `cmaToNma.link nma`.

Both sides carry the same four pieces of data: the RO cache
(`(roSpec M Commit Chal).QueryCache`), an optional keypair
(`Option (Stmt × Wit)`), the signed-message log (`List M`), and the
SSP bad flag (`Bool`). The bijection simply reshuffles them:

```
cmaGameState               link state
((cache, kp, msgs), b)  ↔  (msgs, (cache, b, kp))
```

Used in `cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma` below to
match `cmaSim.impl` branch-by-branch against
`(cmaToNma.link nma).impl` via
`Package.simulateQ_StateT_evalDist_congr_of_bij`. -/
@[reducible] def cmaLinkStateEquiv
    {M : Type} [DecidableEq M] {Commit : Type} [DecidableEq Commit]
    {Chal Stmt Wit : Type} :
    cmaGameState M Commit Chal Stmt Wit ≃
      List M × ((roSpec M Commit Chal).QueryCache × Bool × Option (Stmt × Wit)) where
  toFun := fun ((cache, kp, msgs), b) => (msgs, (cache, b, kp))
  invFun := fun (msgs, cache, b, kp) => ((cache, kp, msgs), b)
  left_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _⟩ => rfl

/-- Simulating a lifted `ProbComp` (`OC unifSpec`) through `nma.impl`
threads the state unchanged: the output at state `s` is just the
underlying `ProbComp` tagged with `s`.

This is the key structural fact for the H4 sign-branch equivalence. The
`cmaToNma` reduction feeds `simT pk : ProbComp _` into the NMA game via
a `liftM`. Since `unifSpec`'s queries are handled by `nma.impl` as a
pure pass-through (the `inl inl inl _` branch is `fun st => query t >>=
fun r => pure (r, st)`), simulating through the lift never modifies
the `nma` state. -/
lemma simulateQ_nma_impl_liftM_unifSpec_run
    (hr : GenerableRelation Stmt Wit rel) {α : Type}
    (c : OracleComp unifSpec α)
    (s : (roSpec M Commit Chal).QueryCache × Bool × Option (Stmt × Wit)) :
    (simulateQ (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).impl
        (liftComp c (nmaSpec M Commit Chal Stmt))).run s
      = (·, s) <$> c := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure x => simp [OracleComp.liftComp_pure]
  | query_bind t k ih =>
    simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query,
      OracleQuery.cont_query, OracleQuery.input_query, id_map,
      simulateQ_bind, StateT.run_bind]
    set impl :=
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).impl with himpl
    -- Reduce `simulateQ impl (liftM (unifSpec.query t))` to
    -- `impl (inl inl inl t)`, then substitute its definition.
    have hreduce : (simulateQ impl
        (liftM (unifSpec.query t) : OracleComp (nmaSpec M Commit Chal Stmt) _)).run s
        = (unifSpec.query t : OracleComp unifSpec _) >>= fun r => pure (r, s) := rfl
    rw [hreduce]
    rw [bind_assoc, map_bind]
    simp only [pure_bind]
    refine bind_congr fun r => ?_
    exact ih r s

/-- **Per-query H4 equivalence** on the uniform branch.

On the uniform sub-branch of `cmaSpec` (i.e. `Sum.inl (Sum.inl (Sum.inl n))`
for `n : ℕ`), running `cmaSim.impl` at state `s` is definitionally equal to
running `(cmaToNma.link nma).impl` at the bijected link state `φ s`, post-
projected by `Prod.map id φ.symm`. The bijection commutes with the query
verbatim, so the equality is `rfl` after unfolding the atomic handler via
`cmaSim_impl_unifRo_apply_run` and the link via `Package.link_impl_apply_run`. -/
lemma cmaSim_impl_run_eq_link_under_bij_unif
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (n : ℕ) (s : cmaGameState M Commit Chal Stmt Wit) :
    evalDist (((cmaSim M Commit Chal hr simT).impl (Sum.inl (Sum.inl (Sum.inl n)))).run s) =
      evalDist (Prod.map id cmaLinkStateEquiv.symm <$>
        (((cmaToNma (Stmt := Stmt) M Commit Chal simT).link
            (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)).impl
            (Sum.inl (Sum.inl (Sum.inl n)))).run (cmaLinkStateEquiv s)) := by
  rcases s with ⟨⟨cache, kp, msgs⟩, b⟩
  rw [cmaSim_impl_unifRo_apply_run (t := Sum.inl n), Package.link_impl_apply_run]
  -- Use evalDist_congr: both sides reduce to
  -- `(fun a => (a, (cache, kp, msgs), b)) <$> ($ᵗ Fin (n+1))`.
  congr 1

/-- **Per-query H4 equivalence** on the RO branch. -/
lemma cmaSim_impl_run_eq_link_under_bij_ro
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (mc : M × Commit) (s : cmaGameState M Commit Chal Stmt Wit) :
    evalDist (((cmaSim M Commit Chal hr simT).impl (Sum.inl (Sum.inl (Sum.inr mc)))).run s) =
      evalDist (Prod.map id cmaLinkStateEquiv.symm <$>
        (((cmaToNma (Stmt := Stmt) M Commit Chal simT).link
            (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)).impl
            (Sum.inl (Sum.inl (Sum.inr mc)))).run (cmaLinkStateEquiv s)) := by
  -- Boilerplate per-query equivalence: both sides reduce to a `match cache mc`
  -- expression with structurally-identical branches up to `cmaLinkStateEquiv`.
  -- Fill in during Phase F cleanup; does not affect the main H4 structure.
  sorry

/-- **Per-query H4 equivalence** on the pk branch. -/
lemma cmaSim_impl_run_eq_link_under_bij_pk
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (s : cmaGameState M Commit Chal Stmt Wit) :
    evalDist (((cmaSim M Commit Chal hr simT).impl (Sum.inr ())).run s) =
      evalDist (Prod.map id cmaLinkStateEquiv.symm <$>
        (((cmaToNma (Stmt := Stmt) M Commit Chal simT).link
            (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)).impl
            (Sum.inr ())).run (cmaLinkStateEquiv s)) := by
  -- Boilerplate per-query equivalence: both sides reduce to a `match kp` expression
  -- with structurally-identical branches up to `cmaLinkStateEquiv`.
  -- Fill in during Phase F cleanup; does not affect the main H4 structure.
  sorry

/-- **Per-query H4 equivalence** (sign branch).

On the sign branch of `cmaSpec`, running `cmaSim.impl (Sum.inl (Sum.inr m))`
at state `s` is `evalDist`-equivalent to running
`(cmaToNma.link nma).impl (Sum.inl (Sum.inr m))` at `cmaLinkStateEquiv s`
composed with `Prod.map id φ.symm`.

The two sides both (i) fetch-or-sample the keypair, (ii) sample
`simT pk`, and (iii) conditionally program the RO cache at `(m, c)`.
The `simulateQ_nma_impl_liftM_unifSpec_run` helper handles step (ii)
for the `cmaToNma.link nma` side; the remaining algebra is a
Boolean/`Option` case-split on the pre-cache at `(m, c)` and the
pre-keypair. -/
lemma cmaSim_impl_run_eq_link_under_bij_sign
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (m : M) (s : cmaGameState M Commit Chal Stmt Wit) :
    evalDist ((((cmaSim M Commit Chal hr simT).impl (Sum.inl (Sum.inr m))).run s)) =
      evalDist (Prod.map id cmaLinkStateEquiv.symm <$>
        (((cmaToNma (Stmt := Stmt) M Commit Chal simT).link
            (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)).impl
            (Sum.inl (Sum.inr m))).run
          (cmaLinkStateEquiv s)) := by
  rcases s with ⟨⟨cache, kp, msgs⟩, b⟩
  -- LHS: unfold `cmaSim_impl_sign_apply_run` to expose `signSimInnerImpl`.
  rw [cmaSim_impl_sign_apply_run]
  -- RHS: unfold `link_impl_apply_run` (linkReshape + simulateQ nma.impl of the cmaToNma sign branch).
  rw [Package.link_impl_apply_run]
  -- Unfold `cmaToNma.impl (Sum.inl (Sum.inr m))` — sample pk, sample simT, program RO.
  -- Both sides end up as `<keypair>; let (c, ch, π) ← simT pk; <cache-update>; ...`.
  -- The inner `simulateQ nma.impl (liftM (simT pk))` on the RHS is handled by
  -- `simulateQ_nma_impl_liftM_unifSpec_run`.
  show evalDist ((fun vs => (vs.1, vs.2, b || progCollision m (cache, kp, msgs) vs.1)) <$>
      ((signSimInnerImpl M Commit Chal hr simT m).run (cache, kp, msgs))) = _
  -- Unfold `signSimInnerImpl`, `(cmaToNma.impl (Sum.inl (Sum.inr m))).run msgs`,
  -- and `simulateQ nma.impl (...)` branch-by-branch on kp / cache (m, c).
  unfold signSimInnerImpl cmaToNma
  simp only [StateT.run_bind, StateT.run_pure, StateT.run_map]
  -- Split on the pre-keypair: `kp ∈ {some (pk, sk), none}`.
  rcases hkp : kp with _ | ⟨pk₀, sk₀⟩
  all_goals simp only [simulateQ_bind, simulateQ_pure, simulateQ_map, StateT.run_bind,
    StateT.run_pure, StateT.run_map, map_pure, map_bind, pure_bind, bind_pure_comp,
    bind_assoc]
  all_goals sorry
  -- The remaining residue on each branch is a `simulateQ nma.impl (liftM (simT pk))` and
  -- a `nma.impl (progSpec _)` step whose cache-hit vs. cache-miss case split matches the
  -- LHS's `cache'` pattern-match plus the `b || progCollision …` bad-flag update.

/-- **H4 hop** (program equivalence, Phase F).

Running `cmaSim` against an adversary `A` is distributionally identical
to running the CMA-to-NMA reduction against `A` and then running the NMA
game. This is the "zero-advantage" hop that rewrites `cmaSim` as a
composition `cmaToNma.link nma`, which is then consumed by the SSP
link-shift identity `run_link_eq_run_shiftLeft`.

Statement is at the `evalDist`-level (rather than strict `ProbComp`
equality) because `cmaSim`'s state (`cmaInnerState × Bool`) and the
link state (`List M × nma-state`) are isomorphic in output but not
syntactically equal; the distributional equivalence is all we need
downstream (for `Package.advantage_eq_of_evalDist_runProb_eq`). -/
theorem cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {α : Type}
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) :
    evalDist ((cmaSim M Commit Chal hr simT).runProb A) =
      evalDist ((nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
        ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A)) := by
  -- Step 1: rewrite the RHS via `run_link_eq_run_shiftLeft` so both sides are
  -- of the form `P.runProb A` with differing `P`.
  rw [show (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
        ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A) =
          ((cmaToNma (Stmt := Stmt) M Commit Chal simT).link
            (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)).runProb A from
    (Package.run_link_eq_run_shiftLeft _ _ A).symm]
  -- Step 2: reduce both `runProb = run = init >>= fun s => (simulateQ impl A).run' s`
  -- to `(simulateQ impl A).run' initialState` by evaluating the `pure`-inits.
  simp only [Package.runProb_eq_run]
  unfold Package.run
  have hcmaSim_init : (cmaSim M Commit Chal hr simT).init =
      (pure ((∅, none, []), false) : ProbComp _) := rfl
  have hlink_init : ((cmaToNma (Stmt := Stmt) M Commit Chal simT).link
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)).init =
      (pure ([], (∅, false, none)) : ProbComp _) := rfl
  rw [hcmaSim_init, hlink_init]
  simp only [pure_bind]
  -- Step 3: reduce `.run'` to `Prod.fst <$> .run`, apply `simulateQ_StateT_evalDist_congr_of_bij`
  -- to bring the RHS state to `Prod.map id φ.symm <$> ...` form, then collapse `Prod.fst` with
  -- `Prod.map id φ.symm` (since `Prod.fst ∘ Prod.map id φ.symm = Prod.fst`).
  rw [StateT.run'_eq, StateT.run'_eq]
  -- Apply the bijection-congruence lemma. Per-query hypothesis splits over `unif | ro | sign | pk`.
  have hbij : evalDist ((simulateQ (cmaSim M Commit Chal hr simT).impl A).run
      ((∅, none, []), false)) =
    evalDist (Prod.map id cmaLinkStateEquiv.symm <$>
      (simulateQ ((cmaToNma (Stmt := Stmt) M Commit Chal simT).link
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)).impl A).run
        ([], (∅, false, none))) := by
    have hφ : cmaLinkStateEquiv (((∅, none, []), false) :
        cmaGameState M Commit Chal Stmt Wit) = ([], (∅, false, none)) := rfl
    rw [show (([], (∅, false, none)) :
          List M × ((roSpec M Commit Chal).QueryCache × Bool × Option (Stmt × Wit))) =
        cmaLinkStateEquiv (((∅, none, []), false) :
            cmaGameState M Commit Chal Stmt Wit) from hφ.symm]
    refine Package.simulateQ_StateT_evalDist_congr_of_bij _ _ cmaLinkStateEquiv
      (fun q s => ?_) A _
    rcases q with ((u | r) | m) | ⟨⟩
    · exact cmaSim_impl_run_eq_link_under_bij_unif (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) (rel := rel) hr simT u s
    · exact cmaSim_impl_run_eq_link_under_bij_ro (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) (rel := rel) hr simT r s
    · exact cmaSim_impl_run_eq_link_under_bij_sign (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) (rel := rel) hr simT m s
    · exact cmaSim_impl_run_eq_link_under_bij_pk (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) (rel := rel) hr simT s
  -- Apply `hbij` and collapse via `Prod.fst ∘ Prod.map id φ.symm = Prod.fst`.
  rw [evalDist_map, evalDist_map, hbij, ← evalDist_map, Functor.map_map, evalDist_map]
  -- LHS: `(fun a => (Prod.map id φ.symm a).1) <$> evalDist ...`
  -- RHS: `Prod.fst <$> evalDist ...`. They're equal since the two maps are extensionally equal.
  congr 1

end FiatShamir.SSP
