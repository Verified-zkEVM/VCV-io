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

This commit lands only the Phase E1 scaffolding for H3:

* `IsCostlyQuery` — the predicate picking out `signSpec` queries inside
  `cmaSpec`, matching the `S` predicate consumed by
  `Package.advantage_le_expectedSCost_plus_probEvent_bad`.
* `cmaReal_impl_eq_cmaSim_impl_of_not_isCostlyQuery` — non-sign queries are
  pointwise identical between `cmaReal` and `cmaSim`. This is the
  `h_step_eq_nS` hypothesis of the SSP bridge.
* `cmaSim_impl_bad_monotone` — once `cmaSim`'s bad flag is set, every
  continuation keeps it set. This is the `h_mono₀` hypothesis of the SSP
  bridge, applied with `G₀ = cmaSim`.

The per-step TV bound on sign queries (`h_step_tv_S`), the bad-event
probability bound, and the top-level H3 statement are scheduled for the
subsequent Phase E2-E5 commits.
-/

universe u

open OracleSpec OracleComp ProbComp VCVio.SSP

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

end FiatShamir.SSP
