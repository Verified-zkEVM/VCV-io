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

/-! ### `h_mono₀`: `cmaSim`'s bad flag is monotonic -/

/-- Once `cmaSim`'s bad flag is `true`, every continuation of `cmaSim.impl`
preserves it. This is the `h_mono₀` hypothesis of the SSP bridge when
instantiated with `G₀ = cmaSim`. -/
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
