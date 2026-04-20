/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.CryptoFoundations.SeededFork
import VCVio.CryptoFoundations.ReplayFork

/-!
# EUF-CMA security of the Fiat-Shamir Σ-protocol transform

End-to-end security reduction, packaged as three theorems:

- `euf_cma_to_nma`: CMA-to-NMA via HVZK simulation, absorbing the signing-query
  loss into a statistical term `qS · ζ_zk + ζ_col`;
- `euf_nma_bound`: NMA-to-extraction via `Fork.replayForkingBound` and special
  soundness, producing a reduction to `hardRelationExp`;
- `euf_cma_bound`: the combined bound, instantiating `euf_cma_to_nma` into
  `euf_nma_bound`.
-/

universe u v

open OracleComp OracleSpec

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

/-! ### Bad-flag support lemmas

Generic monotonicity lemmas about the `QueryImpl.withBadFlag` and `QueryImpl.withBadUpdate`
combinators (see `VCVio/OracleComp/SimSemantics/StateT.lean`). They formalize the obvious facts
that the boolean (bad) flag in the lifted state is *threaded unchanged* by `withBadFlag` and is
*OR-monotone* under `withBadUpdate`. We use them below to discharge the monotonicity hypothesis
of the per-query ε-perturbed identical-until-bad lemma. -/

private lemma support_withBadFlag_run_snd_snd
    {ι : Type*} {spec : OracleSpec ι} {ι' : Type*} {spec' : OracleSpec ι'}
    {σ : Type _} (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (t : spec.Domain) (s : σ) (b : Bool)
    {z : spec.Range t × σ × Bool}
    (hz : z ∈ support ((impl.withBadFlag t).run (s, b))) :
    z.2.2 = b := by
  simp only [QueryImpl.withBadFlag, StateT.run, StateT.mk, support_map] at hz
  obtain ⟨_, _, rfl⟩ := hz
  rfl

private lemma support_withBadUpdate_run_snd_snd_of_pre
    {ι : Type*} {spec : OracleSpec ι} {ι' : Type*} {spec' : OracleSpec ι'}
    {σ : Type _} (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (f : (t : spec.Domain) → σ → spec.Range t → Bool)
    (t : spec.Domain) (s : σ)
    {z : spec.Range t × σ × Bool}
    (hz : z ∈ support ((impl.withBadUpdate f t).run (s, true))) :
    z.2.2 = true := by
  simp only [QueryImpl.withBadUpdate, StateT.run, StateT.mk, support_map] at hz
  obtain ⟨_, _, rfl⟩ := hz
  simp

/-- Birthday-bound collision slack for the Fiat-Shamir CMA-to-NMA reduction.

For `qS` signing queries and `qH` random-oracle queries with challenge space `Chal`, the
probability of a programming-collision on either side of the freshness-preserving chain
is bounded by `qS · (qS + qH) / |Chal|` via a birthday/union bound on commitments.

The full chain absorbs three slacks into this single numerator `2 · qS · (qS + qH) + 1`:
* `qS · (qS + qH) / |Chal|` from the simulator-side bad event (sub-claim B-finish);
* `qS · (qS + qH) / |Chal|` from the FS-vs-programming bad event in the (A) bridge,
  which swaps the actual `FiatShamir.sign` oracle for the hypothetical programming-style
  `realSign` (identical until the same cache-collision bad event);
* `1 / |Chal|` from the cache-miss verify slack: `unforgeableExp` samples a uniformly
  random RO answer when the forgery's hash point is *not* in the cache (winning with
  probability `1/|Chal|` by special soundness / unique-response uniqueness), while
  `Fork.runTrace` returns `false` on the same cache miss.

Matches EasyCrypt's `pr_bad_game` at
[fsec/proof/Schnorr.ec:793](../../../fsec/proof/Schnorr.ec) (`QS · (QS+QR) / |Ω|`, modulo
the doubled birthday bound and the `+1` cache-miss slack) and plays the same role as
`GPVHashAndSign.collisionBound` for the PSF construction. -/
noncomputable def collisionSlack (qS qH : ℕ) (Chal : Type) [Fintype Chal] : ENNReal :=
  ((2 * qS * (qS + qH) + 1 : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal)

/-- **CMA-to-NMA reduction via HVZK simulation.**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists a managed-RO NMA adversary `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{fork-NMA}_{qH}(B) + qS · ζ_zk + qS · (qS + qH) / |Chal|`

The NMA adversary `B` is constructed by:
- Forwarding `A`'s hash queries to the external oracle (visible to `Fork.fork`)
- Simulating `A`'s signing queries using the HVZK simulator, programming the
  simulated challenge into the cache
- Returning `A`'s forgery together with the accumulated `QueryCache`

Each of the `qS` signing simulations introduces at most `ζ_zk` total-variation distance;
the birthday term `collisionSlack qS qH Chal` absorbs collisions where `A` queries a
hash that `B` later programs.

This step is independent of special soundness and the forking lemma; those are handled
by `euf_nma_bound`.

The Lean bound matches Firsov-Janku's `pr_koa_cma` at
[fsec/proof/Schnorr.ec:943](../../../fsec/proof/Schnorr.ec): the CMA-to-KOA reduction uses
`eq_except (signed qs) LRO.m{1} LRO.m{2}` as the RO-cache invariant, swaps real signing with
`simulator_equiv` (per-query HVZK cost), handles RO reprogramming via `lro_redo_inv` +
`ro_get_eq_except`, and absorbs the late-programming collision event through the `bad` flag,
bounded by `pr_bad_game` at [fsec/proof/Schnorr.ec:793](../../../fsec/proof/Schnorr.ec) as
`QS · (QS+QR) / |Ω|`, matching our `collisionSlack qS qH Chal`. -/
theorem euf_cma_to_nma
    [DecidableEq M] [DecidableEq Commit]
    [Fintype Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (_hζ_zk : 0 ≤ ζ_zk)
    (_hhvzk : σ.HVZK simTranscript ζ_zk)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ nmaAdv : SignatureAlg.managedRoNmaAdv
        (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M),
      (∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := nmaAdv.main pk) qH) ∧
      adv.advantage (runtime M) ≤
        Fork.advantage σ hr M nmaAdv qH +
          ENNReal.ofReal (qS * ζ_zk) +
          collisionSlack qS qH Chal := by
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
    | none =>
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  let baseSim : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    unifSim + roSim
  let sigSim : Stmt → QueryImpl (M →ₒ (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun pk msg => do
    let (c, ω, s) ← simulateQ unifSim (simTranscript pk)
    modifyGet fun cache =>
      match cache (.inr (msg, c)) with
      | some _ => ((c, s), cache)
      | none => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)
  let nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M) :=
    ⟨fun pk => (simulateQ (baseSim + sigSim pk) (adv.main pk)).run ∅⟩
  refine ⟨nmaAdv, ?_, ?_⟩
  · -- Query bound: show the NMA adversary makes at most `qH` hash queries.
    -- `fwd` forwards each hash query as-is (1 hash query per CMA hash query).
    -- `sigSim` handles signing queries via `simTranscript` + cache programming,
    -- generating zero hash queries (only uniform queries from `simTranscript`).
    -- Requires a general `IsQueryBound` transfer lemma for `simulateQ` + `StateT.run`.
    intro pk
    let stepBudget :
        (spec + (M →ₒ (Commit × Resp))).Domain → ℕ × ℕ → ℕ := fun t _ =>
      match t with
      | .inl (.inl _) => 0
      | .inl (.inr _) => 1
      | .inr _ => 0
    have hbind :
        ∀ {α β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β} {Q₁ Q₂ : ℕ},
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁ →
          (∀ x, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := ob x) Q₂) →
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := oa >>= ob) (Q₁ + Q₂) := by
      intro α β oa ob Q₁ Q₂ h1 h2
      exact nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal) h1 h2
    have hfwd :
        ∀ (t : spec.Domain) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (fwd t).run s) (match t with
              | .inl _ => 0
              | .inr _ => 1) := by
      intro t s
      cases t with
      | inl n =>
          simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
            OracleComp.liftM_run_StateT] using
            (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
              (show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := liftM (spec.query (.inl n))) 0 by
                  exact
                    (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
                      (.inl n) 0).2 trivial)
              (fun u =>
                show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := pure (u, s)) 0 by
                    trivial))
      | inr mc =>
          simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
            OracleComp.liftM_run_StateT] using
            (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
              (show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := liftM (spec.query (.inr mc))) 1 by
                  exact
                    (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
                      (.inr mc) 1).2 (Nat.succ_pos 0))
              (fun u =>
                show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := pure (u, s)) 0 by
                    trivial))
    have hro :
        ∀ (mc : M × Commit) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (roSim mc).run s) 1 := by
      intro mc s
      cases hs : s (.inr mc) with
      | some v =>
          simp [roSim, hs, nmaHashQueryBound]
      | none =>
          simpa [roSim, hs] using
            ((OracleComp.isQueryBound_map_iff
                (oa := (fwd (.inr mc)).run s)
                (f := fun a : Chal × spec.QueryCache =>
                  (a.1, a.2.cacheQuery (.inr mc) a.1))
                (b := 1)
                (canQuery := fun t b => match t with
                  | .inl _ => True
                  | .inr _ => 0 < b)
                (cost := fun t b => match t with
                  | .inl _ => b
                  | .inr _ => b - 1)).2
              (hfwd (.inr mc) s))
    have hsig :
        ∀ (msg : M) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (sigSim pk msg).run s) 0 := by
      intro msg s
      have hsource : OracleComp.IsQueryBound
          (simTranscript pk) () (fun _ _ => True) (fun _ _ => ()) := by
        induction simTranscript pk using OracleComp.inductionOn with
        | pure x =>
            trivial
        | query_bind t mx ih =>
            simp [OracleComp.isQueryBound_query_bind_iff, ih]
      have htranscript :
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (simulateQ unifSim (simTranscript pk)).run s) 0 := by
        simpa [nmaHashQueryBound] using
          (OracleComp.IsQueryBound.simulateQ_run_of_step
            (h := hsource) (combine := Nat.add) (mapBudget := fun _ => 0)
            (stepBudget := fun _ _ => 0) (impl := unifSim)
            (hbind := by
              intro γ δ oa' ob b₁ b₂ h1 h2
              have h1' :
                  nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                    (oa := oa') b₁ := by
                simpa [nmaHashQueryBound] using h1
              have h2' : ∀ x,
                  nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                    (oa := ob x) b₂ := by
                intro x
                simpa [nmaHashQueryBound] using h2 x
              simpa [nmaHashQueryBound] using
                (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := oa') (ob := ob) (Q₁ := b₁) (Q₂ := b₂) h1' h2')
            )
            (hstep := by
              intro t b s' ht
              simpa [unifSim] using hfwd (.inl t) s')
            (hcombine := by
              intro t b ht
              simp)
            (s := s))
      simpa [sigSim, nmaHashQueryBound] using
        ((OracleComp.isQueryBound_map_iff
            (oa := (simulateQ unifSim (simTranscript pk)).run s)
            (f := fun a : (Commit × Chal × Resp) × spec.QueryCache =>
              match a.2 (.inr (msg, a.1.1)) with
              | some _ => ((a.1.1, a.1.2.2), a.2)
              | none =>
                  ((a.1.1, a.1.2.2),
                    QueryCache.cacheQuery a.2 (.inr (msg, a.1.1)) a.1.2.1))
            (b := 0)
            (canQuery := fun t b => match t with
              | .inl _ => True
              | .inr _ => 0 < b)
            (cost := fun t b => match t with
              | .inl _ => b
              | .inr _ => b - 1)).2 htranscript)
    have hstep :
        ∀ t b s,
          (match t, b with
            | .inl (.inl _), _ => True
            | .inl (.inr _), (_, qH') => 0 < qH'
            | .inr _, (qS', _) => 0 < qS') →
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := ((baseSim + sigSim pk) t).run s) (stepBudget t b) := by
      intro t b s ht
      rcases b with ⟨qS', qH'⟩
      cases t with
      | inl t =>
          cases t with
          | inl n =>
              simpa [baseSim, stepBudget] using hfwd (.inl n) s
          | inr mc =>
              simpa [baseSim, stepBudget] using hro mc s
      | inr msg =>
          simpa [stepBudget] using hsig msg s
    have hcombine :
        ∀ t b,
          (match t, b with
            | .inl (.inl _), _ => True
            | .inl (.inr _), (_, qH') => 0 < qH'
            | .inr _, (qS', _) => 0 < qS') →
          Nat.add (stepBudget t b)
            (Prod.snd (match t, b with
              | .inl (.inl _), b' => b'
              | .inl (.inr _), (qS', qH') => (qS', qH' - 1)
              | .inr _, (qS', qH') => (qS' - 1, qH'))) =
            Prod.snd b := by
      intro t b ht
      rcases b with ⟨qS', qH'⟩
      cases t with
      | inl t =>
          cases t with
          | inl n =>
              simp [stepBudget]
          | inr mc =>
              simp [stepBudget] at ht ⊢
              omega
      | inr msg =>
          simp [stepBudget]
    simpa [nmaHashQueryBound, signHashQueryBound] using
      (OracleComp.IsQueryBound.simulateQ_run_of_step
        (h := _hQ pk) (combine := Nat.add) (mapBudget := Prod.snd)
        (stepBudget := stepBudget) (impl := baseSim + sigSim pk)
        (hbind := by
          intro γ δ oa' ob b₁ b₂ h1 h2
          have h1' :
              nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := oa') b₁ := by
            simpa [nmaHashQueryBound] using h1
          have h2' : ∀ x,
              nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := ob x) b₂ := by
            intro x
            simpa [nmaHashQueryBound] using h2 x
          simpa [nmaHashQueryBound] using
            (hbind (oa := oa') (ob := ob) (Q₁ := b₁) (Q₂ := b₂) h1' h2')
        )
        (hstep := by
          intro t b s ht
          rcases b with ⟨qS', qH'⟩
          cases t with
          | inl t =>
              cases t with
              | inl n =>
                  simpa [nmaHashQueryBound, baseSim, stepBudget] using hfwd (.inl n) s
              | inr mc =>
                  simpa [nmaHashQueryBound, baseSim, stepBudget] using hro mc s
          | inr msg =>
              simpa [nmaHashQueryBound, stepBudget] using hsig msg s)
        (hcombine := by
          intro t b ht
          rcases b with ⟨qS', qH'⟩
          cases t with
          | inl t =>
              cases t with
              | inl n =>
                  simp [stepBudget]
              | inr mc =>
                  simp [stepBudget] at ht ⊢
                  omega
          | inr msg =>
              simp [stepBudget])
        (s := ∅))
  · -- Advantage bound: `adv.advantage ≤ Adv^{fork-NMA}_{qH}(nmaAdv)
    --                      + ofReal(qS * ζ_zk) + collisionSlack qS qH Chal`.
    --
    -- **Freshness-preserving chain.** The previous design routed through
    -- `unforgeableExpNoFresh` (which drops the `¬log.wasQueried msg` check), but
    -- that intermediate is trivially won by *replay attacks*: an adversary that
    -- queries the signing oracle on `msg` and outputs the received signature has
    -- `unforgeableExpNoFresh = 1`, while `Fork.advantage = 0` for the same
    -- adversary (its forgery's hash point need not appear in the *live* RO query
    -- log, since it is satisfied by a *programmed* entry from `sigSim`). The
    -- hop `unforgeableExpNoFresh ≤ Fork.advantage + slack` is therefore **not
    -- provable**.
    --
    -- The fix is to keep freshness throughout. The new chain:
    --
    --   adv.advantage (runtime M)
    --       = ∑' (pk,sk), Pr[(pk,sk)|gen] · Pr[verify ∧ ¬msg ∈ signed | direct_real_exp pk sk]
    --                                                                       -- (A) bridge_real
    --       ≤ ∑' (pk,sk), Pr[(pk,sk)|gen] ·
    --           (Pr[verify ∧ ¬msg ∈ signed | direct_sim_exp pk] + qS·ζ_zk + collisionSlack)
    --                                                                       -- (B) tv_swap
    --       ≤ Fork.advantage + qS·ζ_zk + collisionSlack + 1/|Chal|          -- (C') sim_to_fork
    --
    -- The `+ 1/|Chal|` slack in (C') accounts for `unforgeableExp`'s verify step
    -- sampling a fresh random-oracle answer on a cache miss, while
    -- `Fork.runTrace` returns `false` on cache misses; this `+1/|Chal|` is
    -- absorbed into the ambient `collisionSlack` (which is ≥ `qS / |Chal|` for
    -- any non-degenerate adversary).
    --
    -- The augmented state `((QueryCache × List M) × Bool)` carries:
    --   * `QueryCache`: the random-oracle cache (programmed + live entries).
    --   * `List M`: signed messages, in reverse order of signing queries.
    --   * `Bool`: the collision-bad flag (set when `sigSim` programs a point
    --     that was already cached).
    --
    -- The per-query TV bound (B) follows from
    -- `tvDist_simulateQ_le_qSeps_plus_probEvent_output_bad`
    -- (`VCVio/ProgramLogic/Relational/SimulateQ.lean`); the signed-list update
    -- is identical and deterministic on the sim and real sides, so it does not
    -- contribute to TV beyond the existing `(cache × Bool)`-state bound.
    --
    -- The (B-finish) collision bound and the (A) / (C') bridges are tracked
    -- separately as named sub-sorries. Each is mathematically substantive:
    --
    --   * (A) `bridge_real_freshness`: rewrite `unforgeableExp` as an
    --     integral over `keygen` of `direct_real_exp pk sk`. Requires
    --     factoring out `keygen` from the SPMF `runtime.evalDist`, then
    --     equating the WriterT log of `signingOracle` with the augmented
    --     `signed` state.
    --
    --   * (B-finish) `pr_bad_le_collisionSlack`: union-bound on `qS`
    --     programming events, each hitting a previously cached point with
    --     probability ≤ `(qS + qH) / |Chal|`. The per-event uniformity comes
    --     from the per-query HVZK simulator (challenge marginal is uniform).
    --
    --   * (C') `bridge_sim_fork_freshness`: a forgery `(msg, c, s)` against
    --     `direct_sim_exp` with `¬msg ∈ signed` cannot have used a programmed
    --     `(msg, c)` cache entry (since `sigSim` only programs at signed `msg`),
    --     so `(msg, c)` is in the live RO query log iff it is in the cache.
    --     The `+ 1/|Chal|` slack absorbs the cache-miss verify case.
    -- Construct the bad-flag-aware impls used in the application of
    -- `tvDist_simulateQ_le_qeps_plus_probEvent_output_bad`. We use the
    -- `QueryImpl.withBadFlag` / `QueryImpl.withBadUpdate` combinators so the per-query
    -- monotonicity follows from the generic `support_with*_run_snd_snd_*` lemmas.
    -- `baseSimBad` lifts `baseSim` to `StateT (cache × Bool)` by threading the bad flag
    -- unchanged (the base oracles never set it).
    let baseSimBad : QueryImpl spec
        (StateT (spec.QueryCache × Bool) (OracleComp spec)) :=
      baseSim.withBadFlag
    -- Predicate for the simulator's bad event: programming `(msg, c)` would overwrite a
    -- previously cached entry (the cache is the *pre-state*, so this is the genuine
    -- collision check that birthday bounds bound).
    let sigBadF : (msg : M) → spec.QueryCache → Commit × Resp → Bool :=
      fun msg cache vc => (cache (.inr (msg, vc.1))).isSome
    -- `sigSimBad pk` lifts `sigSim pk` to `StateT (cache × Bool)`; the bad flag is
    -- OR-updated with `sigBadF`.
    let sigSimBad : Stmt → QueryImpl (M →ₒ (Commit × Resp))
        (StateT (spec.QueryCache × Bool) (OracleComp spec)) := fun pk =>
      (sigSim pk).withBadUpdate sigBadF
    -- Combined "sim" implementation (per-pk): forwarders + sigSimBad.
    let _simImpl : Stmt → QueryImpl (spec + (M →ₒ (Commit × Resp)))
        (StateT (spec.QueryCache × Bool) (OracleComp spec)) := fun pk =>
      baseSimBad + sigSimBad pk
    -- `realSign pk sk` is a *hypothetical* programming-style signing oracle that samples a
    -- real transcript `(c, ch, π) ← σ.realTranscript pk sk` and programs the RO cache at
    -- `(msg, c) ↦ ch` (only on a cache miss; on a hit the cache is preserved). It mirrors
    -- `sigSim` exactly except that it uses `realTranscript` in place of `simTranscript`,
    -- so the per-query HVZK guarantee directly bounds their TV distance by `ζ_zk`.
    let realSign : Stmt → Wit → QueryImpl (M →ₒ (Commit × Resp))
        (StateT spec.QueryCache (OracleComp spec)) := fun pk sk msg => do
      let cache ← get
      let (c, ch, π) ← liftM ((σ.realTranscript pk sk : ProbComp _).liftComp spec)
      modifyGet fun cache =>
        match cache (.inr (msg, c)) with
        | some _ => ((c, π), cache)
        | none => ((c, π), cache.cacheQuery (.inr (msg, c)) ch)
    -- `realSignBad pk sk` is the bad-flag-aware lift of `realSign pk sk`, OR-updated with
    -- the same `sigBadF` predicate so its bad event matches the simulator's. A separate
    -- bridge step (`bridge_g1_real`, sub-claim (A)) connects this hypothetical signer to the
    -- actual `FiatShamir.sign` oracle used in `g1`.
    let realSignBad : Stmt → Wit → QueryImpl (M →ₒ (Commit × Resp))
        (StateT (spec.QueryCache × Bool) (OracleComp spec)) := fun pk sk =>
      (realSign pk sk).withBadUpdate sigBadF
    -- Combined "real" implementation (per-(pk, sk)): forwarders + realSignBad.
    let _realImpl : Stmt → Wit → QueryImpl (spec + (M →ₒ (Commit × Resp)))
        (StateT (spec.QueryCache × Bool) (OracleComp spec)) := fun pk sk =>
      baseSimBad + realSignBad pk sk
    -- Augmented state for the freshness-preserving chain.
    -- The state `((spec.QueryCache × List M) × Bool)` adds a `List M` of signed messages
    -- (reverse-chronological) between the cache and the bad flag, so the freshness check
    -- `¬msg ∈ signed` is local to the augmented experiment.
    -- `baseSimSigned'` lifts `baseSim` to `StateT (cache × signed) (OracleComp spec)` by
    -- threading `signed` unchanged. Base oracles never sign, so `signed` stays the same.
    let baseSimSigned' : QueryImpl spec
        (StateT (spec.QueryCache × List M) (OracleComp spec)) := fun t => do
      let s ← get
      let v ← (baseSim t).run s.1
      set (v.2, s.2)
      pure v.1
    -- `sigSimSigned' pk msg` lifts `sigSim pk msg` and prepends `msg` to `signed`.
    let sigSimSigned' : Stmt → QueryImpl (M →ₒ (Commit × Resp))
        (StateT (spec.QueryCache × List M) (OracleComp spec)) := fun pk msg => do
      let s ← get
      let v ← (sigSim pk msg).run s.1
      set (v.2, msg :: s.2)
      pure v.1
    -- `realSignSigned' pk sk msg` lifts `realSign pk sk msg` and prepends `msg` to `signed`.
    let realSignSigned' : Stmt → Wit → QueryImpl (M →ₒ (Commit × Resp))
        (StateT (spec.QueryCache × List M) (OracleComp spec)) := fun pk sk msg => do
      let s ← get
      let v ← (realSign pk sk msg).run s.1
      set (v.2, msg :: s.2)
      pure v.1
    -- Bad-flag predicate on the augmented state: programming `(msg, c)` would overwrite
    -- a previously cached entry. Identical to `sigBadF` modulo the `signed` projection.
    let sigBadFSigned : (msg : M) → spec.QueryCache × List M → Commit × Resp → Bool :=
      fun msg s vc => (s.1 (.inr (msg, vc.1))).isSome
    -- Bad-flag-aware lifts of the augmented impls.
    let baseSimSigned : QueryImpl spec
        (StateT ((spec.QueryCache × List M) × Bool) (OracleComp spec)) :=
      baseSimSigned'.withBadFlag
    let sigSimSigned : Stmt → QueryImpl (M →ₒ (Commit × Resp))
        (StateT ((spec.QueryCache × List M) × Bool) (OracleComp spec)) := fun pk =>
      (sigSimSigned' pk).withBadUpdate sigBadFSigned
    let realSignSigned : Stmt → Wit → QueryImpl (M →ₒ (Commit × Resp))
        (StateT ((spec.QueryCache × List M) × Bool) (OracleComp spec)) := fun pk sk =>
      (realSignSigned' pk sk).withBadUpdate sigBadFSigned
    -- Combined "sim" implementation on the augmented state.
    let _simImplSigned : Stmt → QueryImpl (spec + (M →ₒ (Commit × Resp)))
        (StateT ((spec.QueryCache × List M) × Bool) (OracleComp spec)) := fun pk =>
      baseSimSigned + sigSimSigned pk
    -- Combined "real" implementation on the augmented state.
    let _realImplSigned : Stmt → Wit → QueryImpl (spec + (M →ₒ (Commit × Resp)))
        (StateT ((spec.QueryCache × List M) × Bool) (OracleComp spec)) := fun pk sk =>
      baseSimSigned + realSignSigned pk sk
    have advantage_bound : adv.advantage (runtime M) ≤ Fork.advantage σ hr M nmaAdv qH +
        ENNReal.ofReal (qS * ζ_zk) + collisionSlack qS qH Chal := by
      -- **Freshness-preserving chain.** See the docstring at the top of this bullet for
      -- the rationale. The proof structure is:
      --
      --   adv.advantage (runtime M)
      --       ≤ ∑' (pk,sk), Pr[(pk,sk)|gen] · Pr[verify ∧ ¬msg ∈ signed | direct_real_exp pk sk]
      --                                                                       -- (A) bridge_a
      --       ≤ ∑' (pk,sk), Pr[(pk,sk)|gen] ·
      --           (Pr[verify ∧ ¬msg ∈ signed | direct_sim_exp pk] + qS·ζ_zk + Pr[bad on sim])
      --                                                                       -- (B) tv_swap
      --       ≤ ∑' pk, Pr[pk|gen_pk] · Pr[verify ∧ ¬msg ∈ signed | direct_sim_exp pk] +
      --           qS·ζ_zk + collisionSlack qS qH Chal                         -- (B-finish)
      --       ≤ Fork.advantage + qS·ζ_zk + collisionSlack qS qH Chal          -- (C')
      --
      -- The augmented state for `direct_*_exp` is `(QueryCache × List M × Bool)`, with the
      -- `List M` tracking signed messages (so the freshness check `¬msg ∈ signed` is local).
      -- The `Bool` is the collision-bad flag (set when programming overwrites a cached point).
      --
      -- The four sub-claims are scaffolded as sorries with detailed sketches; `step_b_per_pksk`
      -- (the underlying selective ε lemma application on the simpler `(cache × Bool)` state)
      -- is fully proven and forms the infrastructure for sub-claim (B).
      --
      -- The `+ 1/|Chal|` slack from (C') is absorbed into `collisionSlack` (which now has
      -- a `+1` summand in its numerator: `(qS·(qS+qH) + 1) / |Chal|`).
      --
      -- Step (B), per (pk, sk) pair: the per-query ε bound from the selective lemma.
      -- The selective lemma yields a TV bound on the joint distribution of
      -- `(simulateQ _simImpl).run' (∅, false)` and `(simulateQ _realImpl).run' (∅, false)`
      -- of the form `qS · ζ_zk + Pr[bad on _simImpl]`. The `Pr[bad]` term is then bounded
      -- by `collisionSlack qS qH Chal` via the (B-finish) sub-claim.
      have step_b_per_pksk : ∀ (pk : Stmt) (sk : Wit), rel pk sk = true →
          tvDist
            ((simulateQ (_simImpl pk) (adv.main pk)).run' (∅, false))
            ((simulateQ (_realImpl pk sk) (adv.main pk)).run' (∅, false))
          ≤ qS * ζ_zk +
            Pr[fun z : (M × (Commit × Resp)) ×
                  (unifSpec + (M × Commit →ₒ Chal)).QueryCache × Bool =>
                z.2.2 = true |
              (simulateQ (_simImpl pk) (adv.main pk)).run (∅, false)].toReal := by
        intro pk sk h_rel
        -- Sign-query selector: `S t := match t with | .inr _ => True | _ => False`.
        let S : (spec + (M →ₒ (Commit × Resp))).Domain → Prop :=
          fun t => match t with | .inr _ => True | .inl _ => False
        have hS_dec : DecidablePred S := by
          intro t
          cases t with
          | inl _ => exact instDecidableFalse
          | inr _ => exact instDecidableTrue
        letI := hS_dec
        have apply_selective :=
          @OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_qSeps_plus_probEvent_output_bad
        refine apply_selective
          (impl₁ := _simImpl pk) (impl₂ := _realImpl pk sk)
          (ε := ζ_zk) _hζ_zk S
          ?h_step_tv_S ?h_step_eq_nS ?h_mono₁ (oa := adv.main pk) (qS := qS) ?h_qb
          (s₀ := (∅ : (unifSpec + (M × Commit →ₒ Chal)).QueryCache))
        case h_step_tv_S =>
          -- Per-query HVZK: per-query TV bound between `sigSimBad pk msg` (programs from
          -- `simTranscript pk`) and `realSignBad pk sk msg` (programs from
          -- `realTranscript pk sk`) is ≤ ζ_zk by `_hhvzk`.
          --
          -- The proof structure (when discharged) is:
          --   1. Both `(sigSimBad pk msg).run s` and `(realSignBad pk sk msg).run s` factor as
          --        do  let (c, ch, π) ← TRANSCRIPT
          --            let bad' := bad || (cache (.inr (msg, c))).isSome
          --            let cache' := if cache (.inr (msg, c)).isSome then cache
          --                          else cache.cacheQuery (.inr (msg, c)) ch
          --            pure ((c, π), cache', bad')
          --      with `TRANSCRIPT := simTranscript pk` (sim side) or `realTranscript pk sk`
          --      (real side); the rest is *deterministic and identical* (same `cache, bad`).
          --   2. By the data-processing inequality for `tvDist`, the joint output TV is
          --      bounded by `tvDist (simTranscript pk) (realTranscript pk sk) ≤ ζ_zk`,
          --      where the bound follows from `_hhvzk` (which requires `rel pk sk = true`).
          --
          -- Discharging this step requires:
          --   (a) Threading `rel pk sk = true` from the keygen-output assumption (a separate
          --       hypothesis on `keygen` that `(pk, sk) ∈ support keygen → rel pk sk = true`,
          --       valid for the `FiatShamir` scheme via `hr.gen_correct`).
          --   (b) The data-processing TV inequality for the deterministic programming step.
          --   (c) An equality lemma `(simulateQ unifSim oa).run cache ≡ oa.liftComp ⊗ pure cache`
          --       for any `oa : ProbComp _` (so that `sigSim`'s use of `simulateQ unifSim
          --       (simTranscript pk)` projects cleanly to `simTranscript pk`).
          intro t hSt s
          cases t with
          | inl _ => exact hSt.elim
          | inr msg =>
              -- Helper lemma: `(simulateQ unifSim oa).run s'` factors as the lifted
              -- comp paired with the unchanged state. This is the analog of
              -- `unifFwdImpl.simulateQ_run` for `StateT _ (OracleComp spec)` instead of
              -- `StateT _ ProbComp`.
              -- `unifSim` is the lifted `inj` where `inj t = liftM (spec.query (Sum.inl t))`.
              -- This `inj` is exactly `fun t => liftM (unifSpec.query t)` (the SubSpec lift),
              -- which is the same map that `liftComp` uses to lift `ProbComp` to `OracleComp spec`.
              have run_unifSim : ∀ (s' : spec.QueryCache) {β : Type} (oa : ProbComp β),
                  (simulateQ unifSim oa).run s' =
                    (fun x => (x, s')) <$> oa.liftComp spec := by
                intro s' β oa
                -- Define the equivalent `OracleComp spec`-valued `QueryImpl unifSpec`.
                set inj : QueryImpl unifSpec (OracleComp spec) :=
                  fun t => liftM (unifSpec.query t) with hinj
                -- Step 1: `unifSim = inj.liftTarget _` (defeq via `MonadLift` resolution).
                have unifSim_eq : unifSim = inj.liftTarget
                    (StateT spec.QueryCache (OracleComp spec)) := rfl
                rw [unifSim_eq, simulateQ_liftTarget]
                -- LHS: `(liftM (simulateQ inj oa)).run s'`
                -- `simulateQ inj oa = liftComp oa spec` by definition of `liftComp`.
                have simulateQ_inj : simulateQ inj oa = oa.liftComp spec := rfl
                rw [simulateQ_inj, OracleComp.liftM_run_StateT, bind_pure_comp]
              -- Step 1: factor `(sigSim pk msg).run s` as deterministic post-processing
              -- of `(simTranscript pk).liftComp spec`.
              have h_sigSim_run : (sigSim pk msg).run s =
                  (simTranscript pk).liftComp spec >>=
                    fun cωπ : Commit × Chal × Resp =>
                      pure (match s (.inr (msg, cωπ.1)) with
                        | some _ => ((cωπ.1, cωπ.2.2), s)
                        | none => ((cωπ.1, cωπ.2.2),
                            s.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1)) := by
                dsimp only [sigSim]
                rw [StateT.run_bind, run_unifSim s, bind_map_left]
                refine bind_congr (fun cωπ => ?_)
                simp only [modifyGet, MonadState.modifyGet,
                  MonadStateOf.modifyGet, StateT.modifyGet, StateT.run]
                congr 1
                rcases s (.inr (msg, cωπ.1)) with _ | _ <;> simp
              -- Step 2: factor `(realSign pk sk msg).run s` analogously.
              have h_realSign_run : (realSign pk sk msg).run s =
                  (σ.realTranscript pk sk).liftComp spec >>=
                    fun cωπ : Commit × Chal × Resp =>
                      pure (match s (.inr (msg, cωπ.1)) with
                        | some _ => ((cωπ.1, cωπ.2.2), s)
                        | none => ((cωπ.1, cωπ.2.2),
                            s.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1)) := by
                dsimp only [realSign]
                rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind,
                  OracleComp.liftM_run_StateT, bind_assoc]
                refine bind_congr (fun cωπ => ?_)
                rw [pure_bind]
                simp only [modifyGet, MonadState.modifyGet,
                  MonadStateOf.modifyGet, StateT.modifyGet, StateT.run]
                congr 1
                rcases s (.inr (msg, cωπ.1)) with _ | _ <;> simp
              -- Step 3: unfold the bad-flag wrappers and reduce to inner computations.
              -- `(_simImpl pk (.inr msg)).run (s, false) = (sigSimBad pk msg).run (s, false)`
              -- by `add_apply_inr`, and similarly for `_realImpl`.
              dsimp only [_simImpl, _realImpl, sigSimBad, realSignBad]
              simp only [QueryImpl.add_apply_inr]
              -- Apply `tvDist_map_le` to peel off the deterministic bad-flag map.
              refine le_trans (tvDist_map_le _ _ _) ?_
              -- Now reduce to the inner runs.
              rw [h_sigSim_run, h_realSign_run]
              -- Apply `tvDist_bind_right_le` to peel off the deterministic post-processing.
              refine le_trans (tvDist_bind_right_le _ _ _) ?_
              -- Goal: tvDist ((simTranscript pk).liftComp spec)
              --             ((σ.realTranscript pk sk).liftComp spec) ≤ ζ_zk
              -- Use `evalDist_liftComp` to drop the lift, then `tvDist_comm` and HVZK.
              have h_eq : tvDist ((simTranscript pk).liftComp spec :
                  OracleComp spec _)
                  ((σ.realTranscript pk sk : ProbComp _).liftComp spec) =
                  tvDist (simTranscript pk : ProbComp _)
                    (σ.realTranscript pk sk) := by
                unfold tvDist
                simp only [OracleComp.evalDist_liftComp]
              rw [h_eq, tvDist_comm]
              exact _hhvzk pk sk h_rel
        case h_step_eq_nS =>
          -- On non-sign queries (`t = .inl _`), both `_simImpl` and `_realImpl` dispatch to
          -- `baseSimBad`, so they are pointwise equal.
          intro t hSt p
          cases t with
          | inl t' => rfl
          | inr _ => exact (hSt trivial).elim
        case h_mono₁ =>
          -- Bad flag monotonicity in `_simImpl pk`: once `bad = true`, it stays `true`.
          -- `baseSimBad := baseSim.withBadFlag` threads `bad` unchanged, and
          -- `sigSimBad pk := (sigSim pk).withBadUpdate sigBadF` OR-updates `bad`.
          -- Both monotonicity facts follow from the generic `support_with*_run_snd_snd_*`
          -- lemmas above.
          intro t p hp z hz
          obtain ⟨cache, bad⟩ := p
          dsimp only at hp
          subst hp
          dsimp only [_simImpl, baseSimBad, sigSimBad] at hz
          cases t with
          | inl t' =>
              simp only [QueryImpl.add_apply_inl] at hz
              exact support_withBadFlag_run_snd_snd baseSim t' cache true hz
          | inr msg =>
              simp only [QueryImpl.add_apply_inr] at hz
              exact support_withBadUpdate_run_snd_snd_of_pre (sigSim pk) sigBadF msg cache hz
        case h_qb =>
          -- Project `signHashQueryBound (adv.main pk) qS qH` (a `(qS, qH)`-paired budget) onto
          -- the `qS` coordinate via `IsQueryBound.proj` with `proj := Prod.fst`. The sign queries
          -- (`.inr _`) decrement `qS`; non-sign queries keep `qS` unchanged.
          have h_full : OracleComp.IsQueryBound (adv.main pk) (qS, qH)
              (fun t b => match t, b with
                | .inl (.inl _), _ => True
                | .inl (.inr _), (_, qH') => 0 < qH'
                | .inr _, (qS', _) => 0 < qS')
              (fun t b => match t, b with
                | .inl (.inl _), b' => b'
                | .inl (.inr _), (qS', qH') => (qS', qH' - 1)
                | .inr _, (qS', qH') => (qS' - 1, qH')) := _hQ pk
          refine OracleComp.IsQueryBound.proj Prod.fst ?_ ?_ h_full
          · intro t ⟨qS', qH'⟩ h_can
            cases t with
            | inl t' =>
                cases t' with
                | inl _ => simp [S]
                | inr _ => simp [S]
            | inr _ => simpa [S] using h_can
          · intro t ⟨qS', qH'⟩ h_can
            cases t with
            | inl t' =>
                cases t' with
                | inl _ => simp [S]
                | inr _ => simp [S]
            | inr _ => simp [S]
      -- The augmented "direct" experiments running over `(cache × signed × bad)` state.
      -- These are the canonical objects in the freshness-preserving chain.
      let direct_real_exp : Stmt → Wit → OracleComp spec
          ((M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool) := fun pk sk =>
        (simulateQ (_realImplSigned pk sk) (adv.main pk)).run ((∅, []), false)
      let direct_sim_exp : Stmt → OracleComp spec
          ((M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool) := fun pk =>
        (simulateQ (_simImplSigned pk) (adv.main pk)).run ((∅, []), false)
      -- The "successful fresh forgery on cache hit" event predicate. Captures: the cache
      -- contains the forgery's hash point with some `ω` that makes `verify` succeed, AND
      -- the forgery's message was not signed (freshness).
      let event : Stmt →
          ((M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool) → Prop :=
        fun pk z =>
          (∃ ω, z.2.1.1 (.inr (z.1.1, z.1.2.1)) = some ω ∧
            σ.verify pk z.1.2.1 ω z.1.2.2 = true) ∧
          ¬ z.1.1 ∈ z.2.1.2
      -- The collision-bad flag predicate. Extracted here to avoid inline
      -- `fun z => z.2.2 = true` which interacts badly with the `Pr[… | …]` notation
      -- delimiter inside `calc` first-terms.
      let badPred : (M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool → Prop :=
        fun z => z.2.2 = true
      -- (A) `bridge_real_freshness`: bridge `adv.advantage` to the augmented `direct_real_exp`.
      --
      -- Two slacks are absorbed here:
      --   * `qS · (qS + qH) / |Chal|`: FS-vs-`realSign` swap bad event. The actual
      --     `FiatShamir.sign` queries the live RO at `(msg, c)` (cached if already present),
      --     while `realSignSigned'` samples a fresh challenge from `realTranscript pk sk`
      --     and programs `(msg, c) ↦ chSampled` on a cache miss. They are identical until
      --     a cache hit at `(msg, c)` during signing, with collision probability bounded by
      --     `(qS + qH) / |Chal|` per query (commitment marginal is uniform; live + programmed
      --     entries before this query total ≤ `qS + qH`).
      --   * `1 / |Chal|`: cache-miss verify slack. `unforgeableExp` queries the live RO when
      --     verifying the forgery, sampling a fresh ω on a cache miss; this matches the
      --     forger's response with probability `1/|Chal|` by special soundness / unique
      --     responses. The augmented event `event pk` only counts cache hits, so this slack
      --     is added explicitly.
      --
      -- The `signed` list in the augmented state mirrors the WriterT log used in
      -- `unforgeableExp`: each signing query prepends `msg`, so `¬msg ∈ signed` matches
      -- `¬log.wasQueried msg`.
      have bridge_real_freshness :
          adv.advantage (runtime M) ≤
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) +
              ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) +
              ((1 : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) := by
        sorry
      -- (B) `step_b_per_pksk_signed`: per-(pk, sk), the augmented-state event-level bound.
      --
      -- Derives from `step_b_per_pksk` (proven above on `(cache × Bool)` state) via the data
      -- processing inequality: the `signed`-list update is deterministic and identical on the
      -- `_simImplSigned` and `_realImplSigned` sides (both prepend `msg` on every signing
      -- query, and base oracles never touch `signed`), so the augmented joint TV equals the
      -- `(cache × Bool)`-state TV. Applying the standard "tvDist ⇒ probEvent absorption"
      -- with the deterministic post-processing through `event pk` yields the bound.
      have step_b_per_pksk_signed : ∀ (pk : Stmt) (sk : Wit), rel pk sk = true →
          Pr[event pk | direct_real_exp pk sk] ≤
            Pr[event pk | direct_sim_exp pk] +
              ENNReal.ofReal (qS * ζ_zk) +
              Pr[badPred | direct_sim_exp pk] := by
        sorry
      -- (B-finish) `pr_bad_le_signed`: per-pk, the simulator's bad event is bounded by
      -- `qS · (qS + qH) / |Chal|`.
      --
      -- Union bound on the `qS` programming events. Each `sigSimSigned pk msg` programming
      -- step hits a previously-cached point (live RO query or prior signing programming) with
      -- probability ≤ `(qS + qH) / |Chal|`. The per-event uniformity comes from the per-query
      -- HVZK simulator's challenge marginal (uniform over `Chal`); equivalently from the
      -- commitment marginal being uniform when chosen by `simTranscript pk`.
      have pr_bad_le_signed : ∀ (pk : Stmt),
          Pr[badPred | direct_sim_exp pk] ≤
            ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) := by
        sorry
      -- (C') `bridge_sim_fork_freshness`: bridge the (pk-summed) sim-side event probability
      -- to `Fork.advantage`. No additional slack needed (the `1/|Chal|` cache-miss verify
      -- slack is absorbed into the (A) bridge).
      --
      -- Key insight: a forgery `(msg, c, π)` with `¬msg ∈ signed` cannot have used a
      -- programmed `(msg, c)` cache entry, since `sigSimSigned pk` only programs at signed
      -- `msg`. So if `event pk z` holds (cache contains `(msg, c)` and verify succeeds),
      -- then `(msg, c)` was queried via the live RO (recorded in `Fork.runTrace`'s
      -- `queryLog`), exactly the condition for `forkPoint trace = some _`.
      have bridge_sim_fork_freshness :
          (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
            Pr[event pksk.1 | direct_sim_exp pksk.1]) ≤
            Fork.advantage σ hr M nmaAdv qH := by
        sorry
      -- Wire the four sub-claims into the final advantage bound.
      --
      -- Abbreviations used below:
      --   `S_real := ∑' (pk,sk), evalDist hr.gen (pk,sk) · Pr[event pk | direct_real_exp pk sk]`
      --   `S_sim  := ∑' (pk,sk), evalDist hr.gen (pk,sk) · Pr[event pk | direct_sim_exp pk]`
      --   `S_bad  := ∑' (pk,sk), evalDist hr.gen (pk,sk) · Pr[bad on direct_sim_exp pk]`
      --   `slackA := (qS · (qS+qH) : ℕ) / |Chal|`, `slackOne := 1 / |Chal|`
      --
      -- Chain:
      --   adv.advantage
      --     ≤ S_real + slackA + slackOne                           [bridge_real_freshness]
      --     ≤ (S_sim + ofReal(qS·ζ_zk) + S_bad) + slackA + slackOne [step_b_per_pksk_signed]
      --     ≤ (Fork.advantage + ofReal(qS·ζ_zk) + slackA) + slackA + slackOne
      --                                                            [bridge_sim_fork_freshness,
      --                                                             pr_bad_le_signed]
      --     = Fork.advantage + ofReal(qS·ζ_zk) + collisionSlack qS qH Chal
      --                       [arith: 2·slackA + slackOne = collisionSlack]
      --
      -- Step 2 uses `hr.gen_sound` on the support of `hr.gen` to supply `rel pk sk = true`
      -- to `step_b_per_pksk_signed`.
      -- Helper: `hr.gen` is a PMF, so its evalDist sums to 1.
      have h_keygen_sum_one : (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk) = 1 :=
        HasEvalPMF.tsum_probOutput_eq_one hr.gen
      -- (B) distributed over the sum: `S_real ≤ S_sim + ofReal(qS·ζ_zk) + S_bad`.
      -- The `ofReal(qS·ζ_zk)` factor pulls out via `h_keygen_sum_one`.
      have h_B_distributed :
          (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) ≤
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              Pr[event pksk.1 | direct_sim_exp pksk.1]) +
            ENNReal.ofReal (qS * ζ_zk) +
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              Pr[badPred | direct_sim_exp pksk.1]) := by
        have h_per_term : ∀ (pksk : Stmt × Wit),
            evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2] ≤
              evalDist hr.gen pksk *
                (Pr[event pksk.1 | direct_sim_exp pksk.1] +
                  ENNReal.ofReal (qS * ζ_zk) +
                  Pr[badPred | direct_sim_exp pksk.1]) := by
          intro pksk
          by_cases hmem : pksk ∈ support hr.gen
          · have hrel : rel pksk.1 pksk.2 = true := hr.gen_sound _ _ hmem
            exact mul_le_mul_left' (step_b_per_pksk_signed pksk.1 pksk.2 hrel) _
          · have h0 : evalDist hr.gen pksk = 0 :=
              probOutput_eq_zero_of_not_mem_support hmem
            simp [h0]
        have h_step1 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) ≤
              ∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                (Pr[event pksk.1 | direct_sim_exp pksk.1] +
                  ENNReal.ofReal (qS * ζ_zk) +
                  Pr[badPred | direct_sim_exp pksk.1]) :=
          ENNReal.tsum_le_tsum h_per_term
        have h_step2 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              (Pr[event pksk.1 | direct_sim_exp pksk.1] +
                ENNReal.ofReal (qS * ζ_zk) +
                Pr[badPred | direct_sim_exp pksk.1])) =
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_sim_exp pksk.1]) +
              (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                ENNReal.ofReal (qS * ζ_zk)) +
              (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[badPred | direct_sim_exp pksk.1]) := by
          rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
          refine tsum_congr (fun _ => ?_)
          rw [mul_add, mul_add]
        have h_step3 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              ENNReal.ofReal (qS * ζ_zk)) = ENNReal.ofReal (qS * ζ_zk) := by
          rw [ENNReal.tsum_mul_right, h_keygen_sum_one, one_mul]
        have h_target_eq :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              (Pr[event pksk.1 | direct_sim_exp pksk.1] +
                ENNReal.ofReal (qS * ζ_zk) +
                Pr[badPred | direct_sim_exp pksk.1])) =
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_sim_exp pksk.1]) +
              ENNReal.ofReal (qS * ζ_zk) +
              (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[badPred | direct_sim_exp pksk.1]) := by
          rw [h_step2, h_step3]
        exact h_step1.trans_eq h_target_eq
      -- (B-finish) distributed: `S_bad ≤ slackA` (since `hr.gen` is a PMF).
      have h_bad_sum :
          (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              Pr[badPred | direct_sim_exp pksk.1]) ≤
            ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) := by
        have h_per_term : ∀ (pksk : Stmt × Wit),
            evalDist hr.gen pksk * Pr[badPred | direct_sim_exp pksk.1] ≤
              evalDist hr.gen pksk *
                (((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal)) :=
          fun pksk => mul_le_mul_left' (pr_bad_le_signed pksk.1) _
        have h_step1 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[badPred | direct_sim_exp pksk.1]) ≤
              ∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                (((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal)) :=
          ENNReal.tsum_le_tsum h_per_term
        have h_step2 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              (((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal))) =
            ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) := by
          rw [ENNReal.tsum_mul_right, h_keygen_sum_one, one_mul]
        exact h_step1.trans h_step2.le
      -- Arithmetic: `2·slackA + slackOne = collisionSlack qS qH Chal`.
      have h_slack_eq :
          ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) +
          ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) +
          ((1 : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) =
          collisionSlack qS qH Chal := by
        unfold collisionSlack
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
        congr 1
        push_cast
        ring
      -- Chain the pieces together.
      calc adv.advantage (runtime M)
          _ ≤ (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) +
              ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) +
              ((1 : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) :=
            bridge_real_freshness
          _ ≤ ((∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                  Pr[event pksk.1 | direct_sim_exp pksk.1]) +
                ENNReal.ofReal (qS * ζ_zk) +
                (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                  Pr[badPred | direct_sim_exp pksk.1])) +
              ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) +
              ((1 : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) := by
            gcongr
          _ ≤ (Fork.advantage σ hr M nmaAdv qH +
                ENNReal.ofReal (qS * ζ_zk) +
                ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal)) +
              ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) +
              ((1 : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) := by
            -- `gcongr` decomposes the compound inequality and closes the two leaf goals
            -- `S_sim ≤ Fork.advantage` and `S_bad ≤ slackA` using
            -- `bridge_sim_fork_freshness` and `h_bad_sum` from context.
            gcongr
          _ = Fork.advantage σ hr M nmaAdv qH +
              ENNReal.ofReal (qS * ζ_zk) +
              (((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) +
                ((qS * (qS + qH) : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal) +
                ((1 : ℕ) : ENNReal) / (Fintype.card Chal : ENNReal)) := by
            simp only [add_assoc]
          _ = Fork.advantage σ hr M nmaAdv qH +
              ENNReal.ofReal (qS * ζ_zk) +
              collisionSlack qS qH Chal := by
            rw [h_slack_eq]
    exact advantage_bound
section evalDistBridge

variable [Fintype Chal] [Inhabited Chal] [SampleableType Chal]

/-- The `ofLift + uniformSampleImpl` simulation on `unifSpec + (Unit →ₒ Chal)` preserves
`evalDist`. Both oracle components sample uniformly from their range (the `unifSpec`
side via `liftM (query n) : ProbComp (Fin (n+1))`, the challenge side via `$ᵗ Chal`),
so the simulated computation has the same distribution as the source. -/
private lemma evalDist_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) :
    evalDist (simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    rcases t with n | u
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        id_map, evalDist_bind, ih]
      apply bind_congr
      simp
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, QueryImpl.add_apply_inr, uniformSampleImpl,
        id_map, evalDist_bind, ih]
      have heq : (evalDist ($ᵗ ((ofFn fun _ : Unit => Chal).Range u)) :
            SPMF ((ofFn fun _ : Unit => Chal).Range u)) =
          (evalDist (liftM (query (Sum.inr u)) :
            OracleComp (unifSpec + (Unit →ₒ Chal)) _) :
            SPMF ((unifSpec + (Unit →ₒ Chal)).Range (Sum.inr u))) := by
        rw [evalDist_uniformSample, evalDist_query]; rfl
      exact heq ▸ rfl

/-- Corollary: `probEvent` is preserved by the `ofLift + uniformSampleImpl` simulation. -/
private lemma probEvent_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) (p : α → Prop) :
    Pr[ p | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa] = Pr[ p | oa] := by
  simp only [probEvent_eq_tsum_indicator]
  refine tsum_congr fun x => ?_
  unfold Set.indicator
  split_ifs with hpx
  · exact congrFun (congrArg DFunLike.coe (evalDist_simulateQ_unifChalImpl oa)) x
  · rfl

/-- Corollary: `probOutput` is preserved by the `ofLift + uniformSampleImpl` simulation. -/
private lemma probOutput_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) (x : α) :
    Pr[= x | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ_unifChalImpl oa)) x

end evalDistBridge
section jensenIntegration

/-- **Keygen-indexed Cauchy-Schwarz / Jensen step for the forking lemma.**

Given a per-element bound `acc x · (acc x / q - hinv) ≤ B x`, integrating over a
probabilistic key-generator `gen : ProbComp X` yields the "lifted" bound:

  `μ · (μ / q - hinv) ≤ 𝔼[B]`

where `μ = 𝔼[acc] = ∑' x, Pr[= x | gen] · acc x`.

The proof goes through the convexity identity `μ² ≤ 𝔼[acc²]` (Cauchy-Schwarz on the
probability distribution `Pr[= · | gen]`), together with `ENNReal.mul_sub` to handle the
truncated subtraction. -/
private lemma jensen_keygen_forking_bound
    {X : Type} (gen : ProbComp X)
    (acc B : X → ENNReal) (q hinv : ENNReal)
    (hinv_ne_top : hinv ≠ ⊤)
    (hacc_le : ∀ x, acc x ≤ 1)
    (hper : ∀ x, acc x * (acc x / q - hinv) ≤ B x) :
    (∑' x, Pr[= x | gen] * acc x) *
        ((∑' x, Pr[= x | gen] * acc x) / q - hinv) ≤
      ∑' x, Pr[= x | gen] * B x := by
  classical
  set w : X → ENNReal := fun x => Pr[= x | gen] with hw_def
  set μ : ENNReal := ∑' x, w x * acc x with hμ_def
  have hw_tsum_le_one : ∑' x, w x ≤ 1 := tsum_probOutput_le_one
  have hμ_le_one : μ ≤ 1 := by
    calc μ = ∑' x, w x * acc x := rfl
      _ ≤ ∑' x, w x * 1 := by gcongr with x; exact hacc_le x
      _ = ∑' x, w x := by simp
      _ ≤ 1 := hw_tsum_le_one
  have hμ_ne_top : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hμ_le_one
  -- The integrand `w x * acc x * hinv`, with total sum `μ * hinv`.
  have hμ_hinv_ne_top : μ * hinv ≠ ⊤ := ENNReal.mul_ne_top hμ_ne_top hinv_ne_top
  -- Cauchy-Schwarz: `μ² ≤ ∑' w * acc²`.
  have hCS : μ ^ 2 ≤ ∑' x, w x * acc x ^ 2 :=
    ENNReal.sq_tsum_le_tsum_sq w acc hw_tsum_le_one
  -- Split off the key reverse-Jensen inequality as an intermediate calc.
  -- Integrate the per-element bound.
  calc μ * (μ / q - hinv)
      = μ * (μ / q) - μ * hinv :=
        ENNReal.mul_sub (fun _ _ => hμ_ne_top)
    _ = μ ^ 2 / q - μ * hinv := by
        rw [sq, mul_div_assoc]
    _ ≤ (∑' x, w x * acc x ^ 2) / q - μ * hinv := by
        gcongr
    _ = (∑' x, w x * acc x ^ 2 / q) - ∑' x, w x * acc x * hinv := by
        congr 1
        · simp only [div_eq_mul_inv]
          rw [ENNReal.tsum_mul_right]
        · rw [hμ_def, ENNReal.tsum_mul_right]
    _ ≤ ∑' x, (w x * acc x ^ 2 / q - w x * acc x * hinv) := by
        -- Reverse-Jensen: `∑' f - ∑' g ≤ ∑' (f - g)` in ENNReal when `∑' g ≠ ⊤`.
        set f : X → ENNReal := fun x => w x * acc x ^ 2 / q with hf_def
        set g : X → ENNReal := fun x => w x * acc x * hinv with hg_def
        have hg_sum_ne_top : ∑' x, g x ≠ ⊤ := by
          change ∑' x, w x * acc x * hinv ≠ ⊤
          rw [ENNReal.tsum_mul_right]; exact hμ_hinv_ne_top
        have hfg : ∑' x, f x ≤ ∑' x, (f x - g x) + ∑' x, g x := by
          calc ∑' x, f x ≤ ∑' x, ((f x - g x) + g x) := by
                exact ENNReal.tsum_le_tsum fun x => le_tsub_add
            _ = ∑' x, (f x - g x) + ∑' x, g x := ENNReal.tsum_add
        exact tsub_le_iff_right.2 hfg
    _ = ∑' x, w x * (acc x ^ 2 / q - acc x * hinv) := by
        refine tsum_congr fun x => ?_
        have hwx_ne_top : w x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
        rw [ENNReal.mul_sub (fun _ _ => hwx_ne_top), mul_div_assoc, mul_assoc]
    _ = ∑' x, w x * (acc x * (acc x / q - hinv)) := by
        refine tsum_congr fun x => ?_
        have hax_ne_top : acc x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top (hacc_le x)
        congr 1
        rw [ENNReal.mul_sub (fun _ _ => hax_ne_top), sq, mul_div_assoc]
    _ ≤ ∑' x, w x * B x := by
        gcongr with x
        exact hper x

end jensenIntegration

section eufNmaHelpers

variable [DecidableEq M] [DecidableEq Commit] [DecidableEq Chal]

/-- Replay-fork query budget for the NMA reduction: forward the `.inl unifSpec` component
live (budget `0`) and rewind only the counted challenge oracle on the `.inr` side, capped
at `qH` queries. -/
private def nmaForkBudget (qH : ℕ) : ℕ ⊕ Unit → ℕ
  | .inl _ => 0
  | .inr () => qH

/-- Per-run invariant for the NMA replay fork. If `Fork.forkPoint qH` selects index `s`,
the cached RO value at `x.target`, the outer log's `s`-th counted-oracle response, and the
challenge under which `x.forgery` verifies all coincide.

Holding this for both fork runs lets `Fork.replayForkingBound` deliver two accepting
transcripts with the same commitment and distinct challenges, precisely what special
soundness needs. -/
private def forkSupportInvariant
    (qH : ℕ) (pk : Stmt)
    (x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (log : QueryLog (unifSpec + (Unit →ₒ Chal))) : Prop :=
  ∀ s : Fin (qH + 1),
    Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH x =
        some s →
    ∃ ω : Chal,
      QueryLog.getQueryValue? log (Sum.inr ()) (↑s : ℕ) = some ω ∧
      x.roCache x.target = some ω ∧
      σ.verify pk x.target.2 ω x.forgery.2.2 = true

variable [SampleableType Chal] [Fintype Chal] [Inhabited Chal]

/-- Witness-extraction computation over `unifSpec + (Unit →ₒ Chal)` used by the NMA
reduction. Replay-forks the wrapped adversary at the counted challenge oracle, matches
the two forgeries against the sigma-protocol extractor when the commitments agree and
the cached challenges differ, and falls back to a uniform witness otherwise. -/
private noncomputable def eufNmaForkExtract
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt) :
    OracleComp (unifSpec + (Unit →ₒ Chal)) Wit := do
  let result ← forkReplay (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH)
  match result with
  | none => liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
  | some (x₁, x₂) =>
    let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
    let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
    if _hc : c₁ = c₂ then
      match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
      | some ω₁, some ω₂ =>
          if _hω : ω₁ ≠ ω₂ then
            liftComp (σ.extract ω₁ s₁ ω₂ s₂) (unifSpec + (Unit →ₒ Chal))
          else
            liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
      | _, _ => liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))
    else
      liftComp ($ᵗ Wit) (unifSpec + (Unit →ₒ Chal))

/-- NMA reduction for `euf_nma_bound`: simulate the challenge oracle of
`eufNmaForkExtract` down to `ProbComp`. -/
private noncomputable def eufNmaReduction
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : Stmt → ProbComp Wit := fun pk =>
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (Unit →ₒ Chal)))) (eufNmaForkExtract σ hr M nmaAdv qH pk)

omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] [Fintype Chal] in
/-- **Support invariant of the replay-fork first run.**

Every `(x, log)` in the support of `replayFirstRun (Fork.runTrace σ hr M nmaAdv pk)`
satisfies the per-run invariant `forkSupportInvariant`: at a valid fork point, the cached
RO challenge matches the outer log entry and the forgery verifies. -/
private theorem forkSupportInvariant_of_mem_replayFirstRun
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt)
    {x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {log : QueryLog (unifSpec + (Unit →ₒ Chal))}
    (h : (x, log) ∈ support (replayFirstRun (Fork.runTrace σ hr M nmaAdv pk))) :
    forkSupportInvariant σ M qH pk x log := by
  classical
  intro s hs
  have htarget : x.queryLog[(↑s : ℕ)]? = some x.target :=
    Fork.forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) hs
  have hverified : x.verified = true :=
    Fork.forkPoint_some_imp_verified (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) hs
  have hslt : (↑s : ℕ) < x.queryLog.length := by
    by_contra hge
    push Not at hge
    have hnone : x.queryLog[(↑s : ℕ)]? = none := List.getElem?_eq_none hge
    rw [hnone] at htarget
    exact (Option.some_ne_none x.target htarget.symm).elim
  obtain ⟨ω, hcache_idx, hlog⟩ :=
    Fork.runTrace_cache_outer_lockstep σ hr M nmaAdv pk h (↑s : ℕ) hslt
  have htgt_eq : x.queryLog[(↑s : ℕ)]'hslt = x.target := by
    have h1 : x.queryLog[(↑s : ℕ)]? = some (x.queryLog[(↑s : ℕ)]'hslt) :=
      List.getElem?_eq_getElem hslt
    rw [h1] at htarget
    exact Option.some.inj htarget
  rw [htgt_eq] at hcache_idx
  obtain ⟨ω', hcache', hverify⟩ :=
    Fork.runTrace_verified_imp_verify σ hr M nmaAdv pk h hverified
  have hωeq : ω = ω' := by
    rw [hcache_idx] at hcache'
    exact Option.some.inj hcache'
  refine ⟨ω, hlog, hcache_idx, ?_⟩
  rw [hωeq]
  exact hverify

omit [SampleableType Stmt] [SampleableType Wit] [Fintype Chal] [Inhabited Chal] in
/-- **Target equality across two successful fork runs** sharing the same fork index.

If both runs of `forkReplay (Fork.runTrace σ hr M nmaAdv pk)` select fork point `s`,
their forgery targets agree. The two runs share all counted-oracle responses strictly
before the fork index, and the replay-determinism lemma `Fork.runTrace_queryLog_take_eq`
then forces their internal `queryLog`s to coincide on the first `s + 1` entries, so
`forkPoint_getElem?_eq_some_target` pins both targets to the same value. -/
private theorem target_eq_of_mem_forkReplay
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt)
    (x₁ x₂ : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (s : Fin (qH + 1))
    (hsup : some (x₁, x₂) ∈ support (forkReplay (Fork.runTrace σ hr M nmaAdv pk)
      (nmaForkBudget qH) (Sum.inr ())
      (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH)))
    (h₁ : Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH x₁ = some s)
    (h₂ : Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH x₂ = some s) :
    x₁.target = x₂.target := by
  classical
  -- Unpack the replay-fork success structure.
  obtain ⟨log₁, log₂, s', hx₁, hx₂, hcf₁, hcf₂, _hneq, replacement, st, hz, hlog₂, _hmismatch,
    hfork, _hprefix⟩ := forkReplay_success_log_props
      (main := Fork.runTrace σ hr M nmaAdv pk)
      (qb := nmaForkBudget qH) (i := Sum.inr ())
      (cf := Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH)
      hsup
  -- `s = s'` via `hcf₁` and `h₁`.
  have hs_eq : s' = s := by rw [hcf₁] at h₁; exact Option.some.inj h₁
  cases hs_eq
  -- Abbreviations for readability.
  set main : OracleComp (Fork.wrappedSpec Chal)
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :=
    Fork.runTrace σ hr M nmaAdv pk
  -- Immutable replay parameters.
  have htrace_eq : st.trace = log₁ :=
    replayRunWithTraceValue_trace_eq
      (main := main) (i := Sum.inr ())
      (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz
  have hforkq : st.forkQuery = (↑s : ℕ) :=
    replayRunWithTraceValue_forkQuery_eq
      (main := main) (i := Sum.inr ())
      (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz
  -- Key facts about `st.cursor`.
  obtain ⟨hcur_pos, htrace_in, hobs_in⟩ :=
    replayRunWithTraceValue_forkConsumed_imp_last_input
      (main := main) (i := Sum.inr ())
      (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz hfork
  change 0 < st.cursor at hcur_pos
  change QueryLog.inputAt? st.trace (st.cursor - 1) = some (Sum.inr ()) at htrace_in
  change QueryLog.inputAt? st.observed (st.cursor - 1) = some (Sum.inr ()) at hobs_in
  rw [htrace_eq] at htrace_in
  rw [hlog₂] at hobs_in
  have hInv := replayRunWithTraceValue_preservesPrefixInvariant
    (main := main) (i := Sum.inr ())
    (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz
  have hcur_trace : st.cursor ≤ log₁.length := by rw [← htrace_eq]; exact hInv.1
  have hcur_obs : st.cursor ≤ log₂.length := by rw [← hlog₂]; exact hInv.2.1
  have hc1_lt_t : st.cursor - 1 < log₁.length := by omega
  have hc1_lt_o : st.cursor - 1 < log₂.length := by omega
  -- Count identity: `(log₂.take (c-1)).getQ (· = Sum.inr ()).length = s`.
  have hcount_obs :=
    replayRunWithTraceValue_forkConsumed_imp_prefix_count
      (main := main) (i := Sum.inr ())
      (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz hfork
  change (QueryLog.getQ (st.observed.take (st.cursor - 1))
    (· = Sum.inr ())).length = st.forkQuery at hcount_obs
  rw [hforkq, hlog₂] at hcount_obs
  -- Value-level prefix equality `log₁.take (c-1) = log₂.take (c-1)`.
  have htake_len₁ : (log₁.take (st.cursor - 1)).length = st.cursor - 1 :=
    List.length_take_of_le (by omega)
  have htake_len₂ : (log₂.take (st.cursor - 1)).length = st.cursor - 1 :=
    List.length_take_of_le (by omega)
  have hprefix_val : log₁.take (st.cursor - 1) = log₂.take (st.cursor - 1) := by
    apply List.ext_getElem?
    intro n
    by_cases hn : n < st.cursor - 1
    · have hgetEq : st.observed[n]? = st.trace[n]? :=
        replayRunWithTraceValue_prefix_getElem?_eq
          (main := main) (i := Sum.inr ())
          (trace := log₁) (forkQuery := (↑s : ℕ)) (replacement := replacement) hz
          (n := n) (by rw [if_pos hfork]; exact hn)
      rw [hlog₂, htrace_eq] at hgetEq
      have hn_t : n < log₁.length := by omega
      have hn_o : n < log₂.length := by omega
      have hlen₁ : n < (log₁.take (st.cursor - 1)).length := by rw [htake_len₁]; exact hn
      have hlen₂ : n < (log₂.take (st.cursor - 1)).length := by rw [htake_len₂]; exact hn
      rw [List.getElem?_eq_getElem hlen₁, List.getElem?_eq_getElem hlen₂,
        List.getElem_take, List.getElem_take,
        ← List.getElem?_eq_getElem hn_t, ← List.getElem?_eq_getElem hn_o]
      exact hgetEq.symm
    · push Not at hn
      have hlen₁ : (log₁.take (st.cursor - 1)).length ≤ n := by rw [htake_len₁]; exact hn
      have hlen₂ : (log₂.take (st.cursor - 1)).length ≤ n := by rw [htake_len₂]; exact hn
      rw [List.getElem?_eq_none hlen₁, List.getElem?_eq_none hlen₂]
  -- Extract the distinguished entries at position `c-1` as `⟨Sum.inr (), v_i⟩`.
  have hget₁ : log₁[st.cursor - 1]? = some (log₁[st.cursor - 1]'hc1_lt_t) :=
    List.getElem?_eq_getElem hc1_lt_t
  have hget₂ : log₂[st.cursor - 1]? = some (log₂[st.cursor - 1]'hc1_lt_o) :=
    List.getElem?_eq_getElem hc1_lt_o
  have hfst₁ : (log₁[st.cursor - 1]'hc1_lt_t).1 = Sum.inr () := by
    have := htrace_in
    unfold QueryLog.inputAt? at this
    rw [hget₁] at this
    simpa using this
  have hfst₂ : (log₂[st.cursor - 1]'hc1_lt_o).1 = Sum.inr () := by
    have := hobs_in
    unfold QueryLog.inputAt? at this
    rw [hget₂] at this
    simpa using this
  -- Destructure `log_i[c-1]` as `⟨Sum.inr (), v_i⟩` for some `v_i : Chal`.
  obtain ⟨v₁, hv₁⟩ : ∃ v : Chal, log₁[st.cursor - 1]'hc1_lt_t =
      (⟨Sum.inr (), v⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) := by
    rcases hsig : log₁[st.cursor - 1]'hc1_lt_t with ⟨i, v⟩
    rw [hsig] at hfst₁
    cases i with
    | inl n => cases hfst₁
    | inr u => cases u; exact ⟨v, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : Chal, log₂[st.cursor - 1]'hc1_lt_o =
      (⟨Sum.inr (), v⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) := by
    rcases hsig : log₂[st.cursor - 1]'hc1_lt_o with ⟨i, v⟩
    rw [hsig] at hfst₂
    cases i with
    | inl n => cases hfst₂
    | inr u => cases u; exact ⟨v, rfl⟩
  -- `c - 1 + 1 = c` using `0 < c`.
  have hcsub : st.cursor - 1 + 1 = st.cursor := by omega
  -- Decompose `log_i = log_i.take (c-1) ++ ⟨Sum.inr (), v_i⟩ :: log_i.drop c`.
  have hdec₁ : log₁ = log₁.take (st.cursor - 1) ++
      ((⟨Sum.inr (), v₁⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) ::
        log₁.drop st.cursor) := by
    have hdrop :
        log₁.drop (st.cursor - 1) =
          (log₁[st.cursor - 1]'hc1_lt_t) :: log₁.drop (st.cursor - 1 + 1) :=
      List.drop_eq_getElem_cons hc1_lt_t
    rw [hcsub] at hdrop
    rw [hv₁] at hdrop
    calc log₁ = log₁.take (st.cursor - 1) ++ log₁.drop (st.cursor - 1) :=
        (List.take_append_drop _ _).symm
      _ = log₁.take (st.cursor - 1) ++
          ((⟨Sum.inr (), v₁⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) ::
            log₁.drop st.cursor) := by rw [hdrop]
  have hdec₂ : log₂ = log₁.take (st.cursor - 1) ++
      ((⟨Sum.inr (), v₂⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) ::
        log₂.drop st.cursor) := by
    have hdrop :
        log₂.drop (st.cursor - 1) =
          (log₂[st.cursor - 1]'hc1_lt_o) :: log₂.drop (st.cursor - 1 + 1) :=
      List.drop_eq_getElem_cons hc1_lt_o
    rw [hcsub] at hdrop
    rw [hv₂] at hdrop
    calc log₂ = log₂.take (st.cursor - 1) ++ log₂.drop (st.cursor - 1) :=
        (List.take_append_drop _ _).symm
      _ = log₁.take (st.cursor - 1) ++ log₂.drop (st.cursor - 1) := by rw [hprefix_val]
      _ = log₁.take (st.cursor - 1) ++
          ((⟨Sum.inr (), v₂⟩ : (i : ℕ ⊕ Unit) × (Fork.wrappedSpec Chal).Range i) ::
            log₂.drop st.cursor) := by rw [hdrop]
  -- Count: the common prefix `p = log₁.take (c-1)` has exactly `s` `Sum.inr ()` entries.
  have hpref_count :
      QueryLog.countQ (log₁.take (st.cursor - 1)) (· = Sum.inr ()) = (↑s : ℕ) := by
    unfold QueryLog.countQ
    rw [hprefix_val]
    exact hcount_obs
  -- Apply `runTrace_queryLog_take_eq` to get `x₁.queryLog.take (s+1) = x₂.queryLog.take (s+1)`.
  have htakeEq :
      x₁.queryLog.take (QueryLog.countQ (log₁.take (st.cursor - 1)) (· = Sum.inr ()) + 1) =
        x₂.queryLog.take
          (QueryLog.countQ (log₁.take (st.cursor - 1)) (· = Sum.inr ()) + 1) :=
    Fork.runTrace_queryLog_take_eq σ hr M (Resp := Resp) nmaAdv pk
      (x₁ := x₁) (x₂ := x₂) (outerLog₁ := log₁) (outerLog₂ := log₂) hx₁ hx₂
      (p := log₁.take (st.cursor - 1)) (v₁ := v₁) (v₂ := v₂)
      (rest₁ := log₁.drop st.cursor) (rest₂ := log₂.drop st.cursor) hdec₁ hdec₂
  rw [hpref_count] at htakeEq
  -- Both sides yield `x_i.queryLog[s]? = some x_i.target`; thus targets agree.
  have htgt₁ : x₁.queryLog[(↑s : ℕ)]? = some x₁.target :=
    Fork.forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) h₁
  have htgt₂ : x₂.queryLog[(↑s : ℕ)]? = some x₂.target :=
    Fork.forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) h₂
  have hs_lt₁ : (↑s : ℕ) < x₁.queryLog.length := by
    by_contra hge
    push Not at hge
    rw [List.getElem?_eq_none hge] at htgt₁
    exact (Option.some_ne_none _ htgt₁.symm).elim
  have hs_lt₂ : (↑s : ℕ) < x₂.queryLog.length := by
    by_contra hge
    push Not at hge
    rw [List.getElem?_eq_none hge] at htgt₂
    exact (Option.some_ne_none _ htgt₂.symm).elim
  have hgetElem_take :
      ∀ l : List (M × Commit),
        (l.take ((↑s : ℕ) + 1))[(↑s : ℕ)]? = l[(↑s : ℕ)]? := fun l => by
    rw [List.getElem?_take]
    split_ifs with h; · rfl
    · exact absurd (Nat.lt_succ_self _) h
  have : some x₁.target = some x₂.target := by
    rw [← htgt₁, ← htgt₂, ← hgetElem_take x₁.queryLog, ← hgetElem_take x₂.queryLog, htakeEq]
  exact Option.some.inj this

omit [SampleableType Stmt] in
/-- **Per-pk extraction bound.** Given the structural forking event on `pk` (two fork
runs selecting the same index, with distinct counted-oracle responses, both satisfying
`forkSupportInvariant`), the NMA reduction recovers a valid witness with probability at
least that of the fork event under `forkReplay`. Composes `target_eq_of_mem_forkReplay`
with special soundness. -/
private theorem perPk_extraction_bound
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ)
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    (pk : Stmt) :
    Pr[ fun r : Option
        (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
          Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
        ∃ (x₁ x₂ :
            Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
          (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
          r = some (x₁, x₂) ∧
          Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
            (Chal := Chal) qH x₁ = some s ∧
          Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
            (Chal := Chal) qH x₂ = some s ∧
          QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
            QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
          forkSupportInvariant σ M qH pk x₁ log₁ ∧
          forkSupportInvariant σ M qH pk x₂ log₂
        | forkReplay (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
          (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
            (Chal := Chal) qH)] ≤
      Pr[ fun w : Wit => rel pk w = true | eufNmaReduction σ hr M nmaAdv qH pk] := by
  classical
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  let wrappedMain : OracleComp (unifSpec + chalSpec)
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :=
    Fork.runTrace σ hr M nmaAdv pk
  let cf : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) →
      Option (Fin (qH + 1)) :=
    Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
  let qb : ℕ ⊕ Unit → ℕ := nmaForkBudget qH
  -- Strip the simulator: `eufNmaReduction pk = simulateQ _ (eufNmaForkExtract pk)`.
  rw [show Pr[fun w : Wit => rel pk w = true | eufNmaReduction σ hr M nmaAdv qH pk] =
        Pr[fun w : Wit => rel pk w = true | eufNmaForkExtract σ hr M nmaAdv qH pk] by
      unfold eufNmaReduction
      exact probEvent_simulateQ_unifChalImpl _ _]
  -- Expand `eufNmaForkExtract pk` as a bind over `forkReplay` followed by a
  -- case-matching extractor `branchFn`.
  set branchFn : Option
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
        Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) →
      OracleComp (unifSpec + chalSpec) Wit :=
    fun result => match result with
    | none => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
    | some (x₁, x₂) =>
      let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
      let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
      if _hc : c₁ = c₂ then
        match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
        | some ω₁, some ω₂ =>
            if _hω : ω₁ ≠ ω₂ then
              liftComp (σ.extract ω₁ s₁ ω₂ s₂) (unifSpec + chalSpec)
            else
              liftComp ($ᵗ Wit) (unifSpec + chalSpec)
        | _, _ => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      else
        liftComp ($ᵗ Wit) (unifSpec + chalSpec)
    with hbranchFn_def
  have hforkExtract_eq :
      eufNmaForkExtract σ hr M nmaAdv qH pk =
        forkReplay wrappedMain qb (Sum.inr ()) cf >>= branchFn := by
    unfold eufNmaForkExtract
    rfl
  rw [hforkExtract_eq, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun r => ?_
  -- Pointwise comparison:
  -- `(if E r then Pr[= r | mx] else 0) ≤ Pr[= r | mx] * Pr[rel | branchFn r]`.
  by_cases hE :
      ∃ (x₁ x₂ : Fork.Trace
          (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
        (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
        r = some (x₁, x₂) ∧
        cf x₁ = some s ∧
        cf x₂ = some s ∧
        QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
          QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
        forkSupportInvariant σ M qH pk x₁ log₁ ∧
        forkSupportInvariant σ M qH pk x₂ log₂
  swap
  · rw [if_neg hE]; exact zero_le _
  rw [if_pos hE]
  by_cases hsupp : r ∈ support (forkReplay wrappedMain qb (Sum.inr ()) cf)
  swap
  · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]
  obtain ⟨x₁, x₂, s, log₁, log₂, hreq, hcf₁, hcf₂, hneq, hP₁, hP₂⟩ := hE
  obtain ⟨ω₁, hlog₁, hcache₁, hverify₁⟩ := hP₁ s hcf₁
  obtain ⟨ω₂, hlog₂, hcache₂, hverify₂⟩ := hP₂ s hcf₂
  -- The two cached challenges differ because the outer-log entries do.
  have hω_ne : ω₁ ≠ ω₂ := by
    intro heq
    apply hneq
    rw [hlog₁, hlog₂, heq]
  -- Targets coincide by the shared-prefix property of `forkReplay`.
  have htarget : x₁.target = x₂.target :=
    target_eq_of_mem_forkReplay σ hr M nmaAdv qH pk x₁ x₂ s (hreq ▸ hsupp) hcf₁ hcf₂
  set m₁ := x₁.forgery.1
  set c₁ := x₁.forgery.2.1
  set sr₁ := x₁.forgery.2.2
  set m₂ := x₂.forgery.1
  set c₂ := x₂.forgery.2.1
  set sr₂ := x₂.forgery.2.2
  have htgt₁ : x₁.target = (m₁, c₁) := rfl
  have htgt₂ : x₂.target = (m₂, c₂) := rfl
  have htarget_eq : (m₁, c₁) = (m₂, c₂) := by rw [← htgt₁, ← htgt₂]; exact htarget
  have hc_eq : c₁ = c₂ := (Prod.mk.inj htarget_eq).2
  have hcache₁' : x₁.roCache (m₁, c₁) = some ω₁ := hcache₁
  have hcache₂' : x₂.roCache (m₂, c₂) = some ω₂ := hcache₂
  have hverify₁' : σ.verify pk c₁ ω₁ sr₁ = true := hverify₁
  have hverify₂' : σ.verify pk c₂ ω₂ sr₂ = true := hverify₂
  have hverify₂'' : σ.verify pk c₁ ω₂ sr₂ = true := by rw [hc_eq]; exact hverify₂'
  -- Evaluate `branchFn r` to the extractor call.
  have hbranch :
      branchFn r = liftComp (σ.extract ω₁ sr₁ ω₂ sr₂) (unifSpec + chalSpec) := by
    rw [hbranchFn_def, hreq]
    change (if _hc : c₁ = c₂ then
      match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
      | some ω₁, some ω₂ =>
          if _hω : ω₁ ≠ ω₂ then
            liftComp (σ.extract ω₁ sr₁ ω₂ sr₂) (unifSpec + chalSpec)
          else
            liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      | _, _ => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
    else
      liftComp ($ᵗ Wit) (unifSpec + chalSpec)) = _
    rw [dif_pos hc_eq, hcache₁', hcache₂']
    simp only [dif_pos hω_ne]
  rw [hbranch, probEvent_liftComp]
  -- Probability on the extracted branch is 1 via special soundness + no-failure.
  have hrel_one :
      Pr[fun w : Wit => rel pk w = true | σ.extract ω₁ sr₁ ω₂ sr₂] = 1 := by
    rw [probEvent_eq_one_iff]
    refine ⟨hss_nf ω₁ sr₁ ω₂ sr₂, fun w hw => ?_⟩
    exact SigmaProtocol.extract_sound_of_speciallySoundAt σ (hss pk)
      hω_ne hverify₁' hverify₂'' hw
  rw [hrel_one, mul_one]

end eufNmaHelpers

omit [SampleableType Stmt] in
/-- **NMA-to-extraction via the forking lemma and special soundness.**

For any managed-RO NMA adversary `B` making at most `qH` random-oracle queries, there
exists a witness-extraction reduction such that:

  `Adv^{fork-NMA}_{qH}(B) · (Adv^{fork-NMA}_{qH}(B) / (qH + 1) - 1/|Ω|)
      ≤ Pr[extraction succeeds]`

Runs `B.main pk` twice with shared randomness up to a randomly chosen fork point, then
re-samples the oracle answer. Programmed cache entries are part of `B`'s deterministic
computation given the seed, so they are identical across both fork runs. The reduction
extracts only from fork outputs whose two forged transcripts share a commitment and whose
cached challenges are distinct. The remaining proof obligation is to show that successful
forks satisfy exactly those compatibility checks, after which special soundness applies.

Here `Adv^{fork-NMA}_{qH}(B)` is `Fork.advantage`: it counts exactly the
managed-RO executions whose forgery already verifies from challenge values present in the
adversary's managed cache or in the live hash-query log recorded by
`Fork.runTrace`. This is the precise success event that the forking lemma can
rewind.

This matches Firsov-Janku's `schnorr_koa_secure` at
[fsec/proof/Schnorr.ec:448](../../../fsec/proof/Schnorr.ec), which applies `forking_lemma_ro`
with the single-run postcondition `verify` plus the extractor correctness lemma
`extractor_corr` at [fsec/proof/Schnorr.ec:87](../../../fsec/proof/Schnorr.ec). Our version
uses `Fork.replayForkingBound` for the RO-level packaging and `_hss` for special
soundness, with `σ.extract` playing the role of EC's `extractor`.

The Jensen/Cauchy-Schwarz step that powers `Fork.replayForkingBound` rests on the two
prefix-faithfulness identities
(`evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt` and
`tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt` in ReplayFork.lean). -/
theorem euf_nma_bound
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ)
    (_hQ : ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := nmaAdv.main pk) qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      (Fork.advantage σ hr M nmaAdv qH *
          (Fork.advantage σ hr M nmaAdv qH / (qH + 1 : ENNReal) -
            challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  classical
  refine ⟨eufNmaReduction σ hr M nmaAdv qH, ?_⟩
  set acc : Stmt → ENNReal := fun pk =>
    Pr[ fun x => (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH x).isSome | Fork.runTrace σ hr M nmaAdv pk] with hacc_def
  -- ── Step (a): rewrite `Fork.advantage` as the keygen-marginalized expectation of the
  -- per-pk fork-point success probability.
  have hAdv_eq_tsum :
      Fork.advantage σ hr M nmaAdv qH =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] * acc pkw.1 := by
    change Pr[= true | Fork.exp σ hr M nmaAdv qH] = _
    unfold Fork.exp
    rw [← probEvent_eq_eq_probOutput, probEvent_simulateQ_unifChalImpl,
      probEvent_bind_eq_tsum]
    refine tsum_congr fun pkw => ?_
    rw [probOutput_liftComp]
    congr 1
    rcases pkw with ⟨pk, sk⟩
    simp only [bind_pure_comp, probEvent_map, Function.comp_def, acc]
  -- ── Step (b): rewrite `Pr[= true | hardRelationExp]` as a keygen-marginalized sum of
  -- per-pk relation-recovery probabilities.
  have hRHS_eq_tsum :
      Pr[= true | hardRelationExp hr (eufNmaReduction σ hr M nmaAdv qH)] =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] *
          Pr[ fun w : Wit => rel pkw.1 w = true |
            eufNmaReduction σ hr M nmaAdv qH pkw.1] := by
    unfold hardRelationExp
    rw [← probEvent_eq_eq_probOutput]
    simp only [bind_pure_comp, probEvent_bind_eq_tsum]
    refine tsum_congr fun pkw => ?_
    rcases pkw with ⟨pk, sk⟩
    congr 1
    rw [probEvent_map]
    rfl
  -- ── Step (c): per-pk forking bound via `Fork.replayForkingBound` applied with the
  -- strengthened support invariant `forkSupportInvariant`.
  have hPerPk : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun r : Option
            (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
            ∃ (x₁ x₂ :
                Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
              (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
              r = some (x₁, x₂) ∧
              Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                (Chal := Chal) qH x₁ = some s ∧
              Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                (Chal := Chal) qH x₂ = some s ∧
              QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
                QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
              forkSupportInvariant σ M qH pk x₁ log₁ ∧
              forkSupportInvariant σ M qH pk x₂ log₂
            | forkReplay (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
              (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                (Chal := Chal) qH)] := fun pk =>
    Fork.replayForkingBound (σ := σ) (hr := hr) (M := M) nmaAdv qH pk
      (P_out := forkSupportInvariant σ M qH pk)
      (hP := fun h => forkSupportInvariant_of_mem_replayFirstRun σ hr M nmaAdv qH pk h)
      (hreach := Fork.runTrace_forkPoint_CfReachable
        (σ := σ) (hr := hr) (M := M) nmaAdv qH pk)
  -- ── Step (d): compose (c) with `perPk_extraction_bound`, then integrate over keygen
  -- via `jensen_keygen_forking_bound`.
  have hPerPkFinal : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun w : Wit => rel pk w = true |
          eufNmaReduction σ hr M nmaAdv qH pk] := fun pk =>
    (hPerPk pk).trans (perPk_extraction_bound σ hr M nmaAdv qH hss hss_nf pk)
  rw [hAdv_eq_tsum, hRHS_eq_tsum]
  have hinv_le : challengeSpaceInv Chal ≤ 1 := by
    unfold challengeSpaceInv
    have hcard : (1 : ENNReal) ≤ (Fintype.card Chal : ENNReal) := by
      exact_mod_cast Fintype.card_pos
    exact ENNReal.inv_le_one.2 hcard
  have hinv_ne_top : challengeSpaceInv Chal ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hinv_le
  exact jensen_keygen_forking_bound (gen := hr.gen)
    (acc := fun pkw => acc pkw.1)
    (B := fun pkw => Pr[ fun w : Wit => rel pkw.1 w = true |
      eufNmaReduction σ hr M nmaAdv qH pkw.1])
    (q := (qH : ENNReal) + 1) (hinv := challengeSpaceInv Chal)
    hinv_ne_top (fun _ => probEvent_le_one) (fun pkw => hPerPkFinal pkw.1)

/-- **Combined EUF-CMA bound (Pointcheval-Stern with quantitative HVZK).**

Composes `euf_cma_to_nma` and `euf_nma_bound`:

1. Replace the signing oracle with the HVZK simulator, losing
   `qS · ζ_zk + collisionSlack qS qH Chal`.
2. Apply the forking lemma to the resulting forkable managed-RO NMA experiment.

The combined bound is:

  `(ε - qS·ζ_zk - qS·(qS+qH)/|Ω|) ·
      ((ε - qS·ζ_zk - qS·(qS+qH)/|Ω|) / (qH+1) - 1/|Ω|)
    ≤ Pr[extraction succeeds]`

where `ε = Adv^{EUF-CMA}(A)` and the concrete slack `qS·(qS+qH)/|Ω|` is the
`collisionSlack qS qH Chal` birthday term. The ENNReal subtraction truncates at
zero, so the bound is trivially satisfied when the simulation loss exceeds the
advantage.

The forking-lemma side (the two B1 prefix-faithfulness identities
`evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt` and
`tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt` in ReplayFork.lean) is
discharged and feeds the Jensen/Cauchy-Schwarz step inside `Fork.replayForkingBound`
used by `euf_nma_bound`. The Phase B freshness-drop hop is discharged via
`SignatureAlg.unforgeableAdv.advantage_le_unforgeableExpNoFresh` instantiated with
`runtime_evalDist_bind_pure`. Conditional only on the single combined `hvzk_collision_swap`
sorry inside `euf_cma_to_nma` (HVZK simulator swap and programming-collision bound merged
into one inequality; see the comment there for the algebraic reason a clean two-phase
decomposition is not realizable without new infrastructure). -/
theorem euf_cma_bound
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hhvzk : σ.HVZK simTranscript ζ_zk)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      let eps := adv.advantage (runtime M) -
        (ENNReal.ofReal (qS * ζ_zk) + collisionSlack qS qH Chal)
      (eps * (eps / (qH + 1 : ENNReal) - challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  haveI : DecidableEq M := Classical.decEq M
  haveI : DecidableEq Commit := Classical.decEq Commit
  obtain ⟨nmaAdv, hBound, hAdv⟩ := euf_cma_to_nma σ hr M simTranscript
    ζ_zk hζ_zk hhvzk adv qS qH hQ
  obtain ⟨reduction, hRed⟩ := euf_nma_bound σ hr M hss hss_nf nmaAdv qH hBound
  refine ⟨reduction, le_trans ?_ hRed⟩
  have hle : adv.advantage (runtime M) -
      (ENNReal.ofReal (qS * ζ_zk) + collisionSlack qS qH Chal) ≤
      Fork.advantage σ hr M nmaAdv qH :=
    tsub_le_iff_right.mpr (by rw [← add_assoc]; exact hAdv)
  exact mul_le_mul' hle (tsub_le_tsub_right (ENNReal.div_le_div_right hle _) _)

end FiatShamir
