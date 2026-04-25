/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Chain
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.CryptoFoundations.SeededFork
import VCVio.CryptoFoundations.ReplayFork
import VCVio.EvalDist.Inequalities
import VCVio.SSP.Composition
import ToMathlib.Data.ENNReal.TsumDistrib

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

/-- Birthday-bound collision slack for the Fiat-Shamir CMA-to-NMA reduction,
parameterized by the simulator's commit-predictability bound `β`:

  `collisionSlack qS qH β = 2 · qS · (qS + qH) · β`.

The two `qS · (qS + qH) · β` summands come from the two programming-collision bad
events along the freshness-preserving chain, union-bounded over `qS` signing queries
and ≤ `qS + qH` cached points:
* simulator-side collision (sub-claim B-finish), bounded by `qS · (qS + qH) · β`
  directly from the `simCommitPredictability simTranscript β` hypothesis;
* FS-vs-programming collision in the (A) bridge, bounded by `qS · (qS + qH) · β`
  after absorbing the quadratic HVZK-transport term `qS · (qS + qH) · ζ_zk` into
  the overall `qS · (qS + qH + 1) · ζ_zk` HVZK cost carried by the theorem.

The cache-miss verification contribution is intentionally *not* folded into
`collisionSlack`: it depends on an additional scheme-specific fresh-challenge
acceptance bound (`SigmaProtocol.verifyChallengePredictability`) and is carried
separately in `euf_cma_to_nma`.

For Schnorr, `β = 1/|G|` (uniform commit over `⟨g⟩`), so the collision term is
`2 · qS · (qS + qH) / |G|`.

Matches EasyCrypt's `pr_bad_game` at
[fsec/proof/Schnorr.ec:793](../../../fsec/proof/Schnorr.ec) (`QS · (QS+QR) / |Ω|`,
modulo the doubled birthday bound and the separate cache-miss verification term) and plays the
same role as `GPVHashAndSign.collisionBound` for the PSF construction. -/
noncomputable def collisionSlack (qS qH : ℕ) (β : ENNReal) :
    ENNReal :=
  2 * (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma realCommit_probOutput_le_sim_plus_hvzk
    [Inhabited Chal] [SampleableType Chal]
    {simTranscript : Stmt → ProbComp (Commit × Chal × Resp)}
    {ζ_zk : ℝ} (hζ_zk : 0 ≤ ζ_zk)
    (hhvzk : σ.HVZK simTranscript ζ_zk)
    {x : Stmt} {w : Wit} (hx : rel x w = true) (c₀ : Commit) :
    Pr[= c₀ | Prod.fst <$> σ.realTranscript x w] ≤
      Pr[= c₀ | Prod.fst <$> simTranscript x] + ENNReal.ofReal ζ_zk := by
  classical
  letI := Classical.decEq Commit
  let eventDec : Commit × Chal × Resp → Bool := fun z => decide (z.1 = c₀)
  let eventReal : ProbComp Bool := eventDec <$> σ.realTranscript x w
  let eventSim : ProbComp Bool := eventDec <$> simTranscript x
  have htv_event : tvDist eventReal eventSim ≤ ζ_zk := by
    dsimp [eventReal, eventSim]
    exact le_trans (tvDist_map_le (f := eventDec) _ _) (hhvzk x w hx)
  have h_eventPred_eq :
      ((fun b : Bool => b = true) ∘ eventDec) = (fun z : Commit × Chal × Resp => z.1 = c₀) := by
    funext z
    simp [eventDec]
  have h_event_real :
      Pr[= c₀ | Prod.fst <$> σ.realTranscript x w] = Pr[= true | eventReal] := by
    rw [← probEvent_eq_eq_probOutput]
    calc
      Pr[fun c : Commit => c = c₀ | Prod.fst <$> σ.realTranscript x w] =
          Pr[fun z : Commit × Chal × Resp => z.1 = c₀ | σ.realTranscript x w] := by
            exact probEvent_map (mx := σ.realTranscript x w) (f := Prod.fst)
              (q := fun c : Commit => c = c₀)
      _ = Pr[(· = true) | eventReal] := by
            simpa [eventReal, h_eventPred_eq] using
              (probEvent_map (mx := σ.realTranscript x w)
                (f := eventDec) (q := fun b : Bool => b = true)).symm
      _ = Pr[= true | eventReal] := by
            simp
  have h_event_sim :
      Pr[= c₀ | Prod.fst <$> simTranscript x] = Pr[= true | eventSim] := by
    rw [← probEvent_eq_eq_probOutput]
    calc
      Pr[fun c : Commit => c = c₀ | Prod.fst <$> simTranscript x] =
          Pr[fun z : Commit × Chal × Resp => z.1 = c₀ | simTranscript x] := by
            exact probEvent_map (mx := simTranscript x) (f := Prod.fst)
              (q := fun c : Commit => c = c₀)
      _ = Pr[(· = true) | eventSim] := by
            simpa [eventSim, h_eventPred_eq] using
              (probEvent_map (mx := simTranscript x)
                (f := eventDec) (q := fun b : Bool => b = true)).symm
      _ = Pr[= true | eventSim] := by
            simp
  have hdiff :
      |Pr[= true | eventReal].toReal - Pr[= true | eventSim].toReal| ≤ ζ_zk := by
    exact le_trans (abs_probOutput_toReal_sub_le_tvDist eventReal eventSim) htv_event
  have h_toReal :
      Pr[= c₀ | Prod.fst <$> σ.realTranscript x w].toReal ≤
        Pr[= c₀ | Prod.fst <$> simTranscript x].toReal + ζ_zk := by
    rw [← h_event_real, ← h_event_sim] at hdiff
    rw [abs_le] at hdiff
    linarith
  have h_real_ne : Pr[= c₀ | Prod.fst <$> σ.realTranscript x w] ≠ ⊤ := probOutput_ne_top
  have h_sim_ne : Pr[= c₀ | Prod.fst <$> simTranscript x] ≠ ⊤ := probOutput_ne_top
  calc
    Pr[= c₀ | Prod.fst <$> σ.realTranscript x w] =
        ENNReal.ofReal (Pr[= c₀ | Prod.fst <$> σ.realTranscript x w].toReal) := by
          rw [ENNReal.ofReal_toReal h_real_ne]
    _ ≤ ENNReal.ofReal (Pr[= c₀ | Prod.fst <$> simTranscript x].toReal + ζ_zk) := by
          exact ENNReal.ofReal_le_ofReal h_toReal
    _ = Pr[= c₀ | Prod.fst <$> simTranscript x] + ENNReal.ofReal ζ_zk := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hζ_zk, ENNReal.ofReal_toReal h_sim_ne]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma realCommit_probOutput_le_beta_hvzk
    [Inhabited Chal] [SampleableType Chal]
    {simTranscript : Stmt → ProbComp (Commit × Chal × Resp)}
    {ζ_zk : ℝ} (hζ_zk : 0 ≤ ζ_zk)
    (hhvzk : σ.HVZK simTranscript ζ_zk)
    {β : ENNReal} (hPredSim : σ.simCommitPredictability simTranscript β)
    {x : Stmt} {w : Wit} (hx : rel x w = true) (c₀ : Commit) :
    Pr[= c₀ | Prod.fst <$> σ.realTranscript x w] ≤ β + ENNReal.ofReal ζ_zk := by
  calc
    Pr[= c₀ | Prod.fst <$> σ.realTranscript x w] ≤
        Pr[= c₀ | Prod.fst <$> simTranscript x] + ENNReal.ofReal ζ_zk :=
      realCommit_probOutput_le_sim_plus_hvzk (σ := σ) hζ_zk hhvzk hx c₀
    _ ≤ β + ENNReal.ofReal ζ_zk := by
      gcongr
      exact hPredSim x c₀

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

omit [SampleableType Stmt] [SampleableType Wit] in
/-- **CMA-to-NMA reduction via the HeapSSP theorem chain.**

This is the public Σ-protocol-on-`FiatShamir` CMA-to-NMA bound. It routes
through `VCVio/CryptoFoundations/FiatShamir/Sigma/HeapSSP/Chain.lean`; the
lower `CmaToNma.lean` module supplies the managed-RO adversary construction and
query-bound transport used by that chain.

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists a managed-RO NMA adversary `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{fork-NMA}_{qH}(B)
      + ofReal (qS · ζ_zk) + qS · (qS + qH) · β + δ_verify`

where `β` is the simulator's commit-predictability bound (see
`SigmaProtocol.simCommitPredictability`) and `δ_verify` bounds fresh-challenge
verification acceptance (see `SigmaProtocol.verifyChallengePredictability`).

The bound is tight in the joint-coupling sense: per-step `ζ_zk` paid `qS` times
and a single-side `β` collision term with no factor of 2.

The NMA adversary `B` is constructed by the simulator from `A` (running
`A.main pk` with the signing oracle replaced by the HVZK simulator and the
random oracle programmed on each simulated signature) and returning `A`'s
forgery alongside the live RO query log.

This step is independent of special soundness and the forking lemma; those are
handled by `euf_nma_bound`. -/
theorem euf_cma_to_nma
    [DecidableEq M] [DecidableEq Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simTranscript ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simTranscript β)
    (δ_verify : ENNReal)
    (hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ nmaAdv : SignatureAlg.managedRoNmaAdv
        (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M),
      (∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := nmaAdv.main pk) qH) ∧
      adv.advantage (runtime M) ≤
        Fork.advantage σ hr M nmaAdv qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * (qS + qH) * β +
          δ_verify :=
  HeapSSP.cma_advantage_le_fork_bound (σ := σ) (hr := hr) (M := M)
    simTranscript ζ_zk hζ_zk hHVZK β hPredSim δ_verify hVerifyGuess adv qS qH hQ

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
    simp only [← probEvent_eq_eq_probOutput, probEvent_simulateQ_unifChalImpl,
      probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map, Function.comp_def,
      probEvent_liftComp, acc]
  -- ── Step (b): rewrite `Pr[= true | hardRelationExp]` as a keygen-marginalized sum of
  -- per-pk relation-recovery probabilities.
  have hRHS_eq_tsum :
      Pr[= true | hardRelationExp hr (eufNmaReduction σ hr M nmaAdv qH)] =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] *
          Pr[ fun w : Wit => rel pkw.1 w = true |
            eufNmaReduction σ hr M nmaAdv qH pkw.1] := by
    unfold hardRelationExp
    simp only [← probEvent_eq_eq_probOutput, bind_pure_comp, probEvent_bind_eq_tsum,
      probEvent_map, Function.comp_def]
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
  -- via `OracleComp.EvalDist.marginalized_jensen_forking_bound`.
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
  exact OracleComp.EvalDist.marginalized_jensen_forking_bound (mx := hr.gen)
    (acc := fun pkw => acc pkw.1)
    (B := fun pkw => Pr[ fun w : Wit => rel pkw.1 w = true |
      eufNmaReduction σ hr M nmaAdv qH pkw.1])
    (q := (qH : ENNReal) + 1) (hinv := challengeSpaceInv Chal)
    hinv_ne_top (fun _ => probEvent_le_one) (fun pkw => hPerPkFinal pkw.1)

omit [SampleableType Stmt] in
/-- **Combined EUF-CMA bound (Pointcheval-Stern with quantitative HVZK, β-parametric, tight).**

Composes `euf_cma_to_nma` and `euf_nma_bound`:

1. Replace the signing oracle with the HVZK simulator, losing
   `qS·ζ_zk + qS·(qS+qH)·β + δ_verify`, where `β` is the simulator's
   commit-predictability bound and `δ_verify` bounds fresh-challenge
   verification acceptance.
2. Apply the forking lemma to the resulting forkable managed-RO NMA experiment.

The combined bound is:

  `(ε - qS·ζ_zk - qS·(qS+qH)·β - δ_verify) ·
      ((ε - qS·ζ_zk - qS·(qS+qH)·β - δ_verify) / (qH+1) - 1/|Ω|)
    ≤ Pr[extraction succeeds]`

where `ε = Adv^{EUF-CMA}(A)`, `qS·(qS+qH)·β` is the joint-coupling
programming-collision slack (no factor of 2), `δ_verify` is the fresh-challenge
verification slack, and `qS·ζ_zk` is the per-signing-query HVZK loss (no
quadratic blow-up). The ENNReal subtraction truncates at zero, so the bound is
trivially satisfied when the simulation loss exceeds the advantage.

The tightening compared to the chain-decomposition form (which has
`qS·(qS+qH+1)·ζ_zk + 2·qS·(qS+qH)·β`) is carried by the HeapSSP H3
joint-coupling theorem: it pays the HVZK distance once per signing query and
charges the simulator-commit collision event once.

When HVZK is perfect (`ζ_zk = 0`), the HVZK term vanishes and the bound
specializes to `(ε - qS·(qS+qH)·β - δ_verify) · …`.

The forking-lemma side uses `Fork.replayForkingBound` (via the two B1
prefix-faithfulness identities
`evalDist_uniform_bind_fst_replayRunWithTraceValue_takeBeforeForkAt` and
`tsum_probOutput_replayFirstRun_weight_takeBeforeForkAt` in `ReplayFork.lean`)
to feed the Jensen/Cauchy-Schwarz step inside `euf_nma_bound`. The Phase B
freshness-drop hop uses
`SignatureAlg.unforgeableAdv.advantage_le_unforgeableExpNoFresh` instantiated
with `runtime_evalDist_bind_pure`. -/
theorem euf_cma_bound
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hhvzk : σ.HVZK simTranscript ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simTranscript β)
    (δ_verify : ENNReal)
    (hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      let eps := adv.advantage (runtime M) -
        (ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * (qS + qH) * β + δ_verify)
      (eps * (eps / (qH + 1 : ENNReal) - challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  haveI : DecidableEq M := Classical.decEq M
  haveI : DecidableEq Commit := Classical.decEq Commit
  obtain ⟨nmaAdv, hBound, hAdv⟩ := euf_cma_to_nma σ hr M simTranscript
    ζ_zk hζ_zk hhvzk β hPredSim δ_verify hVerifyGuess adv qS qH hQ
  obtain ⟨reduction, hRed⟩ := euf_nma_bound σ hr M hss hss_nf nmaAdv qH hBound
  refine ⟨reduction, le_trans ?_ hRed⟩
  have hle : adv.advantage (runtime M) -
      (ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
        (qS : ENNReal) * (qS + qH) * β + δ_verify) ≤
      Fork.advantage σ hr M nmaAdv qH :=
    tsub_le_iff_right.mpr (by simpa [add_assoc] using hAdv)
  exact mul_le_mul' hle (tsub_le_tsub_right (ENNReal.div_le_div_right hle _) _)

end FiatShamir
