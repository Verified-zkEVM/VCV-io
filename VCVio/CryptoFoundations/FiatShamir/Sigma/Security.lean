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
    [DecidableEq Commit] [Fintype Chal] [Inhabited Chal] [SampleableType Chal]
    {simTranscript : Stmt → ProbComp (Commit × Chal × Resp)}
    {ζ_zk : ℝ} (hζ_zk : 0 ≤ ζ_zk)
    (hhvzk : σ.HVZK simTranscript ζ_zk)
    {x : Stmt} {w : Wit} (hx : rel x w = true) (c₀ : Commit) :
    Pr[= c₀ | Prod.fst <$> σ.realTranscript x w] ≤
      Pr[= c₀ | Prod.fst <$> simTranscript x] + ENNReal.ofReal ζ_zk := by
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
    [DecidableEq Commit] [Fintype Chal] [Inhabited Chal] [SampleableType Chal]
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

private lemma wasQueried_eq_decide_mem_map_fst
    {S : Type} [DecidableEq M] [DecidableEq S]
    (log : QueryLog (M →ₒ S)) (msg : M) :
    log.wasQueried msg = decide (msg ∈ log.map (fun e => e.1)) := by
  have hiff : log.getQ (· = msg) ≠ [] ↔ msg ∈ log.map (fun e => e.1) := by
    induction log with
    | nil =>
        simp [QueryLog.getQ]
    | cons hd tl ih =>
        by_cases h : hd.1 = msg
        · simp [List.map, List.mem_cons, QueryLog.getQ_cons, h]
        · have hne : msg ≠ hd.1 := by
            simpa [eq_comm] using h
          constructor
          · intro hq
            have hq' : QueryLog.getQ tl (· = msg) ≠ [] := by
              simpa [QueryLog.getQ_cons, h] using hq
            simpa [List.map, List.mem_cons] using Or.inr (ih.mp hq')
          · intro hm
            have hm_cons : msg = hd.1 ∨ msg ∈ tl.map (fun e => e.1) := by
              simpa [List.map, List.mem_cons] using hm
            have hm' : msg ∈ tl.map (fun e => e.1) := by
              rcases hm_cons with hm | hm
              · exact (hne hm).elim
              · exact hm
            have hq' : QueryLog.getQ tl (· = msg) ≠ [] := ih.mpr hm'
            simpa [QueryLog.getQ_cons, h] using hq'
  by_cases hq : log.getQ (· = msg) ≠ []
  · have hm : msg ∈ log.map (fun e => e.1) := hiff.mp hq
    simp [QueryLog.wasQueried, hq, hm]
  · have hm : msg ∉ log.map (fun e => e.1) := by
      intro hm
      exact hq (hiff.mpr hm)
    simp [QueryLog.wasQueried, hq, hm]

private lemma map_run_withLogging_inputs_eq_run_signedAppend
    {ι : Type} {spec : OracleSpec ι} {S α : Type}
    (sign : M → OracleComp spec S)
    (oa : OracleComp (spec + (M →ₒ S)) α)
    (signed₀ : List M) :
    let baseW : QueryImpl spec (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
    let implW : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      baseW + QueryImpl.withLogging sign
    let baseS : QueryImpl spec (StateT (List M) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
    let signAppend : QueryImpl (M →ₒ S) (StateT (List M) (OracleComp spec)) := fun msg => do
      let signed ← get
      let sig ← liftM (sign msg)
      set (signed ++ [msg])
      pure sig
    let implAppend : QueryImpl (spec + (M →ₒ S))
        (StateT (List M) (OracleComp spec)) :=
      baseS + signAppend
    (fun z : α × QueryLog (M →ₒ S) =>
        (z.1, signed₀ ++ z.2.map (fun e => e.1))) <$> (simulateQ implW oa).run =
      (simulateQ implAppend oa).run signed₀ := by
  let baseW : QueryImpl spec (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  let implW : QueryImpl (spec + (M →ₒ S))
      (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
    baseW + QueryImpl.withLogging sign
  let baseS : QueryImpl spec (StateT (List M) (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  let signAppend : QueryImpl (M →ₒ S) (StateT (List M) (OracleComp spec)) := fun msg => do
    let signed ← get
    let sig ← liftM (sign msg)
    set (signed ++ [msg])
    pure sig
  let implAppend : QueryImpl (spec + (M →ₒ S))
      (StateT (List M) (OracleComp spec)) :=
    baseS + signAppend
  induction oa using OracleComp.inductionOn generalizing signed₀ with
  | pure x =>
      simp [implW, implAppend]
  | query_bind t oa ih =>
      cases t with
      | inl t' =>
          simp [implW, implAppend, baseW, baseS, QueryImpl.add_apply_inl, ih]
      | inr msg =>
          simp [implW, implAppend, signAppend, baseW, baseS, QueryImpl.add_apply_inr,
            QueryImpl.withLogging_apply, WriterT.run_bind', StateT.run_bind, StateT.run_get,
            StateT.run_set]
          refine bind_congr fun sig => ?_
          simpa [List.append_assoc] using ih sig (signed₀ ++ [msg])

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
private def simulatedNmaAdv
    [DecidableEq M] [DecidableEq Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)) :
    SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M) :=
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
  let baseSim : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    unifSim + roSim
  let sigSim : Stmt → QueryImpl (M →ₒ (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun pk msg => do
    let (c, ω, s) ← simulateQ unifSim (simTranscript pk)
    modifyGet fun cache =>
      match cache (.inr (msg, c)) with
      | some _ => ((c, s), cache)
      | none => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)
  ⟨fun pk => (simulateQ (baseSim + sigSim pk) (adv.main pk)).run ∅⟩

omit [SampleableType Stmt] [SampleableType Wit] in
private theorem simulatedNmaAdv_hashQueryBound
    [DecidableEq M] [DecidableEq Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulatedNmaAdv (σ := σ) (hr := hr) (M := M)
        (simTranscript := simTranscript) (adv := adv)).main pk) qH := by
  letI : Fintype Chal := Fintype.ofFinite Chal
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
  let baseSim : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    unifSim + roSim
  let sigSim : Stmt → QueryImpl (M →ₒ (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun pk msg => do
    let (c, ω, s) ← simulateQ unifSim (simTranscript pk)
    modifyGet fun cache =>
      match cache (.inr (msg, c)) with
      | some _ => ((c, s), cache)
      | none => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)
  let nmaAdv := simulatedNmaAdv (σ := σ) (hr := hr) (M := M)
    (simTranscript := simTranscript) (adv := adv)
  -- Query bound: show the NMA adversary makes at most `qH` hash queries.
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
  simpa [nmaAdv, simulatedNmaAdv, nmaHashQueryBound, signHashQueryBound] using
    (OracleComp.IsQueryBound.simulateQ_run_of_step
      (h := hQ pk) (combine := Nat.add) (mapBudget := Prod.snd)
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

set_option maxHeartbeats 800000 in
/-- **CMA-to-NMA reduction via HVZK simulation.**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists a managed-RO NMA adversary `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{fork-NMA}_{qH}(B)
      + qS · (qS + qH + 1) · ζ_zk + collisionSlack qS qH β + δ_verify`

where `β` is the simulator's commit-predictability bound (see
`SigmaProtocol.simCommitPredictability`) and `δ_verify` is any bound on
fresh-challenge verification acceptance (see
`SigmaProtocol.verifyChallengePredictability`). The HVZK cost picks up a quadratic
`qS · (qS + qH) · ζ_zk` contribution from the HVZK-transport step in bridge (A),
on top of the linear `qS · ζ_zk` from the direct per-query swap in bridge (B).
When HVZK is perfect (`ζ_zk = 0`) this reduces to
`Fork.advantage + collisionSlack qS qH β + δ_verify`.

The NMA adversary `B` is constructed by:
- Forwarding `A`'s hash queries to the external oracle (visible to `Fork.fork`)
- Simulating `A`'s signing queries using the HVZK simulator, programming the
  simulated challenge into the cache
- Returning `A`'s forgery together with the accumulated `QueryCache`

Each of the `qS` signing simulations introduces at most `ζ_zk` total-variation distance
(direct HVZK cost) and, via HVZK-transport, inflates the real-side commit predictability
from `β` to `β + ζ_zk` for the (A)-bridge collision analysis. The birthday term
`collisionSlack qS qH β = 2·qS·(qS+qH)·β` absorbs the two collision events (sim-side via
`_hPredSim`, real-side via `_hPredSim` + HVZK), while the cache-miss verify contribution is
carried separately through `δ_verify`.

This step is independent of special soundness and the forking lemma; those are handled
by `euf_nma_bound`.

The Lean bound matches Firsov-Janku's `pr_koa_cma` at
[fsec/proof/Schnorr.ec:943](../../../fsec/proof/Schnorr.ec): the CMA-to-KOA reduction uses
`eq_except (signed qs) LRO.m{1} LRO.m{2}` as the RO-cache invariant, swaps real signing with
`simulator_equiv` (per-query HVZK cost), handles RO reprogramming via `lro_redo_inv` +
`ro_get_eq_except`, and absorbs the late-programming collision event through the `bad` flag,
bounded by `pr_bad_game` at [fsec/proof/Schnorr.ec:793](../../../fsec/proof/Schnorr.ec) as
`QS · (QS+QR) / |Ω|`, matching our `collisionSlack qS qH β` at `β = 1/|Ω|`. -/
theorem euf_cma_to_nma
    [DecidableEq M] [DecidableEq Commit]
    [Fintype Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (_hζ_zk : 0 ≤ ζ_zk)
    (_hhvzk : σ.HVZK simTranscript ζ_zk)
    (β : ENNReal)
    (_hPredSim : σ.simCommitPredictability simTranscript β)
    (δ_verify : ENNReal)
    (_hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify)
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
          ENNReal.ofReal ((qS * (qS + qH + 1) : ℕ) * ζ_zk) +
          collisionSlack qS qH β + δ_verify := by
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
    simulatedNmaAdv (σ := σ) (hr := hr) (M := M) (simTranscript := simTranscript)
      (adv := adv)
  refine ⟨nmaAdv, ?_, ?_⟩
  · exact simulatedNmaAdv_hashQueryBound (σ := σ) (hr := hr) (M := M)
      (simTranscript := simTranscript) (adv := adv) qS qH _hQ
  · -- Advantage bound: `adv.advantage ≤ Adv^{fork-NMA}_{qH}(nmaAdv)
    --                      + ofReal(qS · (qS+qH+1) · ζ_zk) + collisionSlack qS qH β + δ_verify`.
    --
    -- **Freshness-preserving chain, β-parametric.** The previous design routed through
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
    --           + qS·(qS+qH)·β + qS·(qS+qH)·ζ_zk + δ_verify                 -- (A) bridge_real
    --       ≤ ∑' (pk,sk), Pr[(pk,sk)|gen] ·
    --           (Pr[verify ∧ ¬msg ∈ signed | direct_sim_exp pk] + qS·ζ_zk + qS·(qS+qH)·β)
    --           + qS·(qS+qH)·β + qS·(qS+qH)·ζ_zk + δ_verify                 -- (B) tv_swap
    --       ≤ Fork.advantage + qS·(qS+qH+1)·ζ_zk + 2·qS·(qS+qH)·β + δ_verify
    --                                                                       -- (C') sim_to_fork
    --       = Fork.advantage + qS·(qS+qH+1)·ζ_zk + collisionSlack qS qH β + δ_verify
    --
    -- The HVZK cost `qS·(qS+qH+1)·ζ_zk` decomposes as:
    --   * `qS·ζ_zk`: direct per-query HVZK swap cost in step (B);
    --   * `qS·(qS+qH)·ζ_zk`: HVZK-transport in step (A), since the real-side commit
    --     predictability inherits a `ζ_zk` gap over the `β`-bound on the simulator side.
    -- The cache-miss verification slack in (C') is carried separately as `δ_verify`.
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
    -- The (B-finish) collision bound and the (A) / (C') bridges are established
    -- as named intermediate `have`s along this proof. Each is mathematically
    -- substantive:
    --
    --   * (A) `bridge_real_freshness`: rewrites `unforgeableExp` as an integral
    --     over `keygen` of `direct_real_exp pk sk`, factoring out `keygen` from
    --     the SPMF `runtime.evalDist` and equating the WriterT log of
    --     `signingOracle` with the augmented `signed` state.
    --
    --   * (B-finish) `pr_bad_le_signed`: a union bound on `qS` programming
    --     events, each hitting a previously cached point with probability
    --     ≤ `(qS + qH) · β`. The per-event uniformity comes from the per-query
    --     HVZK simulator (challenge marginal is `β`-bounded).
    --
    --   * (C') `bridge_sim_fork_freshness`: a forgery `(msg, c, s)` against
    --     `direct_sim_exp` with `¬msg ∈ signed` cannot have used a programmed
    --     `(msg, c)` cache entry (since `sigSim` only programs at signed `msg`),
    --     so `(msg, c)` is in the live RO query log iff it is in the cache.
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
    have run_unifSim : ∀ (s : spec.QueryCache) {α : Type} (oa : ProbComp α),
        (simulateQ unifSim oa).run s = (fun x => (x, s)) <$> oa.liftComp spec := by
      intro s α oa
      set inj : QueryImpl unifSpec (OracleComp spec) := fun t => liftM (unifSpec.query t) with hinj
      have unifSim_eq : unifSim = inj.liftTarget
          (StateT spec.QueryCache (OracleComp spec)) := rfl
      rw [unifSim_eq, simulateQ_liftTarget]
      have simulateQ_inj : simulateQ inj oa = oa.liftComp spec := rfl
      rw [simulateQ_inj, OracleComp.liftM_run_StateT, bind_pure_comp]
    have h_sigSim_run : ∀ (pk : Stmt) (msg : M) (s : spec.QueryCache),
        (sigSim pk msg).run s =
          (simTranscript pk).liftComp spec >>=
            fun cωπ : Commit × Chal × Resp =>
              pure (match s (.inr (msg, cωπ.1)) with
                | some _ => ((cωπ.1, cωπ.2.2), s)
                | none => ((cωπ.1, cωπ.2.2),
                    s.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1)) := by
      intro pk msg s
      dsimp only [sigSim]
      rw [StateT.run_bind, run_unifSim s, bind_map_left]
      refine bind_congr (fun cωπ => ?_)
      simp only [modifyGet, MonadState.modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.run]
      congr 1
      rcases s (.inr (msg, cωπ.1)) with _ | _ <;> simp
    have h_realSign_run : ∀ (pk : Stmt) (sk : Wit) (msg : M) (s : spec.QueryCache),
        (realSign pk sk msg).run s =
          (σ.realTranscript pk sk).liftComp spec >>=
            fun cωπ : Commit × Chal × Resp =>
              pure (match s (.inr (msg, cωπ.1)) with
                | some _ => ((cωπ.1, cωπ.2.2), s)
                | none => ((cωπ.1, cωπ.2.2),
                    s.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1)) := by
      intro pk sk msg s
      dsimp only [realSign]
      rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind,
        OracleComp.liftM_run_StateT, bind_assoc]
      refine bind_congr (fun cωπ => ?_)
      rw [pure_bind]
      simp only [modifyGet, MonadState.modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.run]
      congr 1
      rcases s (.inr (msg, cωπ.1)) with _ | _ <;> simp
    have h_fwd_run : ∀ (t : spec.Domain) (s : spec.QueryCache),
        (fwd t).run s = (fun u => (u, s)) <$> (liftM (spec.query t) : OracleComp spec _) := by
      intro t s
      simp [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
        OracleComp.liftM_run_StateT, bind_pure_comp]
    have h_roSim_run_miss : ∀ (mc : M × Commit) (cache : spec.QueryCache),
        cache (.inr mc) = none →
          (roSim mc).run cache =
            (fun u => (u, cache.cacheQuery (.inr mc) u)) <$>
              (liftM (spec.query (Sum.inr mc)) : OracleComp spec _) := by
      intro mc cache hcache
      simp [roSim, hcache, h_fwd_run (Sum.inr mc) cache, bind_pure_comp,
        bind_map_left, Functor.map_map]
      rfl
    have h_roSim_run_hit : ∀ (mc : M × Commit) (cache : spec.QueryCache) (u : Chal),
        cache (.inr mc) = some u →
          (roSim mc).run cache = pure (u, cache) := by
      intro mc cache u hu
      simp [roSim, hu]
    have h_baseSimBad_unif : ∀ (n : ℕ) (cache : spec.QueryCache),
        (baseSimBad (.inl n)).run (cache, false) =
          (fun u => (u, cache, false)) <$> (liftM (spec.query (Sum.inl n)) : OracleComp spec _) := by
      intro n cache
      have hbase : baseSimBad = baseSim.withBadFlag := rfl
      rw [hbase, QueryImpl.withBadFlag_apply_run]
      simp [baseSim, unifSim, QueryImpl.add_apply_inl, h_fwd_run (Sum.inl n) cache]
    have h_baseSimBad_hash_miss : ∀ (mc : M × Commit) (cache : spec.QueryCache),
        cache (.inr mc) = none →
          (baseSimBad (.inr mc)).run (cache, false) =
            (fun u => (u, cache.cacheQuery (.inr mc) u, false)) <$>
              (liftM (spec.query (Sum.inr mc)) : OracleComp spec _) := by
      intro mc cache hcache
      have hbase : baseSimBad = baseSim.withBadFlag := rfl
      rw [hbase, QueryImpl.withBadFlag_apply_run]
      simp [baseSim, QueryImpl.add_apply_inr]
      exact congrArg
        (fun x : OracleComp spec (Chal × spec.QueryCache) =>
          (fun vs : Chal × spec.QueryCache => (vs.1, vs.2, false)) <$> x)
        (h_roSim_run_miss mc cache hcache)
    have h_baseSimBad_hash_hit : ∀ (mc : M × Commit) (cache : spec.QueryCache) (u : Chal),
        cache (.inr mc) = some u →
          (baseSimBad (.inr mc)).run (cache, false) = pure (u, cache, false) := by
      intro mc cache u hu
      have hbase : baseSimBad = baseSim.withBadFlag := rfl
      rw [hbase, QueryImpl.withBadFlag_apply_run]
      simp [baseSim, QueryImpl.add_apply_inr]
      exact congrArg
        (fun x : OracleComp spec (Chal × spec.QueryCache) =>
          (fun vs : Chal × spec.QueryCache => (vs.1, vs.2, false)) <$> x)
        (h_roSim_run_hit mc cache u hu)
    have h_sigSimBad_run : ∀ (pk : Stmt) (msg : M) (cache : spec.QueryCache),
        (sigSimBad pk msg).run (cache, false) =
          (fun cωπ : Commit × Chal × Resp =>
            ((cωπ.1, cωπ.2.2),
              ((match cache (.inr (msg, cωπ.1)) with
                  | some _ => cache
                  | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                (cache (.inr (msg, cωπ.1))).isSome))) <$>
            (simTranscript pk).liftComp spec := by
      intro pk msg cache
      have hsig : sigSimBad pk = (sigSim pk).withBadUpdate sigBadF := rfl
      rw [hsig, QueryImpl.withBadUpdate_apply_run, h_sigSim_run pk msg cache]
      rw [map_bind]
      refine bind_congr (fun cωπ => ?_)
      cases hcache : cache (.inr (msg, cωπ.1)) with
      | none =>
          simp [sigBadF, hcache]
          change
            (PFunctor.FreeM.pure
              ((cωπ.1, cωπ.2.2),
                cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1, false) :
              OracleComp spec ((Commit × Resp) × spec.QueryCache × Bool)) =
              PFunctor.FreeM.pure
                ((cωπ.1, cωπ.2.2),
                  cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1, false)
          rfl
      | some val =>
          simp [sigBadF, hcache]
          change
            (PFunctor.FreeM.pure ((cωπ.1, cωπ.2.2), cache, true) :
              OracleComp spec ((Commit × Resp) × spec.QueryCache × Bool)) =
              PFunctor.FreeM.pure ((cωπ.1, cωπ.2.2), cache, true)
          rfl
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
    have sign_step_tv : ∀ (pk : Stmt) (sk : Wit) (msg : M) (cache : spec.QueryCache),
        rel pk sk = true →
          tvDist
            (((_simImpl pk) (.inr msg)).run (cache, false))
            (((_realImpl pk sk) (.inr msg)).run (cache, false)) ≤
            ζ_zk := by
      intro pk sk msg cache h_rel
      dsimp only [_simImpl, _realImpl, sigSimBad, realSignBad]
      simp only [QueryImpl.add_apply_inr]
      refine le_trans (tvDist_map_le _ _ _) ?_
      rw [h_sigSim_run pk msg cache, h_realSign_run pk sk msg cache]
      refine le_trans (tvDist_bind_right_le _ _ _) ?_
      have h_eq : tvDist ((simTranscript pk).liftComp spec : OracleComp spec _)
          ((σ.realTranscript pk sk : ProbComp _).liftComp spec) =
          tvDist (simTranscript pk : ProbComp _) (σ.realTranscript pk sk) := by
        unfold tvDist
        simp only [OracleComp.evalDist_liftComp]
      rw [h_eq, tvDist_comm]
      exact _hhvzk pk sk h_rel
    have advantage_bound : adv.advantage (runtime M) ≤ Fork.advantage σ hr M nmaAdv qH +
        ENNReal.ofReal ((qS * (qS + qH + 1) : ℕ) * ζ_zk) + collisionSlack qS qH β +
          δ_verify := by
      -- **Freshness-preserving chain, β-parametric.** See the docstring at the top of this
      -- bullet for the rationale. The proof structure is:
      --
      --   adv.advantage (runtime M)
      --       ≤ ∑' (pk,sk), Pr[(pk,sk)|gen] · Pr[verify ∧ ¬msg ∈ signed | direct_real_exp pk sk]
      --           + qS·(qS+qH)·β + qS·(qS+qH)·ζ_zk + δ_verify                -- (A) bridge_a
      --       ≤ ∑' (pk,sk), Pr[(pk,sk)|gen] ·
      --           (Pr[verify ∧ ¬msg ∈ signed | direct_sim_exp pk] + qS·ζ_zk + Pr[bad on sim])
      --           + qS·(qS+qH)·β + qS·(qS+qH)·ζ_zk + δ_verify                -- (B) tv_swap
      --       ≤ ∑' pk, Pr[pk|gen_pk] · Pr[verify ∧ ¬msg ∈ signed | direct_sim_exp pk] +
      --           qS·ζ_zk + qS·(qS+qH)·ζ_zk + 2·qS·(qS+qH)·β + δ_verify      -- (B-finish)
      --       = ∑' pk, … + qS·(qS+qH+1)·ζ_zk + collisionSlack qS qH β + δ_verify
      --       ≤ Fork.advantage + qS·(qS+qH+1)·ζ_zk + collisionSlack qS qH β + δ_verify
      --                                                                       -- (C')
      --
      -- The augmented state for `direct_*_exp` is `(QueryCache × List M × Bool)`, with the
      -- `List M` tracking signed messages (so the freshness check `¬msg ∈ signed` is local).
      -- The `Bool` is the collision-bad flag (set when programming overwrites a cached point).
      --
      -- The four sub-claims are scaffolded as sorries with detailed sketches; `step_b_per_pksk`
      -- (the underlying selective ε lemma application on the simpler `(cache × Bool)` state)
      -- is fully proven and forms the infrastructure for sub-claim (B).
      --
      -- β-parameterization: bridges (A) and (B) each contribute a collision slack of
      -- `qS·(qS+qH)·β` where `β = simCommitPredictability`. Bridge (A)'s slack additionally
      -- picks up `qS·(qS+qH)·ζ_zk` from HVZK-transport (the real-side commit predictability
      -- is bounded via HVZK by `β + ζ_zk`). The cache-miss verify term is carried separately
      -- as `δ_verify`.
      --
      -- Step (B), per (pk, sk) pair: the per-query ε bound from the selective lemma.
      -- The selective lemma yields a TV bound on the joint distribution of
      -- `(simulateQ _simImpl).run' (∅, false)` and `(simulateQ _realImpl).run' (∅, false)`
      -- of the form `qS · ζ_zk + Pr[bad on _simImpl]`. The `Pr[bad]` term is then bounded
      -- by `qS·(qS+qH)·β` via the (B-finish) sub-claim (union bound using `_hPredSim`).
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
          intro t hSt s
          cases t with
          | inl _ => exact hSt.elim
          | inr msg =>
              simpa using sign_step_tv pk sk msg s h_rel
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
      -- For the simulator-side bad-event bound, the `signed` list is proof-irrelevant. Project
      -- it away to recover the simpler `(cache × bad)` simulation used by `step_b_per_pksk`.
      let signedProj : ((spec.QueryCache × List M) × Bool) → spec.QueryCache × Bool :=
        fun s => (s.1.1, s.2)
      let direct_sim_exp_simple : Stmt → OracleComp spec
          ((M × (Commit × Resp)) × (spec.QueryCache × Bool)) := fun pk =>
        (simulateQ (_simImpl pk) (adv.main pk)).run (∅, false)
      let badPredSimple : (M × (Commit × Resp)) × (spec.QueryCache × Bool) → Prop :=
        fun z => z.2.2 = true
      have h_simImplSigned_proj :
          ∀ (pk : Stmt) (t : (spec + (M →ₒ (Commit × Resp))).Domain)
            (s : ((spec.QueryCache × List M) × Bool)),
            Prod.map id signedProj <$> ((_simImplSigned pk) t).run s =
              ((_simImpl pk) t).run (signedProj s) := by
        intro pk t s
        rcases s with ⟨⟨cache, signed⟩, bad⟩
        cases t with
        | inl t' =>
            simp [signedProj, _simImplSigned, _simImpl, baseSimSigned, baseSimBad,
              baseSimSigned', QueryImpl.add_apply_inl, QueryImpl.withBadFlag_apply_run,
              StateT.run_bind, StateT.run_get, StateT.run_set]
        | inr msg =>
            simp [signedProj, _simImplSigned, _simImpl, sigSimSigned, sigSimBad,
              sigSimSigned', sigBadFSigned, sigBadF, QueryImpl.add_apply_inr,
              QueryImpl.withBadUpdate_apply_run, StateT.run_bind, StateT.run_get, StateT.run_set]
      have h_direct_sim_exp_proj : ∀ (pk : Stmt),
          Prod.map id signedProj <$> direct_sim_exp pk = direct_sim_exp_simple pk := by
        intro pk
        simpa [direct_sim_exp, direct_sim_exp_simple, signedProj] using
          (OracleComp.map_run_simulateQ_eq_of_query_map_eq'
            (impl₁ := _simImplSigned pk) (impl₂ := _simImpl pk)
            (proj := signedProj) (hproj := h_simImplSigned_proj pk)
            (oa := adv.main pk) (s := ((∅, []), false)))
      have pr_bad_eq_simple : ∀ (pk : Stmt),
          Pr[badPred | direct_sim_exp pk] = Pr[badPredSimple | direct_sim_exp_simple pk] := by
        intro pk
        calc
          Pr[badPred | direct_sim_exp pk] =
              Pr[badPredSimple ∘ Prod.map id signedProj | direct_sim_exp pk] := by
                rfl
          _ = Pr[badPredSimple | Prod.map id signedProj <$> direct_sim_exp pk] := by
                rw [← probEvent_map]
          _ = Pr[badPredSimple | direct_sim_exp_simple pk] := by
                rw [h_direct_sim_exp_proj pk]
      -- Proof-only extension of `_simImpl pk` with a passive log of the `(msg, commit)` points
      -- touched by random-oracle or signing queries. The log is only used to enumerate the
      -- candidate cache points in the union bound for `pr_bad_le_signed`.
      let keyAux :
          (t : (spec + (M →ₒ (Commit × Resp))).Domain) →
            (spec + (M →ₒ (Commit × Resp))).Range t → List (M × Commit) → List (M × Commit)
        := fun t u keys =>
          match t with
          | .inl (.inl _) => keys
          | .inl (.inr mc) => mc :: keys
          | .inr msg => (msg, u.1) :: keys
      let _simImplLogged : Stmt → QueryImpl (spec + (M →ₒ (Commit × Resp)))
          (StateT ((spec.QueryCache × Bool) × List (M × Commit)) (OracleComp spec)) := fun pk =>
        QueryImpl.extendState (_simImpl pk) keyAux
      let direct_sim_exp_logged : Stmt → OracleComp spec
          ((M × (Commit × Resp)) × ((spec.QueryCache × Bool) × List (M × Commit))) := fun pk =>
        (simulateQ (_simImplLogged pk) (adv.main pk)).run ((∅, false), [])
      let badPredLogged :
          (M × (Commit × Resp)) × ((spec.QueryCache × Bool) × List (M × Commit)) → Prop :=
        fun z => z.2.1.2 = true
      let keyCovers : ((spec.QueryCache × Bool) × List (M × Commit)) → Prop := fun s =>
        ∀ mc : M × Commit, ∀ ω : Chal, s.1.1 (.inr mc) = some ω → mc ∈ s.2
      have h_simImplLogged_proj :
          ∀ (pk : Stmt) (t : (spec + (M →ₒ (Commit × Resp))).Domain)
            (s : (spec.QueryCache × Bool) × List (M × Commit)),
            Prod.map id Prod.fst <$> ((_simImplLogged pk) t).run s =
              ((_simImpl pk) t).run s.1 := by
        intro pk t s
        rcases s with ⟨st, keys⟩
        change Prod.map id Prod.fst <$>
            ((fun a => (a.1, (a.2, keyAux t a.1 keys))) <$> ((_simImpl pk) t).run st) =
              ((_simImpl pk) t).run st
        simp
      have h_direct_sim_exp_logged_proj : ∀ (pk : Stmt),
          Prod.map id Prod.fst <$> direct_sim_exp_logged pk = direct_sim_exp_simple pk := by
        intro pk
        simpa [direct_sim_exp_logged, direct_sim_exp_simple] using
          (OracleComp.map_run_simulateQ_eq_of_query_map_eq'
            (impl₁ := _simImplLogged pk) (impl₂ := _simImpl pk)
            (proj := Prod.fst) (hproj := h_simImplLogged_proj pk)
            (oa := adv.main pk) (s := ((∅, false), [])))
      have pr_bad_eq_logged : ∀ (pk : Stmt),
          Pr[badPredSimple | direct_sim_exp_simple pk] =
            Pr[badPredLogged | direct_sim_exp_logged pk] := by
        intro pk
        calc
          Pr[badPredSimple | direct_sim_exp_simple pk] =
              Pr[badPredSimple | Prod.map id Prod.fst <$> direct_sim_exp_logged pk] := by
                rw [h_direct_sim_exp_logged_proj pk]
          _ = Pr[badPredSimple ∘ Prod.map id Prod.fst | direct_sim_exp_logged pk] := by
                rw [probEvent_map]
          _ = Pr[badPredLogged | direct_sim_exp_logged pk] := by
                rfl
      have sigStep_bad_eq_cacheHit :
          ∀ (pk : Stmt) (msg : M) (cache : spec.QueryCache) (keys : List (M × Commit)),
            Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                z.2.1.2 = true |
              ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] =
              Pr[fun cωπ : Commit × Chal × Resp =>
                (cache (.inr (msg, cωπ.1))).isSome = true |
                (simTranscript pk).liftComp spec] := by
        intro pk msg cache keys
        calc
          Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
              z.2.1.2 = true |
            ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] =
              Pr[fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true |
                ((_simImpl pk) (.inr msg)).run (cache, false)] := by
                calc
                  Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                      z.2.1.2 = true |
                    ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] =
                      Pr[((fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true) ∘
                        Prod.map id Prod.fst) |
                        ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] := by
                          rfl
                  _ = Pr[fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true |
                        Prod.map id Prod.fst <$>
                          ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] := by
                            exact
                              (probEvent_map
                                (mx := ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys))
                                (f := Prod.map id Prod.fst)
                                (q := fun z : (Commit × Resp) × (spec.QueryCache × Bool) =>
                                  z.2.2 = true)).symm
                  _ = Pr[fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true |
                        ((_simImpl pk) (.inr msg)).run (cache, false)] := by
                            rw [h_simImplLogged_proj pk (.inr msg) ((cache, false), keys)]
          _ = Pr[fun cωπ : Commit × Chal × Resp =>
                (cache (.inr (msg, cωπ.1))).isSome = true |
                  (simTranscript pk).liftComp spec] := by
                dsimp only [_simImpl, sigSimBad]
                simp only [QueryImpl.add_apply_inr]
                change Pr[fun z : (Commit × Resp) × spec.QueryCache × Bool => z.2.2 = true |
                    (fun vs : (Commit × Resp) × spec.QueryCache =>
                      (vs.1, vs.2, sigBadF msg cache vs.1)) <$> (sigSim pk msg).run cache] = _
                rw [probEvent_map, h_sigSim_run pk msg cache, bind_pure_comp, probEvent_map]
                congr with cωπ
                cases hcache : cache (.inr (msg, cωπ.1)) <;> simp [sigBadF, hcache]
      have keyCovers_cons :
          ∀ {cache : spec.QueryCache} {keys : List (M × Commit)} {mc : M × Commit},
            keyCovers ((cache, false), keys) →
              keyCovers ((cache, false), mc :: keys) := by
        intro cache keys mc hKeys mc' ω hcache
        exact List.mem_cons_of_mem _ (hKeys mc' ω hcache)
      have keyCovers_cacheQuery :
          ∀ {cache : spec.QueryCache} {keys : List (M × Commit)} {mc : M × Commit} {ω : Chal},
            keyCovers ((cache, false), keys) →
              keyCovers ((cache.cacheQuery (.inr mc) ω, false), mc :: keys) := by
        intro cache keys mc ω hKeys mc' ω' hcache'
        by_cases hmc : mc' = mc
        · subst hmc
          simp
        · have hne : (.inr mc' : spec.Domain) ≠ .inr mc := by
            intro h
            exact hmc (by simpa using h)
          have hcache : cache (.inr mc') = some ω' := by
            simpa [QueryCache.cacheQuery_of_ne _ _ hne] using hcache'
          exact List.mem_cons_of_mem _ (hKeys mc' ω' hcache)
      have sigStep_bad_le_keys :
          ∀ (pk : Stmt) (msg : M) (cache : spec.QueryCache) (keys : List (M × Commit)),
            keyCovers ((cache, false), keys) →
              Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                  z.2.1.2 = true |
                ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] ≤
                (keys.length : ENNReal) * β := by
        intro pk msg cache keys hKeys
        calc
          Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
              z.2.1.2 = true |
            ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] =
              Pr[fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true |
                ((_simImpl pk) (.inr msg)).run (cache, false)] := by
                calc
                  Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                      z.2.1.2 = true |
                    ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] =
                      Pr[((fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true) ∘
                        Prod.map id Prod.fst) |
                        ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] := by
                          rfl
                  _ = Pr[fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true |
                        Prod.map id Prod.fst <$>
                          ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] := by
                            exact
                              (probEvent_map
                                (mx := ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys))
                                (f := Prod.map id Prod.fst)
                                (q := fun z : (Commit × Resp) × (spec.QueryCache × Bool) =>
                                  z.2.2 = true)).symm
                  _ = Pr[fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true |
                        ((_simImpl pk) (.inr msg)).run (cache, false)] := by
                            rw [h_simImplLogged_proj pk (.inr msg) ((cache, false), keys)]
          _ = Pr[fun cωπ : Commit × Chal × Resp =>
                (cache (.inr (msg, cωπ.1))).isSome = true |
                  (simTranscript pk).liftComp spec] := by
                dsimp only [_simImpl, sigSimBad]
                simp only [QueryImpl.add_apply_inr]
                change Pr[fun z : (Commit × Resp) × spec.QueryCache × Bool => z.2.2 = true |
                    (fun vs : (Commit × Resp) × spec.QueryCache =>
                      (vs.1, vs.2, sigBadF msg cache vs.1)) <$> (sigSim pk msg).run cache] = _
                rw [probEvent_map, h_sigSim_run pk msg cache, bind_pure_comp, probEvent_map]
                congr with cωπ
                cases hcache : cache (.inr (msg, cωπ.1)) <;> simp [sigBadF, hcache]
          _ ≤ Pr[fun cωπ : Commit × Chal × Resp =>
                ∃ mc ∈ keys, mc.1 = msg ∧ mc.2 = cωπ.1 |
                  (simTranscript pk).liftComp spec] := by
                refine probEvent_mono ?_
                intro cωπ _ hhit
                cases hcache : cache (.inr (msg, cωπ.1)) with
                | none =>
                    simp [hcache] at hhit
                | some ω =>
                    refine ⟨(msg, cωπ.1), hKeys (msg, cωπ.1) ω hcache, rfl, rfl⟩
          _ ≤ (keys.length : ENNReal) * β := by
                classical
                have h_finset :
                    Pr[fun cωπ : Commit × Chal × Resp =>
                        ∃ mc ∈ keys.toFinset, mc.1 = msg ∧ mc.2 = cωπ.1 |
                        (simTranscript pk).liftComp spec] ≤
                      Finset.sum keys.toFinset (fun mc =>
                        Pr[fun cωπ : Commit × Chal × Resp =>
                            mc.1 = msg ∧ mc.2 = cωπ.1 |
                            (simTranscript pk).liftComp spec]) :=
                  probEvent_exists_finset_le_sum keys.toFinset
                    ((simTranscript pk).liftComp spec)
                    (fun mc cωπ => mc.1 = msg ∧ mc.2 = cωπ.1)
                refine le_trans ?_ (le_trans h_finset ?_)
                · refine probEvent_mono ?_
                  intro cωπ _ hcωπ
                  rcases hcωπ with ⟨mc, hmc, hmsg, hcommit⟩
                  exact ⟨mc, by simpa using List.mem_toFinset.mpr hmc, hmsg, hcommit⟩
                · calc
                    Finset.sum keys.toFinset (fun mc =>
                        Pr[fun cωπ : Commit × Chal × Resp =>
                            mc.1 = msg ∧ mc.2 = cωπ.1 |
                            (simTranscript pk).liftComp spec])
                        ≤ Finset.sum keys.toFinset (fun _ => β) := by
                              apply Finset.sum_le_sum
                              intro mc hmc
                              by_cases hmsg : mc.1 = msg
                              · rw [show
                                    (fun cωπ : Commit × Chal × Resp => mc.1 = msg ∧ mc.2 = cωπ.1) =
                                      (fun cωπ : Commit × Chal × Resp => cωπ.1 = mc.2) from by
                                        funext cωπ; simp [hmsg, eq_comm]]
                                rw [probEvent_liftComp]
                                have hmapCommit :
                                    Pr[fun cωπ : Commit × Chal × Resp => cωπ.1 = mc.2 |
                                      simTranscript pk] =
                                      Pr[fun c : Commit => c = mc.2 |
                                        Prod.fst <$> simTranscript pk] :=
                                  (probEvent_map (mx := simTranscript pk) (f := Prod.fst)
                                    (q := fun c : Commit => c = mc.2)).symm
                                rw [hmapCommit, probEvent_eq_eq_probOutput]
                                exact _hPredSim pk mc.2
                              · have hzero :
                                  Pr[fun cωπ : Commit × Chal × Resp =>
                                      mc.1 = msg ∧ mc.2 = cωπ.1 |
                                      (simTranscript pk).liftComp spec] = 0 := by
                                    refine probEvent_eq_zero ?_
                                    intro cωπ _ hcωπ
                                    simp [hmsg] at hcωπ
                                rw [hzero]
                                exact zero_le _
                    _ = (keys.toFinset.card : ENNReal) * β := by
                          rw [Finset.sum_const, nsmul_eq_mul]
                    _ ≤ (keys.length : ENNReal) * β := by
                          gcongr
                          exact_mod_cast List.toFinset_card_le keys
      -- (A) `bridge_real_freshness`: bridge `adv.advantage` to the augmented `direct_real_exp`.
      --
      -- Three slacks are absorbed here (β-parametric):
      --   * `qS · (qS + qH) · β`: FS-vs-`realSign` swap bad event, using the sim-side commit
      --     predictability bound `β` on the real side *via HVZK-transport*. The actual
      --     `FiatShamir.sign` queries the live RO at `(msg, c)` (cached if already present),
      --     while `realSignSigned'` samples a fresh challenge from `realTranscript pk sk`
      --     and programs `(msg, c) ↦ chSampled` on a cache miss. They are identical until a
      --     cache hit at `(msg, c)` during signing. Per query bad probability ≤
      --     (cache size) · β_real ≤ (cache size) · β, summed over `qS` queries.
      --   * `qS · (qS + qH) · ζ_zk`: HVZK-transport correction for the real-side
      --     predictability. The gap `β_real - β ≤ ζ_zk` (from HVZK's TV bound
      --     `|Pr_real[commit = c₀] - Pr_sim[commit = c₀]| ≤ ζ_zk`) summed over the same
      --     `qS · (qS + qH)` union-bound points contributes exactly this term.
      --   * `δ_verify`: cache-miss verify slack. `unforgeableExp` queries the live RO when
      --     verifying the forgery, sampling a fresh ω on a cache miss. The theorem assumption
      --     `σ.verifyChallengePredictability δ_verify` bounds the chance that such a fresh
      --     challenge accepts any fixed `(commit, response)` pair. The augmented event
      --     `event pk` only counts cache hits, so this slack is added explicitly.
      --
      -- The `signed` list in the augmented state mirrors the WriterT log used in
      -- `unforgeableExp`: each signing query prepends `msg`, so `¬msg ∈ signed` matches
      -- `¬log.wasQueried msg`.
      have bridge_real_freshness :
          adv.advantage (runtime M) ≤
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) +
              (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β +
              ENNReal.ofReal ((qS * (qS + qH) : ℕ) * ζ_zk) +
              δ_verify := by
        letI : DecidableEq (Commit × Resp) := Classical.decEq _
        let fsAlg : SignatureAlg (OracleComp spec) M Stmt Wit (Commit × Resp) :=
          FiatShamir (m := OracleComp spec) σ hr M
        let actual_pk_game : Stmt → Wit → OracleComp spec Bool := by
          letI : DecidableEq M := Classical.decEq _
          exact fun pk sk => do
            let impl : QueryImpl (spec + (M →ₒ (Commit × Resp)))
                (WriterT (QueryLog (M →ₒ (Commit × Resp))) (OracleComp spec)) :=
              (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
                (WriterT (QueryLog (M →ₒ (Commit × Resp))) (OracleComp spec)) +
                SignatureAlg.signingOracle fsAlg pk sk
            let sim_adv : WriterT (QueryLog (M →ₒ (Commit × Resp))) (OracleComp spec)
                (M × (Commit × Resp)) :=
              simulateQ impl (adv.main pk)
            let ((msg, sig), log) ← sim_adv.run
            let verified ← fsAlg.verify pk msg sig
            pure (!log.wasQueried msg && verified)
        let actualBaseAppend : QueryImpl spec (StateT (List M) (OracleComp spec)) :=
          (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
        let actualSignAppend : Stmt → Wit → QueryImpl (M →ₒ (Commit × Resp))
            (StateT (List M) (OracleComp spec)) := fun pk sk msg => do
          let signed ← get
          let sig ← liftM (fsAlg.sign pk sk msg)
          set (signed ++ [msg])
          pure sig
        let actualImplAppend : Stmt → Wit → QueryImpl (spec + (M →ₒ (Commit × Resp)))
            (StateT (List M) (OracleComp spec)) := fun pk sk =>
          actualBaseAppend + actualSignAppend pk sk
        let actualSignSignedAppend : Stmt → Wit → QueryImpl (M →ₒ (Commit × Resp))
            (StateT (spec.QueryCache × List M) (OracleComp spec)) := fun pk sk msg => do
          let s ← get
          let v ← (simulateQ baseSim (fsAlg.sign pk sk msg)).run s.1
          set (v.2, s.2 ++ [msg])
          pure v.1
        let actualImplSignedAppend : Stmt → Wit → QueryImpl (spec + (M →ₒ (Commit × Resp)))
            (StateT (spec.QueryCache × List M) (OracleComp spec)) := fun pk sk =>
          baseSimSigned' + actualSignSignedAppend pk sk
        have h_actual_append_stateful :
            ∀ (pk : Stmt) (sk : Wit) {α : Type}
              (oa : OracleComp (spec + (M →ₒ (Commit × Resp))) α)
              (cache : spec.QueryCache) (signed : List M),
              (fun z : (α × List M) × spec.QueryCache => (z.1.1, (z.2, z.1.2))) <$>
                (simulateQ baseSim ((simulateQ (actualImplAppend pk sk) oa).run signed)).run cache =
              (simulateQ (actualImplSignedAppend pk sk) oa).run (cache, signed) := by
          intro pk sk α oa cache signed
          induction oa using OracleComp.inductionOn generalizing cache signed with
          | pure x =>
              simp [actualImplAppend, actualImplSignedAppend]
          | query_bind t oa ih =>
              cases t with
              | inl t' =>
                  simp [actualImplAppend, actualImplSignedAppend, actualBaseAppend,
                    baseSimSigned', QueryImpl.add_apply_inl, ih]
              | inr msg =>
                  simp [actualImplAppend, actualImplSignedAppend, actualSignAppend,
                    actualSignSignedAppend, QueryImpl.add_apply_inr, StateT.run_bind,
                    StateT.run_get, StateT.run_set, simulateQ_bind]
                  refine bind_congr fun a => ?_
                  simpa using ih a.1 a.2 (signed ++ [msg])
        let actual_pk_game_append : Stmt → Wit → OracleComp spec Bool := by
          letI : DecidableEq M := Classical.decEq _
          exact fun pk sk => do
            let sim_adv : StateT (List M) (OracleComp spec) (M × (Commit × Resp)) :=
              simulateQ (actualImplAppend pk sk) (adv.main pk)
            let ((msg, sig), signed) ← sim_adv.run []
            let verified ← fsAlg.verify pk msg sig
            pure (decide (msg ∉ signed) && verified)
        have h_actual_append_eq : ∀ pk sk, actual_pk_game pk sk = actual_pk_game_append pk sk := by
          intro pk sk
          letI : DecidableEq M := Classical.decEq _
          have hlogged_append :
              (fun z : (M × (Commit × Resp)) × QueryLog (M →ₒ (Commit × Resp)) =>
                  (z.1, z.2.map (fun e => e.1))) <$>
                (simulateQ
                  ((HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
                    (WriterT (QueryLog (M →ₒ (Commit × Resp))) (OracleComp spec)) +
                    SignatureAlg.signingOracle fsAlg pk sk)
                  (adv.main pk)).run =
                (simulateQ (actualImplAppend pk sk) (adv.main pk)).run [] := by
            simpa [actualImplAppend, actualBaseAppend, actualSignAppend] using
              (map_run_withLogging_inputs_eq_run_signedAppend
                (M := M) (spec := spec) (sign := fsAlg.sign pk sk) (oa := adv.main pk) [])
          calc
            actual_pk_game pk sk =
                (do
                  let ((msg, sig), signed) ←
                    (fun z : (M × (Commit × Resp)) × QueryLog (M →ₒ (Commit × Resp)) =>
                      (z.1, z.2.map (fun e => e.1))) <$>
                        (simulateQ
                          ((HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
                            (WriterT (QueryLog (M →ₒ (Commit × Resp))) (OracleComp spec)) +
                            SignatureAlg.signingOracle fsAlg pk sk)
                          (adv.main pk)).run
                  let verified ← fsAlg.verify pk msg sig
                  pure (decide (msg ∉ signed) && verified)) := by
                    simp [actual_pk_game, wasQueried_eq_decide_mem_map_fst]
            _ = actual_pk_game_append pk sk := by
                  rw [hlogged_append]
        let roProb : QueryImpl (M × Commit →ₒ Chal) (StateT spec.QueryCache ProbComp) := fun mc => do
          let cache ← get
          match cache (.inr mc) with
          | some v => pure v
          | none =>
              let v ← ($ᵗ Chal : ProbComp Chal)
              modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
        let baseProb : QueryImpl spec (StateT spec.QueryCache ProbComp) :=
          (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT spec.QueryCache ProbComp) +
            roProb
        have hlift : ∀ {α : Type} (x : ProbComp α) (s : spec.QueryCache),
            (liftM x : StateT spec.QueryCache ProbComp α).run s = x >>= fun a => pure (a, s) := by
          intro α x s
          simpa using (StateT.run_liftM x s)
        have hmod : ∀ {α : Type}
            (f : spec.QueryCache → α × spec.QueryCache) (s : spec.QueryCache),
            (modifyGet f : StateT spec.QueryCache ProbComp α).run s = pure (f s) := by
          intro α f s
          simp only [modifyGet, MonadState.modifyGet,
            MonadStateOf.modifyGet, StateT.modifyGet, StateT.run]
        have h_roProb_run_miss :
            ∀ (mc : M × Commit) (cache : spec.QueryCache),
              cache (Sum.inr mc) = none →
                (roProb mc).run cache =
                  (fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$> ($ᵗ Chal : ProbComp Chal) := by
          intro mc cache hmc
          simp [roProb, hmc, StateT.run_bind, StateT.run_get, pure_bind,
            hlift, hmod, bind_assoc, bind_pure_comp]
          rfl
        have h_roProb_run_hit :
            ∀ (mc : M × Commit) (cache : spec.QueryCache) (u : Chal),
              cache (Sum.inr mc) = some u → (roProb mc).run cache = pure (u, cache) := by
          intro mc cache u hmc
          simp [roProb, hmc]
        have h_baseSim_step :
            ∀ (t : spec.Domain) (cache : spec.QueryCache),
              evalDist ((baseSim t).run cache) = evalDist ((baseProb t).run cache) := by
          intro t cache
          cases t with
          | inl n =>
              change evalDist
                  ((simulateQ unifSim (unifSpec.query n : ProbComp (Fin (n + 1)))).run cache) =
                evalDist ((baseProb (.inl n)).run cache)
              rw [run_unifSim cache (oa := (unifSpec.query n : ProbComp (Fin (n + 1))))]
              have h_baseProb_inl :
                  (baseProb (.inl n)).run cache =
                    (fun x => (x, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
                change
                    (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
                      StateT spec.QueryCache ProbComp (Fin (n + 1))).run cache =
                  (fun x => (x, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
                rw [hlift]
                simp [bind_pure_comp]
              rw [h_baseProb_inl]
              show
                  evalDist ((fun x => (x, cache)) <$> ((unifSpec.query n : ProbComp (Fin (n + 1))).liftComp spec)) =
                    evalDist ((fun x => (x, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))))
              exact
                evalDist_map_eq_of_evalDist_eq
                  (mx := ((unifSpec.query n : ProbComp (Fin (n + 1))).liftComp spec))
                  (my := (unifSpec.query n : ProbComp (Fin (n + 1))))
                  (f := fun x => (x, cache))
                  (OracleComp.evalDist_liftComp (spec := unifSpec) (superSpec := spec)
                    (mx := (unifSpec.query n : ProbComp (Fin (n + 1)))))
          | inr mc =>
              cases hmc : cache (.inr mc) with
              | none =>
                  change evalDist ((roSim mc).run cache) = evalDist ((baseProb (.inr mc)).run cache)
                  rw [h_roSim_run_miss mc cache hmc]
                  have h_baseProb_miss :
                      (baseProb (.inr mc)).run cache =
                        (fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$> ($ᵗ Chal : ProbComp Chal) := by
                      simpa [baseProb, QueryImpl.add_apply_inr] using h_roProb_run_miss mc cache hmc
                  rw [h_baseProb_miss]
                  let f : Chal → Chal × spec.QueryCache := fun u =>
                    (u, cache.cacheQuery (Sum.inr mc) u)
                  have h_hash_eval :
                      (evalDist ($ᵗ Chal : ProbComp Chal) : SPMF Chal) =
                        (evalDist
                          ((liftM (query (Sum.inr mc) : OracleQuery spec Chal)) :
                            OracleComp spec Chal) : SPMF Chal) := by
                    have h_query :
                        (evalDist
                          ((liftM (query (Sum.inr mc) : OracleQuery spec Chal)) :
                            OracleComp spec Chal) : SPMF Chal) =
                          (liftM (PMF.uniformOfFintype Chal) : SPMF Chal) := by
                      change (liftM (PMF.map id (PMF.uniformOfFintype (spec.Range (Sum.inr mc)))) :
                          SPMF Chal) = (liftM (PMF.uniformOfFintype Chal) : SPMF Chal)
                      rw [PMF.map_id]
                      rfl
                    have h_uniform :
                        (evalDist ($ᵗ Chal : ProbComp Chal) : SPMF Chal) =
                          (liftM (PMF.uniformOfFintype Chal) : SPMF Chal) := by
                      simpa [evalDist_uniformSample]
                    exact h_uniform.trans h_query.symm
                  have h_left_map :
                      evalDist
                        (((fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$>
                          ((liftM (query (Sum.inr mc) : OracleQuery spec Chal)) :
                            OracleComp spec Chal)) :
                          OracleComp spec (Chal × spec.QueryCache)) =
                        ((fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$>
                          (evalDist
                            ((liftM (query (Sum.inr mc) : OracleQuery spec Chal)) :
                              OracleComp spec Chal) : SPMF Chal) :
                          SPMF (Chal × spec.QueryCache)) := by
                    simpa [evalDist_map]
                  have h_right_map :
                      evalDist
                        (((fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$> ($ᵗ Chal : ProbComp Chal)) :
                          ProbComp (Chal × spec.QueryCache)) =
                        ((fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$>
                          (evalDist ($ᵗ Chal : ProbComp Chal) : SPMF Chal) :
                          SPMF (Chal × spec.QueryCache)) := by
                    simpa [evalDist_map]
                  calc
                    evalDist
                        (((fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$>
                          ((liftM (query (Sum.inr mc) : OracleQuery spec Chal)) :
                            OracleComp spec Chal)) :
                          OracleComp spec (Chal × spec.QueryCache)) =
                        ((fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$>
                          (evalDist
                            ((liftM (query (Sum.inr mc) : OracleQuery spec Chal)) :
                              OracleComp spec Chal) : SPMF Chal) :
                          SPMF (Chal × spec.QueryCache)) := h_left_map
                    _ =
                        ((fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$>
                          (evalDist ($ᵗ Chal : ProbComp Chal) : SPMF Chal) :
                          SPMF (Chal × spec.QueryCache)) := by
                            exact congrArg
                              (fun p : SPMF Chal =>
                                ((fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$> p :
                                  SPMF (Chal × spec.QueryCache)))
                              h_hash_eval.symm
                    _ =
                        evalDist
                          (((fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$> ($ᵗ Chal : ProbComp Chal)) :
                            ProbComp (Chal × spec.QueryCache)) := h_right_map.symm
              | some u =>
                  change evalDist ((roSim mc).run cache) = evalDist ((baseProb (.inr mc)).run cache)
                  rw [h_roSim_run_hit mc cache u hmc]
                  have h_baseProb_hit :
                      (baseProb (.inr mc)).run cache = pure (u, cache) := by
                      simpa [baseProb, QueryImpl.add_apply_inr] using
                        h_roProb_run_hit mc cache u hmc
                  rw [h_baseProb_hit]
                  rfl
        have h_evalDist_run_baseSim :
            ∀ (cache : spec.QueryCache) {α : Type} (oa : OracleComp spec α),
              evalDist ((simulateQ baseSim oa).run cache) =
                evalDist ((simulateQ baseProb oa).run cache) := by
          intro cache α oa
          induction oa using OracleComp.inductionOn generalizing cache with
          | pure x =>
              simp
          | query_bind t oa ih =>
              simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
                OracleQuery.cont_query, id_map, StateT.run_bind, evalDist_bind]
              rw [h_baseSim_step t cache]
              refine bind_congr fun x => ?_
              simpa using ih x.1 x.2
        have h_evalDist_run'_baseSim :
            ∀ (cache : spec.QueryCache) {α : Type} (oa : OracleComp spec α),
              evalDist ((simulateQ baseSim oa).run' cache) =
                evalDist ((simulateQ baseProb oa).run' cache) := by
          intro cache α oa
          have hrun := h_evalDist_run_baseSim cache (oa := oa)
          have hmap := congrArg (fun p => Prod.fst <$> p) hrun
          simpa [StateT.run'] using hmap
        let cacheProj : spec.QueryCache → (M × Commit →ₒ Chal).QueryCache := fun cache mc =>
          cache (.inr mc)
        let runtimeRo :
            QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := randomOracle
        let runtimeImpl :
            QueryImpl spec (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
          unifFwdImpl (M × Commit →ₒ Chal) + runtimeRo
        have hliftRuntime : ∀ {α : Type} (x : ProbComp α) (s : (M × Commit →ₒ Chal).QueryCache),
            (liftM x : StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp α).run s =
              x >>= fun a => pure (a, s) := by
          intro α x s
          simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.run_lift]
        have hmodRuntime : ∀ {α : Type}
            (f : (M × Commit →ₒ Chal).QueryCache →
              α × (M × Commit →ₒ Chal).QueryCache)
            (s : (M × Commit →ₒ Chal).QueryCache),
            (modifyGet f : StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp α).run s =
              pure (f s) := by
          intro α f s
          simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, StateT.run]
        have h_baseProb_proj :
            ∀ (t : spec.Domain) (cache : spec.QueryCache),
              Prod.map id cacheProj <$> (baseProb t).run cache =
                (runtimeImpl t).run (cacheProj cache) := by
          intro t cache
          cases t with
          | inl n =>
              have h_baseProb_inl :
                  (baseProb (.inl n)).run cache =
                    (fun x => (x, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
                change
                    (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
                      StateT spec.QueryCache ProbComp (Fin (n + 1))).run cache =
                  (fun x => (x, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
                rw [hlift]
                simp [bind_pure_comp]
              have h_runtime_inl :
                  (runtimeImpl (.inl n)).run (cacheProj cache) =
                    (fun x => (x, cacheProj cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
                simp [runtimeImpl, QueryImpl.add_apply_inl, unifFwdImpl,
                  QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
                change
                    (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
                      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Fin (n + 1))).run
                      (cacheProj cache) =
                  (fun x => (x, cacheProj cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
                rw [hliftRuntime]
                simp [bind_pure_comp]
              rw [h_baseProb_inl, h_runtime_inl]
              simpa [Functor.map_map, cacheProj, Function.comp_def]
          | inr mc =>
              cases hmc : cache (.inr mc) with
              | none =>
                  have h_baseProb_miss :
                      (baseProb (.inr mc)).run cache =
                        (fun u => (u, cache.cacheQuery (Sum.inr mc) u)) <$> ($ᵗ Chal : ProbComp Chal) := by
                    simpa [baseProb, QueryImpl.add_apply_inr] using h_roProb_run_miss mc cache hmc
                  have hproj : (cacheProj cache) mc = none := by
                    simpa [cacheProj] using hmc
                  have h_runtime_miss :
                      (runtimeImpl (.inr mc)).run (cacheProj cache) =
                        (fun u => (u, cacheProj (cache.cacheQuery (Sum.inr mc) u))) <$>
                          ($ᵗ Chal : ProbComp Chal) := by
                    let insert : Chal → Chal × (M × Commit →ₒ Chal).QueryCache := fun u =>
                      (u, (cacheProj cache).cacheQuery mc u)
                    have h_random_miss :
                        (runtimeRo mc).run (cacheProj cache) =
                          insert <$> ($ᵗ Chal : ProbComp Chal) := by
                      simpa [runtimeRo, randomOracle.apply_eq, StateT.run_bind, StateT.run_get, hproj,
                        StateT.run_pure, hliftRuntime, hmodRuntime, bind_assoc, bind_pure_comp,
                        uniformSampleImpl, insert]
                    have hinsert_proj :
                        insert = fun u => (u, cacheProj (cache.cacheQuery (Sum.inr mc) u)) := by
                      funext u
                      apply Prod.ext
                      · rfl
                      · funext mc'
                        by_cases h' : mc' = mc
                        · subst h'
                          simp [insert, cacheProj, QueryCache.cacheQuery]
                          rfl
                        · simp [insert, cacheProj, QueryCache.cacheQuery, h']
                    have hinsert_map :
                        insert <$> ($ᵗ Chal : ProbComp Chal) =
                          (fun u => (u, cacheProj (cache.cacheQuery (Sum.inr mc) u))) <$>
                            ($ᵗ Chal : ProbComp Chal) := by
                      simpa [Functor.map_map, Function.comp_def] using
                        congrArg (fun f => f <$> ($ᵗ Chal : ProbComp Chal)) hinsert_proj
                    have h_runtime_miss0 :
                        (runtimeImpl (.inr mc)).run (cacheProj cache) =
                          insert <$> ($ᵗ Chal : ProbComp Chal) := by
                      simpa [runtimeImpl, QueryImpl.add_apply_inr] using h_random_miss
                    exact h_runtime_miss0.trans hinsert_map
                  rw [h_baseProb_miss, h_runtime_miss]
                  simpa [Functor.map_map, Function.comp_def]
              | some u =>
                  have h_baseProb_hit :
                      (baseProb (.inr mc)).run cache = pure (u, cache) := by
                    simpa [baseProb, QueryImpl.add_apply_inr] using h_roProb_run_hit mc cache u hmc
                  have hproj : (cacheProj cache) mc = some u := by
                    simpa [cacheProj] using hmc
                  have h_runtime_hit :
                      (runtimeImpl (.inr mc)).run (cacheProj cache) = pure (u, cacheProj cache) := by
                    have h_random_hit :
                        (runtimeRo mc).run (cacheProj cache) = pure (u, cacheProj cache) := by
                      simp [runtimeRo, randomOracle.apply_eq, StateT.run_bind, StateT.run_get, hproj,
                        StateT.run_pure, uniformSampleImpl]
                      rfl
                    simpa [runtimeImpl, QueryImpl.add_apply_inr] using h_random_hit
                  rw [h_baseProb_hit, h_runtime_hit]
                  rfl
        have h_runtimeImpl_run' :
            ∀ (cache : spec.QueryCache) {α : Type} (oa : OracleComp spec α),
              (simulateQ baseProb oa).run' cache =
                (simulateQ runtimeImpl oa).run' (cacheProj cache) := by
          intro cache α oa
          exact OracleComp.run'_simulateQ_eq_of_query_map_eq
            baseProb runtimeImpl cacheProj h_baseProb_proj oa cache
        have h_runtime_evalDist_eq_baseSim :
            ∀ {α : Type} (oa : OracleComp spec α),
              (runtime M).evalDist oa = evalDist ((simulateQ baseSim oa).run' ∅) := by
          intro α oa
          rw [runtime_eq_runtimeWithCache_empty]
          let runtimeRoClassical :
              QueryImpl (M × Commit →ₒ Chal)
                (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
            @randomOracle (M × Commit)
              (fun a b =>
                @instDecidableEqProd M Commit
                  (fun a b => Classical.propDecidable (a = b))
                  (fun a b => Classical.propDecidable (a = b)) a b)
              (ofFn fun _ => Chal) (fun _ => inferInstance)
          let runtimeImplClassical :
              QueryImpl (unifSpec + (M × Commit →ₒ Chal))
                (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
            unifFwdImpl (M × Commit →ₒ Chal) + runtimeRoClassical
          have h_runtimeRo_classical_eq :
              ∀ (mc : M × Commit) (cache : (M × Commit →ₒ Chal).QueryCache),
                (runtimeRoClassical mc).run cache = (runtimeRo mc).run cache := by
            intro mc cache
            cases hmc : cache mc with
            | none =>
                let insertClassical : Chal → Chal × (M × Commit →ₒ Chal).QueryCache := fun u =>
                  (u,
                    @QueryCache.cacheQuery (M × Commit) (ofFn fun _ => Chal)
                      (fun a b =>
                        @instDecidableEqProd M Commit
                          (fun a b => Classical.propDecidable (a = b))
                          (fun a b => Classical.propDecidable (a = b)) a b)
                      cache mc u)
                let insertNative : Chal → Chal × (M × Commit →ₒ Chal).QueryCache := fun u =>
                  (u, cache.cacheQuery mc u)
                have h_insert_eq : insertClassical = insertNative := by
                  funext u
                  apply Prod.ext
                  · rfl
                  · funext mc'
                    by_cases h : mc' = mc
                    · subst h
                      simp [insertClassical, insertNative, QueryCache.cacheQuery_self]
                    · simp [insertClassical, insertNative, QueryCache.cacheQuery_of_ne, h]
                have h_classical_miss :
                    (runtimeRoClassical mc).run cache =
                      insertClassical <$> ($ᵗ Chal : ProbComp Chal) := by
                  change
                    (runtimeRoClassical mc).run cache =
                      insertClassical <$>
                        ($ᵗ ((M × Commit →ₒ Chal).Range mc) :
                          ProbComp ((M × Commit →ₒ Chal).Range mc))
                  simp [runtimeRoClassical, StateT.run_bind, StateT.run_get, hmc,
                    uniformSampleImpl, insertClassical]
                have h_native_miss :
                    (runtimeRo mc).run cache = insertNative <$> ($ᵗ Chal : ProbComp Chal) := by
                  let insertRuntime : Chal → Chal × (M × Commit →ₒ Chal).QueryCache := fun u =>
                    (u, @QueryCache.cacheQuery (M × Commit) (ofFn fun _ => Chal)
                      (fun a b => instDecidableEqProd a b) cache mc u)
                  have h_insert_runtime_eq : insertRuntime = insertNative := by
                    funext u
                    apply Prod.ext
                    · rfl
                    · funext mc'
                      by_cases h : mc' = mc
                      · subst h
                        simp [insertRuntime, insertNative, QueryCache.cacheQuery_self]
                      · simp [insertRuntime, insertNative, QueryCache.cacheQuery_of_ne, h]
                  have h_native_miss_raw :
                      (runtimeRo mc).run cache =
                        insertRuntime <$>
                          ($ᵗ ((M × Commit →ₒ Chal).Range mc) :
                            ProbComp ((M × Commit →ₒ Chal).Range mc)) := by
                    change
                      (runtimeRo mc).run cache =
                        insertRuntime <$>
                          ($ᵗ ((M × Commit →ₒ Chal).Range mc) :
                            ProbComp ((M × Commit →ₒ Chal).Range mc))
                    simp [runtimeRo, StateT.run_bind, StateT.run_get, hmc, uniformSampleImpl,
                      insertRuntime]
                  calc
                    (runtimeRo mc).run cache =
                        insertRuntime <$> ($ᵗ Chal : ProbComp Chal) := by
                          simpa using h_native_miss_raw
                    _ = insertNative <$> ($ᵗ Chal : ProbComp Chal) := by rw [h_insert_runtime_eq]
                calc
                  (runtimeRoClassical mc).run cache =
                      insertClassical <$> ($ᵗ Chal : ProbComp Chal) := h_classical_miss
                  _ = insertNative <$> ($ᵗ Chal : ProbComp Chal) := by rw [h_insert_eq]
                  _ = (runtimeRo mc).run cache := h_native_miss.symm
            | some u =>
                have h_classical_hit :
                    (runtimeRoClassical mc).run cache = pure (u, cache) := by
                  simp [runtimeRoClassical, StateT.run_bind, StateT.run_get, hmc, uniformSampleImpl]
                have h_native_hit :
                    (runtimeRo mc).run cache = pure (u, cache) := by
                  simp [runtimeRo, StateT.run_bind, StateT.run_get, hmc, uniformSampleImpl]
                exact h_classical_hit.trans h_native_hit.symm
          have h_runtimeImpl_classical_eq :
              ∀ (t : spec.Domain) (cache : (M × Commit →ₒ Chal).QueryCache),
                Prod.map id id <$> (runtimeImplClassical t).run cache =
                  (runtimeImpl t).run cache := by
            intro t cache
            cases t with
            | inl n =>
                have h_classical_inl :
                    (runtimeImplClassical (.inl n)).run cache =
                      (fun x => (x, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
                  simp [runtimeImplClassical, QueryImpl.add_apply_inl, unifFwdImpl,
                    QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
                have h_native_inl :
                    (runtimeImpl (.inl n)).run cache =
                      (fun x => (x, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
                  simp [runtimeImpl, QueryImpl.add_apply_inl, unifFwdImpl,
                    QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
                  change
                    (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
                      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp (Fin (n + 1))).run cache =
                      (fun x => (x, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
                  rw [hliftRuntime]
                  simp [bind_pure_comp]
                rw [h_classical_inl, h_native_inl]
                simp
            | inr mc =>
                simpa [runtimeImplClassical, runtimeImpl, QueryImpl.add_apply_inr] using
                  h_runtimeRo_classical_eq mc cache
          have hruntime :
              (runtimeWithCache M ∅).evalDist oa =
                evalDist ((simulateQ runtimeImpl oa).run' (∅ : (M × Commit →ₒ Chal).QueryCache)) := by
            letI : DecidableEq (M × Commit) := Classical.decEq _
            have h_unif_toQueryImpl :
                (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) =
                  QueryImpl.ofLift unifSpec ProbComp := by
              funext t
              rw [HasQuery.toQueryImpl_apply, HasQuery.instOfMonadLift_query,
                QueryImpl.ofLift_apply]
            have hrunClassical :
                (simulateQ runtimeImplClassical oa).run'
                    (∅ : (M × Commit →ₒ Chal).QueryCache) =
                  (simulateQ runtimeImpl oa).run' (∅ : (M × Commit →ₒ Chal).QueryCache) := by
              simpa using
                (OracleComp.run'_simulateQ_eq_of_query_map_eq
                  runtimeImplClassical runtimeImpl id h_runtimeImpl_classical_eq oa
                  (∅ : (M × Commit →ₒ Chal).QueryCache))
            simpa [runtimeWithCache, ProbCompRuntime.evalDist, SPMFSemantics.evalDist,
              SemanticsVia.denote, SPMFSemantics.withStateOracle, runtimeImplClassical,
              runtimeRoClassical, runtimeImpl, runtimeRo, unifFwdImpl, h_unif_toQueryImpl,
              QueryImpl.ofLift_eq_id', StateT.run'_eq, evalDist_def] using
              congrArg (fun p => evalDist p) hrunClassical
          rw [hruntime]
          have hcache_empty : cacheProj (∅ : spec.QueryCache) = ∅ := by
            funext mc
            rfl
          have hrunEmpty :
              (simulateQ baseProb oa).run' (∅ : spec.QueryCache) =
                (simulateQ runtimeImpl oa).run' (∅ : (M × Commit →ₒ Chal).QueryCache) := by
            simpa [hcache_empty] using
              (h_runtimeImpl_run' (cache := (∅ : spec.QueryCache)) (oa := oa))
          rw [← hrunEmpty]
          rw [← h_evalDist_run'_baseSim (cache := (∅ : spec.QueryCache)) (oa := oa)]
        let actual_pk_exp : Stmt → Wit → SPMF Bool := fun pk sk =>
          (runtime M).evalDist (actual_pk_game pk sk)
        have hAdv_eq_tsum_actual :
            adv.advantage (runtime M) =
              ∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[= true | actual_pk_exp pksk.1 pksk.2] := by
          have hExp :
              SignatureAlg.unforgeableExp (sigAlg := fsAlg) (runtime M) adv =
                evalDist hr.gen >>= fun pksk => actual_pk_exp pksk.1 pksk.2 := by
            simpa only [SignatureAlg.unforgeableExp, actual_pk_exp, actual_pk_game, fsAlg,
              FiatShamir, SignatureAlg.signingOracle, MonadLiftT.monadLift,
              MonadLift.monadLift, liftComp_eq_liftM] using
              (runtime_evalDist_bind_liftComp (M := M) (oa := hr.gen)
                (rest := fun pksk => actual_pk_game pksk.1 pksk.2))
          unfold SignatureAlg.unforgeableAdv.advantage
          rw [hExp, probOutput_bind_eq_tsum]
          refine tsum_congr fun pksk => ?_
          rfl
        classical
        let actualSignBadAppend : Stmt → Wit → QueryImpl (M →ₒ (Commit × Resp))
            (StateT ((spec.QueryCache × List M) × Bool) (OracleComp spec)) := fun pk sk =>
          (actualSignSignedAppend pk sk).withBadUpdate sigBadFSigned
        let actualImplBadAppend : Stmt → Wit → QueryImpl (spec + (M →ₒ (Commit × Resp)))
            (StateT ((spec.QueryCache × List M) × Bool) (OracleComp spec)) := fun pk sk =>
          baseSimSigned + actualSignBadAppend pk sk
        let direct_actual_exp_append : Stmt → Wit → OracleComp spec
            ((M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool) := fun pk sk =>
          (simulateQ (actualImplBadAppend pk sk) (adv.main pk)).run ((∅, []), false)
        let actual_stateful_exp_append : Stmt → Wit → OracleComp spec
            ((M × (Commit × Resp)) × (spec.QueryCache × List M)) := fun pk sk =>
          (simulateQ (actualImplSignedAppend pk sk) (adv.main pk)).run (∅, [])
        let realSignSignedAppend : Stmt → Wit → QueryImpl (M →ₒ (Commit × Resp))
            (StateT (spec.QueryCache × List M) (OracleComp spec)) := fun pk sk msg => do
          let s ← get
          let v ← (realSign pk sk msg).run s.1
          set (v.2, s.2 ++ [msg])
          pure v.1
        let realSignBadAppend : Stmt → Wit → QueryImpl (M →ₒ (Commit × Resp))
            (StateT ((spec.QueryCache × List M) × Bool) (OracleComp spec)) := fun pk sk =>
          (realSignSignedAppend pk sk).withBadUpdate sigBadFSigned
        let realImplBadAppend : Stmt → Wit → QueryImpl (spec + (M →ₒ (Commit × Resp)))
            (StateT ((spec.QueryCache × List M) × Bool) (OracleComp spec)) := fun pk sk =>
          baseSimSigned + realSignBadAppend pk sk
        let direct_real_exp_append : Stmt → Wit → OracleComp spec
            ((M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool) := fun pk sk =>
          (simulateQ (realImplBadAppend pk sk) (adv.main pk)).run ((∅, []), false)
        let direct_real_exp_simple : Stmt → Wit → OracleComp spec
            ((M × (Commit × Resp)) × (spec.QueryCache × Bool)) := fun pk sk =>
          (simulateQ (_realImpl pk sk) (adv.main pk)).run (∅, false)
        let eventNoBad : Stmt →
            ((M × (Commit × Resp)) × (spec.QueryCache × List M)) → Prop :=
          fun pk z =>
            (∃ ω, z.2.1 (.inr (z.1.1, z.1.2.1)) = some ω ∧
              σ.verify pk z.1.2.1 ω z.1.2.2 = true) ∧
            ¬ z.1.1 ∈ z.2.2
        let reverseSigned : ((spec.QueryCache × List M) × Bool) →
            ((spec.QueryCache × List M) × Bool) :=
          fun s => ((s.1.1, s.1.2.reverse), s.2)
        let verifyFromState : Stmt →
            ((M × (Commit × Resp)) × (spec.QueryCache × List M)) → OracleComp spec Bool :=
          fun pk z => do
            match z.2.1 (.inr (z.1.1, z.1.2.1)) with
            | some ω => pure (decide (z.1.1 ∉ z.2.2) && σ.verify pk z.1.2.1 ω z.1.2.2)
            | none =>
                let ω ←
                  (liftM (query (Sum.inr (z.1.1, z.1.2.1)) : OracleQuery spec Chal) :
                    OracleComp spec Chal)
                pure (decide (z.1.1 ∉ z.2.2) && σ.verify pk z.1.2.1 ω z.1.2.2)
        have h_actual_pk_exp_stateful : ∀ (pk : Stmt) (sk : Wit),
            actual_pk_exp pk sk =
              evalDist (actual_stateful_exp_append pk sk >>= verifyFromState pk) := by
          intro pk sk
          simp [actual_pk_exp, h_actual_append_eq pk sk]
          rw [← runtime_eq_runtimeWithCache_empty (M := M)]
          rw [h_runtime_evalDist_eq_baseSim (oa := actual_pk_game_append pk sk)]
          have h_prefix :
              (fun z : ((M × (Commit × Resp)) × List M) × spec.QueryCache =>
                (z.1.1, (z.2, z.1.2))) <$>
                  (simulateQ baseSim
                    ((simulateQ (actualImplAppend pk sk) (adv.main pk)).run [])).run
                    (∅ : spec.QueryCache) =
                actual_stateful_exp_append pk sk := by
            simpa [actual_stateful_exp_append] using
              (h_actual_append_stateful pk sk (oa := adv.main pk)
                (cache := (∅ : spec.QueryCache)) (signed := ([] : List M)))
          have h_verify :
              ∀ (msg : M) (sig : Commit × Resp) (signed : List M) (cache : spec.QueryCache),
                ((simulateQ baseSim (fsAlg.verify pk msg sig)).run' cache >>= fun verified =>
                  pure (decide (msg ∉ signed) && verified)) =
                  verifyFromState pk ((msg, sig), (cache, signed)) := by
            intro msg sig signed cache
            rcases sig with ⟨c, resp⟩
            cases hcache : cache (.inr (msg, c)) with
            | some ω =>
                have hSimQuery :
                    simulateQ baseSim
                      ((liftM
                        ((query (msg, c)) : OracleQuery (M × Commit →ₒ Chal) Chal)) :
                        OracleComp spec Chal) = roSim (msg, c) := by
                  change simulateQ (unifSim + roSim)
                      ((liftM
                        ((liftM
                          ((query (msg, c)) : OracleQuery (M × Commit →ₒ Chal) Chal)) :
                          OracleQuery spec Chal)) : OracleComp spec Chal) =
                        roSim (msg, c)
                  simp [simulateQ_query]
                have hRunQuery :
                    (simulateQ baseSim
                      ((liftM
                        ((query (msg, c)) : OracleQuery (M × Commit →ₒ Chal) Chal)) :
                        OracleComp spec Chal)).run cache = pure (ω, cache) := by
                  rw [hSimQuery, h_roSim_run_hit (mc := (msg, c)) (cache := cache) (u := ω) hcache]
                  rfl
                simp [verifyFromState, fsAlg, FiatShamir, hcache, hRunQuery,
                  bind_assoc, bind_pure_comp]
                rfl
            | none =>
                have hSimQuery :
                    simulateQ baseSim
                      ((liftM
                        ((query (msg, c)) : OracleQuery (M × Commit →ₒ Chal) Chal)) :
                        OracleComp spec Chal) = roSim (msg, c) := by
                  change simulateQ (unifSim + roSim)
                      ((liftM
                        ((liftM
                          ((query (msg, c)) : OracleQuery (M × Commit →ₒ Chal) Chal)) :
                          OracleQuery spec Chal)) : OracleComp spec Chal) =
                        roSim (msg, c)
                  simp [simulateQ_query]
                have hRunQuery :
                    (simulateQ baseSim
                      ((liftM
                        ((query (msg, c)) : OracleQuery (M × Commit →ₒ Chal) Chal)) :
                        OracleComp spec Chal)).run cache =
                      (fun u => (u, cache.cacheQuery (Sum.inr (msg, c)) u)) <$>
                        liftM (query (Sum.inr (msg, c))) := by
                  rw [hSimQuery, h_roSim_run_miss (mc := (msg, c)) (cache := cache) hcache]
                simp [verifyFromState, fsAlg, FiatShamir, hcache, hRunQuery,
                  bind_assoc, bind_pure_comp]
                rfl
          have h_run' :
              (simulateQ baseSim (actual_pk_game_append pk sk)).run' (∅ : spec.QueryCache) =
                ((simulateQ baseSim
                    ((simulateQ (actualImplAppend pk sk) (adv.main pk)).run [])).run
                    (∅ : spec.QueryCache)) >>=
                  fun z => verifyFromState pk (z.1.1, z.2, z.1.2) := by
            unfold actual_pk_game_append
            simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, bind_assoc,
              bind_pure_comp]
            refine (bind_congr (m := OracleComp spec) ?_)
            intro a
            rcases a with ⟨⟨⟨msg, sig⟩, signed⟩, cache⟩
            simpa [StateT.run'_eq, bind_assoc, bind_pure_comp] using
              h_verify msg sig signed cache
          calc
            evalDist ((simulateQ baseSim (actual_pk_game_append pk sk)).run' (∅ : spec.QueryCache)) =
                evalDist
                  ((((simulateQ baseSim
                      ((simulateQ (actualImplAppend pk sk) (adv.main pk)).run [])).run
                        (∅ : spec.QueryCache))) >>=
                    fun z => verifyFromState pk (z.1.1, z.2, z.1.2)) := by
                  rw [h_run']
            _ = evalDist
                  (((fun z : (((M × (Commit × Resp)) × List M) × spec.QueryCache) =>
                      (z.1.1, z.2, z.1.2)) <$>
                    (simulateQ baseSim
                      ((simulateQ (actualImplAppend pk sk) (adv.main pk)).run [])).run
                        (∅ : spec.QueryCache)) >>= verifyFromState pk) := by
                  rw [← bind_map_left]
            _ = evalDist (actual_stateful_exp_append pk sk >>= verifyFromState pk) := by
                  rw [h_prefix]
            _ = evalDist (actual_stateful_exp_append pk sk) >>= fun x =>
                  evalDist (verifyFromState pk x) := by
                  rw [evalDist_bind]
        have h_actual_hit_le : ∀ (pk : Stmt) (sk : Wit),
            Pr[= true | actual_pk_exp pk sk] ≤
              Pr[eventNoBad pk | actual_stateful_exp_append pk sk] + δ_verify := by
          let missVerifyComp : Stmt →
              ((M × (Commit × Resp)) × (spec.QueryCache × List M)) → OracleComp spec Bool :=
            fun pk z => do
              let ω ←
                (liftM (query (Sum.inr (z.1.1, z.1.2.1)) : OracleQuery spec Chal) :
                  OracleComp spec Chal)
              pure (σ.verify pk z.1.2.1 ω z.1.2.2)
          have h_verifyFromState_split :
              ∀ (pk : Stmt) (z : ((M × (Commit × Resp)) × (spec.QueryCache × List M))),
                Pr[= true | verifyFromState pk z] ≤
                  Pr[= true | (pure (decide (eventNoBad pk z)) : OracleComp spec Bool)] +
                    Pr[= true | missVerifyComp pk z] := by
            intro pk z
            rcases z with ⟨⟨msg, sig⟩, s⟩
            rcases sig with ⟨c, resp⟩
            rcases s with ⟨cache, signed⟩
            cases hcache : cache (.inr (msg, c)) with
            | some ω =>
                simp [verifyFromState, eventNoBad, missVerifyComp, hcache]
                have hnonneg :
                    0 ≤ Pr[= true | missVerifyComp pk ((msg, (c, resp)), (cache, signed))] := by
                  exact bot_le
                simpa [missVerifyComp, and_left_comm, and_assoc, and_comm] using
                  le_add_of_nonneg_right hnonneg
            | none =>
                by_cases hsigned : msg ∈ signed
                · simp [verifyFromState, eventNoBad, missVerifyComp, hcache, hsigned]
                · simp [verifyFromState, eventNoBad, missVerifyComp, hcache, hsigned]
          have h_missVerify_le :
              ∀ (pk : Stmt) (z : ((M × (Commit × Resp)) × (spec.QueryCache × List M))),
                Pr[= true | missVerifyComp pk z] ≤ δ_verify := by
            intro pk z
            rcases z with ⟨⟨msg, sig⟩, s⟩
            rcases sig with ⟨c, resp⟩
            rcases s with ⟨cache, signed⟩
            have h_query :
                Pr[(fun ω : Chal => σ.verify pk c ω resp = true) |
                    (spec.query (Sum.inr (msg, c)) : OracleComp spec Chal)] =
                  Pr[(fun ω : Chal => σ.verify pk c ω resp = true) |
                    ($ᵗ Chal : ProbComp Chal)] := by
              rw [probEvent_query, probEvent_uniformSample]
              have hcard : Fintype.card (spec.Range (Sum.inr (msg, c))) = Fintype.card Chal := rfl
              rw [hcard]
              rfl
            have h_guess :
                Pr[(fun ω : Chal => σ.verify pk c ω resp = true) |
                    (spec.query (Sum.inr (msg, c)) : OracleComp spec Chal)] ≤ δ_verify := by
              rw [h_query]
              exact _hVerifyGuess pk c resp
            calc
              Pr[= true | missVerifyComp pk ((msg, (c, resp)), (cache, signed))] =
                  Pr[(· = true) |
                    (fun ω : Chal => σ.verify pk c ω resp) <$>
                      (spec.query (Sum.inr (msg, c)) : OracleComp spec Chal)] := by
                    change
                      Pr[= true |
                        (fun ω : Chal => σ.verify pk c ω resp) <$>
                          (spec.query (Sum.inr (msg, c)) : OracleComp spec Chal)] = _
                    rw [← probEvent_true_eq_probOutput]
              _ = Pr[(fun ω : Chal => σ.verify pk c ω resp = true) |
                    (spec.query (Sum.inr (msg, c)) : OracleComp spec Chal)] := by
                    rw [probEvent_map]
                    rfl
              _ ≤ δ_verify := h_guess
          have h_miss_total :
              ∀ (pk : Stmt) (sk : Wit),
                Pr[= true | actual_stateful_exp_append pk sk >>= missVerifyComp pk] ≤ δ_verify := by
            intro pk sk
            rw [probOutput_bind_eq_tsum]
            calc
              ∑' x, Pr[= x | actual_stateful_exp_append pk sk] * Pr[= true | missVerifyComp pk x]
                  ≤ ∑' x, Pr[= x | actual_stateful_exp_append pk sk] * δ_verify := by
                    refine ENNReal.tsum_le_tsum fun x => ?_
                    exact mul_le_mul' le_rfl (h_missVerify_le pk x)
              _ = (∑' x, Pr[= x | actual_stateful_exp_append pk sk]) * δ_verify := by
                    rw [ENNReal.tsum_mul_right]
              _ ≤ 1 * δ_verify := by
                    exact mul_le_mul' tsum_probOutput_le_one le_rfl
              _ = δ_verify := by simp
          have h_event_bind :
              ∀ (pk : Stmt) (sk : Wit),
                Pr[= true | actual_stateful_exp_append pk sk >>= fun z =>
                    pure (decide (eventNoBad pk z))] =
                  Pr[eventNoBad pk | actual_stateful_exp_append pk sk] := by
            intro pk sk
            rw [show (actual_stateful_exp_append pk sk >>= fun z =>
                pure (decide (eventNoBad pk z))) =
                  (fun z => decide (eventNoBad pk z)) <$> actual_stateful_exp_append pk sk by
                rw [map_eq_bind_pure_comp]
                rfl]
            rw [← probEvent_true_eq_probOutput, probEvent_map]
            have hpred :
                ((fun x => x = true) ∘ fun z => decide (eventNoBad pk z)) = eventNoBad pk := by
              funext z
              simp
            simpa using congrArg (probEvent (actual_stateful_exp_append pk sk)) hpred
          intro pk sk
          calc
            Pr[= true | actual_pk_exp pk sk] =
                Pr[= true | actual_stateful_exp_append pk sk >>= verifyFromState pk] := by
                  simpa [probOutput_def] using
                    congrArg (fun d => d true) (h_actual_pk_exp_stateful pk sk)
            _ ≤ Pr[= true | actual_stateful_exp_append pk sk >>= fun z =>
                  pure (decide (eventNoBad pk z))] +
                Pr[= true | actual_stateful_exp_append pk sk >>= missVerifyComp pk] := by
                  refine probOutput_bind_congr_le_add ?_
                  intro z hz
                  exact h_verifyFromState_split pk z
            _ = Pr[eventNoBad pk | actual_stateful_exp_append pk sk] +
                Pr[= true | actual_stateful_exp_append pk sk >>= missVerifyComp pk] := by
                  rw [h_event_bind pk sk]
            _ ≤ Pr[eventNoBad pk | actual_stateful_exp_append pk sk] + δ_verify := by
                  exact add_le_add le_rfl (h_miss_total pk sk)
        have h_event_actual_proj : ∀ (pk : Stmt) (sk : Wit),
            Pr[eventNoBad pk | actual_stateful_exp_append pk sk] =
              Pr[event pk | direct_actual_exp_append pk sk] := by
          have h_actualImplBadAppend_proj :
              ∀ (pk : Stmt) (sk : Wit) (t : (spec + (M →ₒ (Commit × Resp))).Domain)
                (s : ((spec.QueryCache × List M) × Bool)),
                Prod.map id Prod.fst <$> ((actualImplBadAppend pk sk) t).run s =
                  ((actualImplSignedAppend pk sk) t).run s.1 := by
            intro pk sk t s
            rcases s with ⟨⟨cache, signed⟩, bad⟩
            cases t with
            | inl t' =>
                simp [actualImplBadAppend, actualImplSignedAppend, baseSimSigned, baseSimSigned',
                  QueryImpl.add_apply_inl, QueryImpl.withBadFlag_apply_run, StateT.run_bind,
                  StateT.run_get, StateT.run_set]
            | inr msg =>
                simp [actualImplBadAppend, actualImplSignedAppend, actualSignBadAppend,
                  actualSignSignedAppend, sigBadFSigned, QueryImpl.add_apply_inr,
                  QueryImpl.withBadUpdate_apply_run, StateT.run_bind, StateT.run_get,
                  StateT.run_set]
          have h_direct_actual_append_proj : ∀ (pk : Stmt) (sk : Wit),
              Prod.map id Prod.fst <$> direct_actual_exp_append pk sk =
                actual_stateful_exp_append pk sk := by
            intro pk sk
            simpa [direct_actual_exp_append, actual_stateful_exp_append] using
              (OracleComp.map_run_simulateQ_eq_of_query_map_eq'
                (impl₁ := actualImplBadAppend pk sk) (impl₂ := actualImplSignedAppend pk sk)
                (proj := Prod.fst) (hproj := h_actualImplBadAppend_proj pk sk)
                (oa := adv.main pk) (s := ((∅, []), false)))
          intro pk sk
          calc
            Pr[eventNoBad pk | actual_stateful_exp_append pk sk] =
                Pr[eventNoBad pk | Prod.map id Prod.fst <$> direct_actual_exp_append pk sk] := by
                  rw [h_direct_actual_append_proj pk sk]
            _ = Pr[eventNoBad pk ∘ Prod.map id Prod.fst | direct_actual_exp_append pk sk] := by
                  rw [probEvent_map]
            _ = Pr[event pk | direct_actual_exp_append pk sk] := by
                  rfl
        have h_actual_vs_real_append : ∀ (pk : Stmt) (sk : Wit), rel pk sk = true →
            Pr[event pk | direct_actual_exp_append pk sk] ≤
              Pr[event pk | direct_real_exp_append pk sk] +
                Pr[badPred | direct_real_exp_append pk sk] := by
          have h_actual_real_sign_run_miss :
              ∀ (pk : Stmt) (sk : Wit) (msg : M) (cache : spec.QueryCache)
                (u : Commit × Resp) (cache' : spec.QueryCache),
                cache (.inr (msg, u.1)) = none →
                Pr[= (u, cache') | (simulateQ baseSim (fsAlg.sign pk sk msg)).run cache] =
                  Pr[= (u, cache') | (realSign pk sk msg).run cache] := by
            intro pk sk msg cache u cache' hmiss
            have h_commit_run (cache : spec.QueryCache) :
                (simulateQ baseSim
                  (monadLift (σ.commit pk sk) : OracleComp spec (Commit × PrvState))).run cache =
                    (fun x => (x, cache)) <$> liftComp (σ.commit pk sk) spec := by
              change (simulateQ baseSim (liftComp (σ.commit pk sk) spec)).run cache = _
              rw [show simulateQ baseSim (liftComp (σ.commit pk sk) spec) =
                  simulateQ unifSim (σ.commit pk sk) from by
                    simpa [baseSim] using
                      (QueryImpl.simulateQ_add_liftComp_left
                        (impl₁' := unifSim) (impl₂' := roSim) (oa := σ.commit pk sk))]
              exact run_unifSim cache (oa := σ.commit pk sk)
            have h_respond_run (e : PrvState) (ω : Chal) (cache : spec.QueryCache) :
                (simulateQ baseSim
                  (monadLift (σ.respond pk sk e ω) : OracleComp spec Resp)).run cache =
                    (fun x => (x, cache)) <$> liftComp (σ.respond pk sk e ω) spec := by
              change (simulateQ baseSim (liftComp (σ.respond pk sk e ω) spec)).run cache = _
              rw [show simulateQ baseSim (liftComp (σ.respond pk sk e ω) spec) =
                  simulateQ unifSim (σ.respond pk sk e ω) from by
                    simpa [baseSim] using
                      (QueryImpl.simulateQ_add_liftComp_left
                        (impl₁' := unifSim) (impl₂' := roSim)
                        (oa := σ.respond pk sk e ω))]
              exact run_unifSim cache (oa := σ.respond pk sk e ω)
            have hSimQuery (c : Commit) :
                simulateQ baseSim
                  ((liftM
                    ((query (msg, c)) : OracleQuery (M × Commit →ₒ Chal) Chal)) :
                    OracleComp spec Chal) = roSim (msg, c) := by
              change simulateQ (unifSim + roSim)
                  ((liftM
                    ((liftM
                      ((query (msg, c)) : OracleQuery (M × Commit →ₒ Chal) Chal)) :
                      OracleQuery spec Chal)) : OracleComp spec Chal) =
                    roSim (msg, c)
              simp [simulateQ_query]
            have h_actual_comp :
                (simulateQ baseSim (fsAlg.sign pk sk msg)).run cache =
                  (σ.commit pk sk).liftComp spec >>= fun ce =>
                    (simulateQ baseSim
                      (do
                        let ω ←
                          (liftM (query (Sum.inr (msg, ce.1)) : OracleQuery spec Chal) :
                            OracleComp spec Chal)
                        let π ← liftM (σ.respond pk sk ce.2 ω)
                        pure (ce.1, π))).run cache := by
              dsimp [fsAlg, FiatShamir]
              simp only [simulateQ_bind, StateT.run_bind]
              rw [h_commit_run cache, bind_map_left]
              refine bind_congr fun ce => ?_
              rcases ce with ⟨c, e⟩
              have hRunQuery :
                  (simulateQ baseSim
                    ((liftM ((query (msg, c)) : OracleQuery (M × Commit →ₒ Chal) Chal)) :
                      OracleComp spec Chal)).run cache =
                    (roSim (msg, c)).run cache := by
                exact congrArg (fun oa => oa.run cache) (hSimQuery c)
              rw [hRunQuery]
              simp [h_respond_run, simulateQ_pure, baseSim, QueryImpl.add_apply_inr]
              refine bind_congr fun p => ?_
              simpa using congrArg
                (fun x => (fun a => ((c, a), p.2)) <$> x)
                (rfl : liftM (σ.respond pk sk e p.1) = liftM (σ.respond pk sk e p.1))
            have h_real_comp :
                (realSign pk sk msg).run cache =
                  (σ.commit pk sk).liftComp spec >>= fun ce =>
                    (($ᵗ Chal : ProbComp Chal).liftComp spec >>= fun ω =>
                      (σ.respond pk sk ce.2 ω).liftComp spec >>= fun π =>
                        pure
                          (match cache (.inr (msg, ce.1)) with
                          | some _ => ((ce.1, π), cache)
                          | none => ((ce.1, π), cache.cacheQuery (.inr (msg, ce.1)) ω))) := by
              rw [h_realSign_run pk sk msg cache]
              dsimp [fsAlg, FiatShamir]
              rw [SigmaProtocol.realTranscript]
              simp [OracleComp.liftComp_bind, OracleComp.liftComp_pure,
                bind_assoc, bind_pure_comp, liftComp_eq_liftM]
              refine bind_congr fun ce => ?_
              refine bind_congr fun ω => ?_
              cases hcache : cache (Sum.inr (msg, ce.1)) <;> rfl
            rw [h_actual_comp, h_real_comp]
            refine probOutput_bind_congr' ((σ.commit pk sk).liftComp spec) (u, cache') ?_
            intro ce
            rcases ce with ⟨c, e⟩
            dsimp
            by_cases hc : c = u.1
            · subst c
              let oa : Chal → OracleComp spec ((Commit × Resp) × spec.QueryCache) := fun ω =>
                (σ.respond pk sk e ω).liftComp spec >>= fun π =>
                  pure ((u.1, π), cache.cacheQuery (.inr (msg, u.1)) ω)
              have hRunQuery :
                  (simulateQ baseSim
                    ((liftM (query (Sum.inr (msg, u.1)) : OracleQuery spec Chal)) :
                      OracleComp spec Chal)).run cache =
                    (fun ω => (ω, cache.cacheQuery (Sum.inr (msg, u.1)) ω)) <$>
                      liftM (query (Sum.inr (msg, u.1))) := by
                calc
                  (simulateQ baseSim
                    ((liftM (query (Sum.inr (msg, u.1)) : OracleQuery spec Chal)) :
                      OracleComp spec Chal)).run cache =
                      (roSim (msg, u.1)).run cache := by
                        simpa using congrArg (fun oa => oa.run cache) (hSimQuery u.1)
                  _ =
                      (fun ω => (ω, cache.cacheQuery (Sum.inr (msg, u.1)) ω)) <$>
                        liftM (query (Sum.inr (msg, u.1))) := by
                        rw [h_roSim_run_miss (mc := (msg, u.1)) (cache := cache) hmiss]
              have h_actual_cont :
                  (simulateQ baseSim
                    (do
                      let ω ←
                        (liftM (query (Sum.inr (msg, u.1)) : OracleQuery spec Chal) :
                          OracleComp spec Chal)
                      let π ← liftM (σ.respond pk sk e ω)
                      pure (u.1, π))).run cache =
                    ((spec.query (Sum.inr (msg, u.1)) : OracleComp spec Chal) >>= oa) := by
                simp only [simulateQ_bind, StateT.run_bind]
                rw [hRunQuery]
                simp [h_respond_run, simulateQ_pure]
                change
                  (((liftM (query (Sum.inr (msg, u.1)) : OracleQuery spec Chal) :
                      OracleComp spec Chal)) >>= oa) = _
                rfl
              have h_eval :
                  evalDist
                      ((((($ᵗ Chal : ProbComp Chal).liftComp spec : OracleComp spec Chal)) >>= oa)) =
                    evalDist
                      (((spec.query (Sum.inr (msg, u.1)) : OracleComp spec Chal) >>= oa)) := by
                rw [evalDist_bind, evalDist_bind, evalDist_liftComp, evalDist_uniformSample,
                  evalDist_query]
                rfl
              calc
                Pr[= (u, cache') |
                    (simulateQ baseSim
                      (do
                        let ω ←
                          (liftM (query (Sum.inr (msg, u.1)) : OracleQuery spec Chal) :
                            OracleComp spec Chal)
                        let π ← liftM (σ.respond pk sk e ω)
                        pure (u.1, π))).run cache] =
                    Pr[= (u, cache') |
                      ((spec.query (Sum.inr (msg, u.1)) : OracleComp spec Chal) >>= oa)] := by
                      rw [h_actual_cont]
                _ =
                    Pr[= (u, cache') |
                      ((((($ᵗ Chal : ProbComp Chal).liftComp spec : OracleComp spec Chal)) >>= oa))] := by
                      exact congrFun (congrArg DFunLike.coe h_eval.symm) (u, cache')
                _ =
                    Pr[= (u, cache') |
                      (($ᵗ Chal : ProbComp Chal).liftComp spec >>= fun ω =>
                        (σ.respond pk sk e ω).liftComp spec >>= fun π =>
                          pure ((u.1, π), cache.cacheQuery (.inr (msg, u.1)) ω))] := by
                      rfl
                _ =
                    Pr[= (u, cache') |
                      (($ᵗ Chal : ProbComp Chal).liftComp spec >>= fun ω =>
                        (σ.respond pk sk e ω).liftComp spec >>= fun π =>
                          pure
                            (match cache (.inr (msg, u.1)) with
                            | some _ => ((u.1, π), cache)
                            | none => ((u.1, π), cache.cacheQuery (.inr (msg, u.1)) ω)))] := by
                      simp [hmiss]
                _ =
                    Pr[= (u, cache') |
                      (($ᵗ Chal : ProbComp Chal).liftComp spec >>= fun ω =>
                        (σ.respond pk sk e ω).liftComp spec >>= fun π =>
                          pure ((u.1, π), cache.cacheQuery (.inr (msg, u.1)) ω))] := by
                      simp [hmiss]
                _ =
                    Pr[= (u, cache') |
                      (($ᵗ Chal : ProbComp Chal).liftComp spec >>= fun ω =>
                        (σ.respond pk sk (u.1, e).2 ω).liftComp spec >>= fun π =>
                          pure
                            (match cache (.inr (msg, (u.1, e).1)) with
                            | some _ => (((u.1, e).1, π), cache)
                            | none =>
                                (((u.1, e).1, π),
                                  cache.cacheQuery (.inr (msg, (u.1, e).1)) ω)))] := by
                      cases hcache : cache (.inr (msg, (u.1, e).1)) with
                      | some v =>
                          simp [hmiss] at hcache
                      | none =>
                          simpa [hcache]
              rw [probOutput_def, probOutput_def]
              refine tsum_congr ?_
              intro x
              by_cases hx : (u, cache') = x
              · subst x
                congr
                funext ω
                congr
                · funext a
                  cases hcache : cache (Sum.inr (msg, u.1)) <;> rfl
              · simp [hx]
            · have h_actual_zero :
                  Pr[= (u, cache') |
                    (simulateQ baseSim
                      (do
                        let ω ←
                          (liftM (query (Sum.inr (msg, c)) : OracleQuery spec Chal) :
                            OracleComp spec Chal)
                        let π ← liftM (σ.respond pk sk e ω)
                        pure (c, π))).run cache] = 0 := by
                apply probOutput_eq_zero_of_not_mem_support
                intro hmem
                simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure] at hmem
                rw [mem_support_bind_iff] at hmem
                rcases hmem with ⟨p, hp, hcont⟩
                rw [h_respond_run e p.1 p.2] at hcont
                rw [mem_support_bind_iff] at hcont
                rcases hcont with ⟨r, hr, hEq⟩
                rw [support_map, Set.mem_image] at hr
                rcases hr with ⟨π, hπ, rfl⟩
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hEq
                have hpair : (c, π) = u := by
                  simpa using (congrArg Prod.fst hEq).symm
                exact hc (by simpa using congrArg Prod.fst hpair)
              rw [h_actual_zero]
              symm
              apply probOutput_eq_zero_of_not_mem_support
              intro hmem
              rw [mem_support_bind_iff] at hmem
              rcases hmem with ⟨ω, hω, hcont⟩
              rw [mem_support_bind_iff] at hcont
              rcases hcont with ⟨π, hπ, hEq⟩
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hEq
              have hpair : (c, π) = u := by
                cases hcache : cache (Sum.inr (msg, c)) <;>
                  simpa [hcache] using (congrArg Prod.fst hEq).symm
              exact hc (by simpa using congrArg Prod.fst hpair)
          have h_sign_good_output :
              ∀ (pk : Stmt) (sk : Wit) (msg : M) (cache : spec.QueryCache) (signed : List M)
                (u : Commit × Resp) (s' : spec.QueryCache × List M),
                Pr[= (u, (s', false)) | (realSignBadAppend pk sk msg).run ((cache, signed), false)] =
                  Pr[= (u, (s', false)) |
                    (actualSignBadAppend pk sk msg).run ((cache, signed), false)] := by
            intro pk sk msg cache signed u s'
            rcases s' with ⟨cache', signed'⟩
            by_cases hs : signed' = signed ++ [msg]
            · subst signed'
              cases hcache : cache (.inr (msg, u.1)) with
              | some ω =>
                  have hR :
                      Pr[= (u, (((cache', signed ++ [msg]), false))) |
                          (realSignBadAppend pk sk msg).run ((cache, signed), false)] = 0 := by
                    apply probOutput_eq_zero_of_not_mem_support
                    simp [realSignBadAppend, realSignSignedAppend,
                      QueryImpl.withBadUpdate_apply_run, StateT.run_bind, StateT.run_get,
                      StateT.run_set]
                    intro x x_1 hx hu
                    subst hu
                    simp [sigBadFSigned, hcache]
                  have hA :
                      Pr[= (u, (((cache', signed ++ [msg]), false))) |
                          (actualSignBadAppend pk sk msg).run ((cache, signed), false)] = 0 := by
                    apply probOutput_eq_zero_of_not_mem_support
                    simp [actualSignBadAppend, actualSignSignedAppend,
                      QueryImpl.withBadUpdate_apply_run, StateT.run_bind, StateT.run_get,
                      StateT.run_set]
                    intro x x_1 hx hu
                    subst hu
                    simp [sigBadFSigned, hcache]
                  rw [hR, hA]
              | none =>
                  let φ :
                      (Commit × Resp) × spec.QueryCache →
                        (Commit × Resp) × ((spec.QueryCache × List M) × Bool) :=
                    fun a => (a.1, ((a.2, signed ++ [msg]),
                      (cache (Sum.inr (msg, a.1.1))).isSome))
                  have hφ_inj : Function.Injective φ := by
                    intro a b hab
                    apply Prod.ext
                    · simpa [φ] using congrArg Prod.fst hab
                    · have hs : (a.2, signed ++ [msg]) = (b.2, signed ++ [msg]) := by
                        simpa [φ] using congrArg (fun z => z.2.1) hab
                      exact congrArg Prod.fst hs
                  have hφ_real :
                      Pr[= (u, ((cache', signed ++ [msg]), false)) |
                          φ <$> (realSign pk sk msg).run cache] =
                        Pr[= (u, cache') | (realSign pk sk msg).run cache] := by
                    simpa [φ, hcache] using
                      (probOutput_map_injective ((realSign pk sk msg).run cache)
                        (f := φ) hφ_inj (x := (u, cache')))
                  have hφ_actual :
                      Pr[= (u, ((cache', signed ++ [msg]), false)) |
                          φ <$> (simulateQ baseSim (fsAlg.sign pk sk msg)).run cache] =
                        Pr[= (u, cache') | (simulateQ baseSim (fsAlg.sign pk sk msg)).run cache] := by
                    simpa [φ, hcache] using
                      (probOutput_map_injective
                        ((simulateQ baseSim (fsAlg.sign pk sk msg)).run cache)
                        (f := φ) hφ_inj (x := (u, cache')))
                  calc
                    Pr[= (u, (((cache', signed ++ [msg]), false))) |
                        (realSignBadAppend pk sk msg).run ((cache, signed), false)] =
                        Pr[= (u, ((cache', signed ++ [msg]), false)) |
                          φ <$> (realSign pk sk msg).run cache] := by
                          simp [realSignBadAppend, realSignSignedAppend, sigBadFSigned, φ,
                            QueryImpl.withBadUpdate_apply_run, StateT.run_bind,
                            StateT.run_get, StateT.run_set]
                    _ = Pr[= (u, cache') | (realSign pk sk msg).run cache] := hφ_real
                    _ = Pr[= (u, cache') | (simulateQ baseSim (fsAlg.sign pk sk msg)).run cache] := by
                          symm
                          exact h_actual_real_sign_run_miss pk sk msg cache u cache' hcache
                    _ = Pr[= (u, ((cache', signed ++ [msg]), false)) |
                          φ <$> (simulateQ baseSim (fsAlg.sign pk sk msg)).run cache] := hφ_actual.symm
                    _ = Pr[= (u, (((cache', signed ++ [msg]), false))) |
                          (actualSignBadAppend pk sk msg).run ((cache, signed), false)] := by
                          simp [actualSignBadAppend, actualSignSignedAppend, sigBadFSigned, φ,
                            QueryImpl.withBadUpdate_apply_run, StateT.run_bind,
                            StateT.run_get, StateT.run_set]
            · have hR :
                  Pr[= (u, (((cache', signed'), false))) |
                      (realSignBadAppend pk sk msg).run ((cache, signed), false)] = 0 := by
                    have hs' : signed ++ [msg] ≠ signed' := by
                      simpa [eq_comm] using hs
                    simp [realSignBadAppend, realSignSignedAppend, QueryImpl.withBadUpdate_apply_run,
                      StateT.run_bind, StateT.run_get, StateT.run_set, hs']
              have hA :
                  Pr[= (u, (((cache', signed'), false))) |
                    (actualSignBadAppend pk sk msg).run ((cache, signed), false)] = 0 := by
                    have hs' : signed ++ [msg] ≠ signed' := by
                      simpa [eq_comm] using hs
                    simp [actualSignBadAppend, actualSignSignedAppend,
                      QueryImpl.withBadUpdate_apply_run, StateT.run_bind, StateT.run_get,
                      StateT.run_set, hs']
              rw [hR, hA]
          have h_tv :
              ∀ (pk : Stmt) (sk : Wit),
                tvDist (direct_real_exp_append pk sk) (direct_actual_exp_append pk sk) ≤
                  Pr[badPred | direct_real_exp_append pk sk].toReal := by
            have h_probOutput_zero_of_bad
                {α : Type} {ι : Type} {specQ : OracleSpec ι} {σ' : Type}
                (impl : QueryImpl specQ (StateT σ' (OracleComp spec)))
                (bad : σ' → Prop)
                (h_mono : ∀ (t : specQ.Domain) (s : σ'), bad s →
                  ∀ x ∈ support ((impl t).run s), bad x.2)
                (oa : OracleComp specQ α) (s₀ : σ') (h_bad : bad s₀)
                (x : α) (s : σ') (hs : ¬ bad s) :
                Pr[= (x, s) | (simulateQ impl oa).run s₀] = 0 := by
              induction oa using OracleComp.inductionOn generalizing s₀ with
              | pure a =>
                  rw [simulateQ_pure]
                  show Pr[= (x, s) | (pure a : StateT σ' (OracleComp spec) α).run s₀] = 0
                  simp only [StateT.run_pure, probOutput_eq_zero_iff, support_pure,
                    Set.mem_singleton_iff, Prod.ext_iff, not_and]
                  rintro rfl rfl
                  exact hs h_bad
              | query_bind t oa ih =>
                  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
                    OracleQuery.cont_query, id_map, StateT.run_bind, probOutput_eq_zero_iff,
                    support_bind, Set.mem_iUnion, exists_prop, Prod.exists, not_exists, not_and]
                  intro u s' h_mem
                  rw [← probOutput_eq_zero_iff]
                  exact ih u s' (h_mono t s₀ h_bad (u, s') h_mem)
            have h_probOutput_eq_of_not_output_bad
                {α : Type} {ι : Type} {specQ : OracleSpec ι} {σ' : Type}
                (impl₁ impl₂ : QueryImpl specQ (StateT (σ' × Bool) (OracleComp spec)))
                (h_agree_good : ∀ (t : specQ.Domain) (s : σ') (u : specQ.Range t) (s' : σ'),
                  Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
                    Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
                (h_mono₁ : ∀ (t : specQ.Domain) (p : σ' × Bool), p.2 = true →
                  ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
                (h_mono₂ : ∀ (t : specQ.Domain) (p : σ' × Bool), p.2 = true →
                  ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
                (oa : OracleComp specQ α) (s₀ : σ') (x : α) (s : σ') :
                Pr[= (x, (s, false)) | (simulateQ impl₁ oa).run (s₀, false)] =
                  Pr[= (x, (s, false)) | (simulateQ impl₂ oa).run (s₀, false)] := by
              induction oa using OracleComp.inductionOn generalizing s₀ with
              | pure a =>
                  simp only [simulateQ_pure]
              | query_bind t oa ih =>
                  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
                    OracleQuery.cont_query, id_map, StateT.run_bind]
                  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
                  refine tsum_congr ?_
                  rintro ⟨u, ⟨s', b⟩⟩
                  cases b with
                  | true =>
                      have h₁ :
                          Pr[= (x, (s, false)) | (simulateQ impl₁ (oa u)).run (s', true)] = 0 :=
                        h_probOutput_zero_of_bad (impl := impl₁)
                          (bad := fun p : σ' × Bool => p.2 = true)
                          (h_mono := h_mono₁) (oa := oa u) (s₀ := (s', true)) rfl x (s, false)
                          (by simp)
                      have h₂ :
                          Pr[= (x, (s, false)) | (simulateQ impl₂ (oa u)).run (s', true)] = 0 :=
                        h_probOutput_zero_of_bad (impl := impl₂)
                          (bad := fun p : σ' × Bool => p.2 = true)
                          (h_mono := h_mono₂) (oa := oa u) (s₀ := (s', true)) rfl x (s, false)
                          (by simp)
                      simp [h₁, h₂]
                  | false =>
                      rw [h_agree_good t s₀ u s', ih u s']
            have h_probEvent_output_bad_eq
                {α : Type} {ι : Type} {specQ : OracleSpec ι} {σ' : Type}
                (impl₁ impl₂ : QueryImpl specQ (StateT (σ' × Bool) (OracleComp spec)))
                (h_agree_good : ∀ (t : specQ.Domain) (s : σ') (u : specQ.Range t) (s' : σ'),
                  Pr[= (u, (s', false)) | (impl₁ t).run (s, false)] =
                    Pr[= (u, (s', false)) | (impl₂ t).run (s, false)])
                (h_mono₁ : ∀ (t : specQ.Domain) (p : σ' × Bool), p.2 = true →
                  ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
                (h_mono₂ : ∀ (t : specQ.Domain) (p : σ' × Bool), p.2 = true →
                  ∀ z ∈ support ((impl₂ t).run p), z.2.2 = true)
                (oa : OracleComp specQ α) (s₀ : σ') :
                Pr[fun z : α × σ' × Bool => z.2.2 = true | (simulateQ impl₁ oa).run (s₀, false)] =
                  Pr[fun z : α × σ' × Bool => z.2.2 = true | (simulateQ impl₂ oa).run (s₀, false)] := by
              let sim₁ := (simulateQ impl₁ oa).run (s₀, false)
              let sim₂ := (simulateQ impl₂ oa).run (s₀, false)
              have h₁ := probEvent_compl sim₁ (fun z : α × σ' × Bool => z.2.2 = true)
              have h₂ := probEvent_compl sim₂ (fun z : α × σ' × Bool => z.2.2 = true)
              simp only [NeverFail.probFailure_eq_zero, tsub_zero] at h₁ h₂
              have h_not_eq :
                  Pr[fun z : α × σ' × Bool => ¬z.2.2 = true | sim₁] =
                    Pr[fun z : α × σ' × Bool => ¬z.2.2 = true | sim₂] := by
                rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
                refine tsum_congr ?_
                rintro ⟨a, s, b⟩
                by_cases hb : b = true
                · simp [hb]
                · cases b with
                  | false =>
                      simpa using
                        h_probOutput_eq_of_not_output_bad impl₁ impl₂ h_agree_good h_mono₁ h_mono₂
                          oa s₀ a s
                  | true =>
                      exact (hb rfl).elim
              have hne₁ : Pr[fun z : α × σ' × Bool => ¬z.2.2 = true | sim₁] ≠ ⊤ :=
                ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one
              calc Pr[fun z : α × σ' × Bool => z.2.2 = true | sim₁]
                  = 1 - Pr[fun z : α × σ' × Bool => ¬z.2.2 = true | sim₁] := by
                      rw [← h₁]
                      exact (ENNReal.add_sub_cancel_right hne₁).symm
                _ = 1 - Pr[fun z : α × σ' × Bool => ¬z.2.2 = true | sim₂] := by
                      rw [h_not_eq]
                _ = Pr[fun z : α × σ' × Bool => z.2.2 = true | sim₂] := by
                      rw [← h₂]
                      exact ENNReal.add_sub_cancel_right
                        (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one)
            intro pk sk
            have h_agree_good :
                ∀ (t : (spec + (M →ₒ (Commit × Resp))).Domain) (s : spec.QueryCache × List M)
                  (u : (spec + (M →ₒ (Commit × Resp))).Range t) (s' : spec.QueryCache × List M),
                  Pr[= (u, (s', false)) | (realImplBadAppend pk sk t).run (s, false)] =
                    Pr[= (u, (s', false)) | (actualImplBadAppend pk sk t).run (s, false)] := by
              intro t s u s'
              rcases s with ⟨cache, signed⟩
              cases t with
              | inl t' =>
                  simp [realImplBadAppend, actualImplBadAppend, baseSimSigned,
                    QueryImpl.add_apply_inl, QueryImpl.withBadFlag_apply_run]
              | inr msg =>
                  simpa [realImplBadAppend, actualImplBadAppend, QueryImpl.add_apply_inr] using
                    h_sign_good_output pk sk msg cache signed u s'
            have h_mono₁ :
                ∀ (t : (spec + (M →ₒ (Commit × Resp))).Domain)
                  (p : (spec.QueryCache × List M) × Bool), p.2 = true →
                    ∀ z ∈ support ((realImplBadAppend pk sk t).run p), z.2.2 = true := by
              intro t p hp z hz
              obtain ⟨s, bad⟩ := p
              dsimp only at hp
              subst hp
              dsimp only [realImplBadAppend, baseSimSigned, realSignBadAppend] at hz
              cases t with
              | inl t' =>
                  simp only [QueryImpl.add_apply_inl] at hz
                  exact support_withBadFlag_run_snd_snd baseSimSigned' t' s true hz
              | inr msg =>
                  simp only [QueryImpl.add_apply_inr] at hz
                  exact support_withBadUpdate_run_snd_snd_of_pre
                    (realSignSignedAppend pk sk) sigBadFSigned msg s hz
            have h_mono₂ :
                ∀ (t : (spec + (M →ₒ (Commit × Resp))).Domain)
                  (p : (spec.QueryCache × List M) × Bool), p.2 = true →
                    ∀ z ∈ support ((actualImplBadAppend pk sk t).run p), z.2.2 = true := by
              intro t p hp z hz
              obtain ⟨s, bad⟩ := p
              dsimp only at hp
              subst hp
              dsimp only [actualImplBadAppend, baseSimSigned, actualSignBadAppend] at hz
              cases t with
              | inl t' =>
                  simp only [QueryImpl.add_apply_inl] at hz
                  exact support_withBadFlag_run_snd_snd baseSimSigned' t' s true hz
              | inr msg =>
                  simp only [QueryImpl.add_apply_inr] at hz
                  exact support_withBadUpdate_run_snd_snd_of_pre
                    (actualSignSignedAppend pk sk) sigBadFSigned msg s hz
            have h_eq :
                ∀ z : ((M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool),
                  ¬ badPred z →
                    Pr[= z | direct_real_exp_append pk sk] =
                      Pr[= z | direct_actual_exp_append pk sk] := by
              rintro ⟨x, s, b⟩ hb
              have hb' : b = false := by
                cases b with
                | false => rfl
                | true =>
                    exfalso
                    exact hb (by simp [badPred])
              subst b
              simpa [direct_real_exp_append, direct_actual_exp_append] using
                h_probOutput_eq_of_not_output_bad
                  (impl₁ := realImplBadAppend pk sk) (impl₂ := actualImplBadAppend pk sk)
                  h_agree_good h_mono₁ h_mono₂ (oa := adv.main pk)
                  (s₀ := ((∅ : spec.QueryCache), ([] : List M))) x s
            have h_event_eq :
                Pr[badPred | direct_real_exp_append pk sk] =
                  Pr[badPred | direct_actual_exp_append pk sk] := by
              simpa [direct_real_exp_append, direct_actual_exp_append, badPred] using
                h_probEvent_output_bad_eq
                  (impl₁ := realImplBadAppend pk sk) (impl₂ := actualImplBadAppend pk sk)
                  h_agree_good h_mono₁ h_mono₂ (oa := adv.main pk)
                  (s₀ := ((∅ : spec.QueryCache), ([] : List M)))
            exact tvDist_le_probEvent_of_probOutput_eq_of_not
              (mx := direct_real_exp_append pk sk) (my := direct_actual_exp_append pk sk)
              badPred h_eq h_event_eq
          intro pk sk h_rel
          let eventDec :
              ((M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool) → Bool :=
            fun z => decide (event pk z)
          let eventGameReal : OracleComp spec Bool := eventDec <$> direct_real_exp_append pk sk
          let eventGameActual : OracleComp spec Bool := eventDec <$> direct_actual_exp_append pk sk
          have h_eventPred_eq :
              ((fun b : Bool => b = true) ∘ fun z :
                  (M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool =>
                    decide (event pk z)) = event pk := by
            funext z
            simp
          have htv_event :
              tvDist eventGameActual eventGameReal ≤
                Pr[badPred | direct_real_exp_append pk sk].toReal := by
            dsimp [eventGameReal, eventGameActual, eventDec]
            refine le_trans (tvDist_map_le _ _ _) ?_
            rw [tvDist_comm]
            exact h_tv pk sk
          have h_event_real :
              Pr[event pk | direct_real_exp_append pk sk] = Pr[= true | eventGameReal] := by
            dsimp [eventGameReal, eventDec]
            rw [← probEvent_true_eq_probOutput]
            simpa [h_eventPred_eq] using
              (probEvent_map (mx := direct_real_exp_append pk sk) (f := fun z =>
                decide (event pk z)) (q := fun b : Bool => b = true)).symm
          have h_event_actual :
              Pr[event pk | direct_actual_exp_append pk sk] = Pr[= true | eventGameActual] := by
            dsimp [eventGameActual, eventDec]
            rw [← probEvent_true_eq_probOutput]
            simpa [h_eventPred_eq] using
              (probEvent_map (mx := direct_actual_exp_append pk sk) (f := fun z =>
                decide (event pk z)) (q := fun b : Bool => b = true)).symm
          have hdiff :
              |Pr[= true | eventGameActual].toReal - Pr[= true | eventGameReal].toReal| ≤
                Pr[badPred | direct_real_exp_append pk sk].toReal := by
            exact le_trans (abs_probOutput_toReal_sub_le_tvDist eventGameActual eventGameReal) htv_event
          have h_event_toReal :
              Pr[event pk | direct_actual_exp_append pk sk].toReal ≤
                Pr[event pk | direct_real_exp_append pk sk].toReal +
                  Pr[badPred | direct_real_exp_append pk sk].toReal := by
            rw [← h_event_actual, ← h_event_real] at hdiff
            rw [abs_le] at hdiff
            linarith
          have h_event_actual_ne : Pr[event pk | direct_actual_exp_append pk sk] ≠ ⊤ :=
            probEvent_ne_top
          have h_event_real_ne : Pr[event pk | direct_real_exp_append pk sk] ≠ ⊤ :=
            probEvent_ne_top
          have h_bad_ne : Pr[badPred | direct_real_exp_append pk sk] ≠ ⊤ := probEvent_ne_top
          have hslack_nonneg :
              0 ≤ Pr[badPred | direct_real_exp_append pk sk].toReal :=
            ENNReal.toReal_nonneg
          calc
            Pr[event pk | direct_actual_exp_append pk sk]
                = ENNReal.ofReal (Pr[event pk | direct_actual_exp_append pk sk].toReal) := by
                    rw [ENNReal.ofReal_toReal h_event_actual_ne]
            _ ≤ ENNReal.ofReal
                  (Pr[event pk | direct_real_exp_append pk sk].toReal +
                    Pr[badPred | direct_real_exp_append pk sk].toReal) := by
                    exact ENNReal.ofReal_le_ofReal h_event_toReal
            _ = Pr[event pk | direct_real_exp_append pk sk] +
                  Pr[badPred | direct_real_exp_append pk sk] := by
                    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hslack_nonneg,
                      ENNReal.ofReal_toReal h_event_real_ne,
                      ENNReal.ofReal_toReal h_bad_ne]
        have h_pr_bad_real_append : ∀ (pk : Stmt) (sk : Wit), rel pk sk = true →
            Pr[badPred | direct_real_exp_append pk sk] ≤
              (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β +
                ENNReal.ofReal ((qS * (qS + qH) : ℕ) * ζ_zk) := by
          let realImplLogged : Stmt → Wit → QueryImpl (spec + (M →ₒ (Commit × Resp)))
              (StateT ((spec.QueryCache × Bool) × List (M × Commit)) (OracleComp spec)) :=
            fun pk sk => QueryImpl.extendState (_realImpl pk sk) keyAux
          let direct_real_exp_logged : Stmt → Wit → OracleComp spec
              ((M × (Commit × Resp)) × ((spec.QueryCache × Bool) × List (M × Commit))) :=
            fun pk sk => (simulateQ (realImplLogged pk sk) (adv.main pk)).run ((∅, false), [])
          have h_realImplSigned_proj :
              ∀ (pk : Stmt) (sk : Wit) (t : (spec + (M →ₒ (Commit × Resp))).Domain)
                (s : ((spec.QueryCache × List M) × Bool)),
                Prod.map id signedProj <$> ((_realImplSigned pk sk) t).run s =
                  ((_realImpl pk sk) t).run (signedProj s) := by
            intro pk sk t s
            rcases s with ⟨⟨cache, signed⟩, bad⟩
            cases t with
            | inl t' =>
                simp [signedProj, _realImplSigned, _realImpl, baseSimSigned, baseSimBad,
                  baseSimSigned', QueryImpl.add_apply_inl, QueryImpl.withBadFlag_apply_run,
                  StateT.run_bind, StateT.run_get, StateT.run_set]
            | inr msg =>
                simp [signedProj, _realImplSigned, _realImpl, realSignSigned, realSignBad,
                  realSignSigned', sigBadFSigned, sigBadF, QueryImpl.add_apply_inr,
                  QueryImpl.withBadUpdate_apply_run, StateT.run_bind, StateT.run_get,
                  StateT.run_set]
          have h_direct_real_exp_proj_simple : ∀ (pk : Stmt) (sk : Wit),
              Prod.map id signedProj <$> direct_real_exp pk sk =
                direct_real_exp_simple pk sk := by
            intro pk sk
            simpa [direct_real_exp, direct_real_exp_simple, signedProj] using
              (OracleComp.map_run_simulateQ_eq_of_query_map_eq'
                (impl₁ := _realImplSigned pk sk) (impl₂ := _realImpl pk sk)
                (proj := signedProj) (hproj := h_realImplSigned_proj pk sk)
                (oa := adv.main pk) (s := ((∅, []), false)))
          have h_pr_bad_real_eq_simple : ∀ (pk : Stmt) (sk : Wit),
              Pr[badPred | direct_real_exp pk sk] =
                Pr[badPredSimple | direct_real_exp_simple pk sk] := by
            intro pk sk
            calc
              Pr[badPred | direct_real_exp pk sk] =
                  Pr[badPredSimple ∘ Prod.map id signedProj | direct_real_exp pk sk] := by
                    rfl
              _ = Pr[badPredSimple | Prod.map id signedProj <$> direct_real_exp pk sk] := by
                    rw [← probEvent_map]
              _ = Pr[badPredSimple | direct_real_exp_simple pk sk] := by
                    rw [h_direct_real_exp_proj_simple pk sk]
          have h_realImpl_append_proj_bad :
              ∀ (pk : Stmt) (sk : Wit) (t : (spec + (M →ₒ (Commit × Resp))).Domain)
                (s : ((spec.QueryCache × List M) × Bool)),
                Prod.map id reverseSigned <$> ((_realImplSigned pk sk) t).run s =
                  ((realImplBadAppend pk sk) t).run (reverseSigned s) := by
            intro pk sk t s
            rcases s with ⟨⟨cache, signed⟩, bad⟩
            cases t with
            | inl t' =>
                simp [reverseSigned, realImplBadAppend, _realImplSigned, baseSimSigned,
                  baseSimSigned', QueryImpl.add_apply_inl, QueryImpl.withBadFlag_apply_run,
                  StateT.run_bind, StateT.run_get, StateT.run_set]
            | inr msg =>
                simp [reverseSigned, realImplBadAppend, _realImplSigned, realSignBadAppend,
                  realSignSignedAppend, realSignSigned, realSignSigned', sigBadFSigned,
                  QueryImpl.add_apply_inr, QueryImpl.withBadUpdate_apply_run, StateT.run_bind,
                  StateT.run_get, StateT.run_set, List.reverse_reverse, List.reverse_cons,
                  List.reverse_append, List.reverse_singleton, List.append_assoc]
          have h_direct_real_append_proj_bad : ∀ (pk : Stmt) (sk : Wit),
              Prod.map id reverseSigned <$> direct_real_exp pk sk =
                direct_real_exp_append pk sk := by
            intro pk sk
            simpa [direct_real_exp, direct_real_exp_append, reverseSigned] using
              (OracleComp.map_run_simulateQ_eq_of_query_map_eq'
                (impl₁ := _realImplSigned pk sk) (impl₂ := realImplBadAppend pk sk)
                (proj := reverseSigned) (hproj := h_realImpl_append_proj_bad pk sk)
                (oa := adv.main pk) (s := ((∅, []), false)))
          have h_bad_reverse : badPred ∘ Prod.map id reverseSigned = badPred := by
            funext z
            simp [badPred, reverseSigned]
          have h_bad_real_append_eq : ∀ (pk : Stmt) (sk : Wit),
              Pr[badPred | direct_real_exp_append pk sk] =
                Pr[badPred | direct_real_exp pk sk] := by
            intro pk sk
            calc
              Pr[badPred | direct_real_exp_append pk sk] =
                  Pr[badPred | Prod.map id reverseSigned <$> direct_real_exp pk sk] := by
                    rw [h_direct_real_append_proj_bad pk sk]
              _ = Pr[badPred ∘ Prod.map id reverseSigned | direct_real_exp pk sk] := by
                    rw [probEvent_map]
              _ = Pr[badPred | direct_real_exp pk sk] := by
                    rw [h_bad_reverse]
          have h_realImplLogged_proj :
              ∀ (pk : Stmt) (sk : Wit) (t : (spec + (M →ₒ (Commit × Resp))).Domain)
                (s : (spec.QueryCache × Bool) × List (M × Commit)),
                Prod.map id Prod.fst <$> ((realImplLogged pk sk) t).run s =
                  ((_realImpl pk sk) t).run s.1 := by
            intro pk sk t s
            rcases s with ⟨st, keys⟩
            change Prod.map id Prod.fst <$>
                ((fun a => (a.1, (a.2, keyAux t a.1 keys))) <$> ((_realImpl pk sk) t).run st) =
                  ((_realImpl pk sk) t).run st
            simp
          have h_direct_real_exp_logged_proj : ∀ (pk : Stmt) (sk : Wit),
              Prod.map id Prod.fst <$> direct_real_exp_logged pk sk =
                direct_real_exp_simple pk sk := by
            intro pk sk
            simpa [direct_real_exp_logged, direct_real_exp_simple] using
              (OracleComp.map_run_simulateQ_eq_of_query_map_eq'
                (impl₁ := realImplLogged pk sk) (impl₂ := _realImpl pk sk)
                (proj := Prod.fst) (hproj := h_realImplLogged_proj pk sk)
                (oa := adv.main pk) (s := ((∅, false), [])))
          have h_pr_bad_real_eq_logged : ∀ (pk : Stmt) (sk : Wit),
              Pr[badPredSimple | direct_real_exp_simple pk sk] =
                Pr[badPredLogged | direct_real_exp_logged pk sk] := by
            intro pk sk
            calc
              Pr[badPredSimple | direct_real_exp_simple pk sk] =
                  Pr[badPredSimple | Prod.map id Prod.fst <$> direct_real_exp_logged pk sk] := by
                    rw [h_direct_real_exp_logged_proj pk sk]
              _ = Pr[badPredSimple ∘ Prod.map id Prod.fst | direct_real_exp_logged pk sk] := by
                    rw [probEvent_map]
              _ = Pr[badPredLogged | direct_real_exp_logged pk sk] := by
                    rfl
          have h_realSignBad_run : ∀ (pk : Stmt) (sk : Wit) (msg : M) (cache : spec.QueryCache),
              (realSignBad pk sk msg).run (cache, false) =
                (fun cωπ : Commit × Chal × Resp =>
                  ((cωπ.1, cωπ.2.2),
                    ((match cache (.inr (msg, cωπ.1)) with
                        | some _ => cache
                        | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                      (cache (.inr (msg, cωπ.1))).isSome))) <$>
                  (σ.realTranscript pk sk).liftComp spec := by
            intro pk sk msg cache
            have hsig : realSignBad pk sk = (realSign pk sk).withBadUpdate sigBadF := rfl
            rw [hsig, QueryImpl.withBadUpdate_apply_run, h_realSign_run pk sk msg cache]
            rw [map_bind]
            refine bind_congr (fun cωπ => ?_)
            cases hcache : cache (.inr (msg, cωπ.1)) with
            | none =>
                simp [sigBadF, hcache]
                change
                  (PFunctor.FreeM.pure
                    ((cωπ.1, cωπ.2.2),
                      cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1, false) :
                    OracleComp spec ((Commit × Resp) × spec.QueryCache × Bool)) =
                    PFunctor.FreeM.pure
                      ((cωπ.1, cωπ.2.2),
                        cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1, false)
                rfl
            | some val =>
                simp [sigBadF, hcache]
                change
                  (PFunctor.FreeM.pure ((cωπ.1, cωπ.2.2), cache, true) :
                    OracleComp spec ((Commit × Resp) × spec.QueryCache × Bool)) =
                    PFunctor.FreeM.pure ((cωπ.1, cωπ.2.2), cache, true)
                rfl
          have realStep_bad_eq_cacheHit :
              ∀ (pk : Stmt) (sk : Wit) (msg : M) (cache : spec.QueryCache)
                (keys : List (M × Commit)),
                Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                    z.2.1.2 = true |
                  ((realImplLogged pk sk) (.inr msg)).run ((cache, false), keys)] =
                  Pr[fun cωπ : Commit × Chal × Resp =>
                    (cache (.inr (msg, cωπ.1))).isSome = true |
                    (σ.realTranscript pk sk).liftComp spec] := by
            intro pk sk msg cache keys
            calc
              Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                    z.2.1.2 = true |
                  ((realImplLogged pk sk) (.inr msg)).run ((cache, false), keys)] =
                  Pr[fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true |
                    ((_realImpl pk sk) (.inr msg)).run (cache, false)] := by
                    calc
                      Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                          z.2.1.2 = true |
                        ((realImplLogged pk sk) (.inr msg)).run ((cache, false), keys)] =
                          Pr[((fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true) ∘
                              Prod.map id Prod.fst) |
                            ((realImplLogged pk sk) (.inr msg)).run ((cache, false), keys)] := by
                              rfl
                      _ = Pr[fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true |
                            Prod.map id Prod.fst <$>
                              ((realImplLogged pk sk) (.inr msg)).run ((cache, false), keys)] := by
                              exact
                                (probEvent_map
                                  (mx := ((realImplLogged pk sk) (.inr msg)).run ((cache, false), keys))
                                  (f := Prod.map id Prod.fst)
                                  (q := fun z : (Commit × Resp) × (spec.QueryCache × Bool) =>
                                    z.2.2 = true)).symm
                      _ = Pr[fun z : (Commit × Resp) × (spec.QueryCache × Bool) => z.2.2 = true |
                            ((_realImpl pk sk) (.inr msg)).run (cache, false)] := by
                              rw [h_realImplLogged_proj pk sk (.inr msg) ((cache, false), keys)]
              _ = Pr[fun cωπ : Commit × Chal × Resp =>
                    (cache (.inr (msg, cωπ.1))).isSome = true |
                      (σ.realTranscript pk sk).liftComp spec] := by
                    dsimp only [_realImpl, realSignBad]
                    simp only [QueryImpl.add_apply_inr]
                    change
                      Pr[fun z : (Commit × Resp) × spec.QueryCache × Bool => z.2.2 = true |
                        (fun vs : (Commit × Resp) × spec.QueryCache =>
                          (vs.1, vs.2, sigBadF msg cache vs.1)) <$> (realSign pk sk msg).run cache] = _
                    rw [probEvent_map, h_realSign_run pk sk msg cache, bind_pure_comp, probEvent_map]
                    congr with cωπ
                    cases hcache : cache (.inr (msg, cωπ.1)) <;> simp [sigBadF, hcache]
          have realStep_bad_le_keys :
              ∀ (pk : Stmt) (sk : Wit) (msg : M) (cache : spec.QueryCache)
                (keys : List (M × Commit)),
                rel pk sk = true →
                keyCovers ((cache, false), keys) →
                  Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                      z.2.1.2 = true |
                    ((realImplLogged pk sk) (.inr msg)).run ((cache, false), keys)] ≤
                    (keys.length : ENNReal) * β +
                      (keys.length : ENNReal) * ENNReal.ofReal ζ_zk := by
            intro pk sk msg cache keys h_rel hKeys
            calc
              Pr[fun z : (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                    z.2.1.2 = true |
                  ((realImplLogged pk sk) (.inr msg)).run ((cache, false), keys)] =
                  Pr[fun cωπ : Commit × Chal × Resp =>
                    (cache (.inr (msg, cωπ.1))).isSome = true |
                      (σ.realTranscript pk sk).liftComp spec] := by
                    exact realStep_bad_eq_cacheHit pk sk msg cache keys
              _ ≤ Pr[fun cωπ : Commit × Chal × Resp =>
                    ∃ mc ∈ keys, mc.1 = msg ∧ mc.2 = cωπ.1 |
                      (σ.realTranscript pk sk).liftComp spec] := by
                    refine probEvent_mono ?_
                    intro cωπ _ hhit
                    cases hcache : cache (.inr (msg, cωπ.1)) with
                    | none =>
                        simp [hcache] at hhit
                    | some ω =>
                        refine ⟨(msg, cωπ.1), hKeys (msg, cωπ.1) ω hcache, rfl, rfl⟩
              _ ≤ (keys.length : ENNReal) * β +
                    (keys.length : ENNReal) * ENNReal.ofReal ζ_zk := by
                    classical
                    have h_finset :
                        Pr[fun cωπ : Commit × Chal × Resp =>
                            ∃ mc ∈ keys.toFinset, mc.1 = msg ∧ mc.2 = cωπ.1 |
                            (σ.realTranscript pk sk).liftComp spec] ≤
                          Finset.sum keys.toFinset (fun mc =>
                            Pr[fun cωπ : Commit × Chal × Resp =>
                                mc.1 = msg ∧ mc.2 = cωπ.1 |
                                (σ.realTranscript pk sk).liftComp spec]) :=
                      probEvent_exists_finset_le_sum keys.toFinset
                        ((σ.realTranscript pk sk).liftComp spec)
                        (fun mc cωπ => mc.1 = msg ∧ mc.2 = cωπ.1)
                    refine le_trans ?_ (le_trans h_finset ?_)
                    · refine probEvent_mono ?_
                      intro cωπ _ hcωπ
                      rcases hcωπ with ⟨mc, hmc, hmsg, hcommit⟩
                      exact ⟨mc, by simpa using List.mem_toFinset.mpr hmc, hmsg, hcommit⟩
                    · calc
                        Finset.sum keys.toFinset (fun mc =>
                            Pr[fun cωπ : Commit × Chal × Resp =>
                                mc.1 = msg ∧ mc.2 = cωπ.1 |
                                (σ.realTranscript pk sk).liftComp spec])
                            ≤ Finset.sum keys.toFinset
                                (fun _ => β + ENNReal.ofReal ζ_zk) := by
                                  apply Finset.sum_le_sum
                                  intro mc hmc
                                  by_cases hmsg : mc.1 = msg
                                  · rw [show
                                        (fun cωπ : Commit × Chal × Resp => mc.1 = msg ∧ mc.2 = cωπ.1) =
                                          (fun cωπ : Commit × Chal × Resp => cωπ.1 = mc.2) from by
                                            funext cωπ
                                            simp [hmsg, eq_comm]]
                                    rw [probEvent_liftComp]
                                    have hmapCommit :
                                        Pr[fun cωπ : Commit × Chal × Resp => cωπ.1 = mc.2 |
                                          σ.realTranscript pk sk] =
                                          Pr[fun c : Commit => c = mc.2 |
                                            Prod.fst <$> σ.realTranscript pk sk] :=
                                      (probEvent_map (mx := σ.realTranscript pk sk) (f := Prod.fst)
                                        (q := fun c : Commit => c = mc.2)).symm
                                    rw [hmapCommit, probEvent_eq_eq_probOutput]
                                    exact realCommit_probOutput_le_beta_hvzk (σ := σ)
                                      _hζ_zk _hhvzk _hPredSim h_rel mc.2
                                  · have hzero :
                                      Pr[fun cωπ : Commit × Chal × Resp =>
                                          mc.1 = msg ∧ mc.2 = cωπ.1 |
                                          (σ.realTranscript pk sk).liftComp spec] = 0 := by
                                        refine probEvent_eq_zero ?_
                                        intro cωπ _ hcωπ
                                        simp [hmsg] at hcωπ
                                    rw [hzero]
                                    exact zero_le _
                        _ = (keys.toFinset.card : ENNReal) * (β + ENNReal.ofReal ζ_zk) := by
                              rw [Finset.sum_const, nsmul_eq_mul]
                        _ ≤ (keys.length : ENNReal) * (β + ENNReal.ofReal ζ_zk) := by
                              gcongr
                              exact_mod_cast List.toFinset_card_le keys
                        _ = (keys.length : ENNReal) * β +
                              (keys.length : ENNReal) * ENNReal.ofReal ζ_zk := by
                              rw [left_distrib]
          let stepSlack : ℕ → ENNReal := fun K =>
            (K : ENNReal) * β + (K : ENNReal) * ENNReal.ofReal ζ_zk
          have pr_bad_real_logged_le :
              ∀ {α : Type} (pk : Stmt) (sk : Wit)
                (oa : OracleComp (spec + (M →ₒ (Commit × Resp))) α)
                (s h K : ℕ) (cache : spec.QueryCache) (keys : List (M × Commit)),
                rel pk sk = true →
                signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := oa) s h →
                keyCovers ((cache, false), keys) →
                keys.length + s + h ≤ K →
                Pr[fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                    z.2.1.2 = true |
                  (simulateQ (realImplLogged pk sk) oa).run ((cache, false), keys)] ≤
                  (s : ENNReal) * stepSlack K := by
            intro α pk sk oa
            induction oa using OracleComp.inductionOn with
            | pure x =>
                intro s h K cache keys h_rel hQ hKeys hLen
                simp [simulateQ_pure, stepSlack]
            | query_bind t mx ih =>
                intro s h K cache keys h_rel hQ hKeys hLen
                rw [signHashQueryBound, OracleComp.isQueryBound_query_bind_iff] at hQ
                obtain ⟨hcan, hrest⟩ := hQ
                cases t with
                | inl t' =>
                    cases t' with
                    | inl n =>
                        let qn :
                            OracleComp spec
                              ((spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inl n))) :=
                          show OracleComp spec
                              ((spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inl n))) from
                            (liftM (spec.query (Sum.inl n)) : OracleComp spec _)
                        have hstep :
                            (liftM ((realImplLogged pk sk) (.inl (.inl n))) :
                                StateT ((spec.QueryCache × Bool) × List (M × Commit))
                                  (OracleComp spec) _).run ((cache, false), keys) =
                                ((fun u : (spec + (M →ₒ (Commit × Resp))).Range
                                    (Sum.inl (Sum.inl n)) =>
                                    (u, (cache, false), keys)) <$> qn) := by
                              change ((realImplLogged pk sk) (.inl (.inl n))).run ((cache, false), keys) =
                                ((fun u : (spec + (M →ₒ (Commit × Resp))).Range
                                    (Sum.inl (Sum.inl n)) =>
                                    (u, (cache, false), keys)) <$> qn)
                              have hlogged :
                                  realImplLogged pk sk = QueryImpl.extendState (_realImpl pk sk) keyAux := rfl
                              rw [hlogged, QueryImpl.extendState_apply]
                              simp [_realImpl, QueryImpl.add_apply_inl, h_baseSimBad_unif n cache,
                                qn, keyAux, bind_pure_comp]
                        have hrun :
                            (simulateQ (realImplLogged pk sk)
                              ((liftM (query (Sum.inl (Sum.inl n)))) >>= mx)).run
                                ((cache, false), keys) =
                              (qn >>= fun u =>
                                (simulateQ (realImplLogged pk sk) (mx u)).run ((cache, false), keys)) := by
                              simp only [simulateQ_query_bind, OracleQuery.input_query,
                                StateT.run_bind]
                              rw [hstep]
                              simp [qn, OracleQuery.cont_query, bind_assoc, bind_pure_comp]
                        rw [hrun]
                        rw [probEvent_bind_eq_tsum]
                        calc
                          ∑' u, Pr[= u | qn] *
                              Pr[fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                                  z.2.1.2 = true |
                                (simulateQ (realImplLogged pk sk) (mx u)).run ((cache, false), keys)]
                              ≤
                              ∑' u, Pr[= u | qn] * ((s : ENNReal) * stepSlack K) := by
                                refine ENNReal.tsum_le_tsum fun u => ?_
                                exact mul_le_mul' le_rfl
                                  (ih u s h K cache keys h_rel (hrest u) hKeys hLen)
                          _ = (∑' u, Pr[= u | qn]) * ((s : ENNReal) * stepSlack K) := by
                                rw [ENNReal.tsum_mul_right]
                          _ = (s : ENNReal) * stepSlack K := by
                                rw [HasEvalPMF.tsum_probOutput_eq_one, one_mul]
                    | inr mc =>
                        by_cases hcache : cache (.inr mc) = none
                        · let qmc :
                              OracleComp spec
                                ((spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) :=
                            show OracleComp spec
                                ((spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) from
                              (liftM (spec.query (Sum.inr mc)) : OracleComp spec _)
                          have hstep :
                              (liftM ((realImplLogged pk sk) (.inl (.inr mc))) :
                                  StateT ((spec.QueryCache × Bool) × List (M × Commit))
                                    (OracleComp spec) _).run ((cache, false), keys) =
                                ((fun u : (spec + (M →ₒ (Commit × Resp))).Range
                                    (Sum.inl (Sum.inr mc)) =>
                                    (u, (cache.cacheQuery (.inr mc) u, false), mc :: keys)) <$>
                                  qmc) := by
                                change ((realImplLogged pk sk) (.inl (.inr mc))).run ((cache, false), keys) =
                                  ((fun u : (spec + (M →ₒ (Commit × Resp))).Range
                                      (Sum.inl (Sum.inr mc)) =>
                                      (u, (cache.cacheQuery (.inr mc) u, false), mc :: keys)) <$>
                                    qmc)
                                have hlogged :
                                    realImplLogged pk sk = QueryImpl.extendState (_realImpl pk sk) keyAux := rfl
                                rw [hlogged, QueryImpl.extendState_apply]
                                simp [_realImpl, QueryImpl.add_apply_inl,
                                  h_baseSimBad_hash_miss mc cache hcache, qmc, keyAux,
                                  bind_pure_comp]
                          have hrun :
                              (simulateQ (realImplLogged pk sk)
                                ((liftM (query (Sum.inl (Sum.inr mc)))) >>= mx)).run
                                  ((cache, false), keys) =
                                (qmc >>= fun u =>
                                  (simulateQ (realImplLogged pk sk) (mx u)).run
                                    ((cache.cacheQuery (.inr mc) u, false), mc :: keys)) := by
                                simp only [simulateQ_query_bind, OracleQuery.input_query,
                                  StateT.run_bind]
                                rw [hstep]
                                simp [qmc, OracleQuery.cont_query, bind_assoc, bind_pure_comp]
                          rw [hrun]
                          rw [probEvent_bind_eq_tsum]
                          calc
                            ∑' u, Pr[= u | qmc] *
                                Pr[fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                                    z.2.1.2 = true |
                                  (simulateQ (realImplLogged pk sk) (mx u)).run
                                    ((cache.cacheQuery (.inr mc) u, false), mc :: keys)]
                                ≤
                                ∑' u, Pr[= u | qmc] * ((s : ENNReal) * stepSlack K) := by
                                  refine ENNReal.tsum_le_tsum fun u => ?_
                                  apply mul_le_mul' le_rfl
                                  have hh : 0 < h := by simpa using hcan
                                  have hLen' : (mc :: keys).length + s + (h - 1) ≤ K := by
                                    have hEq :
                                        (mc :: keys).length + s + (h - 1) =
                                          keys.length + s + h := by
                                      simp [List.length]
                                      omega
                                    rw [hEq]
                                    exact hLen
                                  exact ih u s (h - 1) K
                                    (cache.cacheQuery (.inr mc) u) (mc :: keys)
                                    h_rel (hrest u)
                                    (keyCovers_cacheQuery (mc := mc) (ω := u) hKeys) hLen'
                            _ = (∑' u, Pr[= u | qmc]) * ((s : ENNReal) * stepSlack K) := by
                                  rw [ENNReal.tsum_mul_right]
                            _ = (s : ENNReal) * stepSlack K := by
                                  rw [HasEvalPMF.tsum_probOutput_eq_one, one_mul]
                        · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists.mp hcache
                          have hstep :
                              (liftM ((realImplLogged pk sk) (.inl (.inr mc))) :
                                  StateT ((spec.QueryCache × Bool) × List (M × Commit))
                                    (OracleComp spec) _).run ((cache, false), keys) =
                                  pure (u, ((cache, false), mc :: keys)) := by
                                change ((realImplLogged pk sk) (.inl (.inr mc))).run ((cache, false), keys) =
                                  pure (u, ((cache, false), mc :: keys))
                                have hlogged :
                                    realImplLogged pk sk = QueryImpl.extendState (_realImpl pk sk) keyAux := rfl
                                rw [hlogged, QueryImpl.extendState_apply]
                                simp [_realImpl, QueryImpl.add_apply_inl, keyAux]
                                rw [h_baseSimBad_hash_hit mc cache u hu.symm]
                                change
                                  (fun a :
                                      (spec + (M →ₒ (Commit × Resp))).Range
                                        (Sum.inl (Sum.inr mc)) × (spec.QueryCache × Bool) =>
                                      (a.1, a.2, mc :: keys)) <$>
                                    (pure (u, (cache, false)) :
                                      OracleComp spec
                                        ((spec + (M →ₒ (Commit × Resp))).Range
                                          (Sum.inl (Sum.inr mc)) × (spec.QueryCache × Bool))) =
                                      pure (u, (cache, false), mc :: keys)
                                have hmap :
                                    (fun a :
                                        (spec + (M →ₒ (Commit × Resp))).Range
                                          (Sum.inl (Sum.inr mc)) × (spec.QueryCache × Bool) =>
                                        (a.1, a.2, mc :: keys)) <$>
                                      (pure (u, (cache, false)) :
                                        OracleComp spec
                                          ((spec + (M →ₒ (Commit × Resp))).Range
                                            (Sum.inl (Sum.inr mc)) × (spec.QueryCache × Bool))) =
                                        pure (u, (cache, false), mc :: keys) := by
                                      simpa [bind_pure_comp] using
                                        (pure_bind
                                          (f := fun a :
                                            (spec + (M →ₒ (Commit × Resp))).Range
                                              (Sum.inl (Sum.inr mc)) × (spec.QueryCache × Bool) =>
                                              pure (a.1, a.2, mc :: keys))
                                          (x := (u, (cache, false))))
                                exact hmap
                          have hrun :
                              (simulateQ (realImplLogged pk sk)
                                ((liftM (query (Sum.inl (Sum.inr mc)))) >>= mx)).run
                                  ((cache, false), keys) =
                                (simulateQ (realImplLogged pk sk) (mx u)).run
                                  ((cache, false), mc :: keys) := by
                                simp only [simulateQ_query_bind, OracleQuery.input_query,
                                  StateT.run_bind]
                                rw [hstep]
                                simp [OracleQuery.cont_query]
                          rw [hrun]
                          have hh : 0 < h := by simpa using hcan
                          have hLen' : (mc :: keys).length + s + (h - 1) ≤ K := by
                            have hEq : (mc :: keys).length + s + (h - 1) = keys.length + s + h := by
                              simp [List.length]
                              omega
                            rw [hEq]
                            exact hLen
                          simpa using
                            ih u s (h - 1) K cache (mc :: keys) h_rel (hrest u)
                              (keyCovers_cons (mc := mc) hKeys) hLen'
                | inr msg =>
                    let qsig : OracleComp spec (Commit × Chal × Resp) :=
                      liftM (σ.realTranscript pk sk)
                    have hstep :
                        (liftM ((realImplLogged pk sk) (.inr msg)) :
                            StateT ((spec.QueryCache × Bool) × List (M × Commit))
                              (OracleComp spec) _).run ((cache, false), keys) =
                          ((fun cωπ =>
                              ((cωπ.1, cωπ.2.2),
                                ((match cache (.inr (msg, cωπ.1)) with
                                    | some _ => cache
                                    | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                                  (cache (.inr (msg, cωπ.1))).isSome),
                                (msg, cωπ.1) :: keys)) <$> qsig) := by
                          change ((realImplLogged pk sk) (.inr msg)).run ((cache, false), keys) =
                            ((fun cωπ =>
                                ((cωπ.1, cωπ.2.2),
                                  ((match cache (.inr (msg, cωπ.1)) with
                                      | some _ => cache
                                      | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                                    (cache (.inr (msg, cωπ.1))).isSome),
                                  (msg, cωπ.1) :: keys)) <$> qsig)
                          have hlogged :
                              realImplLogged pk sk = QueryImpl.extendState (_realImpl pk sk) keyAux := rfl
                          rw [hlogged, QueryImpl.extendState_apply]
                          simp [_realImpl, QueryImpl.add_apply_inr, h_realSignBad_run pk sk msg cache,
                            qsig, keyAux, bind_pure_comp, liftComp_eq_liftM]
                    have hrun :
                        (simulateQ (realImplLogged pk sk)
                          ((liftM (query (Sum.inr msg))) >>= mx)).run ((cache, false), keys) =
                          (qsig >>= fun cωπ =>
                            (simulateQ (realImplLogged pk sk) (mx (cωπ.1, cωπ.2.2))).run
                              (((match cache (.inr (msg, cωπ.1)) with
                                    | some _ => cache
                                    | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                                  (cache (.inr (msg, cωπ.1))).isSome),
                                (msg, cωπ.1) :: keys)) := by
                          simp only [simulateQ_query_bind, OracleQuery.input_query,
                            StateT.run_bind]
                          rw [hstep]
                          simp [qsig, OracleQuery.cont_query, bind_assoc, bind_pure_comp]
                    rw [hrun]
                    have hstepBad :
                        Pr[fun cωπ : Commit × Chal × Resp =>
                            ¬ ((cache (.inr (msg, cωπ.1))).isSome = false) |
                          qsig] ≤
                          stepSlack K := by
                      have hcongr :
                          Pr[fun cωπ : Commit × Chal × Resp =>
                              ¬ ((cache (.inr (msg, cωπ.1))).isSome = false) |
                            qsig] =
                            Pr[fun cωπ : Commit × Chal × Resp =>
                              (cache (.inr (msg, cωπ.1))).isSome = true |
                              qsig] := by
                        refine probEvent_congr' (oa := qsig) ?_ rfl
                        intro cωπ _
                        cases hhit : (cache (.inr (msg, cωπ.1))).isSome <;> simp [hhit]
                      calc
                        Pr[fun cωπ : Commit × Chal × Resp =>
                            ¬ ((cache (.inr (msg, cωπ.1))).isSome = false) |
                          qsig]
                            = Pr[fun cωπ : Commit × Chal × Resp =>
                                (cache (.inr (msg, cωπ.1))).isSome = true |
                                qsig] := hcongr
                        _ = Pr[fun z :
                              (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                                z.2.1.2 = true |
                              ((realImplLogged pk sk) (.inr msg)).run ((cache, false), keys)] := by
                                symm
                                simpa [qsig, liftComp_eq_liftM] using
                                  realStep_bad_eq_cacheHit pk sk msg cache keys
                        _ ≤ (keys.length : ENNReal) * β +
                              (keys.length : ENNReal) * ENNReal.ofReal ζ_zk := by
                                exact realStep_bad_le_keys pk sk msg cache keys h_rel hKeys
                        _ ≤ stepSlack K := by
                              dsimp [stepSlack]
                              gcongr <;> omega
                    have hcombine := probEvent_bind_le_add
                      (mx := qsig)
                      (my := fun cωπ =>
                        (simulateQ (realImplLogged pk sk) (mx (cωπ.1, cωπ.2.2))).run
                          (((match cache (.inr (msg, cωπ.1)) with
                                | some _ => cache
                                | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                              (cache (.inr (msg, cωπ.1))).isSome),
                            (msg, cωπ.1) :: keys))
                      (p := fun cωπ : Commit × Chal × Resp =>
                        (cache (.inr (msg, cωπ.1))).isSome = false)
                      (q := fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                        z.2.1.2 = false)
                      (ε₁ := stepSlack K)
                      (ε₂ := ((s - 1 : ℕ) : ENNReal) * stepSlack K)
                      hstepBad
                      (by
                        intro cωπ _ hmiss
                        have hs : 0 < s := by simpa using hcan
                        have hnone : cache (.inr (msg, cωπ.1)) = none := by
                          cases hcache' : cache (.inr (msg, cωπ.1)) with
                          | none => rfl
                          | some v =>
                              simp [hcache'] at hmiss
                        have hLen' : ((msg, cωπ.1) :: keys).length + (s - 1) + h ≤ K := by
                          have hEq :
                              ((msg, cωπ.1) :: keys).length + (s - 1) + h = keys.length + s + h := by
                            simp [List.length]
                            omega
                          rw [hEq]
                          exact hLen
                        simpa [hnone, stepSlack] using
                          (ih (cωπ.1, cωπ.2.2) (s - 1) h K
                            (cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1)
                            ((msg, cωπ.1) :: keys) h_rel (hrest (cωπ.1, cωπ.2.2))
                            (keyCovers_cacheQuery (mc := (msg, cωπ.1)) (ω := cωπ.2.1) hKeys)
                            hLen'))
                    have hcombine' :
                        Pr[fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                            z.2.1.2 = true |
                          qsig >>= fun cωπ =>
                            (simulateQ (realImplLogged pk sk) (mx (cωπ.1, cωπ.2.2))).run
                              (((match cache (.inr (msg, cωπ.1)) with
                                    | some _ => cache
                                    | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                                  (cache (.inr (msg, cωπ.1))).isSome),
                                (msg, cωπ.1) :: keys)] ≤
                          stepSlack K + ((s - 1 : ℕ) : ENNReal) * stepSlack K := by
                      simpa using hcombine
                    calc
                      Pr[fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                          z.2.1.2 = true |
                        qsig >>= fun cωπ =>
                          (simulateQ (realImplLogged pk sk) (mx (cωπ.1, cωπ.2.2))).run
                            (((match cache (.inr (msg, cωπ.1)) with
                                  | some _ => cache
                                  | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                                (cache (.inr (msg, cωπ.1))).isSome),
                              (msg, cωπ.1) :: keys)]
                          ≤ stepSlack K + ((s - 1 : ℕ) : ENNReal) * stepSlack K := hcombine'
                      _ = (s : ENNReal) * stepSlack K := by
                            have hs : 1 + (s - 1) = s := by omega
                            have hs_cast : (1 : ENNReal) + (s - 1 : ℕ) = s := by
                              exact_mod_cast hs
                            calc
                              stepSlack K + ((s - 1 : ℕ) : ENNReal) * stepSlack K
                                  = (1 : ENNReal) * stepSlack K +
                                      ((s - 1 : ℕ) : ENNReal) * stepSlack K := by
                                        simp
                              _ = ((1 : ENNReal) + (s - 1 : ℕ)) * stepSlack K := by
                                    rw [← add_mul]
                              _ = (s : ENNReal) * stepSlack K := by
                                    rw [hs_cast]
          intro pk sk h_rel
          have hLen : ([] : List (M × Commit)).length + qS + qH ≤ qS + qH := by simp
          have hlogged :=
            pr_bad_real_logged_le pk sk (adv.main pk) qS qH (qS + qH) ∅ [] h_rel (_hQ pk)
              (by
                intro mc ω hcache
                simp at hcache)
              hLen
          have hmul_nat :
              (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) =
                ((qS * (qS + qH) : ℕ) : ENNReal) := by
            exact_mod_cast (show qS * (qS + qH) = qS * (qS + qH) by rfl)
          have hprod_nonneg : 0 ≤ (((qS * (qS + qH) : ℕ) : ℝ)) := by positivity
          calc
            Pr[badPred | direct_real_exp_append pk sk]
                = Pr[badPred | direct_real_exp pk sk] := h_bad_real_append_eq pk sk
            _ = Pr[badPredSimple | direct_real_exp_simple pk sk] := h_pr_bad_real_eq_simple pk sk
            _ = Pr[badPredLogged | direct_real_exp_logged pk sk] := h_pr_bad_real_eq_logged pk sk
            _ ≤ (qS : ENNReal) * stepSlack (qS + qH) := by
                  simpa [direct_real_exp_logged] using hlogged
            _ = (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β +
                  ENNReal.ofReal ((qS * (qS + qH) : ℕ) * ζ_zk) := by
                  dsimp [stepSlack]
                  calc
                    (qS : ENNReal) *
                        (((qS + qH : ℕ) : ENNReal) * β +
                          ((qS + qH : ℕ) : ENNReal) * ENNReal.ofReal ζ_zk)
                        = (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β +
                            (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) *
                              ENNReal.ofReal ζ_zk := by
                                rw [mul_add, mul_assoc, mul_assoc]
                    _ = (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β +
                          (((qS * (qS + qH) : ℕ) : ENNReal) * ENNReal.ofReal ζ_zk) := by
                                rw [hmul_nat]
                    _ = (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β +
                          ENNReal.ofReal (((qS * (qS + qH) : ℕ) : ℝ) * ζ_zk) := by
                                rw [show ((qS * (qS + qH) : ℕ) : ENNReal) =
                                    ENNReal.ofReal (((qS * (qS + qH) : ℕ) : ℝ)) by
                                      rw [ENNReal.ofReal_natCast]]
                                rw [← ENNReal.ofReal_mul hprod_nonneg]
                    _ = (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β +
                          ENNReal.ofReal ((qS * (qS + qH) : ℕ) * ζ_zk) := by
                                rfl
        have h_event_real_append_eq : ∀ (pk : Stmt) (sk : Wit),
            Pr[event pk | direct_real_exp_append pk sk] =
              Pr[event pk | direct_real_exp pk sk] := by
          have h_realImpl_append_proj :
              ∀ (pk : Stmt) (sk : Wit) (t : (spec + (M →ₒ (Commit × Resp))).Domain)
                (s : ((spec.QueryCache × List M) × Bool)),
                Prod.map id reverseSigned <$> ((_realImplSigned pk sk) t).run s =
                  ((realImplBadAppend pk sk) t).run (reverseSigned s) := by
            intro pk sk t s
            rcases s with ⟨⟨cache, signed⟩, bad⟩
            cases t with
            | inl t' =>
                simp [reverseSigned, realImplBadAppend, _realImplSigned, baseSimSigned,
                  baseSimSigned', QueryImpl.add_apply_inl, QueryImpl.withBadFlag_apply_run,
                  StateT.run_bind, StateT.run_get, StateT.run_set]
            | inr msg =>
                simp [reverseSigned, realImplBadAppend, _realImplSigned, realSignBadAppend,
                  realSignSignedAppend, realSignSigned, realSignSigned', sigBadFSigned,
                  QueryImpl.add_apply_inr, QueryImpl.withBadUpdate_apply_run, StateT.run_bind,
                  StateT.run_get, StateT.run_set, List.reverse_reverse, List.reverse_cons,
                  List.reverse_append, List.reverse_singleton, List.append_assoc]
          have h_direct_real_append_proj : ∀ (pk : Stmt) (sk : Wit),
              Prod.map id reverseSigned <$> direct_real_exp pk sk =
                direct_real_exp_append pk sk := by
            intro pk sk
            simpa [direct_real_exp, direct_real_exp_append, reverseSigned] using
              (OracleComp.map_run_simulateQ_eq_of_query_map_eq'
                (impl₁ := _realImplSigned pk sk) (impl₂ := realImplBadAppend pk sk)
                (proj := reverseSigned) (hproj := h_realImpl_append_proj pk sk)
                (oa := adv.main pk) (s := ((∅, []), false)))
          have h_event_reverse :
              ∀ (pk : Stmt),
                event pk ∘ Prod.map id reverseSigned = event pk := by
            intro pk
            funext z
            simp [event, reverseSigned, List.mem_reverse]
          intro pk sk
          calc
            Pr[event pk | direct_real_exp_append pk sk] =
                Pr[event pk | Prod.map id reverseSigned <$> direct_real_exp pk sk] := by
                  rw [h_direct_real_append_proj pk sk]
            _ = Pr[event pk ∘ Prod.map id reverseSigned | direct_real_exp pk sk] := by
                  rw [probEvent_map]
            _ = Pr[event pk | direct_real_exp pk sk] := by
                  rw [h_event_reverse pk]
        have h_keygen_sum_one : (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk) = 1 :=
          HasEvalPMF.tsum_probOutput_eq_one hr.gen
        let slackReal : ENNReal :=
          (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β +
            ENNReal.ofReal ((qS * (qS + qH) : ℕ) * ζ_zk) + δ_verify
        have h_per_term : ∀ (pksk : Stmt × Wit),
            evalDist hr.gen pksk * Pr[= true | actual_pk_exp pksk.1 pksk.2] ≤
              evalDist hr.gen pksk *
                (Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2] + slackReal) := by
          intro pksk
          by_cases h0 : evalDist hr.gen pksk = 0
          · rw [h0, zero_mul, zero_mul]
          · have hmem : pksk ∈ support hr.gen := by
              exact (mem_support_iff_evalDist_apply_ne_zero hr.gen pksk).2 h0
            have hrel : rel pksk.1 pksk.2 = true := hr.gen_sound _ _ hmem
            gcongr
            calc
              Pr[= true | actual_pk_exp pksk.1 pksk.2]
                  ≤ Pr[eventNoBad pksk.1 | actual_stateful_exp_append pksk.1 pksk.2] + δ_verify :=
                    h_actual_hit_le pksk.1 pksk.2
              _ = Pr[event pksk.1 | direct_actual_exp_append pksk.1 pksk.2] + δ_verify := by
                    rw [h_event_actual_proj pksk.1 pksk.2]
              _ ≤ (Pr[event pksk.1 | direct_real_exp_append pksk.1 pksk.2] +
                    Pr[badPred | direct_real_exp_append pksk.1 pksk.2]) + δ_verify := by
                    gcongr
                    exact h_actual_vs_real_append pksk.1 pksk.2 hrel
              _ ≤ (Pr[event pksk.1 | direct_real_exp_append pksk.1 pksk.2] +
                    ((qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β +
                      ENNReal.ofReal ((qS * (qS + qH) : ℕ) * ζ_zk))) + δ_verify := by
                    gcongr
                    exact h_pr_bad_real_append pksk.1 pksk.2 hrel
              _ = Pr[event pksk.1 | direct_real_exp_append pksk.1 pksk.2] +
                    slackReal := by
                    simp [slackReal, add_assoc]
              _ = Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2] + slackReal := by
                    rw [h_event_real_append_eq pksk.1 pksk.2]
        rw [hAdv_eq_tsum_actual]
        have h_step1 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              Pr[= true | actual_pk_exp pksk.1 pksk.2]) ≤
              ∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                (Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2] + slackReal) :=
          ENNReal.tsum_le_tsum h_per_term
        have h_step2 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              (Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2] + slackReal)) =
              (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) +
                slackReal :=
          ENNReal.tsum_mul_add_const_of_tsum_eq_one _ _ _ h_keygen_sum_one
        calc
          (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
            Pr[= true | actual_pk_exp pksk.1 pksk.2])
              ≤ ∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                (Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2] + slackReal) := h_step1
          _ = (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) + slackReal := h_step2
          _ ≤ (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) +
                (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β +
                ENNReal.ofReal ((qS * (qS + qH) : ℕ) * ζ_zk) +
                δ_verify := by
                  simpa [slackReal, add_assoc]
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
        classical
        have h_simImplSigned_sign_lift :
            ∀ (pk : Stmt) (msg : M) (cache : spec.QueryCache) (signed : List M),
              ((_simImplSigned pk) (.inr msg)).run ((cache, signed), false) =
                (fun z : (Commit × Resp) × spec.QueryCache × Bool =>
                  (z.1, ((z.2.1, msg :: signed), z.2.2))) <$>
                  ((_simImpl pk) (.inr msg)).run (cache, false) := by
          intro pk msg cache signed
          simp [sigBadFSigned, sigBadF, _simImplSigned, _simImpl, sigSimSigned, sigSimBad,
            sigSimSigned', QueryImpl.add_apply_inr, QueryImpl.withBadUpdate_apply_run,
            StateT.run_bind, StateT.run_get, StateT.run_set]
        have h_realImplSigned_sign_lift :
            ∀ (pk : Stmt) (sk : Wit) (msg : M) (cache : spec.QueryCache) (signed : List M),
              ((_realImplSigned pk sk) (.inr msg)).run ((cache, signed), false) =
                (fun z : (Commit × Resp) × spec.QueryCache × Bool =>
                  (z.1, ((z.2.1, msg :: signed), z.2.2))) <$>
                  ((_realImpl pk sk) (.inr msg)).run (cache, false) := by
          intro pk sk msg cache signed
          simp [sigBadFSigned, sigBadF, _realImplSigned, _realImpl, realSignSigned,
            realSignBad, realSignSigned', QueryImpl.add_apply_inr,
            QueryImpl.withBadUpdate_apply_run, StateT.run_bind, StateT.run_get, StateT.run_set]
        have sign_step_tv_signed :
            ∀ (pk : Stmt) (sk : Wit) (msg : M) (cache : spec.QueryCache) (signed : List M),
              rel pk sk = true →
                tvDist
                  (((_simImplSigned pk) (.inr msg)).run ((cache, signed), false))
                  (((_realImplSigned pk sk) (.inr msg)).run ((cache, signed), false)) ≤
                  ζ_zk := by
          intro pk sk msg cache signed h_rel
          rw [h_simImplSigned_sign_lift pk msg cache signed,
            h_realImplSigned_sign_lift pk sk msg cache signed]
          refine le_trans (tvDist_map_le _ _ _) ?_
          exact sign_step_tv pk sk msg cache h_rel
        have step_b_per_pksk_signed_tv : ∀ (pk : Stmt) (sk : Wit), rel pk sk = true →
            tvDist (direct_sim_exp pk) (direct_real_exp pk sk) ≤
              qS * ζ_zk + Pr[badPred | direct_sim_exp pk].toReal := by
          intro pk sk h_rel
          let S : (spec + (M →ₒ (Commit × Resp))).Domain → Prop :=
            fun t => match t with | .inr _ => True | .inl _ => False
          have hS_dec : DecidablePred S := by
            intro t
            cases t with
            | inl _ => exact instDecidableFalse
            | inr _ => exact instDecidableTrue
          letI := hS_dec
          have apply_selective :=
            @OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_qSeps_plus_probEvent_output_bad
          refine apply_selective
            (impl₁ := _simImplSigned pk) (impl₂ := _realImplSigned pk sk)
            (ε := ζ_zk) _hζ_zk S
            ?h_step_tv_S ?h_step_eq_nS ?h_mono₁ (oa := adv.main pk) (qS := qS) ?h_qb
            (s₀ := ((∅ : spec.QueryCache), ([] : List M)))
          case h_step_tv_S =>
            intro t hSt s
            cases t with
            | inl _ => exact hSt.elim
            | inr msg =>
                rcases s with ⟨cache, signed⟩
                simpa using sign_step_tv_signed pk sk msg cache signed h_rel
          case h_step_eq_nS =>
            intro t hSt p
            cases t with
            | inl _ =>
                simp [_simImplSigned, _realImplSigned, QueryImpl.add_apply_inl]
            | inr _ => exact (hSt trivial).elim
          case h_mono₁ =>
            intro t p hp z hz
            obtain ⟨⟨cache, signed⟩, bad⟩ := p
            dsimp only at hp
            subst hp
            dsimp only [_simImplSigned, baseSimSigned, sigSimSigned] at hz
            cases t with
            | inl t' =>
                simp only [QueryImpl.add_apply_inl] at hz
                exact support_withBadFlag_run_snd_snd baseSimSigned' t' (cache, signed) true hz
            | inr msg =>
                simp only [QueryImpl.add_apply_inr] at hz
                exact support_withBadUpdate_run_snd_snd_of_pre (sigSimSigned' pk) sigBadFSigned
                  msg (cache, signed) hz
          case h_qb =>
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
        intro pk sk h_rel
        let eventDec :
            ((M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool) → Bool :=
          fun z => decide (event pk z)
        let eventGameReal : OracleComp spec Bool := eventDec <$> direct_real_exp pk sk
        let eventGameSim : OracleComp spec Bool := eventDec <$> direct_sim_exp pk
        have h_eventPred_eq :
            ((fun b : Bool => b = true) ∘ fun z :
                (M × (Commit × Resp)) × (spec.QueryCache × List M) × Bool =>
                  decide (event pk z)) = event pk := by
          funext z
          simp
        have htv_event :
            tvDist eventGameReal eventGameSim ≤
              qS * ζ_zk + Pr[badPred | direct_sim_exp pk].toReal := by
          dsimp [eventGameReal, eventGameSim, eventDec]
          refine le_trans (tvDist_map_le _ _ _) ?_
          rw [tvDist_comm]
          exact step_b_per_pksk_signed_tv pk sk h_rel
        have h_event_real :
            Pr[event pk | direct_real_exp pk sk] = Pr[= true | eventGameReal] := by
          dsimp [eventGameReal, eventDec]
          rw [← probEvent_true_eq_probOutput]
          simpa [h_eventPred_eq] using
            (probEvent_map (mx := direct_real_exp pk sk) (f := fun z =>
              decide (event pk z)) (q := fun b : Bool => b = true)).symm
        have h_event_sim :
            Pr[event pk | direct_sim_exp pk] = Pr[= true | eventGameSim] := by
          dsimp [eventGameSim, eventDec]
          rw [← probEvent_true_eq_probOutput]
          simpa [h_eventPred_eq] using
            (probEvent_map (mx := direct_sim_exp pk) (f := fun z =>
              decide (event pk z)) (q := fun b : Bool => b = true)).symm
        have hdiff :
            |Pr[= true | eventGameReal].toReal - Pr[= true | eventGameSim].toReal| ≤
              qS * ζ_zk + Pr[badPred | direct_sim_exp pk].toReal :=
          le_trans (abs_probOutput_toReal_sub_le_tvDist eventGameReal eventGameSim) htv_event
        have h_event_toReal :
            Pr[event pk | direct_real_exp pk sk].toReal ≤
              Pr[event pk | direct_sim_exp pk].toReal +
                (qS * ζ_zk + Pr[badPred | direct_sim_exp pk].toReal) := by
          rw [← h_event_real, ← h_event_sim] at hdiff
          rw [abs_le] at hdiff
          linarith
        have h_event_real_ne : Pr[event pk | direct_real_exp pk sk] ≠ ⊤ := probEvent_ne_top
        have h_event_sim_ne : Pr[event pk | direct_sim_exp pk] ≠ ⊤ := probEvent_ne_top
        have h_bad_ne : Pr[badPred | direct_sim_exp pk] ≠ ⊤ := probEvent_ne_top
        have hqζ_nonneg : 0 ≤ qS * ζ_zk := mul_nonneg (Nat.cast_nonneg _) _hζ_zk
        have hslack_nonneg :
            0 ≤ qS * ζ_zk + Pr[badPred | direct_sim_exp pk].toReal :=
          add_nonneg hqζ_nonneg ENNReal.toReal_nonneg
        calc
          Pr[event pk | direct_real_exp pk sk]
              = ENNReal.ofReal (Pr[event pk | direct_real_exp pk sk].toReal) := by
                  rw [ENNReal.ofReal_toReal h_event_real_ne]
          _ ≤ ENNReal.ofReal
                (Pr[event pk | direct_sim_exp pk].toReal +
                  (qS * ζ_zk + Pr[badPred | direct_sim_exp pk].toReal)) := by
                  exact ENNReal.ofReal_le_ofReal h_event_toReal
          _ = Pr[event pk | direct_sim_exp pk] +
                (ENNReal.ofReal (qS * ζ_zk) + Pr[badPred | direct_sim_exp pk]) := by
                rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hslack_nonneg,
                  ENNReal.ofReal_toReal h_event_sim_ne,
                  ENNReal.ofReal_add hqζ_nonneg ENNReal.toReal_nonneg,
                  ENNReal.ofReal_toReal h_bad_ne]
          _ = Pr[event pk | direct_sim_exp pk] +
                ENNReal.ofReal (qS * ζ_zk) +
                Pr[badPred | direct_sim_exp pk] := by
                ac_rfl
      -- (B-finish) `pr_bad_le_signed`: per-pk, the simulator's bad event is bounded by
      -- `qS · (qS + qH) · β` using the `simCommitPredictability simTranscript β` hypothesis.
      --
      -- **Union bound structure.** The bad flag `z.2.2 = true` flips at a `sigSimSigned pk msg`
      -- query iff the sampled commit `c` (from `simTranscript pk`) hits a previously-cached
      -- entry `(.inr (msg, c)) ↦ _`. The bound follows from three facts:
      --   (F1) The flag is monotone: once `true`, every subsequent query preserves it
      --        (by `support_withBadUpdate_run_snd_snd_of_pre` and `support_withBadFlag_run_snd_snd`
      --        at the level of `sigSimSigned` and `baseSimSigned` respectively).
      --   (F2) Per-step collision bound: at any signing query `msg` with cache state `c'`, the
      --        probability that a freshly sampled commit `c ← simTranscript pk` satisfies
      --        `c'.isSome (.inr (msg, c))` is at most
      --        `|{c : c' (.inr (msg, c)) = some _}| · β ≤ |c'.dom| · β ≤ (qS + qH) · β`
      --        (using `simCommitPredictability simTranscript β` and the query-count bound).
      --   (F3) At most `qS` sign queries fire (by `signHashQueryBound.proj₁ _hQ pk`).
      --
      -- **Formal union bound.** Structure the proof as an induction on `adv.main pk` using
      -- `OracleComp.inductionOn`, with invariant
      --
      --   Pr[z.2.2 = true | (simulateQ (_simImplSigned pk) oa).run ((c₀, ℓ₀), false)]
      --     ≤ (qS_rem) · (qH_rem + |c₀.dom ∩ .inr|) · β
      --
      -- where `qS_rem`, `qH_rem` are the remaining sign / hash query budgets of `oa` and
      -- `|c₀.dom ∩ .inr|` counts cached `.inr` entries. At the start `c₀ = ∅`, `qS_rem = qS`,
      -- `qH_rem = qH`, giving the stated `qS · (qS + qH) · β` bound.
      --
      -- The `pure` case is `Pr[false | pure _] = 0`. The `.inl` query case (RO/unif) grows the
      -- `.inl` cache entries and preserves the bad flag; the `.inr` query case (signing)
      -- samples from `simTranscript pk` and contributes at most `(qH_rem + |c₀.dom ∩ .inr|) · β`
      -- from this step (by `simCommitPredictability`), plus the IH bound with `qS_rem - 1` and
      -- `|c'.dom ∩ .inr| ≤ |c₀.dom ∩ .inr| + 1`.
      --
      -- **Structure.** The induction has three ingredients:
      --   * A per-step collision bound on the per-sign-query bad flip probability,
      --     using `simCommitPredictability`.
      --   * A cache-size bookkeeping bound tied to `signHashQueryBound`.
      --   * The induction itself, lifting per-step bounds to the total bound
      --     through `probEvent_bind_le_add` at each query step.
      have pr_bad_le_signed : ∀ (pk : Stmt),
          Pr[badPred | direct_sim_exp pk] ≤
            (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β := by
        have pr_bad_logged_le :
            ∀ {α : Type} (pk : Stmt)
              (oa : OracleComp (spec + (M →ₒ (Commit × Resp))) α)
              (s h K : ℕ) (cache : spec.QueryCache) (keys : List (M × Commit)),
              signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := oa) s h →
              keyCovers ((cache, false), keys) →
              keys.length + s + h ≤ K →
              Pr[fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                  z.2.1.2 = true |
                (simulateQ (_simImplLogged pk) oa).run ((cache, false), keys)] ≤
                (s : ENNReal) * (K : ENNReal) * β := by
          intro α pk oa
          induction oa using OracleComp.inductionOn with
          | pure x =>
              intro s h K cache keys hQ hKeys hLen
              simp [simulateQ_pure]
          | query_bind t mx ih =>
              intro s h K cache keys hQ hKeys hLen
              rw [signHashQueryBound, OracleComp.isQueryBound_query_bind_iff] at hQ
              obtain ⟨hcan, hrest⟩ := hQ
              cases t with
              | inl t' =>
                  cases t' with
                  | inl n =>
                      let qn :
                          OracleComp spec
                            ((spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inl n))) :=
                        show OracleComp spec
                            ((spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inl n))) from
                          (liftM (spec.query (Sum.inl n)) : OracleComp spec _)
                      have hstep :
                          (liftM ((_simImplLogged pk) (.inl (.inl n))) :
                              StateT ((spec.QueryCache × Bool) × List (M × Commit))
                                (OracleComp spec) _).run ((cache, false), keys) =
                              ((fun u : (spec + (M →ₒ (Commit × Resp))).Range
                                  (Sum.inl (Sum.inl n)) =>
                                  (u, (cache, false), keys)) <$> qn) := by
                            change ((_simImplLogged pk) (.inl (.inl n))).run ((cache, false), keys) =
                              ((fun u : (spec + (M →ₒ (Commit × Resp))).Range
                                  (Sum.inl (Sum.inl n)) =>
                                  (u, (cache, false), keys)) <$> qn)
                            have hlogged :
                                _simImplLogged pk = QueryImpl.extendState (_simImpl pk) keyAux := rfl
                            rw [hlogged, QueryImpl.extendState_apply]
                            simp [_simImpl, QueryImpl.add_apply_inl, h_baseSimBad_unif n cache,
                              qn, keyAux, bind_pure_comp]
                      have hrun :
                          (simulateQ (_simImplLogged pk)
                            ((liftM (query (Sum.inl (Sum.inl n)))) >>= mx)).run
                              ((cache, false), keys) =
                            (qn >>= fun u =>
                              (simulateQ (_simImplLogged pk) (mx u)).run ((cache, false), keys)) := by
                            simp only [simulateQ_query_bind, OracleQuery.input_query,
                              StateT.run_bind]
                            rw [hstep]
                            simp [qn, OracleQuery.cont_query, bind_assoc, bind_pure_comp]
                      rw [hrun]
                      rw [probEvent_bind_eq_tsum]
                      calc
                        ∑' u, Pr[= u | qn] *
                            Pr[fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                                z.2.1.2 = true |
                              (simulateQ (_simImplLogged pk) (mx u)).run ((cache, false), keys)]
                            ≤
                            ∑' u, Pr[= u | qn] *
                              ((s : ENNReal) * (K : ENNReal) * β) := by
                                refine ENNReal.tsum_le_tsum fun u => ?_
                                exact mul_le_mul' le_rfl
                                  (ih u s h K cache keys (hrest u) hKeys hLen)
                        _ = (∑' u, Pr[= u | qn]) *
                              ((s : ENNReal) * (K : ENNReal) * β) := by
                                rw [ENNReal.tsum_mul_right]
                        _ = (s : ENNReal) * (K : ENNReal) * β := by
                                rw [HasEvalPMF.tsum_probOutput_eq_one, one_mul]
                  | inr mc =>
                      by_cases hcache : cache (.inr mc) = none
                      · let qmc :
                            OracleComp spec
                              ((spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) :=
                          show OracleComp spec
                              ((spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) from
                            (liftM (spec.query (Sum.inr mc)) : OracleComp spec _)
                        have hstep :
                          (liftM ((_simImplLogged pk) (.inl (.inr mc))) :
                              StateT ((spec.QueryCache × Bool) × List (M × Commit))
                                (OracleComp spec) _).run ((cache, false), keys) =
                              ((fun u : (spec + (M →ₒ (Commit × Resp))).Range
                                  (Sum.inl (Sum.inr mc)) =>
                                  (u, (cache.cacheQuery (.inr mc) u, false), mc :: keys)) <$>
                                qmc) := by
                            change ((_simImplLogged pk) (.inl (.inr mc))).run ((cache, false), keys) =
                              ((fun u : (spec + (M →ₒ (Commit × Resp))).Range
                                  (Sum.inl (Sum.inr mc)) =>
                                  (u, (cache.cacheQuery (.inr mc) u, false), mc :: keys)) <$>
                                qmc)
                            have hlogged :
                                _simImplLogged pk = QueryImpl.extendState (_simImpl pk) keyAux := rfl
                            rw [hlogged, QueryImpl.extendState_apply]
                            simp [_simImpl, QueryImpl.add_apply_inl,
                              h_baseSimBad_hash_miss mc cache hcache, qmc, keyAux,
                              bind_pure_comp]
                        have hrun :
                            (simulateQ (_simImplLogged pk)
                              ((liftM (query (Sum.inl (Sum.inr mc)))) >>= mx)).run
                                ((cache, false), keys) =
                              (qmc >>= fun u =>
                                (simulateQ (_simImplLogged pk) (mx u)).run
                                  ((cache.cacheQuery (.inr mc) u, false), mc :: keys)) := by
                              simp only [simulateQ_query_bind, OracleQuery.input_query,
                                StateT.run_bind]
                              rw [hstep]
                              simp [qmc, OracleQuery.cont_query, bind_assoc, bind_pure_comp]
                        rw [hrun]
                        rw [probEvent_bind_eq_tsum]
                        calc
                          ∑' u, Pr[= u | qmc] *
                              Pr[fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                                  z.2.1.2 = true |
                                (simulateQ (_simImplLogged pk) (mx u)).run
                                  ((cache.cacheQuery (.inr mc) u, false), mc :: keys)]
                              ≤
                              ∑' u, Pr[= u | qmc] *
                                ((s : ENNReal) * (K : ENNReal) * β) := by
                                  refine ENNReal.tsum_le_tsum fun u => ?_
                                  apply mul_le_mul' le_rfl
                                  have hh : 0 < h := by simpa using hcan
                                  have hLen' : (mc :: keys).length + s + (h - 1) ≤ K := by
                                    have hEq :
                                        (mc :: keys).length + s + (h - 1) =
                                          keys.length + s + h := by
                                      simp [List.length]
                                      omega
                                    rw [hEq]
                                    exact hLen
                                  exact ih u s (h - 1) K
                                    (cache.cacheQuery (.inr mc) u) (mc :: keys)
                                    (hrest u)
                                    (keyCovers_cacheQuery (mc := mc) (ω := u) hKeys) hLen'
                          _ = (∑' u, Pr[= u | qmc]) *
                                ((s : ENNReal) * (K : ENNReal) * β) := by
                                  rw [ENNReal.tsum_mul_right]
                          _ = (s : ENNReal) * (K : ENNReal) * β := by
                                  rw [HasEvalPMF.tsum_probOutput_eq_one, one_mul]
                      · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists.mp hcache
                        have hstep :
                            (liftM ((_simImplLogged pk) (.inl (.inr mc))) :
                                StateT ((spec.QueryCache × Bool) × List (M × Commit))
                                  (OracleComp spec) _).run ((cache, false), keys) =
                                pure (u, ((cache, false), mc :: keys)) := by
                              change ((_simImplLogged pk) (.inl (.inr mc))).run ((cache, false), keys) =
                                pure (u, ((cache, false), mc :: keys))
                              have hlogged :
                                  _simImplLogged pk = QueryImpl.extendState (_simImpl pk) keyAux := rfl
                              rw [hlogged, QueryImpl.extendState_apply]
                              simp [_simImpl, QueryImpl.add_apply_inl, keyAux]
                              rw [h_baseSimBad_hash_hit mc cache u hu.symm]
                              change
                                (fun a :
                                    (spec + (M →ₒ (Commit × Resp))).Range
                                      (Sum.inl (Sum.inr mc)) × (spec.QueryCache × Bool) =>
                                    (a.1, a.2, mc :: keys)) <$>
                                  (pure (u, (cache, false)) :
                                    OracleComp spec
                                      ((spec + (M →ₒ (Commit × Resp))).Range
                                        (Sum.inl (Sum.inr mc)) × (spec.QueryCache × Bool))) =
                                    pure (u, (cache, false), mc :: keys)
                              have hmap :
                                  (fun a :
                                      (spec + (M →ₒ (Commit × Resp))).Range
                                        (Sum.inl (Sum.inr mc)) × (spec.QueryCache × Bool) =>
                                      (a.1, a.2, mc :: keys)) <$>
                                    (pure (u, (cache, false)) :
                                      OracleComp spec
                                        ((spec + (M →ₒ (Commit × Resp))).Range
                                          (Sum.inl (Sum.inr mc)) × (spec.QueryCache × Bool))) =
                                      pure (u, (cache, false), mc :: keys) := by
                                    simpa [bind_pure_comp] using
                                      (pure_bind
                                        (f := fun a :
                                          (spec + (M →ₒ (Commit × Resp))).Range
                                            (Sum.inl (Sum.inr mc)) × (spec.QueryCache × Bool) =>
                                            pure (a.1, a.2, mc :: keys))
                                        (x := (u, (cache, false))))
                              exact hmap
                        have hrun :
                            (simulateQ (_simImplLogged pk)
                              ((liftM (query (Sum.inl (Sum.inr mc)))) >>= mx)).run
                                ((cache, false), keys) =
                              (simulateQ (_simImplLogged pk) (mx u)).run
                                ((cache, false), mc :: keys) := by
                              simp only [simulateQ_query_bind, OracleQuery.input_query,
                                StateT.run_bind]
                              rw [hstep]
                              simp [OracleQuery.cont_query]
                        rw [hrun]
                        have hh : 0 < h := by simpa using hcan
                        have hLen' : (mc :: keys).length + s + (h - 1) ≤ K := by
                          have hEq : (mc :: keys).length + s + (h - 1) = keys.length + s + h := by
                            simp [List.length]
                            omega
                          rw [hEq]
                          exact hLen
                        simpa using
                          ih u s (h - 1) K cache (mc :: keys) (hrest u)
                            (keyCovers_cons (mc := mc) hKeys) hLen'
              | inr msg =>
                  let qsig : OracleComp spec (Commit × Chal × Resp) := liftM (simTranscript pk)
                  have hstep :
                      (liftM ((_simImplLogged pk) (.inr msg)) :
                          StateT ((spec.QueryCache × Bool) × List (M × Commit))
                            (OracleComp spec) _).run ((cache, false), keys) =
                          ((fun cωπ =>
                              ((cωπ.1, cωπ.2.2),
                                ((match cache (.inr (msg, cωπ.1)) with
                                    | some _ => cache
                                    | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                                  (cache (.inr (msg, cωπ.1))).isSome),
                                (msg, cωπ.1) :: keys)) <$> qsig) := by
                        change ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys) =
                          ((fun cωπ =>
                              ((cωπ.1, cωπ.2.2),
                                ((match cache (.inr (msg, cωπ.1)) with
                                    | some _ => cache
                                    | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                                  (cache (.inr (msg, cωπ.1))).isSome),
                                (msg, cωπ.1) :: keys)) <$> qsig)
                        have hlogged :
                            _simImplLogged pk = QueryImpl.extendState (_simImpl pk) keyAux := rfl
                        rw [hlogged, QueryImpl.extendState_apply]
                        simp [_simImpl, QueryImpl.add_apply_inr, h_sigSimBad_run pk msg cache,
                          qsig, keyAux, bind_pure_comp, liftComp_eq_liftM]
                  have hrun :
                      (simulateQ (_simImplLogged pk)
                        ((liftM (query (Sum.inr msg))) >>= mx)).run ((cache, false), keys) =
                        (qsig >>= fun cωπ =>
                          (simulateQ (_simImplLogged pk) (mx (cωπ.1, cωπ.2.2))).run
                            (((match cache (.inr (msg, cωπ.1)) with
                                  | some _ => cache
                                  | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                                (cache (.inr (msg, cωπ.1))).isSome),
                              (msg, cωπ.1) :: keys)) := by
                        simp only [simulateQ_query_bind, OracleQuery.input_query,
                          StateT.run_bind]
                        rw [hstep]
                        simp [qsig, OracleQuery.cont_query, bind_assoc, bind_pure_comp]
                  rw [hrun]
                  have hstepBad :
                      Pr[fun cωπ : Commit × Chal × Resp =>
                          ¬ ((cache (.inr (msg, cωπ.1))).isSome = false) |
                        qsig] ≤
                        (K : ENNReal) * β := by
                    have hcongr :
                        Pr[fun cωπ : Commit × Chal × Resp =>
                            ¬ ((cache (.inr (msg, cωπ.1))).isSome = false) |
                          qsig] =
                          Pr[fun cωπ : Commit × Chal × Resp =>
                            (cache (.inr (msg, cωπ.1))).isSome = true |
                            qsig] := by
                      refine probEvent_congr' (oa := qsig) ?_ rfl
                      intro cωπ _
                      cases hhit : (cache (.inr (msg, cωπ.1))).isSome <;> simp [hhit]
                    calc
                      Pr[fun cωπ : Commit × Chal × Resp =>
                          ¬ ((cache (.inr (msg, cωπ.1))).isSome = false) |
                        qsig]
                          = Pr[fun cωπ : Commit × Chal × Resp =>
                              (cache (.inr (msg, cωπ.1))).isSome = true |
                              qsig] := hcongr
                      _ = Pr[fun z :
                            (Commit × Resp) × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                              z.2.1.2 = true |
                            ((_simImplLogged pk) (.inr msg)).run ((cache, false), keys)] := by
                              symm
                              simpa [qsig, liftComp_eq_liftM] using
                                sigStep_bad_eq_cacheHit pk msg cache keys
                      _ ≤ (keys.length : ENNReal) * β := sigStep_bad_le_keys pk msg cache keys hKeys
                      _ ≤ (K : ENNReal) * β := by
                              gcongr
                              omega
                  have hcombine := probEvent_bind_le_add
                    (mx := qsig)
                    (my := fun cωπ =>
                      (simulateQ (_simImplLogged pk) (mx (cωπ.1, cωπ.2.2))).run
                        (((match cache (.inr (msg, cωπ.1)) with
                              | some _ => cache
                              | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                            (cache (.inr (msg, cωπ.1))).isSome),
                          (msg, cωπ.1) :: keys))
                    (p := fun cωπ : Commit × Chal × Resp =>
                      (cache (.inr (msg, cωπ.1))).isSome = false)
                    (q := fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                      z.2.1.2 = false)
                    (ε₁ := (K : ENNReal) * β)
                    (ε₂ := ((s - 1 : ℕ) : ENNReal) * (K : ENNReal) * β)
                    hstepBad
                    (by
                      intro cωπ _ hmiss
                      have hs : 0 < s := by simpa using hcan
                      have hnone : cache (.inr (msg, cωπ.1)) = none := by
                        cases hcache' : cache (.inr (msg, cωπ.1)) with
                        | none => rfl
                        | some v =>
                            simp [hcache'] at hmiss
                      have hLen' : ((msg, cωπ.1) :: keys).length + (s - 1) + h ≤ K := by
                        have hEq :
                            ((msg, cωπ.1) :: keys).length + (s - 1) + h = keys.length + s + h := by
                          simp [List.length]
                          omega
                        rw [hEq]
                        exact hLen
                      simpa [hnone] using
                        (ih (cωπ.1, cωπ.2.2) (s - 1) h K
                          (cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1)
                          ((msg, cωπ.1) :: keys) (hrest (cωπ.1, cωπ.2.2))
                          (keyCovers_cacheQuery (mc := (msg, cωπ.1)) (ω := cωπ.2.1) hKeys)
                          hLen'))
                  have hcombine' :
                      Pr[fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                          z.2.1.2 = true |
                        qsig >>= fun cωπ =>
                          (simulateQ (_simImplLogged pk) (mx (cωπ.1, cωπ.2.2))).run
                            (((match cache (.inr (msg, cωπ.1)) with
                                  | some _ => cache
                                  | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                                (cache (.inr (msg, cωπ.1))).isSome),
                              (msg, cωπ.1) :: keys)] ≤
                        (K : ENNReal) * β + ((s - 1 : ℕ) : ENNReal) * (K : ENNReal) * β := by
                    simpa using hcombine
                  calc
                    Pr[fun z : α × ((spec.QueryCache × Bool) × List (M × Commit)) =>
                        z.2.1.2 = true |
                      qsig >>= fun cωπ =>
                        (simulateQ (_simImplLogged pk) (mx (cωπ.1, cωπ.2.2))).run
                          (((match cache (.inr (msg, cωπ.1)) with
                                | some _ => cache
                                | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1),
                              (cache (.inr (msg, cωπ.1))).isSome),
                            (msg, cωπ.1) :: keys)]
                        ≤ (K : ENNReal) * β +
                            ((s - 1 : ℕ) : ENNReal) * (K : ENNReal) * β := hcombine'
                    _ = (s : ENNReal) * (K : ENNReal) * β := by
                        have hs : 1 + (s - 1) = s := by omega
                        have hs_cast : (1 : ENNReal) + (s - 1 : ℕ) = s := by
                          exact_mod_cast hs
                        calc
                          (K : ENNReal) * β + ((s - 1 : ℕ) : ENNReal) * (K : ENNReal) * β
                              = (K : ENNReal) * β +
                                  ((s - 1 : ℕ) : ENNReal) * ((K : ENNReal) * β) := by
                                      rw [mul_assoc]
                          _ = (1 : ENNReal) * ((K : ENNReal) * β) +
                                  ((s - 1 : ℕ) : ENNReal) * ((K : ENNReal) * β) := by
                                  congr 1
                                  simp
                          _ = ((1 : ENNReal) + (s - 1 : ℕ)) * ((K : ENNReal) * β) := by
                                  rw [← add_mul]
                          _ = (s : ENNReal) * ((K : ENNReal) * β) := by
                                  rw [hs_cast]
                          _ = (s : ENNReal) * (K : ENNReal) * β := by
                                  rw [mul_assoc]
        intro pk
        have hLen : ([] : List (M × Commit)).length + qS + qH ≤ qS + qH := by simp
        have hlogged :=
          pr_bad_logged_le pk (adv.main pk) qS qH (qS + qH) ∅ [] (_hQ pk)
            (by
              intro mc ω hcache
              simp at hcache)
            hLen
        calc
          Pr[badPred | direct_sim_exp pk]
              = Pr[badPredSimple | direct_sim_exp_simple pk] := pr_bad_eq_simple pk
          _ = Pr[badPredLogged | direct_sim_exp_logged pk] := pr_bad_eq_logged pk
          _ ≤ (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β := by
              simpa [direct_sim_exp_logged]
                using hlogged
      -- (C') `bridge_sim_fork_freshness`: bridge the (pk-summed) sim-side event probability
      -- to `Fork.advantage`. No additional slack is needed here, the fresh-challenge miss term
      -- is already isolated in the (A) bridge as `δ_verify`.
      --
      -- Proof structure:
      --   (1) Distribute `Fork.advantage` as a keygen-indexed tsum, matching the shape of the
      --       LHS (this mirrors `hAdv_eq_tsum` in `euf_nma_bound`).
      --   (2) Apply a per-pk inequality
      --         `Pr[event pk | direct_sim_exp pk] ≤ Pr[forkPoint.isSome | runTrace pk]`
      --       which is the genuine coupling content (`per_pk_event_le_forkPoint` below).
      --   (3) Chain via `ENNReal.tsum_le_tsum` and `mul_le_mul_left'`.
      --
      -- Key insight driving (2): a forgery `(msg, c, π)` with `¬msg ∈ signed` cannot have
      -- used a programmed `(msg, c)` cache entry, since `sigSimSigned pk` only programs at
      -- signed `msg`. So if `event pk z` holds (cache contains `(msg, c)` and verify
      -- succeeds), then `(msg, c)` was queried via the live RO (recorded in
      -- `Fork.runTrace`'s `queryLog`), exactly the condition for `forkPoint trace = some _`.
      -- Formally, this requires a coupling between `direct_sim_exp pk` and `runTrace pk`
      -- that preserves the shared `(forgery, advCache)` marginal and tracks the
      -- `advCache \ roCache` delta, as built below via `richSim`.
      have bridge_sim_fork_freshness :
          (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
            Pr[event pksk.1 | direct_sim_exp pksk.1]) ≤
            Fork.advantage σ hr M nmaAdv qH := by
        -- Per-pk inequality: the LHS event at `direct_sim_exp pk` is dominated by the
        -- fork-point success probability at `runTrace pk`. This is the coupling content.
        --
        -- Proof structure: build a "rich" simulator
        --   `richSim pk : QueryImpl (spec + sigSpec)
        --       (StateT ((QueryCache × List M × Bool) × (roCache × queryLog)) ProbComp)`
        -- that simultaneously tracks `direct_sim_exp`'s and `runTrace`'s full state.
        -- Two projection lemmas then recover each side:
        --   (P1) forgetting `(roCache, queryLog)` recovers `direct_sim_exp pk`;
        --   (P2) forgetting `(signed, bad)` recovers `runTrace pk` (up to the `verified`
        --        reconstruction from `roCache`).
        -- The pointwise event implication on the joint state: `event pk z ⟹
        -- (forkPoint qH (trace_of z)).isSome` uses the key invariant that in any rich-sim
        -- execution, `roCache ⊆ advCache` (roCache only receives roSim-sourced entries,
        -- which are also cached in advCache), hence
        -- `advCache (.inr (msg, c)) = some ω ∧ msg ∉ signed ⟹ roCache (msg, c) = some ω`
        -- (since `msg ∉ signed` rules out sign-programmed entries as the only other source
        -- of advCache writes); the lockstep invariant
        -- `(msg, c) ∈ roCache.domain ⟺ (msg, c) ∈ queryLog` then finishes.
        -- Three sub-claims in full:
        --
        --   (P1) Distributional equality: there is a "rich" simulation `richSim pk` over `spec`
        --        that jointly tracks `direct_sim_exp pk`'s state `(advCache, signed, bad)` and
        --        `runTrace pk`'s state `(roCache, queryLog)`. Projecting rich→sim recovers
        --        `direct_sim_exp pk` exactly.
        --   (P2) Distributional equality: converting rich's spec-level `(M × Commit →ₒ Chal)`
        --        queries into `wrappedSpec`'s `(Unit →ₒ Chal)` queries and post-processing
        --        `(roCache, queryLog)` into a `Trace` gives the same distribution as
        --        `Fork.runTrace σ hr M nmaAdv pk` (treated as a ProbComp after Fork.exp's
        --        outer `ofLift + uniformSampleImpl` conversion).
        --   (P3) Pointwise implication: on the rich sim's support, `event pk z` implies
        --        `forkPoint qH (trace_of z)).isSome`, where `trace_of` is the rich→trace
        --        projection used in (P2). The proof uses the invariants:
        --          (I1) `roCache mc = some v ⟹ advCache (.inr mc) = some v` (roSim caches);
        --          (I2) `advCache (.inr (msg, c)) = some v ∧ msg ∉ signed ⟹
        --                roCache (msg, c) = some v` (sign-programming only touches `msg∈signed`);
        --          (I3) `roCache mc ≠ none ↔ mc ∈ queryLog` (lockstep);
        --          (I4) `queryLog.length ≤ qH` (from `nmaHashQueryBound`).
        --        Given event, (I2) yields roCache (msg, c) = some ω; then trace.verified = true
        --        (since verify σ holds). (I3) yields (msg, c) ∈ queryLog, so target ∈ queryLog.
        --        (I4) bounds `findIdx < qH + 1`. Hence forkPoint qH trace = some _.
        --
        -- Integration:  LHS = Pr[event | direct_sim_exp]  = Pr[event' | richSim]    (by P1)
        --                                                ≤ Pr[forkPoint' | richSim] (by P3)
        --                                                = Pr[forkPoint | runTrace] (by P2).
        have per_pk_event_le_forkPoint : ∀ (pk : Stmt),
            Pr[event pk | direct_sim_exp pk] ≤
              Pr[fun trace => (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                  (Chal := Chal) qH trace).isSome |
                Fork.runTrace σ hr M nmaAdv pk] :=
          by
            intro pk
            let AdvState : Type := ((spec.QueryCache × List M) × Bool)
            let RoState : Type := Fork.simSt M Commit Chal
            let RichState : Type := AdvState × RoState
            let TraceState : Type := spec.QueryCache × RoState
            let cacheProj : AdvState → spec.QueryCache := fun s => s.1.1
            let simProj : RichState → AdvState := Prod.fst
            let traceProj : RichState → TraceState := fun s => (cacheProj s.1, s.2)
            let advInit : AdvState := ((∅, []), false)
            let roInit : RoState := (∅, [])
            let traceCacheInit : spec.QueryCache := ∅
            let richInit : RichState := (advInit, roInit)
            let traceInit : TraceState := (traceCacheInit, roInit)
            let innerPkg : VCVio.SSP.Package (Fork.wrappedSpec Chal) spec RoState :=
              { init := pure roInit
                impl := Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal }
            let richOuter : VCVio.SSP.Package spec (spec + (M →ₒ (Commit × Resp))) AdvState :=
              { init := pure advInit
                impl := _simImplSigned pk }
            let traceOuter :
                VCVio.SSP.Package spec (spec + (M →ₒ (Commit × Resp))) spec.QueryCache :=
              { init := pure traceCacheInit
                impl := baseSim + sigSim pk }
            let richImpl :
                QueryImpl (spec + (M →ₒ (Commit × Resp)))
                  (StateT RichState (OracleComp (Fork.wrappedSpec Chal))) :=
              (richOuter.link innerPkg).impl
            let traceImpl :
                QueryImpl (spec + (M →ₒ (Commit × Resp)))
                  (StateT TraceState (OracleComp (Fork.wrappedSpec Chal))) :=
              (traceOuter.link innerPkg).impl
            let traceOfState :
                (M × (Commit × Resp)) × TraceState →
                  Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) :=
              fun z =>
                let forgery := z.1
                let advCache := z.2.1
                let roCache := z.2.2.1
                let queryLog := z.2.2.2
                let verified :=
                  match roCache (forgery.1, forgery.2.1) with
                  | some ω => σ.verify pk forgery.2.1 ω forgery.2.2
                  | none => false
                { forgery := forgery
                  advCache := advCache
                  roCache := roCache
                  queryLog := queryLog
                  verified := verified }
            let traceOfRich :
                (M × (Commit × Resp)) × RichState →
                  Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) :=
              fun z => traceOfState (Prod.map id traceProj z)
            let richExp : OracleComp (Fork.wrappedSpec Chal)
                ((M × (Commit × Resp)) × RichState) :=
              (simulateQ richImpl (adv.main pk)).run richInit
            let traceExp : OracleComp (Fork.wrappedSpec Chal)
                (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :=
              traceOfRich <$> richExp
            let richInv : RichState → Prop := fun s =>
              (∀ mc ω, s.2.1 mc = some ω → s.1.1.1 (.inr mc) = some ω) ∧
              (∀ msg c ω, s.1.1.1 (.inr (msg, c)) = some ω →
                s.2.1 (msg, c) = some ω ∨ msg ∈ s.1.1.2) ∧
              (∀ mc, (∃ ω, s.2.1 mc = some ω) ↔ mc ∈ s.2.2)
            have h_nmaHashBound :
                nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := nmaAdv.main pk) qH := by
              simpa [nmaAdv, simulatedNmaAdv] using
                (simulatedNmaAdv_hashQueryBound
                  (σ := σ) (hr := hr) (M := M)
                  (simTranscript := simTranscript)
                  (adv := adv) (qS := qS) (qH := qH) _hQ pk)
            have h_queryLog_len_le_of_nmaHashQueryBound :
                ∀ {α : Type} {oa : OracleComp spec α} {Q : ℕ}
                  (hQ :
                    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                      (oa := oa) Q)
                  (st : RoState) {z : α × RoState},
                  z ∈ support ((simulateQ innerPkg.impl oa).run st) →
                    z.2.2.length ≤ st.2.length + Q := by
              intro α oa Q hQ st z hz
              simpa [innerPkg] using
                (Fork.queryLog_length_le_of_nmaHashQueryBound
                  (M := M) (Commit := Commit) (Chal := Chal)
                  (hQ := hQ) (st := st) (z := z) hz)
            have h_unifFwd_run :
                ∀ {α : Type} (oa : ProbComp α) (st : RoState),
                  (simulateQ (Fork.unifFwd M Commit Chal) oa).run st =
                    (fun x => (x, st)) <$> liftComp oa (Fork.wrappedSpec Chal) := by
              intro α oa st
              let inj : QueryImpl unifSpec (OracleComp (Fork.wrappedSpec Chal)) := fun t =>
                liftM (unifSpec.query t)
              have h_unifFwd_eq :
                  Fork.unifFwd M Commit Chal =
                    inj.liftTarget (StateT RoState (OracleComp (Fork.wrappedSpec Chal))) := rfl
              rw [h_unifFwd_eq, simulateQ_liftTarget]
              have h_simulateQ_inj :
                  simulateQ inj oa = liftComp oa (Fork.wrappedSpec Chal) := rfl
              rw [h_simulateQ_inj, OracleComp.liftM_run_StateT, bind_pure_comp]
            have h_inner_liftComp_run :
                ∀ {α : Type} (oa : ProbComp α) (st : RoState),
                  (simulateQ innerPkg.impl (liftComp oa spec)).run st =
                    (fun x => (x, st)) <$> liftComp oa (Fork.wrappedSpec Chal) := by
              intro α oa st
              rw [show simulateQ innerPkg.impl (liftComp oa spec) =
                  simulateQ (Fork.unifFwd M Commit Chal) oa by
                    simpa [innerPkg] using
                      (QueryImpl.simulateQ_add_liftComp_left
                        (impl₁' := Fork.unifFwd M Commit Chal)
                        (impl₂' := Fork.roImpl M Commit Chal) oa)]
              exact h_unifFwd_run oa st
            have h_richInv_init : richInv richInit := by
              constructor
              · intro mc ω hω
                simp [richInit, advInit, roInit] at hω
              · constructor
                · intro msg c ω hω
                  simp [richInit, advInit, roInit] at hω
                · intro mc
                  simp [richInit, advInit, roInit]
            have h_simImplSigned_unif_run :
                ∀ (n : ℕ) (cache : spec.QueryCache) (signed : List M) (bad : Bool),
                  ((_simImplSigned pk) (Sum.inl (Sum.inl n))).run ((cache, signed), bad) =
                    show OracleComp spec
                        (((spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inl n))) × AdvState) from
                      ((fun u : spec.Range (Sum.inl n) => (u, (((cache, signed), bad) : AdvState))) <$>
                        (liftM (query (Sum.inl n)) : OracleComp spec (spec.Range (Sum.inl n)))) := by
              intro n cache signed bad
              simp [fwd, _simImplSigned, baseSimSigned, baseSimSigned', baseSim, unifSim,
                QueryImpl.add_apply_inl, QueryImpl.withBadFlag_apply_run,
                QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
                StateT.run_bind, StateT.run_get, StateT.run_set, bind_pure_comp]
            have h_simImplSigned_hash_hit :
                ∀ (mc : M × Commit) (cache : spec.QueryCache) (signed : List M)
                  (bad : Bool) (ω : Chal),
                  cache (.inr mc) = some ω →
                    ((_simImplSigned pk) (.inl (.inr mc))).run ((cache, signed), bad) =
                      pure (ω, ((cache, signed), bad)) := by
              intro mc cache signed bad ω hcache
              simp [_simImplSigned, baseSimSigned, baseSimSigned', QueryImpl.add_apply_inl,
                QueryImpl.withBadFlag_apply_run, StateT.run_bind, StateT.run_get, StateT.run_set]
              exact congrArg
                (fun x : OracleComp spec (Chal × spec.QueryCache) =>
                  (fun vs : Chal × spec.QueryCache =>
                    (vs.1, (((vs.2, signed), bad) : AdvState))) <$> x)
                (h_roSim_run_hit mc cache ω hcache)
            have h_simImplSigned_hash_miss :
                ∀ (mc : M × Commit) (cache : spec.QueryCache) (signed : List M)
                  (bad : Bool),
                  cache (.inr mc) = none →
                    ((_simImplSigned pk) (.inl (.inr mc))).run ((cache, signed), bad) =
                      show OracleComp spec
                          (spec.Range (Sum.inr mc) × AdvState) from
                        ((fun u : spec.Range (Sum.inr mc) =>
                          (u, (((cache.cacheQuery (.inr mc) u, signed), bad) : AdvState))) <$>
                          (liftM (query (Sum.inr mc)) :
                            OracleComp spec (spec.Range (Sum.inr mc)))) := by
              intro mc cache signed bad hcache
              simp [_simImplSigned, baseSimSigned, baseSimSigned', QueryImpl.add_apply_inl,
                QueryImpl.withBadFlag_apply_run, StateT.run_bind, StateT.run_get, StateT.run_set]
              exact congrArg
                (fun x : OracleComp spec (spec.Range (Sum.inr mc) × spec.QueryCache) =>
                  (fun vs : spec.Range (Sum.inr mc) × spec.QueryCache =>
                    (vs.1, (((vs.2, signed), bad) : AdvState))) <$> x)
                (h_roSim_run_miss mc cache hcache)
            have h_simImplSigned_sign_run :
                ∀ (msg : M) (cache : spec.QueryCache) (signed : List M) (bad : Bool),
                  ((_simImplSigned pk) (.inr msg)).run ((cache, signed), bad) =
                    (fun cωπ =>
                      let newCache :=
                        match cache (.inr (msg, cωπ.1)) with
                        | some _ => cache
                        | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1
                      ((cωπ.1, cωπ.2.2),
                        (((newCache, msg :: signed),
                          bad || (cache (.inr (msg, cωπ.1))).isSome) : AdvState))) <$>
                      liftComp (simTranscript pk) spec := by
              intro msg cache signed bad
              simp [sigBadFSigned, _simImplSigned, sigSimSigned, sigSimSigned',
                QueryImpl.add_apply_inr, QueryImpl.withBadUpdate_apply_run,
                StateT.run_bind, StateT.run_get, StateT.run_set, h_sigSim_run pk msg cache]
              congr 1
              funext cωπ
              cases hcache : cache (.inr (msg, cωπ.1)) <;> simp [hcache]
            have h_outer_trace_proj :
                ∀ t s,
                  Prod.map id cacheProj <$> ((_simImplSigned pk) t).run s =
                    ((baseSim + sigSim pk) t).run (cacheProj s) := by
              intro t s
              rcases s with ⟨⟨cache, signed⟩, bad⟩
              cases t with
              | inl t' =>
                  simp [cacheProj, _simImplSigned, baseSimSigned, baseSimSigned',
                    QueryImpl.add_apply_inl, QueryImpl.withBadFlag_apply_run,
                    StateT.run_bind, StateT.run_get, StateT.run_set]
              | inr msg =>
                  simp [cacheProj, _simImplSigned, sigSimSigned, sigSimSigned',
                    sigBadFSigned, QueryImpl.add_apply_inr,
                    QueryImpl.withBadUpdate_apply_run, StateT.run_bind,
                    StateT.run_get, StateT.run_set]
            have h_rich_trace_proj :
                ∀ t s,
                  Prod.map id traceProj <$> (richImpl t).run s =
                    (traceImpl t).run (traceProj s) := by
              intro t s
              rcases s with ⟨sAdv, sRo⟩
              simpa [richImpl, traceImpl, traceProj] using
                (VCVio.SSP.Package.map_run_link_impl_eq_of_query_map_eq'
                  (P₁ := richOuter) (P₂ := traceOuter) (Q := innerPkg)
                  (proj := cacheProj) (hproj := h_outer_trace_proj)
                  (t := t) (s₁ := sAdv) (s₂ := sRo))
            have h_rich_sim_run :
                Prod.map id simProj <$> richExp =
                  Prod.fst <$> (simulateQ innerPkg.impl (direct_sim_exp pk)).run
                    roInit := by
              simpa [richExp, direct_sim_exp, richOuter, innerPkg, richInit, advInit, roInit,
                simProj] using
                (VCVio.SSP.Package.map_simulateQ_link_run
                  (P := richOuter) (Q := innerPkg)
                  (A := adv.main pk) (s₁ := advInit) (s₂ := roInit)
                  (f := fun z => (z.1, z.2.1)))
            let unifSimWrapped :
                QueryImpl unifSpec
                  (StateT spec.QueryCache (OracleComp (Fork.wrappedSpec Chal))) :=
              (HasQuery.toQueryImpl (spec := unifSpec)
                (m := OracleComp (Fork.wrappedSpec Chal))).liftTarget _
            let roSimWrapped :
                QueryImpl (M × Commit →ₒ Chal)
                  (StateT spec.QueryCache (OracleComp (Fork.wrappedSpec Chal))) := fun mc => do
              let cache ← get
              match cache (.inr mc) with
              | some v => pure v
              | none => do
                  let v ←
                    liftM (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                      OracleComp (Fork.wrappedSpec Chal) Chal)
                  modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
            let baseSimWrapped :
                QueryImpl spec
                  (StateT spec.QueryCache (OracleComp (Fork.wrappedSpec Chal))) :=
              unifSimWrapped + roSimWrapped
            let sigSimWrapped :
                QueryImpl (M →ₒ (Commit × Resp))
                  (StateT spec.QueryCache (OracleComp (Fork.wrappedSpec Chal))) := fun msg => do
              let (c, ω, s) ← simulateQ unifSimWrapped (simTranscript pk)
              modifyGet fun cache =>
                match cache (.inr (msg, c)) with
                | some _ => ((c, s), cache)
                | none => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)
            let baseSimSignedWrapped' :
                QueryImpl spec
                  (StateT (spec.QueryCache × List M)
                    (OracleComp (Fork.wrappedSpec Chal))) := fun t => do
              let s ← get
              let v ← (baseSimWrapped t).run s.1
              set (v.2, s.2)
              pure v.1
            let sigSimSignedWrapped' :
                QueryImpl (M →ₒ (Commit × Resp))
                  (StateT (spec.QueryCache × List M)
                    (OracleComp (Fork.wrappedSpec Chal))) := fun msg => do
              let s ← get
              let v ← (sigSimWrapped msg).run s.1
              set (v.2, msg :: s.2)
              pure v.1
            let baseSimSignedWrapped :
                QueryImpl spec
                  (StateT AdvState (OracleComp (Fork.wrappedSpec Chal))) :=
              baseSimSignedWrapped'.withBadFlag
            let sigSimSignedWrapped :
                QueryImpl (M →ₒ (Commit × Resp))
                  (StateT AdvState (OracleComp (Fork.wrappedSpec Chal))) :=
              sigSimSignedWrapped'.withBadUpdate sigBadFSigned
            let simWrappedImpl :
                QueryImpl (spec + (M →ₒ (Commit × Resp)))
                  (StateT AdvState (OracleComp (Fork.wrappedSpec Chal))) :=
              baseSimSignedWrapped + sigSimSignedWrapped
            have h_unifSimWrapped_run :
                ∀ {α : Type} (oa : ProbComp α) (cache : spec.QueryCache),
                  (simulateQ unifSimWrapped oa).run cache =
                    (fun x => (x, cache)) <$> liftComp oa (Fork.wrappedSpec Chal) := by
              intro α oa cache
              let inj : QueryImpl unifSpec (OracleComp (Fork.wrappedSpec Chal)) :=
                HasQuery.toQueryImpl (spec := unifSpec)
                  (m := OracleComp (Fork.wrappedSpec Chal))
              have hunif_eq :
                  unifSimWrapped =
                    inj.liftTarget
                      (StateT spec.QueryCache (OracleComp (Fork.wrappedSpec Chal))) := rfl
              rw [hunif_eq, simulateQ_liftTarget]
              have hsim : simulateQ inj oa = liftComp oa (Fork.wrappedSpec Chal) := rfl
              rw [hsim, OracleComp.liftM_run_StateT, bind_pure_comp]
            have h_roSimWrapped_run_miss :
                ∀ (mc : M × Commit) (cache : spec.QueryCache),
                  cache (.inr mc) = none →
                    (roSimWrapped mc).run cache =
                      (fun u => (u, cache.cacheQuery (.inr mc) u)) <$>
                        ((((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                          OracleComp (Fork.wrappedSpec Chal) Chal)) := by
              intro mc cache hcache
              simp [roSimWrapped, hcache, StateT.run_bind, StateT.run_get, bind_pure_comp,
                Functor.map_map]
              rfl
            have h_roSimWrapped_run_hit :
                ∀ (mc : M × Commit) (cache : spec.QueryCache) (u : Chal),
                  cache (.inr mc) = some u →
                    (roSimWrapped mc).run cache = pure (u, cache) := by
              intro mc cache u hcache
              simp [roSimWrapped, hcache]
            have h_sigSimWrapped_run :
                ∀ (msg : M) (cache : spec.QueryCache),
                  (sigSimWrapped msg).run cache =
                    liftComp (simTranscript pk) (Fork.wrappedSpec Chal) >>=
                      fun cωπ : Commit × Chal × Resp =>
                        pure (match cache (.inr (msg, cωπ.1)) with
                          | some _ => ((cωπ.1, cωπ.2.2), cache)
                          | none => ((cωπ.1, cωπ.2.2),
                              cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1)) := by
              intro msg cache
              dsimp only [sigSimWrapped]
              rw [StateT.run_bind, h_unifSimWrapped_run (oa := simTranscript pk) (cache := cache),
                bind_map_left]
              refine bind_congr fun cωπ => ?_
              simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
                StateT.modifyGet, StateT.run]
              congr 1
              rcases cache (.inr (msg, cωπ.1)) with _ | _ <;> simp
            have h_baseSimSignedWrapped_unif :
                ∀ (n : ℕ) (cache : spec.QueryCache) (signed : List M),
                  (baseSimSignedWrapped' (.inl n)).run (cache, signed) =
                    ((fun u : spec.Range (Sum.inl n) => (u, (cache, signed))) <$>
                      ((((Fork.wrappedSpec Chal).query (Sum.inl n)) :
                        OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inl n))))) := by
              intro n cache signed
              have hunif :
                  (baseSimWrapped (.inl n)).run cache =
                    ((fun x => (x, cache)) <$>
                      ((((Fork.wrappedSpec Chal).query (Sum.inl n)) :
                        OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inl n))))) := by
                simpa [baseSimWrapped, QueryImpl.add_apply_inl, liftComp_eq_liftM] using
                  (h_unifSimWrapped_run (oa := (unifSpec.query n : ProbComp (Fin (n + 1))))
                    (cache := cache))
              rw [show (baseSimSignedWrapped' (.inl n)).run (cache, signed) =
                  ((baseSimWrapped (.inl n)).run cache >>= fun v =>
                    pure (v.1, (v.2, signed))) by
                    simp [baseSimSignedWrapped', StateT.run_bind, StateT.run_get, StateT.run_set]]
              rw [hunif]
              let mx : OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inl n)) :=
                (((Fork.wrappedSpec Chal).query (Sum.inl n)) :
                  OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inl n)))
              change
                ((fun v : spec.Range (Sum.inl n) × spec.QueryCache => (v.1, (v.2, signed))) <$>
                  ((fun x : spec.Range (Sum.inl n) => (x, cache)) <$> mx)) =
                  ((fun u : spec.Range (Sum.inl n) => (u, (cache, signed))) <$> mx)
              simpa [mx, Functor.map_map, Function.comp_def]
            have h_baseSimSignedWrapped_hash_hit :
                ∀ (mc : M × Commit) (cache : spec.QueryCache) (signed : List M) (ω : Chal),
                  cache (.inr mc) = some ω →
                    (baseSimSignedWrapped' (.inr mc)).run (cache, signed) =
                      pure (ω, (cache, signed)) := by
              intro mc cache signed ω hcache
              simp [baseSimSignedWrapped', StateT.run_bind, StateT.run_get, StateT.run_set]
              exact congrArg
                (fun x : OracleComp (Fork.wrappedSpec Chal) (Chal × spec.QueryCache) =>
                  (fun vs : Chal × spec.QueryCache => (vs.1, (vs.2, signed))) <$> x)
                (show (baseSimWrapped (.inr mc)).run cache = pure (ω, cache) by
                  simpa [baseSimWrapped, QueryImpl.add_apply_inr] using
                    (h_roSimWrapped_run_hit mc cache ω hcache))
            have h_baseSimSignedWrapped_hash_miss :
                ∀ (mc : M × Commit) (cache : spec.QueryCache) (signed : List M),
                  cache (.inr mc) = none →
                    (baseSimSignedWrapped' (.inr mc)).run (cache, signed) =
                      ((fun u : spec.Range (Sum.inr mc) =>
                          (u, (cache.cacheQuery (.inr mc) u, signed))) <$>
                        ((((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                          OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inr mc))))) := by
              intro mc cache signed hcache
              simp [baseSimSignedWrapped', StateT.run_bind, StateT.run_get, StateT.run_set]
              exact congrArg
                (fun x : OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inr mc) × spec.QueryCache) =>
                  (fun vs : spec.Range (Sum.inr mc) × spec.QueryCache =>
                    (vs.1, (vs.2, signed))) <$> x)
                (show (baseSimWrapped (.inr mc)).run cache =
                    ((fun u => (u, cache.cacheQuery (.inr mc) u)) <$>
                      ((((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                        OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inr mc))))) by
                  simpa [baseSimWrapped, QueryImpl.add_apply_inr] using
                    (h_roSimWrapped_run_miss mc cache hcache))
            have h_simWrapped_unif_run :
                ∀ (n : ℕ) (cache : spec.QueryCache) (signed : List M) (bad : Bool),
                  (simWrappedImpl (Sum.inl (Sum.inl n))).run ((cache, signed), bad) =
                    show OracleComp (Fork.wrappedSpec Chal)
                      (((spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inl n))) × AdvState)
                      from
                        ((fun u : spec.Range (Sum.inl n) =>
                            (u, (((cache, signed), bad) : AdvState))) <$>
                          ((((Fork.wrappedSpec Chal).query (Sum.inl n)) :
                            OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inl n))))) := by
              intro n cache signed bad
              simpa [baseSimSignedWrapped, QueryImpl.add_apply_inl,
                QueryImpl.withBadFlag_apply_run] using
                congrArg
                  (fun x :
                    OracleComp (Fork.wrappedSpec Chal)
                      (spec.Range (Sum.inl n) × (spec.QueryCache × List M)) =>
                    (fun vs : spec.Range (Sum.inl n) × (spec.QueryCache × List M) =>
                      (vs.1, ((vs.2, bad) : AdvState))) <$> x)
                  (h_baseSimSignedWrapped_unif n cache signed)
            have h_simWrapped_hash_hit :
                ∀ (mc : M × Commit) (cache : spec.QueryCache) (signed : List M)
                  (bad : Bool) (ω : Chal),
                  cache (.inr mc) = some ω →
                    (simWrappedImpl (Sum.inl (Sum.inr mc))).run ((cache, signed), bad) =
                      pure (ω, ((cache, signed), bad)) := by
              intro mc cache signed bad ω hcache
              simpa [baseSimSignedWrapped, QueryImpl.add_apply_inr,
                QueryImpl.withBadFlag_apply_run] using
                congrArg
                  (fun x :
                    OracleComp (Fork.wrappedSpec Chal) (Chal × (spec.QueryCache × List M)) =>
                    (fun vs : Chal × (spec.QueryCache × List M) =>
                      (vs.1, ((vs.2, bad) : AdvState))) <$> x)
                  (h_baseSimSignedWrapped_hash_hit mc cache signed ω hcache)
            have h_simWrapped_hash_miss :
                ∀ (mc : M × Commit) (cache : spec.QueryCache) (signed : List M)
                  (bad : Bool),
                  cache (.inr mc) = none →
                    (simWrappedImpl (Sum.inl (Sum.inr mc))).run ((cache, signed), bad) =
                      show OracleComp (Fork.wrappedSpec Chal)
                        (spec.Range (Sum.inr mc) × AdvState) from
                        ((fun u : spec.Range (Sum.inr mc) =>
                            (u, (((cache.cacheQuery (.inr mc) u, signed), bad) : AdvState))) <$>
                          ((((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                            OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inr mc))))) := by
              intro mc cache signed bad hcache
              simpa [baseSimSignedWrapped, QueryImpl.add_apply_inr,
                QueryImpl.withBadFlag_apply_run] using
                congrArg
                  (fun x :
                    OracleComp (Fork.wrappedSpec Chal)
                      (spec.Range (Sum.inr mc) × (spec.QueryCache × List M)) =>
                    (fun vs : spec.Range (Sum.inr mc) × (spec.QueryCache × List M) =>
                      (vs.1, ((vs.2, bad) : AdvState))) <$> x)
                  (h_baseSimSignedWrapped_hash_miss mc cache signed hcache)
            have h_simWrapped_sign_run :
                ∀ (msg : M) (cache : spec.QueryCache) (signed : List M) (bad : Bool),
                  (simWrappedImpl (.inr msg)).run ((cache, signed), bad) =
                    (fun cωπ =>
                      let newCache :=
                        match cache (.inr (msg, cωπ.1)) with
                        | some _ => cache
                        | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1
                      ((cωπ.1, cωπ.2.2),
                        (((newCache, msg :: signed),
                          bad || (cache (.inr (msg, cωπ.1))).isSome) : AdvState))) <$>
                      liftComp (simTranscript pk) (Fork.wrappedSpec Chal) := by
              intro msg cache signed bad
              have hsigSigned :
                  (sigSimSignedWrapped' msg).run (cache, signed) =
                    (fun cωπ =>
                      ((cωπ.1, cωπ.2.2),
                        (match cache (.inr (msg, cωπ.1)) with
                        | some _ => cache
                        | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1,
                          msg :: signed))) <$>
                      liftComp (simTranscript pk) (Fork.wrappedSpec Chal) := by
                have hsigMap :
                    (sigSimWrapped msg).run cache =
                      (fun cωπ =>
                        match cache (.inr (msg, cωπ.1)) with
                        | some _ => ((cωπ.1, cωπ.2.2), cache)
                        | none => ((cωπ.1, cωπ.2.2), cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1)) <$>
                        liftComp (simTranscript pk) (Fork.wrappedSpec Chal) := by
                  simpa [map_eq_bind_pure_comp] using h_sigSimWrapped_run msg cache
                rw [show (sigSimSignedWrapped' msg).run (cache, signed) =
                    ((sigSimWrapped msg).run cache >>= fun v =>
                      pure (v.1, (v.2, msg :: signed))) by
                    simp [sigSimSignedWrapped', StateT.run_bind, StateT.run_get, StateT.run_set]]
                rw [hsigMap]
                change
                  ((fun v : (Commit × Resp) × spec.QueryCache => (v.1, (v.2, msg :: signed))) <$>
                    ((fun cωπ =>
                        match cache (.inr (msg, cωπ.1)) with
                        | some _ => ((cωπ.1, cωπ.2.2), cache)
                        | none => ((cωπ.1, cωπ.2.2), cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1)) <$>
                      liftComp (simTranscript pk) (Fork.wrappedSpec Chal))) =
                    ((fun cωπ =>
                        ((cωπ.1, cωπ.2.2),
                          (match cache (.inr (msg, cωπ.1)) with
                          | some _ => cache
                          | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1,
                            msg :: signed))) <$>
                      liftComp (simTranscript pk) (Fork.wrappedSpec Chal))
                let innerF : Commit × Chal × Resp → (Commit × Resp) × spec.QueryCache :=
                  fun cωπ =>
                    match cache (.inr (msg, cωπ.1)) with
                    | some _ => ((cωπ.1, cωπ.2.2), cache)
                    | none => ((cωπ.1, cωπ.2.2), cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1)
                let outerF : (Commit × Resp) × spec.QueryCache →
                    (Commit × Resp) × (spec.QueryCache × List M) :=
                  fun v => (v.1, (v.2, msg :: signed))
                let finalF : Commit × Chal × Resp →
                    (Commit × Resp) × (spec.QueryCache × List M) :=
                  fun cωπ =>
                    ((cωπ.1, cωπ.2.2),
                      (match cache (.inr (msg, cωπ.1)) with
                      | some _ => cache
                      | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1,
                        msg :: signed))
                have hcomp : outerF ∘ innerF = finalF := by
                  funext a
                  cases hcache : cache (.inr (msg, a.1)) <;> simp [innerF, outerF, finalF, hcache]
                simpa [innerF, outerF, finalF, Functor.map_map, Function.comp_def] using
                  congrArg
                    (fun f => f <$> liftComp (simTranscript pk) (Fork.wrappedSpec Chal))
                    hcomp
              simpa [simWrappedImpl, sigSimSignedWrapped, sigBadFSigned,
                QueryImpl.add_apply_inr, QueryImpl.withBadUpdate_apply_run,
                Functor.map_map, Function.comp_def] using
                congrArg
                  (fun x : OracleComp (Fork.wrappedSpec Chal)
                    ((Commit × Resp) × (spec.QueryCache × List M)) =>
                    (fun vs : (Commit × Resp) × (spec.QueryCache × List M) =>
                      (vs.1, (vs.2, bad || sigBadFSigned msg (cache, signed) vs.1))) <$> x)
                  hsigSigned
            have h_rich_step_sim_link :
                ∀ (t : (spec + (M →ₒ (Commit × Resp))).Domain) (s : RichState),
                  Prod.map id simProj <$> (richImpl t).run s =
                    Prod.fst <$> (simulateQ innerPkg.impl (((_simImplSigned pk) t).run s.1)).run
                      s.2 := by
              intro t s
              rcases s with ⟨sAdv, sRo⟩
              simpa [richImpl, richOuter, simProj, Function.comp_def] using
                (VCVio.SSP.Package.map_simulateQ_link_run
                  (P := richOuter) (Q := innerPkg)
                  (A := OracleSpec.query t) (s₁ := sAdv) (s₂ := sRo)
                  (f := fun z => (z.1, z.2.1)))
            have h_simWrapped_step_evalDist :
                ∀ (t : (spec + (M →ₒ (Commit × Resp))).Domain) (s : AdvState),
                  evalDist ((simWrappedImpl t).run s) =
                    evalDist (((_simImplSigned pk) t).run s) := by
              intro t s
              rcases s with ⟨⟨cache, signed⟩, bad⟩
              cases t with
              | inl t' =>
                  cases t' with
                  | inl n =>
                      rw [h_simWrapped_unif_run n cache signed bad,
                        h_simImplSigned_unif_run n cache signed bad]
                      change
                        evalDist
                            ((fun u : spec.Range (Sum.inl n) =>
                                (u, (((cache, signed), bad) : AdvState))) <$>
                              ((liftM
                                  (query (spec := Fork.wrappedSpec Chal) (Sum.inl n) :
                                    OracleQuery (Fork.wrappedSpec Chal) (spec.Range (Sum.inl n))) :
                                OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inl n))))) =
                          evalDist
                            ((fun u : spec.Range (Sum.inl n) =>
                                (u, (((cache, signed), bad) : AdvState))) <$>
                              ((liftM
                                  (query (spec := spec) (Sum.inl n) :
                                    OracleQuery spec (spec.Range (Sum.inl n))) :
                                OracleComp spec (spec.Range (Sum.inl n)))))
                      have hLeft :
                          evalDist
                            ((liftM
                                (query (spec := Fork.wrappedSpec Chal) (Sum.inl n) :
                                  OracleQuery (Fork.wrappedSpec Chal) (spec.Range (Sum.inl n))) :
                              OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inl n)))) =
                            (liftM (PMF.uniformOfFintype (spec.Range (Sum.inl n))) :
                              SPMF (spec.Range (Sum.inl n))) := by
                        simpa using
                          (evalDist_query (spec := Fork.wrappedSpec Chal) (t := Sum.inl n))
                      have hRight :
                          evalDist
                            ((liftM
                                (query (spec := spec) (Sum.inl n) :
                                  OracleQuery spec (spec.Range (Sum.inl n))) :
                              OracleComp spec (spec.Range (Sum.inl n)))) =
                            (liftM (PMF.uniformOfFintype (spec.Range (Sum.inl n))) :
                              SPMF (spec.Range (Sum.inl n))) := by
                        simpa using (evalDist_query (spec := spec) (t := Sum.inl n))
                      simpa [evalDist_map] using
                        congrArg
                          (fun p : SPMF (spec.Range (Sum.inl n)) =>
                            (fun u : spec.Range (Sum.inl n) =>
                              (u, (((cache, signed), bad) : AdvState))) <$> p)
                          (hLeft.trans hRight.symm)
                  | inr mc =>
                      cases hcache : cache (.inr mc) with
                      | none =>
                          rw [h_simWrapped_hash_miss mc cache signed bad hcache,
                            h_simImplSigned_hash_miss mc cache signed bad hcache]
                          change
                            evalDist
                                ((fun u : Chal =>
                                    (u, (((cache.cacheQuery (.inr mc) u, signed), bad) : AdvState))) <$>
                                  ((liftM
                                      (query (spec := Fork.wrappedSpec Chal) (Sum.inr ()) :
                                        OracleQuery (Fork.wrappedSpec Chal) Chal) :
                                    OracleComp (Fork.wrappedSpec Chal) Chal))) =
                              evalDist
                                ((fun u : Chal =>
                                    (u, (((cache.cacheQuery (.inr mc) u, signed), bad) : AdvState))) <$>
                                  ((liftM
                                      (query (spec := spec) (Sum.inr mc) :
                                        OracleQuery spec Chal) :
                                    OracleComp spec Chal)))
                          have hLeft :
                              evalDist
                                ((liftM
                                    (query (spec := Fork.wrappedSpec Chal) (Sum.inr ()) :
                                      OracleQuery (Fork.wrappedSpec Chal) Chal) :
                                  OracleComp (Fork.wrappedSpec Chal) Chal)) =
                                (liftM (PMF.uniformOfFintype Chal) : SPMF Chal) := by
                            simpa [PMF.map_id] using
                              (evalDist_liftM
                                (q := (query (spec := Fork.wrappedSpec Chal) (Sum.inr ()) :
                                  OracleQuery (Fork.wrappedSpec Chal) Chal)))
                          have hRight :
                              evalDist
                                ((liftM
                                    (query (spec := spec) (Sum.inr mc) :
                                      OracleQuery spec Chal) :
                                  OracleComp spec Chal)) =
                                (liftM (PMF.uniformOfFintype Chal) : SPMF Chal) := by
                            simpa [evalDist_liftM, PMF.map_id]
                          simpa [evalDist_map] using
                            congrArg
                              (fun p : SPMF Chal =>
                                (fun u : Chal =>
                                  (u, (((cache.cacheQuery (.inr mc) u, signed), bad) : AdvState))) <$> p)
                              (hLeft.trans hRight.symm)
                      | some ω =>
                          rw [h_simWrapped_hash_hit mc cache signed bad ω hcache,
                            h_simImplSigned_hash_hit mc cache signed bad ω hcache]
                          rfl
              | inr msg =>
                  rw [h_simWrapped_sign_run msg cache signed bad,
                    h_simImplSigned_sign_run msg cache signed bad]
                  let outF : Commit × Chal × Resp → (Commit × Resp) × AdvState :=
                    fun cωπ =>
                      let newCache :=
                        match cache (.inr (msg, cωπ.1)) with
                        | some _ => cache
                        | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1
                      ((cωπ.1, cωπ.2.2),
                        (((newCache, msg :: signed),
                          bad || (cache (.inr (msg, cωπ.1))).isSome) : AdvState))
                  change
                    evalDist (outF <$> liftComp (simTranscript pk) (Fork.wrappedSpec Chal)) =
                      evalDist (outF <$> liftComp (simTranscript pk) spec)
                  have hEq :
                      evalDist (liftComp (simTranscript pk) (Fork.wrappedSpec Chal)) =
                        evalDist (liftComp (simTranscript pk) spec) := by
                    calc
                      evalDist (liftComp (simTranscript pk) (Fork.wrappedSpec Chal))
                          = evalDist (simTranscript pk) :=
                            OracleComp.evalDist_liftComp (spec := unifSpec)
                              (superSpec := Fork.wrappedSpec Chal)
                              (mx := simTranscript pk)
                      _ = evalDist (liftComp (simTranscript pk) spec) := by
                            symm
                            exact OracleComp.evalDist_liftComp (spec := unifSpec)
                              (superSpec := spec) (mx := simTranscript pk)
                  simpa [evalDist_map] using
                    congrArg (fun p : SPMF (Commit × Chal × Resp) => outF <$> p) hEq
            have h_rich_trace_run :
                Prod.map id traceProj <$> richExp =
                  (simulateQ traceImpl (adv.main pk)).run traceInit := by
              simpa [richExp, traceInit, richInit, traceProj] using
                (OracleComp.map_run_simulateQ_eq_of_query_map_eq'
                  (impl₁ := richImpl) (impl₂ := traceImpl)
                  (proj := traceProj) (hproj := h_rich_trace_proj)
                  (oa := adv.main pk) (s := richInit))
            have h_traceImpl_runTrace :
                traceOfState <$> (simulateQ traceImpl (adv.main pk)).run traceInit =
                  Fork.runTrace σ hr M nmaAdv pk := by
              let traceMap :
                  (((M × Commit × Resp) × spec.QueryCache) × RoState) →
                    Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) :=
                fun a =>
                  { forgery := a.1.1
                    advCache := a.1.2
                    roCache := a.2.1
                    queryLog := a.2.2
                    verified :=
                      match a.2.1 (a.1.1.1, a.1.1.2.1) with
                      | some ω => σ.verify pk a.1.1.2.1 ω a.1.1.2.2
                      | none => false }
              have htraceMap :
                  traceOfState ∘
                      (fun x : (((M × Commit × Resp) × spec.QueryCache) × RoState) =>
                        (x.1.1, (x.1.2, x.2))) =
                    traceMap := by
                funext x
                rcases x with ⟨⟨forgery, advCache⟩, st⟩
                rcases st with ⟨roCache, queryLog⟩
                rcases forgery with ⟨msg, cs⟩
                rcases cs with ⟨c, resp⟩
                cases h : roCache (msg, c) <;> simp [traceOfState, traceMap, Function.comp_def, h]
              calc
                traceOfState <$> (simulateQ traceImpl (adv.main pk)).run traceInit
                    = (traceOfState ∘
                        (fun x : (((M × Commit × Resp) × spec.QueryCache) × RoState) =>
                          (x.1.1, (x.1.2, x.2)))) <$>
                        (simulateQ innerPkg.impl
                          ((simulateQ traceOuter.impl (adv.main pk)).run traceCacheInit)).run
                          roInit := by
                            simpa [traceImpl, traceInit, traceCacheInit, roInit,
                              Function.comp_def] using
                              (VCVio.SSP.Package.map_simulateQ_link_run
                                (P := traceOuter) (Q := innerPkg)
                                (A := adv.main pk) (s₁ := traceCacheInit) (s₂ := roInit)
                                (f := traceOfState))
                _ = traceMap <$>
                      (simulateQ innerPkg.impl
                        ((simulateQ traceOuter.impl (adv.main pk)).run traceCacheInit)).run
                        roInit := by
                          simpa using
                            congrArg
                              (fun f =>
                                f <$>
                                  (simulateQ innerPkg.impl
                                    ((simulateQ traceOuter.impl (adv.main pk)).run
                                      traceCacheInit)).run roInit)
                              htraceMap
                _ = Fork.runTrace σ hr M nmaAdv pk := by
                      rw [map_eq_bind_pure_comp, Fork.runTrace]
                      unfold nmaAdv traceOuter innerPkg traceMap
                      simp [Function.comp_def]
                      congr
                      · funext a
                        rcases a with ⟨⟨forgery, advCache⟩, ⟨roCache, queryLog⟩⟩
                        rcases forgery with ⟨msg, c, s⟩
                        simp
                        cases h : roCache (msg, c) <;> rfl
            have h_traceExp_eq_runTrace :
                traceExp = Fork.runTrace σ hr M nmaAdv pk := by
              calc
                traceExp
                    = traceOfState <$> (Prod.map id traceProj <$> richExp) := by
                        simp [traceExp, richExp, traceOfRich, traceOfState, Functor.map_map]
                _ = traceOfState <$> (simulateQ traceImpl (adv.main pk)).run traceInit := by
                        rw [h_rich_trace_run]
                _ = Fork.runTrace σ hr M nmaAdv pk := h_traceImpl_runTrace
            have h_rich_step_state :
                ∀ (t : (spec + (M →ₒ (Commit × Resp))).Domain) (s : RichState),
                  Prod.snd <$> (richImpl t).run s =
                    (fun x :
                        (((spec + (M →ₒ (Commit × Resp))).Range t × AdvState) × RoState) =>
                      (x.1.2, x.2)) <$>
                      (simulateQ innerPkg.impl (((_simImplSigned pk) t).run s.1)).run s.2 := by
              intro t s
              rcases s with ⟨sAdv, sRo⟩
              simpa [richImpl, richOuter, Function.comp_def] using
                (VCVio.SSP.Package.map_simulateQ_link_run
                  (P := richOuter) (Q := innerPkg)
                  (A := OracleSpec.query t) (s₁ := sAdv) (s₂ := sRo)
                  (f := Prod.snd))
            have h_richInv_step :
                ∀ (t : (spec + (M →ₒ (Commit × Resp))).Domain) (s : RichState)
                  {z : ((spec + (M →ₒ (Commit × Resp))).Range t) × RichState},
                  richInv s →
                    z ∈ support ((richImpl t).run s) →
                      richInv z.2 := by
              intro t s z hs hz
              have hzState : z.2 ∈ support (Prod.snd <$> (richImpl t).run s) := by
                rw [support_map]
                exact ⟨z, hz, rfl⟩
              rw [h_rich_step_state t s] at hzState
              rw [support_map] at hzState
              rcases hzState with ⟨w, hw, hwEq⟩
              rcases s with ⟨sAdv, sRo⟩
              rcases sAdv with ⟨⟨cache, signed⟩, bad⟩
              rcases sRo with ⟨roCache, queryLog⟩
              rcases hs with ⟨hRoToAdv, hAdvToRoOrSigned, hRoMem⟩
              cases t with
              | inl t' =>
                  cases t' with
                  | inl n =>
                      have hinner :
                          (simulateQ innerPkg.impl
                              (liftM (spec.query (Sum.inl n)) :
                                OracleComp spec ((spec + (M →ₒ (Commit × Resp))).Range
                                  (Sum.inl (Sum.inl n))))).run
                              (roCache, queryLog) =
                            (fun u => (u, ((roCache, queryLog) : RoState))) <$>
                              (((Fork.wrappedSpec Chal).query (Sum.inl n)) :
                                OracleComp (Fork.wrappedSpec Chal)
                                  ((spec + (M →ₒ (Commit × Resp))).Range
                                    (Sum.inl (Sum.inl n)))) := by
                        change
                          (simulateQ innerPkg.impl
                              (liftComp
                                (unifSpec.query n :
                                  ProbComp ((spec + (M →ₒ (Commit × Resp))).Range
                                    (Sum.inl (Sum.inl n))))
                                spec)).run
                              ((roCache, queryLog) : RoState) =
                            (fun u => (u, ((roCache, queryLog) : RoState))) <$>
                              liftComp
                                (unifSpec.query n :
                                  ProbComp ((spec + (M →ₒ (Commit × Resp))).Range
                                    (Sum.inl (Sum.inl n))))
                                (Fork.wrappedSpec Chal)
                        simpa [liftComp_eq_liftM] using
                          (h_inner_liftComp_run
                            (oa := (unifSpec.query n :
                              ProbComp ((spec + (M →ₒ (Commit × Resp))).Range
                                (Sum.inl (Sum.inl n)))))
                            (st := ((roCache, queryLog) : RoState)))
                      rw [h_simImplSigned_unif_run n cache signed bad] at hw
                      have hw' :
                          w ∈ support
                            ((fun p => ((p.1, (cache, signed), bad), p.2)) <$>
                              (simulateQ innerPkg.impl
                                  (liftM (spec.query (Sum.inl n)) :
                                    OracleComp spec
                                      ((spec + (M →ₒ (Commit × Resp))).Range
                                        (Sum.inl (Sum.inl n))))).run
                                ((roCache, queryLog) : RoState)) := by
                        simpa using hw
                      rw [hinner] at hw'
                      simp only [Functor.map_map, Function.comp_def, support_map] at hw'
                      rcases hw' with ⟨u, hu, hw⟩
                      subst w
                      have huState : u.2 = ((roCache, queryLog) : RoState) := by
                        have hu' :
                            u ∈
                              (fun u : (spec + (M →ₒ (Commit × Resp))).Range (Sum.inl (Sum.inl n)) =>
                                  (u, ((roCache, queryLog) : RoState))) ''
                                support
                                  ((((Fork.wrappedSpec Chal).query (Sum.inl n)) :
                                    OracleComp (Fork.wrappedSpec Chal)
                                      ((spec + (M →ₒ (Commit × Resp))).Range
                                        (Sum.inl (Sum.inl n))))) := by
                          have hq :
                              ((((Fork.wrappedSpec Chal).query (Sum.inl n)) :
                                  OracleComp (Fork.wrappedSpec Chal)
                                    ((spec + (M →ₒ (Commit × Resp))).Range
                                      (Sum.inl (Sum.inl n))))) =
                                ((liftM
                                    (query (spec := Fork.wrappedSpec Chal) (Sum.inl n) :
                                      OracleQuery (Fork.wrappedSpec Chal)
                                        ((spec + (M →ₒ (Commit × Resp))).Range
                                          (Sum.inl (Sum.inl n)))) :
                                  OracleComp (Fork.wrappedSpec Chal)
                                    ((spec + (M →ₒ (Commit × Resp))).Range
                                      (Sum.inl (Sum.inl n))))) := by
                            rfl
                          rw [← support_map]
                          convert hu using 1
                        obtain ⟨u₀, _, huEq⟩ := hu'
                        simpa using (congrArg Prod.snd huEq).symm
                      have hzEq :
                          z.2 =
                            ((((cache, signed), bad) : AdvState), ((roCache, queryLog) : RoState)) := by
                        calc
                          z.2 = ((((cache, signed), bad) : AdvState), u.2) := by
                            simpa using hwEq.symm
                          _ = ((((cache, signed), bad) : AdvState), ((roCache, queryLog) : RoState)) := by
                            simp [huState]
                      rw [hzEq]
                      exact ⟨hRoToAdv, hAdvToRoOrSigned, hRoMem⟩
                  | inr mc =>
                      cases hcache : cache (.inr mc) with
                      | some ω =>
                          rw [h_simImplSigned_hash_hit mc cache signed bad ω hcache] at hw
                          simp at hw
                          subst w
                          have hzEq :
                              z.2 =
                                ((((cache, signed), bad) : AdvState),
                                  ((roCache, queryLog) : RoState)) := by
                            simpa using hwEq.symm
                          rw [hzEq]
                          exact ⟨hRoToAdv, hAdvToRoOrSigned, hRoMem⟩
                      | none =>
                          have hroMiss : roCache mc = none := by
                            cases hro : roCache mc with
                            | none =>
                                exact rfl
                            | some ω =>
                                have hadv : cache (.inr mc) = some ω := hRoToAdv mc ω hro
                                simp [hcache] at hadv
                          have hinner :
                              (simulateQ innerPkg.impl
                                  (liftM (spec.query (Sum.inr mc)) :
                                    OracleComp spec
                                      ((spec + (M →ₒ (Commit × Resp))).Range
                                        (Sum.inl (Sum.inr mc))))).run
                                  (roCache, queryLog) =
                                (fun u =>
                                  (u,
                                    ((roCache.cacheQuery mc u, queryLog ++ [mc]) :
                                      RoState))) <$>
                                  (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                                    OracleComp (Fork.wrappedSpec Chal)
                                      ((spec + (M →ₒ (Commit × Resp))).Range
                                        (Sum.inl (Sum.inr mc)))) := by
                            change
                              (simulateQ innerPkg.impl
                                  (liftComp
                                    (((M × Commit →ₒ Chal).query mc) :
                                      OracleComp (M × Commit →ₒ Chal)
                                        ((spec + (M →ₒ (Commit × Resp))).Range
                                          (Sum.inl (Sum.inr mc))))
                                    spec)).run
                                  ((roCache, queryLog) : RoState) =
                                (fun u =>
                                  (u,
                                    ((roCache.cacheQuery mc u, queryLog ++ [mc]) :
                                      RoState))) <$>
                                  (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                                    OracleComp (Fork.wrappedSpec Chal)
                                      ((spec + (M →ₒ (Commit × Resp))).Range
                                        (Sum.inl (Sum.inr mc))))
                            rw [QueryImpl.simulateQ_add_liftComp_right
                              (impl₁' := Fork.unifFwd M Commit Chal)
                              (impl₂' := Fork.roImpl M Commit Chal)]
                            rw [simulateQ_query]
                            simp [innerPkg, QueryImpl.add_apply_inr, Fork.roImpl, StateT.run_bind,
                              StateT.run_get, StateT.run_set, hroMiss, bind_pure_comp,
                              liftComp_eq_liftM]
                          rw [h_simImplSigned_hash_miss mc cache signed bad hcache] at hw
                          have hw' :
                              w ∈ support
                                ((fun p =>
                                    ((p.1, (cache.cacheQuery (.inr mc) p.1, signed), bad), p.2)) <$>
                                  (simulateQ innerPkg.impl
                                      (liftM (spec.query (Sum.inr mc)) :
                                        OracleComp spec
                                          ((spec + (M →ₒ (Commit × Resp))).Range
                                            (Sum.inl (Sum.inr mc))))).run
                                    ((roCache, queryLog) : RoState)) := by
                            simpa using hw
                          rw [hinner] at hw'
                          rw [support_map] at hw'
                          rcases hw' with ⟨⟨u, st'⟩, hp, hw⟩
                          have hp' :
                              (u, st') ∈
                                (fun u =>
                                  (u, ((roCache.cacheQuery mc u, queryLog ++ [mc]) : RoState))) ''
                                  support
                                    (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                                      OracleComp (Fork.wrappedSpec Chal)
                                        ((spec + (M →ₒ (Commit × Resp))).Range
                                          (Sum.inl (Sum.inr mc)))) := by
                            rw [← support_map]
                            exact hp
                          have hst' :
                              ((roCache.cacheQuery mc u, queryLog ++ [mc]) : RoState) = st' := by
                            rcases hp' with ⟨u', hu', huEq⟩
                            simp [support_query] at hu'
                            cases huEq
                            rfl
                          cases hst'
                          subst w
                          have hzEq :
                              z.2 =
                                ((((cache.cacheQuery (.inr mc) u, signed), bad) : AdvState),
                                  ((roCache.cacheQuery mc u, queryLog ++ [mc]) : RoState)) := by
                            simpa using hwEq.symm
                          rw [hzEq]
                          constructor
                          · intro mc' ω' hro'
                            by_cases hEq : mc' = mc
                            · subst hEq
                              have hu : u = ω' := by
                                simpa using hro'
                              simpa only [QueryCache.cacheQuery_self] using
                                (congrArg some hu : some u = some ω')
                            · have hroOld : roCache mc' = some ω' := by
                                simpa [QueryCache.cacheQuery_of_ne (cache := roCache) u hEq] using
                                  hro'
                              have hEqSum :
                                  (Sum.inr mc' : spec.Domain) ≠ (Sum.inr mc : spec.Domain) := by
                                intro hEq'
                                apply hEq
                                simpa using hEq'
                              have hadvOld : cache (.inr mc') = some ω' := hRoToAdv mc' ω' hroOld
                              simpa [QueryCache.cacheQuery_of_ne (cache := cache)
                                (t' := Sum.inr mc') (t := Sum.inr mc) u hEqSum] using
                                hadvOld
                          · constructor
                            · intro msg c ω' hadv'
                              by_cases hEq : (msg, c) = mc
                              · subst hEq
                                left
                                have hu : u = ω' := by
                                  simpa using hadv'
                                simpa only [QueryCache.cacheQuery_self] using
                                  (congrArg some hu : some u = some ω')
                              · have hadvOld : cache (.inr (msg, c)) = some ω' := by
                                  have hEqSum :
                                      (Sum.inr (msg, c) : spec.Domain) ≠ (Sum.inr mc : spec.Domain) := by
                                    intro hEq'
                                    apply hEq
                                    simpa using hEq'
                                  simpa [QueryCache.cacheQuery_of_ne (cache := cache)
                                    (t' := Sum.inr (msg, c)) (t := Sum.inr mc) u hEqSum] using
                                    hadv'
                                rcases hAdvToRoOrSigned msg c ω' hadvOld with hroOld | hsigned
                                · left
                                  simpa [QueryCache.cacheQuery_of_ne (cache := roCache) u hEq] using
                                    hroOld
                                · right
                                  exact hsigned
                            · intro mc'
                              by_cases hEq : mc' = mc
                              · subst hEq
                                simp
                              · simpa [QueryCache.cacheQuery_of_ne (cache := roCache) u hEq,
                                  List.mem_append, hEq] using hRoMem mc'
              | inr msg =>
                  rw [h_simImplSigned_sign_run msg cache signed bad] at hw
                  let F : Commit × Chal × Resp → (Commit × Resp) × AdvState := fun cωπ =>
                    let newCache :=
                      match cache (.inr (msg, cωπ.1)) with
                      | some _ => cache
                      | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1
                    ((cωπ.1, cωπ.2.2),
                      (((newCache, msg :: signed),
                        bad || (cache (.inr (msg, cωπ.1))).isSome) : AdvState))
                  have hinner :
                      (simulateQ innerPkg.impl (F <$> liftComp (simTranscript pk) spec)).run
                          ((roCache, queryLog) : RoState) =
                        (fun cωπ => (F cωπ, ((roCache, queryLog) : RoState))) <$>
                          liftComp (simTranscript pk) (Fork.wrappedSpec Chal) := by
                    rw [show simulateQ innerPkg.impl (F <$> liftComp (simTranscript pk) spec) =
                        F <$> simulateQ innerPkg.impl (liftComp (simTranscript pk) spec) by
                          rw [simulateQ_map]]
                    rw [StateT.run_map, h_inner_liftComp_run (oa := simTranscript pk)
                      (st := ((roCache, queryLog) : RoState))]
                    simp [Functor.map_map, Function.comp_def, F]
                  have hw' :
                      w ∈ support
                        ((fun cωπ => (F cωπ, ((roCache, queryLog) : RoState))) <$>
                          liftComp (simTranscript pk) (Fork.wrappedSpec Chal)) := by
                    rw [← hinner]
                    exact hw
                  rw [support_map] at hw'
                  rcases hw' with ⟨cωπ, _, hw⟩
                  subst w
                  let newCache : spec.QueryCache :=
                    match cache (.inr (msg, cωπ.1)) with
                    | some _ => cache
                    | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1
                  have hzEq :
                      z.2 =
                        ((((newCache, msg :: signed),
                          bad || (cache (.inr (msg, cωπ.1))).isSome) : AdvState),
                          ((roCache, queryLog) : RoState)) := by
                    simpa [newCache, F] using hwEq.symm
                  rw [hzEq]
                  constructor
                  · intro mc ω hro
                    by_cases hEq : mc = (msg, cωπ.1)
                    · subst hEq
                      cases hcache' : cache (.inr (msg, cωπ.1)) with
                      | none =>
                          have hadv : cache (.inr (msg, cωπ.1)) = some ω := hRoToAdv _ _ hro
                          simp [hcache'] at hadv
                      | some _ =>
                          simpa [newCache, hcache'] using hRoToAdv _ _ hro
                    · cases hcache' : cache (.inr (msg, cωπ.1)) with
                      | none =>
                          have hnewCache_ne : newCache (.inr mc) = cache (.inr mc) := by
                            simp [newCache, hcache',
                              QueryCache.cacheQuery_of_ne (cache := cache)
                                (t' := Sum.inr mc) (t := Sum.inr (msg, cωπ.1)) cωπ.2.1
                                (by simpa using hEq)]
                          simpa [hnewCache_ne] using hRoToAdv mc ω hro
                      | some _ =>
                          simpa [newCache, hcache'] using hRoToAdv mc ω hro
                  · constructor
                    · intro msg' c ω hadv
                      by_cases hEq : (msg', c) = (msg, cωπ.1)
                      · cases hEq
                        right
                        simp
                      · have hadvOld : cache (.inr (msg', c)) = some ω := by
                          cases hcache' : cache (.inr (msg, cωπ.1)) with
                          | none =>
                              have hnewCache_ne :
                                  newCache (.inr (msg', c)) = cache (.inr (msg', c)) := by
                                simp [newCache, hcache',
                                  QueryCache.cacheQuery_of_ne (cache := cache)
                                    (t' := Sum.inr (msg', c)) (t := Sum.inr (msg, cωπ.1))
                                    cωπ.2.1 (by simpa using hEq)]
                              simpa [hnewCache_ne] using hadv
                          | some _ =>
                              simpa [newCache, hcache'] using hadv
                        rcases hAdvToRoOrSigned msg' c ω hadvOld with hro | hsigned
                        · left
                          exact hro
                        · right
                          simp [hsigned]
                    · intro mc
                      simpa using hRoMem mc
            have h_richInv_run :
                ∀ {α : Type} (oa : OracleComp (spec + (M →ₒ (Commit × Resp))) α)
                  (s : RichState),
                  richInv s →
                    ∀ z ∈ support ((simulateQ richImpl oa).run s), richInv z.2 := by
              intro α oa
              induction oa using OracleComp.inductionOn with
              | pure x =>
                  intro s hs z hz
                  simp [simulateQ_pure, StateT.run_pure, support_pure] at hz
                  subst z
                  simpa using hs
              | query_bind t oa ih =>
                  intro s hs z hz
                  have hz' :
                      z ∈ support
                        (((richImpl t).run s) >>= fun us =>
                          (simulateQ richImpl (oa us.1)).run us.2) := by
                    simpa [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
                      OracleQuery.cont_query, id_map, StateT.run_bind] using hz
                  rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
                  have husInv : richInv us.2 := h_richInv_step t s hs hus
                  exact ih us.1 us.2 husInv z hzcont
            have h_rich_simWrapped_step_proj :
                ∀ (t : (spec + (M →ₒ (Commit × Resp))).Domain) (s : RichState),
                  richInv s →
                  Prod.map id simProj <$> (richImpl t).run s =
                    (simWrappedImpl t).run (simProj s) := by
              intro t s hs
              rcases s with ⟨⟨⟨cache, signed⟩, bad⟩, ⟨roCache, queryLog⟩⟩
              rcases hs with ⟨hRoToAdv, hAdvToRoOrSigned, hRoMem⟩
              have hstep :=
                h_rich_step_sim_link (t := t)
                  (s := ((((cache, signed), bad) : AdvState), ((roCache, queryLog) : RoState)))
              cases t with
              | inl t' =>
                  cases t' with
                  | inl n =>
                      have hinner :
                          (simulateQ innerPkg.impl
                              (liftM (spec.query (Sum.inl n)) :
                                OracleComp spec (spec.Range (Sum.inl n)))).run
                              ((roCache, queryLog) : RoState) =
                            (fun u => (u, ((roCache, queryLog) : RoState))) <$>
                              (((Fork.wrappedSpec Chal).query (Sum.inl n)) :
                                OracleComp (Fork.wrappedSpec Chal) (spec.Range (Sum.inl n))) := by
                        change
                          (simulateQ innerPkg.impl
                              (liftComp
                                (unifSpec.query n : ProbComp (spec.Range (Sum.inl n)))
                                spec)).run
                              ((roCache, queryLog) : RoState) =
                            (fun u => (u, ((roCache, queryLog) : RoState))) <$>
                              liftComp
                                (unifSpec.query n : ProbComp (spec.Range (Sum.inl n)))
                                (Fork.wrappedSpec Chal)
                        simpa [liftComp_eq_liftM] using
                          (h_inner_liftComp_run
                            (oa := (unifSpec.query n : ProbComp (Fin (n + 1))))
                            (st := ((roCache, queryLog) : RoState)))
                      have hlhs :
                          Prod.fst <$>
                              (simulateQ innerPkg.impl
                                  ((fun u => (u, (cache, signed), bad)) <$>
                                    liftM (spec.query (Sum.inl n)))).run
                                ((roCache, queryLog) : RoState) =
                            (simWrappedImpl (Sum.inl (Sum.inl n))).run
                              (simProj ((((cache, signed), bad) : AdvState),
                                ((roCache, queryLog) : RoState))) := by
                        rw [simulateQ_map, StateT.run_map, hinner]
                        simpa [h_simWrapped_unif_run n cache signed bad, Functor.map_map,
                          Function.comp_def]
                      rw [hstep, h_simImplSigned_unif_run n cache signed bad]
                      simpa using hlhs
                  | inr mc =>
                      cases hcache : cache (.inr mc) with
                      | some ω =>
                          rw [hstep, h_simImplSigned_hash_hit mc cache signed bad ω hcache]
                          simpa [simulateQ_pure, StateT.run_pure] using
                            (h_simWrapped_hash_hit mc cache signed bad ω hcache).symm
                      | none =>
                          have hroMiss : roCache mc = none := by
                            cases hro : roCache mc with
                            | none =>
                                exact rfl
                            | some ω =>
                                have hadv : cache (.inr mc) = some ω := hRoToAdv mc ω hro
                                simp [hcache] at hadv
                          have hinner :
                              (simulateQ innerPkg.impl
                                  (liftM (spec.query (Sum.inr mc)) :
                                    OracleComp spec (spec.Range (Sum.inr mc)))).run
                                  ((roCache, queryLog) : RoState) =
                                (fun u =>
                                  (u,
                                    ((roCache.cacheQuery mc u, queryLog ++ [mc]) :
                                      RoState))) <$>
                                  (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                                    OracleComp (Fork.wrappedSpec Chal)
                                      (spec.Range (Sum.inr mc))) := by
                            change
                              (simulateQ innerPkg.impl
                                  (liftComp
                                    (((M × Commit →ₒ Chal).query mc) :
                                      OracleComp (M × Commit →ₒ Chal) (spec.Range (Sum.inr mc)))
                                    spec)).run
                                  ((roCache, queryLog) : RoState) =
                                (fun u =>
                                  (u,
                                    ((roCache.cacheQuery mc u, queryLog ++ [mc]) :
                                      RoState))) <$>
                                  (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                                    OracleComp (Fork.wrappedSpec Chal)
                                      (spec.Range (Sum.inr mc)))
                            rw [QueryImpl.simulateQ_add_liftComp_right
                              (impl₁' := Fork.unifFwd M Commit Chal)
                              (impl₂' := Fork.roImpl M Commit Chal)]
                            rw [simulateQ_query]
                            simp [innerPkg, QueryImpl.add_apply_inr, Fork.roImpl, hroMiss,
                              StateT.run_bind, StateT.run_get, StateT.run_set, bind_pure_comp,
                              liftComp_eq_liftM]
                          have hlhs :
                              Prod.fst <$>
                                  (simulateQ innerPkg.impl
                                      ((fun u =>
                                          (u, (cache.cacheQuery (.inr mc) u, signed), bad)) <$>
                                        liftM (spec.query (Sum.inr mc)))).run
                                    ((roCache, queryLog) : RoState) =
                                (simWrappedImpl (Sum.inl (Sum.inr mc))).run
                                  (simProj ((((cache, signed), bad) : AdvState),
                                    ((roCache, queryLog) : RoState))) := by
                            rw [simulateQ_map, StateT.run_map, hinner]
                            simpa [Functor.map_map, Function.comp_def, simProj] using
                              (h_simWrapped_hash_miss mc cache signed bad hcache).symm
                          rw [hstep, h_simImplSigned_hash_miss mc cache signed bad hcache]
                          simpa using hlhs
              | inr msg =>
                  let F : Commit × Chal × Resp → (Commit × Resp) × AdvState := fun cωπ =>
                    let newCache :=
                      match cache (.inr (msg, cωπ.1)) with
                      | some _ => cache
                      | none => cache.cacheQuery (.inr (msg, cωπ.1)) cωπ.2.1
                    ((cωπ.1, cωπ.2.2),
                      (((newCache, msg :: signed),
                        bad || (cache (.inr (msg, cωπ.1))).isSome) : AdvState))
                  have hinner :
                      (simulateQ innerPkg.impl (F <$> liftComp (simTranscript pk) spec)).run
                          ((roCache, queryLog) : RoState) =
                        (fun cωπ => (F cωπ, ((roCache, queryLog) : RoState))) <$>
                          liftComp (simTranscript pk) (Fork.wrappedSpec Chal) := by
                    rw [show simulateQ innerPkg.impl (F <$> liftComp (simTranscript pk) spec) =
                        F <$> simulateQ innerPkg.impl (liftComp (simTranscript pk) spec) by
                          rw [simulateQ_map]]
                    rw [StateT.run_map, h_inner_liftComp_run (oa := simTranscript pk)
                      (st := ((roCache, queryLog) : RoState))]
                    simp [Functor.map_map, Function.comp_def, F]
                  have hlhs :
                      Prod.fst <$>
                          (simulateQ innerPkg.impl (F <$> liftComp (simTranscript pk) spec)).run
                            ((roCache, queryLog) : RoState) =
                        (simWrappedImpl (Sum.inr msg)).run
                          (simProj ((((cache, signed), bad) : AdvState),
                            ((roCache, queryLog) : RoState))) := by
                    rw [hinner]
                    simpa [Functor.map_map, Function.comp_def, F, simProj] using
                      (h_simWrapped_sign_run msg cache signed bad).symm
                  rw [hstep, h_simImplSigned_sign_run msg cache signed bad]
                  simpa [F] using hlhs
            have h_pr_event_rich :
                Pr[event pk | direct_sim_exp pk] =
                  Pr[fun z => event pk (Prod.map id simProj z) | richExp] := by
              let wrappedExp :
                  OracleComp (Fork.wrappedSpec Chal) ((M × (Commit × Resp)) × AdvState) :=
                (simulateQ simWrappedImpl (adv.main pk)).run advInit
              have h_rich_proj :
                  Prod.map id simProj <$> richExp = wrappedExp := by
                simpa [wrappedExp, richExp] using
                  (OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
                    (impl₁ := richImpl) (impl₂ := simWrappedImpl)
                    (inv := richInv) (proj := simProj)
                    (hinv := fun t s hs y hy => h_richInv_step t s hs hy)
                    (hproj := h_rich_simWrapped_step_proj)
                    (oa := adv.main pk) (s := richInit) h_richInv_init)
              have h_step_rel :
                  ∀ (t : (spec + (M →ₒ (Commit × Resp))).Domain) (s : AdvState),
                    OracleComp.ProgramLogic.Relational.RelTriple
                      ((simWrappedImpl t).run s) (((_simImplSigned pk) t).run s)
                      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) := by
                intro t s
                have hrel :
                    OracleComp.ProgramLogic.Relational.RelTriple
                      ((simWrappedImpl t).run s) (((_simImplSigned pk) t).run s)
                      (OracleComp.ProgramLogic.Relational.EqRel
                        (((spec + (M →ₒ (Commit × Resp))).Range t) × AdvState)) :=
                  OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_evalDist_eq
                    (h_simWrapped_step_evalDist t s)
                exact OracleComp.ProgramLogic.Relational.relTriple_post_mono hrel (by
                  intro p₁ p₂ hp
                  rcases hp with rfl
                  exact ⟨rfl, rfl⟩)
              have h_wrapped_direct_rel :
                  OracleComp.ProgramLogic.Relational.RelTriple wrappedExp (direct_sim_exp pk)
                    (OracleComp.ProgramLogic.Relational.EqRel
                      ((M × (Commit × Resp)) × AdvState)) := by
                have hrun :
                    OracleComp.ProgramLogic.Relational.RelTriple wrappedExp (direct_sim_exp pk)
                      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) := by
                  exact OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run
                    simWrappedImpl (_simImplSigned pk) (fun s₁ s₂ => s₁ = s₂) (adv.main pk)
                    (fun t s₁ s₂ hsEq => by
                      subst s₂
                      exact h_step_rel t s₁)
                    advInit advInit rfl
                exact OracleComp.ProgramLogic.Relational.relTriple_post_mono hrun (by
                  intro p₁ p₂ hp
                  rcases hp with ⟨hfst, hsnd⟩
                  simpa [OracleComp.ProgramLogic.Relational.EqRel] using Prod.ext hfst hsnd)
              have h_wrapped_direct_eq :
                  evalDist wrappedExp = evalDist (direct_sim_exp pk) :=
                OracleComp.ProgramLogic.Relational.evalDist_eq_of_relTriple_eqRel
                  h_wrapped_direct_rel
              symm
              calc
                Pr[fun z => event pk (Prod.map id simProj z) | richExp]
                    = Pr[event pk | Prod.map id simProj <$> richExp] := by
                        exact
                          (probEvent_map (mx := richExp) (f := Prod.map id simProj)
                            (q := event pk)).symm
                _ = Pr[event pk | wrappedExp] := by
                        rw [h_rich_proj]
                _ = Pr[event pk | direct_sim_exp pk] := by
                        refine probEvent_congr' (oa := wrappedExp) (oa' := direct_sim_exp pk)
                          (p := event pk) (q := event pk) ?_ h_wrapped_direct_eq
                        intro x hx
                        rfl
            have h_event_imp_forkPoint :
                ∀ z ∈ support richExp,
                  event pk (Prod.map id simProj z) →
                    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                      (Chal := Chal) qH (traceOfRich z)).isSome = true := by
              intro z hz hzEvent
              have hzInv : richInv z.2 :=
                h_richInv_run (oa := adv.main pk) (s := richInit) h_richInv_init z hz
              rcases z with ⟨⟨msg, cs⟩, s⟩
              rcases cs with ⟨c, resp⟩
              rcases s with ⟨sAdv, sRo⟩
              rcases sAdv with ⟨⟨cache, signed⟩, bad⟩
              rcases sRo with ⟨roCache, queryLog⟩
              rcases hzInv with ⟨hRoToAdv, hAdvToRoOrSigned, hRoMem⟩
              rcases hzEvent with ⟨⟨ω, hcache, hVerify⟩, hFresh⟩
              have hro : roCache (msg, c) = some ω := by
                rcases hAdvToRoOrSigned msg c ω hcache with hro | hsigned
                · exact hro
                · exact False.elim (hFresh hsigned)
              have hmem : (msg, c) ∈ queryLog := by
                exact (hRoMem (msg, c)).1 ⟨ω, hro⟩
              have hzTrace :
                  Prod.map id traceProj ((msg, (c, resp)), (((cache, signed), bad), (roCache, queryLog))) ∈
                    support ((simulateQ traceImpl (adv.main pk)).run traceInit) := by
                rw [← h_rich_trace_run]
                rw [support_map]
                exact ⟨((msg, (c, resp)), (((cache, signed), bad), (roCache, queryLog))), hz, rfl⟩
              have h_traceRo_run :
                  (fun y : (M × (Commit × Resp)) × TraceState => y.2.2) <$>
                    (simulateQ traceImpl (adv.main pk)).run traceInit =
                      Prod.snd <$> (simulateQ innerPkg.impl (nmaAdv.main pk)).run roInit := by
                simpa [traceImpl, traceOuter, nmaAdv, traceInit, innerPkg, traceCacheInit,
                  roInit, Function.comp_def] using
                  (VCVio.SSP.Package.map_simulateQ_link_run
                    (P := traceOuter) (Q := innerPkg)
                    (A := adv.main pk) (s₁ := traceCacheInit) (s₂ := roInit)
                    (f := fun y : (M × (Commit × Resp)) × TraceState => y.2.2))
              have hzRo :
                  ((roCache, queryLog) : RoState) ∈
                    support (Prod.snd <$> (simulateQ innerPkg.impl (nmaAdv.main pk)).run
                      roInit) := by
                have hzRo' :
                    ((roCache, queryLog) : RoState) ∈
                      support ((fun y : (M × (Commit × Resp)) × TraceState => y.2.2) <$>
                        (simulateQ traceImpl (adv.main pk)).run traceInit) := by
                  rw [support_map]
                  exact ⟨Prod.map id traceProj ((msg, (c, resp)),
                    (((cache, signed), bad), (roCache, queryLog))), hzTrace, rfl⟩
                rw [h_traceRo_run] at hzRo'
                exact hzRo'
              rw [support_map] at hzRo
              rcases hzRo with ⟨w, hw, hwEq⟩
              have hlen :
                  queryLog.length ≤ qH := by
                have hlen' :=
                  h_queryLog_len_le_of_nmaHashQueryBound (hQ := h_nmaHashBound)
                    (st := roInit) (z := w) hw
                rw [hwEq] at hlen'
                simpa [roInit] using hlen'
              have hidxLen : queryLog.findIdx (· == (msg, c)) < queryLog.length := by
                exact List.findIdx_lt_length_of_exists ⟨(msg, c), hmem, by simp⟩
              have hidx : queryLog.findIdx (· == (msg, c)) < qH + 1 := by
                omega
              have hidx_le : queryLog.findIdx (· == (msg, c)) ≤ qH := by
                exact Nat.lt_succ_iff.mp hidx
              unfold Fork.forkPoint
              simpa [traceOfRich, traceOfState, traceProj, cacheProj, Fork.Trace.target,
                hro, hVerify, hmem, hidx_le]
            calc
              Pr[event pk | direct_sim_exp pk]
                  = Pr[fun z => event pk (Prod.map id simProj z) | richExp] := by
                      exact h_pr_event_rich
              _ ≤ Pr[fun z =>
                    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                      (Chal := Chal) qH (traceOfRich z)).isSome | richExp] := by
                      refine probEvent_mono ?_
                      intro z hz hzEvent
                      exact h_event_imp_forkPoint z hz hzEvent
              _ = Pr[fun trace =>
                    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                      (Chal := Chal) qH trace).isSome | traceExp] := by
                      change
                        Pr[fun z =>
                            (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                              (Chal := Chal) qH (traceOfRich z)).isSome | richExp] =
                          Pr[fun trace =>
                            (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                              (Chal := Chal) qH trace).isSome | traceOfRich <$> richExp]
                      exact
                        (probEvent_map
                          (mx := richExp) (f := traceOfRich)
                          (q := fun trace =>
                            (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                              (Chal := Chal) qH trace).isSome)).symm
              _ = Pr[fun trace =>
                    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                      (Chal := Chal) qH trace).isSome | Fork.runTrace σ hr M nmaAdv pk] := by
                      rw [h_traceExp_eq_runTrace]
        -- Distribute `Fork.advantage` over keygen, mirroring the `hAdv_eq_tsum` pattern in
        -- `euf_nma_bound`.
        have hFork_tsum : Fork.advantage σ hr M nmaAdv qH =
            ∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              Pr[fun trace => (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                  (Chal := Chal) qH trace).isSome |
                Fork.runTrace σ hr M nmaAdv pksk.1] := by
          change Pr[= true | Fork.exp σ hr M nmaAdv qH] = _
          unfold Fork.exp
          rw [← probEvent_eq_eq_probOutput, probEvent_simulateQ_unifChalImpl,
            probEvent_bind_eq_tsum]
          refine tsum_congr fun pksk => ?_
          rw [probOutput_liftComp]
          congr 1
          rcases pksk with ⟨pk, sk⟩
          simp only [bind_pure_comp, probEvent_map, Function.comp_def]
        -- Chain the per-pk bound over the sum.
        rw [hFork_tsum]
        refine ENNReal.tsum_le_tsum fun pksk => ?_
        exact mul_le_mul_right (per_pk_event_le_forkPoint pksk.1) _
      -- Wire the four sub-claims into the final advantage bound.
      --
      -- Abbreviations used below:
      --   `S_real := ∑' (pk,sk), evalDist hr.gen (pk,sk) · Pr[event pk | direct_real_exp pk sk]`
      --   `S_sim  := ∑' (pk,sk), evalDist hr.gen (pk,sk) · Pr[event pk | direct_sim_exp pk]`
      --   `S_bad  := ∑' (pk,sk), evalDist hr.gen (pk,sk) · Pr[bad on direct_sim_exp pk]`
      --   `slackA    := qS · (qS+qH) · β` (ENNReal)
      --   `slackHT   := ofReal(qS·(qS+qH)·ζ_zk)`        -- HVZK-transport for real predictability
      --   `slackHVZK := ofReal(qS·ζ_zk)`                -- direct per-query HVZK cost
      --   `slackVerify := δ_verify`
      --
      -- Chain:
      --   adv.advantage
      --     ≤ S_real + slackA + slackHT + slackVerify             [bridge_real_freshness]
      --     ≤ (S_sim + slackHVZK + S_bad) + slackA + slackHT + slackVerify
      --                                                             [step_b_per_pksk_signed]
      --     ≤ (Fork.advantage + slackHVZK + slackA) + slackA + slackHT + slackVerify
      --                                                             [bridge_sim_fork_freshness,
      --                                                              pr_bad_le_signed]
      --     = Fork.advantage + (slackHVZK + slackHT) + 2·slackA + slackVerify
      --     = Fork.advantage + ofReal(qS·(qS+qH+1)·ζ_zk) + collisionSlack qS qH β + δ_verify
      --                       [arith: slackHVZK+slackHT combines via ofReal_add;
      --                               2·slackA = collisionSlack]
      --
      -- Step 2 uses `hr.gen_sound` on the support of `hr.gen` to supply `rel pk sk = true`
      -- to `step_b_per_pksk_signed`.
      -- Helper: `hr.gen` is a PMF, so its evalDist sums to 1.
      have h_keygen_sum_one : (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk) = 1 :=
        HasEvalPMF.tsum_probOutput_eq_one hr.gen
      let slackA : ENNReal := (qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β
      let slackHT : ENNReal := ENNReal.ofReal ((qS * (qS + qH) : ℕ) * ζ_zk)
      let slackHVZK : ENNReal := ENNReal.ofReal (qS * ζ_zk)
      -- (B) distributed over the sum: `S_real ≤ S_sim + slackHVZK + S_bad`.
      -- The `slackHVZK` factor pulls out via `h_keygen_sum_one`.
      have h_B_distributed :
          (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) ≤
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_sim_exp pksk.1]) +
              slackHVZK +
              (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[badPred | direct_sim_exp pksk.1]) := by
        have h_per_term : ∀ (pksk : Stmt × Wit),
            evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2] ≤
              evalDist hr.gen pksk *
                (Pr[event pksk.1 | direct_sim_exp pksk.1] +
                  slackHVZK +
                  Pr[badPred | direct_sim_exp pksk.1]) := by
          intro pksk
          by_cases h0 : evalDist hr.gen pksk = 0
          · rw [h0, zero_mul, zero_mul]
          · have hmem : pksk ∈ support hr.gen := by
              exact (mem_support_iff_evalDist_apply_ne_zero hr.gen pksk).2 h0
            have hrel : rel pksk.1 pksk.2 = true := hr.gen_sound _ _ hmem
            exact mul_le_mul_right (step_b_per_pksk_signed pksk.1 pksk.2 hrel) _
        have h_step1 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) ≤
              ∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                (Pr[event pksk.1 | direct_sim_exp pksk.1] +
                  slackHVZK +
                  Pr[badPred | direct_sim_exp pksk.1]) :=
          ENNReal.tsum_le_tsum h_per_term
        have h_step2 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              (Pr[event pksk.1 | direct_sim_exp pksk.1] +
                slackHVZK +
                Pr[badPred | direct_sim_exp pksk.1])) =
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_sim_exp pksk.1]) +
              slackHVZK +
              (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[badPred | direct_sim_exp pksk.1]) :=
          ENNReal.tsum_mul_add_const_add_of_tsum_eq_one _ _ _ _ h_keygen_sum_one
        exact h_step1.trans_eq h_step2
      -- (B-finish) distributed: `S_bad ≤ slackA` (since `hr.gen` is a PMF).
      have h_bad_sum :
          (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
              Pr[badPred | direct_sim_exp pksk.1]) ≤
            slackA := by
        have h_per_term : ∀ (pksk : Stmt × Wit),
            evalDist hr.gen pksk * Pr[badPred | direct_sim_exp pksk.1] ≤
              evalDist hr.gen pksk * slackA :=
          fun pksk => mul_le_mul_right (pr_bad_le_signed pksk.1) _
        have h_step1 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[badPred | direct_sim_exp pksk.1]) ≤
              ∑' (pksk : Stmt × Wit), evalDist hr.gen pksk * slackA :=
          ENNReal.tsum_le_tsum h_per_term
        have h_step2 :
            (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk * slackA) = slackA := by
          rw [ENNReal.tsum_mul_right, h_keygen_sum_one, one_mul]
        exact h_step1.trans h_step2.le
      -- Arithmetic: `2·slackA = collisionSlack qS qH β`.
      have h_slack_eq :
          slackA + slackA = collisionSlack qS qH β := by
        simpa [slackA, collisionSlack, mul_assoc] using
          (two_mul ((qS : ENNReal) * ((qS + qH : ℕ) : ENNReal) * β)).symm
      -- Arithmetic: `slackHVZK + slackHT = ofReal(qS·(qS+qH+1)·ζ_zk)`.
      have h_hvzk_eq :
          slackHVZK + slackHT =
          ENNReal.ofReal ((qS * (qS + qH + 1) : ℕ) * ζ_zk) := by
        rw [show slackHVZK = ENNReal.ofReal ((qS : ℝ) * ζ_zk) by rfl,
          show slackHT = ENNReal.ofReal ((qS * (qS + qH) : ℕ) * ζ_zk) by rfl]
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        ring
      -- Chain the pieces together.
      calc adv.advantage (runtime M)
          _ ≤ (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                Pr[event pksk.1 | direct_real_exp pksk.1 pksk.2]) +
              slackA + slackHT + δ_verify := by
            simpa [slackA, slackHT] using bridge_real_freshness
          _ ≤ (((∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                  Pr[event pksk.1 | direct_sim_exp pksk.1]) +
                slackHVZK) +
                (∑' (pksk : Stmt × Wit), evalDist hr.gen pksk *
                  Pr[badPred | direct_sim_exp pksk.1])) +
              slackA + slackHT + δ_verify := by
            gcongr
          _ ≤ (Fork.advantage σ hr M nmaAdv qH + slackHVZK + slackA) +
              slackA + slackHT +
              δ_verify := by
            -- `gcongr` decomposes the compound inequality and closes the two leaf goals
            -- `S_sim ≤ Fork.advantage` and `S_bad ≤ slackA` using
            -- `bridge_sim_fork_freshness` and `h_bad_sum` from context.
            gcongr
          _ = Fork.advantage σ hr M nmaAdv qH +
              (slackHVZK + slackHT) +
              (slackA + slackA) +
              δ_verify := by
            calc
              Fork.advantage σ hr M nmaAdv qH + slackHVZK + slackA + slackA + slackHT + δ_verify
                  = Fork.advantage σ hr M nmaAdv qH + slackHVZK +
                      ((slackA + slackA) + slackHT) + δ_verify := by
                        repeat rw [add_assoc]
              _ = Fork.advantage σ hr M nmaAdv qH + slackHVZK +
                    (slackHT + (slackA + slackA)) + δ_verify := by
                        rw [add_comm (slackA + slackA) slackHT]
              _ = Fork.advantage σ hr M nmaAdv qH +
                    (slackHVZK + slackHT) + (slackA + slackA) + δ_verify := by
                        repeat rw [add_assoc]
          _ = Fork.advantage σ hr M nmaAdv qH +
              ENNReal.ofReal ((qS * (qS + qH + 1) : ℕ) * ζ_zk) +
              collisionSlack qS qH β + δ_verify := by
            rw [h_hvzk_eq]
            rw [h_slack_eq]
    exact advantage_bound
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

/-- **Combined EUF-CMA bound (Pointcheval-Stern with quantitative HVZK, β-parametric).**

Composes `euf_cma_to_nma` and `euf_nma_bound`:

1. Replace the signing oracle with the HVZK simulator, losing
   `qS·(qS+qH+1)·ζ_zk + collisionSlack qS qH β + δ_verify`, where `β` is the
   simulator's commit-predictability bound and `δ_verify` bounds fresh-challenge
   verification acceptance.
2. Apply the forking lemma to the resulting forkable managed-RO NMA experiment.

The combined bound is:

  `(ε - qS·(qS+qH+1)·ζ_zk - 2·qS·(qS+qH)·β - δ_verify) ·
      ((ε - qS·(qS+qH+1)·ζ_zk - 2·qS·(qS+qH)·β - δ_verify) / (qH+1) - 1/|Ω|)
    ≤ Pr[extraction succeeds]`

where `ε = Adv^{EUF-CMA}(A)`, `2·qS·(qS+qH)·β` is `collisionSlack qS qH β`,
`δ_verify` is the fresh-challenge verification slack, and
`qS·(qS+qH+1)·ζ_zk` is the inflated HVZK cost
(`qS·ζ_zk` direct + `qS·(qS+qH)·ζ_zk` HVZK-transport). The ENNReal subtraction
truncates at zero, so the bound is trivially satisfied when the simulation loss
exceeds the advantage.

When HVZK is perfect (`ζ_zk = 0`), the HVZK term vanishes and the bound specializes to
`(ε - collisionSlack qS qH β - δ_verify) · …`.

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
        (ENNReal.ofReal ((qS * (qS + qH + 1) : ℕ) * ζ_zk) + collisionSlack qS qH β + δ_verify)
      (eps * (eps / (qH + 1 : ENNReal) - challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  haveI : DecidableEq M := Classical.decEq M
  haveI : DecidableEq Commit := Classical.decEq Commit
  obtain ⟨nmaAdv, hBound, hAdv⟩ := euf_cma_to_nma σ hr M simTranscript
    ζ_zk hζ_zk hhvzk β hPredSim δ_verify hVerifyGuess adv qS qH hQ
  obtain ⟨reduction, hRed⟩ := euf_nma_bound σ hr M hss hss_nf nmaAdv qH hBound
  refine ⟨reduction, le_trans ?_ hRed⟩
  have hle : adv.advantage (runtime M) -
      (ENNReal.ofReal ((qS * (qS + qH + 1) : ℕ) * ζ_zk) + collisionSlack qS qH β + δ_verify) ≤
      Fork.advantage σ hr M nmaAdv qH :=
    tsub_le_iff_right.mpr (by simpa [add_assoc] using hAdv)
  exact mul_le_mul' hle (tsub_le_tsub_right (ENNReal.div_le_div_right hle _) _)

end FiatShamir
