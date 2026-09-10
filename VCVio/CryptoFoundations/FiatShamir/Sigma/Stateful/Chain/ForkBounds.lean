/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Hops
public import VCVio.CryptoFoundations.FiatShamir.Sigma.CmaToNma
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
public import VCVio.CryptoFoundations.FiatShamir.QueryBounds
public import VCVio.ProgramLogic.Relational.SimulateQ

import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Hops
import all VCVio.CryptoFoundations.FiatShamir.Sigma.CmaToNma
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import all VCVio.CryptoFoundations.FiatShamir.QueryBounds
import all VCVio.ProgramLogic.Relational.SimulateQ
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Simulation
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Simulation

/-!
# Stateful Fiat-Shamir fork experiment bounds
-/

public section

universe u

open ENNReal OracleSpec OracleComp ProbComp OracleComp.ProgramLogic.Relational

namespace FiatShamir.Stateful

/-! Tag the CMA-to-NMA simulator handler family from `Sigma/CmaToNma.lean`
into the local `fs_simp` simp set. These defs live upstream (not under
`Sigma/Stateful/`), so we attach the FS-stateful local attribute here rather
than at the definition sites. -/

attribute [fs_simp]
  simulatedNmaFwd
  simulatedNmaUnifSim
  simulatedNmaRoSim
  simulatedNmaBaseSim
  simulatedNmaSigSim
  simulatedNmaImpl

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
  [Finite Chal] [Inhabited Chal]

attribute [local instance] instIsUniformSpecChalSingleton

@[fs_simp] private noncomputable def forkWrappedUniformImpl :
    QueryImpl (Fork.wrappedSpec Chal) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (Unit →ₒ Chal)))

@[fs_simp] private noncomputable def forkVerifyFreshComp
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (x : M × (Commit × Resp))
    (s : ForkBaseState M Commit Chal × List M) :
    OracleComp (Fork.wrappedSpec Chal) Bool := do
  let msg := x.1
  let c := x.2.1
  let resp := x.2.2
  match s.1.1 (.inr (msg, c)) with
  | some ch => pure (!decide (msg ∈ s.2) && σ.verify pk c ch resp)
  | none => do
      let ch ← (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
        OracleComp (Fork.wrappedSpec Chal) Chal)
      pure (!decide (msg ∈ s.2) && σ.verify pk c ch resp)

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
omit [DecidableEq Commit] in
private lemma forkVerifyFreshComp_project
    (pk : Stmt) (x : M × (Commit × Resp))
    (s : ForkBaseState M Commit Chal × List M) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x s) =
      simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk x
        (forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal) s) := by
  rcases x with ⟨msg, c, resp⟩
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  cases hcache : advCache (.inr (msg, c)) with
  | some ch =>
      change Chal at ch
      simp [forkVerifyFreshComp, simLoggedVerifyFreshComp, forkLoggedProj,
        forkWrappedUniformImpl, hcache]
      congr 1
  | none =>
      simp only [forkWrappedUniformImpl, QueryImpl.ofLift_eq_id',
        forkVerifyFreshComp, hcache, add_apply_inr, bind_pure_comp,
        simulateQ_map, simLoggedVerifyFreshComp, forkLoggedProj]
      congr 1
      exact simulateQ_id_add_uniform_query_inr (Unit →ₒ Chal) ()

private noncomputable def forkFinalQueryTrace
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (x : M × (Commit × Resp))
    (s : ForkBaseState M Commit Chal × List M) :
    OracleComp (Fork.wrappedSpec Chal)
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) := do
  let y ← (Fork.roImpl M Commit Chal (x.1, x.2.1)).run s.1.2
  let ch := y.1
  let liveSt := y.2
  pure {
    forgery := x
    advCache := s.1.1
    roCache := liveSt.1
    queryLog := liveSt.2
    verified := σ.verify pk x.2.1 ch x.2.2
  }

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] [Finite Chal] in
private lemma forkVerifyFreshComp_prob_true_le_finalQueryTrace_fresh
    [Fintype Chal]
    {qH : ℕ} {pk : Stmt} {msg : M} {c : Commit} {resp : Resp}
    {advCache : (fsRoSpec M Commit Chal).QueryCache}
    {liveCache : (M × Commit →ₒ Chal).QueryCache} {queryLog : List (M × Commit)}
    {signed : List M}
    (hsigned : msg ∉ signed) (hcache : advCache (.inr (msg, c)) = none)
    (hlive : liveCache (msg, c) = none) (hlenq : queryLog.length ≤ qH) :
    Pr[= true |
        forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk (msg, (c, resp)) (((advCache, (liveCache, queryLog)), signed))]
      ≤
    Pr[= true |
        forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk (msg, (c, resp))
          (((advCache, (liveCache, queryLog)), signed)) >>= fun trace =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
  classical
  let : SampleableType Chal := SampleableType.ofFintype Chal
  calc
    Pr[= true |
        forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk (msg, (c, resp))
          (((advCache, (liveCache, queryLog)), signed))]
        =
      Pr[fun ch : Chal => σ.verify pk c ch resp = true |
          (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
            OracleComp (Fork.wrappedSpec Chal) Chal)] := by
        conv_lhs =>
          simp [forkVerifyFreshComp, hcache, hsigned]
        rw [← probEvent_eq_eq_probOutput, probEvent_map]
        apply probEvent_ext
        intro ch _
        simp only [Function.comp_apply]
    _ ≤
      Pr[= true |
          forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ pk (msg, (c, resp))
            (((advCache, (liveCache, queryLog)), signed)) >>= fun trace =>
              pure ((Fork.forkPoint (M := M) (Commit := Commit)
                (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
        simp only [forkFinalQueryTrace, Fork.roImpl, StateT.run_bind,
          StateT.run_get, hlive, StateT.run_set,
          StateT.run_pure, monad_norm]
        rw [← probEvent_eq_eq_probOutput, bind_pure_comp, probEvent_map]
        rw [StateT.run_lift, bind_pure_comp, probEvent_map]
        refine _root_.probEvent_mono
          (mx := (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
            OracleComp (Fork.wrappedSpec Chal) Chal))
          (p := fun ch : Chal => σ.verify pk c ch resp = true)
          fun ch _hch hverify => ?_
        have hmem : (msg, c) ∈ queryLog ++ [(msg, c)] := by simp
        have hidx : (queryLog ++ [(msg, c)]).findIdx (· == (msg, c)) ≤ qH := by
          have hlt := List.findIdx_lt_length_of_exists
            (xs := queryLog ++ [(msg, c)]) (p := (· == (msg, c))) ⟨(msg, c), hmem, by simp⟩
          simp only [List.length_append, List.length_cons, List.length_nil] at hlt
          omega
        simpa [Function.comp_def] using forkPoint_isSome_of_mem_verified_findIdx_le
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (qH := qH)
          { forgery := (msg, (c, resp))
            advCache := advCache
            roCache := liveCache.cacheQuery (msg, c) ch
            queryLog := queryLog ++ [(msg, c)]
            verified := σ.verify pk c ch resp }
          (by simpa using hverify) (by simp [Fork.Trace.target, hmem])
          (by simpa [Fork.Trace.target] using hidx)

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] [Finite Chal] in
private lemma forkVerifyFreshComp_prob_true_le_finalQueryTrace
    [Fintype Chal]
    {qH : ℕ} {pk : Stmt} {x : M × (Commit × Resp)}
    {s : ForkBaseState M Commit Chal × List M}
    (hinv : forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) s)
    (hliveAdv : forkLiveCacheAdvCacheInv (M := M) (Commit := Commit)
      (Chal := Chal) s)
    (hlen : s.1.2.2.length ≤ qH) :
    Pr[= true |
        forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x s]
      ≤
    Pr[= true |
        forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x s >>= fun trace =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
  classical
  rcases x with ⟨msg, c, resp⟩
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  have hlenq : queryLog.length ≤ qH := by
    simpa using hlen
  by_cases hsigned : msg ∈ signed
  · cases hcache : advCache (.inr (msg, c)) <;>
      simp [forkVerifyFreshComp, hcache, hsigned]
  · cases hcache : advCache (.inr (msg, c)) with
    | some ch =>
        change Chal at ch
        have hlive : liveCache (msg, c) = some ch := hinv.1 (msg, c) ch hcache hsigned
        by_cases hverify : σ.verify pk c ch resp = true
        · have hfork :
            (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
              (Chal := Chal) qH
              { forgery := (msg, (c, resp))
                advCache := advCache
                roCache := liveCache
                queryLog := queryLog
                verified := σ.verify pk c ch resp }).isSome = true := by
              have hmem : (msg, c) ∈ queryLog := hinv.2 (msg, c) ch hlive
              apply forkPoint_isSome_of_mem_verified_length
              · simp [hverify]
              · simpa [Fork.Trace.target]
              · exact hlenq
          have hfork' :
            (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
              (Chal := Chal) qH
              { forgery := (msg, (c, resp))
                advCache := advCache
                roCache := liveCache
                queryLog := queryLog
                verified := true }).isSome = true := by
            simpa [hverify] using hfork
          simp [forkVerifyFreshComp, forkFinalQueryTrace, Fork.roImpl, hcache,
            hlive, hsigned, hverify, hfork']
        · have hverify_false : σ.verify pk c ch resp = false := Bool.not_eq_true _ ▸ hverify
          simp [forkVerifyFreshComp, hcache, hsigned, hverify_false]
    | none =>
        cases hlive : liveCache (msg, c) with
        | some liveCh =>
            have hcontra : advCache (.inr (msg, c)) = some liveCh :=
              hliveAdv (msg, c) liveCh hlive
            rw [hcache] at hcontra
            cases hcontra
        | none =>
            exact forkVerifyFreshComp_prob_true_le_finalQueryTrace_fresh
              (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ
              hsigned hcache hlive hlenq

omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private lemma forkBase_finalQuery_runTrace_eq
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) :
    Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk =
      ((simulateQ (forkBaseImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
        (forkInitialBaseState M Commit Chal) >>= fun z =>
          forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ pk z.1 (z.2, ([] : List M))) := by
  unfold Fork.runTrace nmaAdvFromCmaWithFinalQuery nmaAdvFromCma
    FiatShamir.simulatedNmaAdv forkBaseImpl forkInitialBaseState forkFinalQueryTrace
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, StateT.run_bind, QueryImpl.add_apply_inr,
    bind_assoc]
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (outer := Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
    (inner := simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (oa := adv.main pk)
    (s := (∅ : (fsRoSpec M Commit Chal).QueryCache))
    (q := ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit))))]
  simp only [monad_norm]
  refine bind_congr fun z ↦ ?_
  obtain ⟨⟨msg, c, resp⟩, advCache, liveCache, queryLog⟩ := z
  cases hcache : liveCache (msg, c) <;> simp [Fork.roImpl, hcache]

@[fs_simp] private noncomputable def forkLoggedProbImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (ForkBaseState M Commit Chal × List M) ProbComp) :=
  (forkWrappedUniformImpl (Chal := Chal)).mapStateTBase
    (forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)

omit [SampleableType Stmt] [Inhabited Chal] in
private lemma forkLoggedProbImpl_run
    {α : Type}
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    (s : ForkBaseState M Commit Chal × List M) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT pk) oa).run s) =
      (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run s := by
  simpa [forkLoggedProbImpl] using
    QueryImpl.simulateQ_mapStateTBase_run
      (outer := forkWrappedUniformImpl (Chal := Chal))
      (inner := forkLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk)
      (oa := oa) (s := s)

omit [Finite Chal] [Inhabited Chal] in
private lemma forkWrappedUniform_forkSim_query_inl_run
     (n : unifSpec.Domain)
    (liveSt : Fork.SimState M Commit Chal) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
          (liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inl n)))).run liveSt) =
      (fun u => (u, liveSt)) <$>
        (liftM (unifSpec.query n) : ProbComp
          ((unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inl n))) := by
  rw [Fork.simulateQ_unifForward_add_roImpl_query_inl_run]
  simp only [add_apply_inl, bind_pure_comp, simulateQ_map, Prod.mk.injEq,
    and_true, imp_self, implies_true, map_inj_right_of_nonempty]
  exact simulateQ_id_add_uniform_query_inl (Unit →ₒ Chal) n

omit [Finite Chal] [Inhabited Chal] in
private lemma forkWrappedUniform_forkSim_query_inr_run_none
     (mc : M × Commit)
    (cache : (M × Commit →ₒ Chal).QueryCache) (log : List (M × Commit))
    (hcache : cache mc = none) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
          (liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inr mc)))).run
            (cache, log)) =
      (fun v => (v, (cache.cacheQuery mc v, log ++ [mc]))) <$>
        (($ᵗ Chal) : ProbComp
          ((unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inr mc))) := by
  rw [Fork.simulateQ_unifForward_add_roImpl_query_inr_run_none
    (M := M) (Commit := Commit) (Chal := Chal) mc cache log hcache]
  change simulateQ (forkWrappedUniformImpl (Chal := Chal))
      ((Fork.wrappedChallengeQuery Chal >>= fun v =>
        pure (v, (cache.cacheQuery mc v, log ++ [mc]))) :
        OracleComp (Fork.wrappedSpec Chal) (Chal × Fork.SimState M Commit Chal)) =
    (fun v : Chal => (v, (cache.cacheQuery mc v, log ++ [mc]))) <$> ($ᵗ Chal)
  simp only [simulateQ_bind, simulateQ_pure]
  have hquery := simulateQ_id_add_uniform_query_inr (Unit →ₒ Chal) ()
  change simulateQ (forkWrappedUniformImpl (Chal := Chal))
      (Fork.wrappedChallengeQuery Chal) = ($ᵗ Chal) at hquery
  rw [hquery]
  exact (map_eq_bind_pure_comp ProbComp
    (fun v : Chal => (v, (cache.cacheQuery mc v, log ++ [mc]))) ($ᵗ Chal)).symm

omit [Finite Chal] [Inhabited Chal] in
private lemma forkWrappedUniform_forkSim_query_inr_run_none_map_fst
     {β : Type} (f : Chal → β) (mc : M × Commit)
    (cache : (M × Commit →ₒ Chal).QueryCache) (log : List (M × Commit))
    (hcache : cache mc = none) :
    (fun a => f a.1) <$> simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
          (liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inr mc)))).run
            (cache, log)) =
      f <$> ($ᵗ Chal) := by
  have hrun := forkWrappedUniform_forkSim_query_inr_run_none
    (M := M) (Commit := Commit) (Chal := Chal) mc cache log hcache
  calc
    _ = (fun a => f a.1) <$>
        ((fun v => (v, (cache.cacheQuery mc v, log ++ [mc]))) <$> ($ᵗ Chal)) :=
      congrArg (fun q => (fun a => f a.1) <$> q) hrun
    _ = _ := by rw [Functor.map_map]

omit [Finite Chal] [Inhabited Chal] in
private lemma simulatedNmaUnifSim_forkWrapped_run
    {α : Type} (oa : ProbComp α)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.SimState M Commit Chal) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
          ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
            (Chal := Chal)) oa).run advCache)).run liveSt) =
      (fun a ↦ ((a, advCache), liveSt)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing advCache liveSt with
  | pure x =>
      simp [forkWrappedUniformImpl]
  | query_bind n k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      simp only [simulatedNmaUnifSim, simulatedNmaFwd, QueryImpl.liftTarget_apply,
        add_apply_inl, HasQuery.toQueryImpl_apply, QueryImpl.toHasQuery_query,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, simulateQ_map,
        StateT.run_map, bind_map_left, map_bind]
      have hquery := forkWrappedUniform_forkSim_query_inl_run
        (M := M) (Commit := Commit) (Chal := Chal) n liveSt
      refine (congrArg (fun q => q >>= fun a =>
        simulateQ (forkWrappedUniformImpl (Chal := Chal))
          ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
            ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
              (Chal := Chal)) (k a.1)).run advCache)).run a.2)) hquery).trans ?_
      rw [bind_map_left]
      exact bind_congr (m := ProbComp) fun u ↦ ih u advCache liveSt

omit [Finite Chal] in
private lemma evalSPMF_simulateQ_forkWrappedUniformImpl [Fintype Chal]
    {α : Type} (oa : OracleComp (Fork.wrappedSpec Chal) α) :
    𝒮[simulateQ (forkWrappedUniformImpl (Chal := Chal)) oa] =
      𝒮[oa] := by
  apply OracleComp.evalSPMF_simulateQ_eq_evalSPMF
  rintro (n | u)
  · simp only [forkWrappedUniformImpl, QueryImpl.add_apply_inl,
      QueryImpl.ofLift_eq_id', QueryImpl.id'_apply]
    rw [OracleComp.evalSPMF_query (spec := Fork.wrappedSpec Chal)]
    exact OracleComp.evalSPMF_query (spec := unifSpec) n
  · simp only [forkWrappedUniformImpl, QueryImpl.add_apply_inr,
      uniformSampleImpl_apply]
    exact evalSPMF_uniformSample_eq_query
      (spec := Fork.wrappedSpec Chal) (Sum.inr u)

private lemma support_simulateQ_forkWrappedUniformImpl
    {α : Type} (oa : OracleComp (Fork.wrappedSpec Chal) α) :
    support (simulateQ (forkWrappedUniformImpl (Chal := Chal)) oa) =
      support oa := by
  let : Fintype Chal := Fintype.ofFinite Chal
  exact Set.ext fun x => mem_support_iff_of_evalSPMF_eq
    (evalSPMF_simulateQ_forkWrappedUniformImpl oa) x

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] [Finite Chal]
  [Inhabited Chal] in
omit [DecidableEq M] [DecidableEq Commit] in
private lemma forkInitialState_liveCacheAdvCacheInv :
    forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal)
      (forkInitialState M Commit Chal) := by
  intro mc ch hcache
  simp [forkInitialState] at hcache

omit [SampleableType Stmt] in
private def forkLoggedProbOrnament
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl.StateOrnament
      (forkLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk)
      (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) where
  inv := forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal)
  proj := forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal)
  preserves_inv := by
    simpa only [forkLoggedProbImpl] using
      QueryImpl.mapStateTBase_preserves_inv
        (outer := forkWrappedUniformImpl (Chal := Chal))
        (inner := forkLoggedImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT pk)
        (inv := forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal))
        (houter := support_simulateQ_forkWrappedUniformImpl (Chal := Chal))
        (hinner := forkLoggedImpl_preserves_live_adv_inv_step
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
  project_step := fun t s hs => by
    rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
    rcases t with ((n | mc) | m)
    · have hleft := forkWrappedUniform_forkSim_query_inl_run
        (M := M) (Commit := Commit) (Chal := Chal) n (liveCache, queryLog)
      have hright := simulateQ_id_add_uniform_query_inl
        (M × Commit →ₒ Chal) n
      have hleft' := congrArg
        (fun q => (fun a => (a.1, advCache, signed)) <$> q) hleft
      simp only [Functor.map_map] at hleft'
      have hright' := congrArg
        (fun q => (fun u => (u, advCache, signed)) <$> q) hright.symm
      simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase] using hleft'.trans hright'
    · cases hadv : advCache (.inr mc) with
      | some ch =>
          change Chal at ch
          simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, hadv]
      | none =>
          cases hlive : liveCache mc with
          | some liveCh =>
              have hcontra : advCache (.inr mc) = some liveCh := hs mc liveCh hlive
              rw [hadv] at hcontra
              cases hcontra
          | none =>
              have hleft := forkWrappedUniform_forkSim_query_inr_run_none_map_fst
                (M := M) (Commit := Commit) (Chal := Chal)
                (fun v => (v, advCache.cacheQuery (.inr mc) v, signed))
                mc liveCache queryLog hlive
              have hright := simulateQ_id_add_uniform_query_inr
                (M × Commit →ₒ Chal) mc
              simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
                QueryImpl.mapStateTBase, hadv] using
                  hleft.trans (congrArg (fun q => (fun v =>
                    (v, advCache.cacheQuery (.inr mc) v, signed)) <$> q) hright.symm)
    · simp only [add_apply_inr, fs_simp, QueryImpl.mapStateTBase,
        QueryImpl.ofLift_eq_id', QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_modifyGet,
        Prod.mk.eta, bind_pure_comp, simulateQ_map, StateT.run_mk, StateT.run_map,
        Functor.map_map, Prod.map_apply, id_eq]
      have hleft :
          simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
              ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
                ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
                  (Chal := Chal)) (simT pk)).run advCache)).run
                (liveCache, queryLog)) =
            (fun a => ((a, advCache), (liveCache, queryLog))) <$> simT pk := by
        simpa [forkWrappedUniformImpl] using
          (simulatedNmaUnifSim_forkWrapped_run (M := M) (Commit := Commit)
            (Chal := Chal) (oa := simT pk) (advCache := advCache)
            (liveSt := (liveCache, queryLog)))
      have hright :
          simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
              ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
                (Chal := Chal)) (simT pk)).run advCache) =
            (fun a => (a, advCache)) <$> simT pk := by
        simpa [fsUniformImpl] using
          (simulatedNmaUnifSim_fsUniform_run (M := M) (Commit := Commit)
            (Chal := Chal) (oa := simT pk) (cache := advCache))
      simp [hleft, hright, Functor.map_map]

omit [Finite Chal] in
private lemma probOutput_simulateQ_forkWrappedUniformImpl [Fintype Chal]
    {α : Type} (oa : OracleComp (Fork.wrappedSpec Chal) α) (x : α) :
    Pr[= x | simulateQ (forkWrappedUniformImpl (Chal := Chal)) oa] =
      Pr[= x | oa] :=
  by simpa only [probOutput_def] using
    congrFun (congrArg DFunLike.coe (evalSPMF_simulateQ_forkWrappedUniformImpl oa)) x

private noncomputable def forkH5Body
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    OracleComp (Fork.wrappedSpec Chal) Bool := do
  let (pk, _) ← OracleComp.liftComp hr.gen (Fork.wrappedSpec Chal)
  let z ← (simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
    (forkInitialState M Commit Chal)
  forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) σ pk z.1 z.2

private noncomputable def forkLoggedVerifyBody
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    OracleComp (Fork.wrappedSpec Chal) Bool := do
  let z ← (simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
    (forkInitialState M Commit Chal)
  forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) σ pk z.1 z.2

omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private lemma forkLogged_base_support
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    {z : (M × (Commit × Resp)) × (ForkBaseState M Commit Chal × List M)}
    (hz : z ∈ support
      ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
        (forkInitialState M Commit Chal))) :
    (z.1, z.2.1) ∈ support
      ((simulateQ (forkBaseImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
        (forkInitialBaseState M Commit Chal)) := by
  have hproj := OracleComp.extendState_run_proj_eq
    (so := forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (aux := cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp))
    (oa := adv.main pk)
    (s := forkInitialBaseState M Commit Chal)
    (q := ([] : List M))
  have hmem :
      (z.1, z.2.1) ∈ support
        (Prod.map id Prod.fst <$>
          (simulateQ (QueryImpl.extendState
            (forkBaseImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) simT pk)
            (cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp))) (adv.main pk)).run
            (forkInitialBaseState M Commit Chal, ([] : List M))) := by
    rw [support_map]
    exact ⟨z, by simpa [forkLoggedImpl, forkInitialState, forkInitialBaseState] using hz, rfl⟩
  rw [hproj] at hmem
  simpa [forkLoggedImpl, forkInitialState, forkInitialBaseState] using hmem

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma forkLogged_queryLog_length_le
    [Finite Commit] [Finite Resp]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) {qS qH : ℕ}
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit)
      (Chal := Chal) (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    {z : (M × (Commit × Resp)) × (ForkBaseState M Commit Chal × List M)}
    (hz : z ∈ support
      ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
        (forkInitialState M Commit Chal))) :
    z.2.1.2.2.length ≤ qH := by
  have hbase := forkLogged_base_support (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) σ hr adv simT pk hz
  have hnested :
      ((z.1, z.2.1.1), z.2.1.2) ∈ support
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
          ((simulateQ (simulatedNmaImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
            (∅ : (fsRoSpec M Commit Chal).QueryCache))).run
          ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit)))) := by
    have hmap :
        ((z.1, z.2.1.1), z.2.1.2) ∈ support
          ((fun y : (M × (Commit × Resp)) ×
              ((fsRoSpec M Commit Chal).QueryCache × Fork.SimState M Commit Chal) =>
              ((y.1, y.2.1), y.2.2)) <$>
            (simulateQ (forkBaseImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
              (forkInitialBaseState M Commit Chal)) := by
      rw [support_map]
      exact ⟨(z.1, z.2.1), hbase, rfl⟩
    have hmap_base := by
      simpa [forkBaseImpl, forkInitialBaseState] using hmap
    have hmap' :
        ((z.1, z.2.1.1), z.2.1.2) ∈ support
          ((fun y : (M × (Commit × Resp)) ×
              ((fsRoSpec M Commit Chal).QueryCache × Fork.SimState M Commit Chal) =>
              ((y.1, y.2.1), y.2.2)) <$>
            (simulateQ
              ((Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
                (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
                  (Resp := Resp) simT pk)).flattenStateT
              (adv.main pk)).run
              ((∅ : (fsRoSpec M Commit Chal).QueryCache),
                ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit))))) := by
      rw [support_map]
      exact ⟨(z.1, z.2.1), hmap_base, rfl⟩
    rw [← OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
      (outer := Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
      (inner := simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) simT pk)
      (oa := adv.main pk)
      (s := (∅ : (fsRoSpec M Commit Chal).QueryCache))
      (q := ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit))))] at hmap'
    simpa using hmap'
  have hQnma :
      nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := (nmaAdvFromCma σ hr M adv simT).main pk) qH :=
    nmaAdvFromCma_nmaHashQueryBound σ hr M adv simT qS qH hQ pk
  have hlen := Fork.queryLog_length_le_of_nmaHashQueryBound
    (M := M) (Commit := Commit) (Chal := Chal)
    (oa := (nmaAdvFromCma σ hr M adv simT).main pk)
    (Q := qH) hQnma
    ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit)))
    (z := ((z.1, z.2.1.1), z.2.1.2)) hnested
  simpa [nmaAdvFromCma, FiatShamir.simulatedNmaAdv] using hlen

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The H5 verify body's success probability is bounded by the live `forkPoint`
event for the verify-wrapped adversary. The fork slot parameter is `qH`:
`Fork.forkPoint qH` indexes `Fin (qH + 1)`, accommodating the wrapped
adversary's source-`qH` plus verifier-point query. -/
private lemma forkLogged_verify_prob_true_le_forkPoint_run
    [Fintype Chal] [Finite Commit] [Finite Resp]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) {qS qH : ℕ}
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit)
      (Chal := Chal) (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    Pr[= true |
        forkLoggedVerifyBody (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT pk]
      ≤
    Pr[= true |
        Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk
          >>= fun trace =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
  let loggedRun :=
    ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
      (forkInitialState M Commit Chal))
  let finalRun :=
    loggedRun >>= fun z =>
      forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk z.1 z.2 >>= fun trace =>
        pure ((Fork.forkPoint (M := M) (Commit := Commit)
          (Resp := Resp) (Chal := Chal) qH trace).isSome)
  have hbind := probEvent_bind_congr_le_add
    (mx := loggedRun)
    (my := fun z => forkVerifyFreshComp (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) σ pk z.1 z.2)
    (oc := fun z =>
      forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk z.1 z.2 >>= fun trace =>
        pure ((Fork.forkPoint (M := M) (Commit := Commit)
          (Resp := Resp) (Chal := Chal) qH trace).isSome))
    (q := fun b => b = true) (ε := 0) (by
      intro z hz
      have hinv := forkLoggedImpl_preserves_inv (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk (adv.main pk) hz
      have hliveAdv := forkLoggedImpl_preserves_live_adv_inv (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk
        (adv.main pk) hz
      have hlen := forkLogged_queryLog_length_le (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) σ hr adv simT pk hQ hz
      simpa [probEvent_eq_eq_probOutput] using
        forkVerifyFreshComp_prob_true_le_finalQueryTrace (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) σ
          (qH := qH) (pk := pk) (x := z.1) (s := z.2)
          hinv hliveAdv hlen)
  have hbind' :
      Pr[= true |
          forkLoggedVerifyBody (σ := σ) (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT pk]
        ≤ Pr[= true | finalRun] := by
    simpa [forkLoggedVerifyBody, loggedRun, finalRun, probEvent_eq_eq_probOutput]
      using hbind
  have hproj := OracleComp.extendState_run_proj_eq
    (so := forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (aux := cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp))
    (oa := adv.main pk)
    (s := forkInitialBaseState M Commit Chal)
    (q := ([] : List M))
  have hpoint :
      Pr[= true | finalRun] =
        Pr[= true |
          Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk
            >>= fun trace =>
              pure ((Fork.forkPoint (M := M) (Commit := Commit)
                (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
    calc
      Pr[= true | finalRun]
          =
        Pr[= true |
          (Prod.map id Prod.fst <$>
            (simulateQ (QueryImpl.extendState
              (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp) simT pk)
              (cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp))) (adv.main pk)).run
              (forkInitialBaseState M Commit Chal, ([] : List M))) >>= fun z =>
            forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) σ pk z.1 (z.2, ([] : List M)) >>= fun trace =>
              pure ((Fork.forkPoint (M := M) (Commit := Commit)
                (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
          simp [finalRun, loggedRun, forkLoggedImpl, forkInitialState,
            forkInitialBaseState, monad_norm, forkFinalQueryTrace]
      _ =
        Pr[= true |
          (simulateQ (forkBaseImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
            (forkInitialBaseState M Commit Chal) >>= fun z =>
            forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) σ pk z.1 (z.2, ([] : List M)) >>= fun trace =>
              pure ((Fork.forkPoint (M := M) (Commit := Commit)
                (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
          rw [hproj]
      _ =
        Pr[= true |
          Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk
            >>= fun trace =>
              pure ((Fork.forkPoint (M := M) (Commit := Commit)
                (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
          rw [forkBase_finalQuery_runTrace_eq (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) σ hr adv simT pk]
          simp
  exact hbind'.trans_eq hpoint

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The H5 body's success probability is bounded by the wrapped adversary's
fork advantage at slot parameter `qH`. The framework's `Fin (qH + 1)` indexing
provides exactly enough slots for the wrapped adversary's source-`qH` plus
verifier-point query. -/
private lemma forkH5Body_prob_true_le_fork_advantage
    [Fintype Chal] [Finite Commit] [Finite Resp]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) {qS qH : ℕ}
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit)
      (Chal := Chal) (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    Pr[= true |
        forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ hr adv simT]
      ≤
    Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH := by
  have hbind := probEvent_bind_congr_le_add
    (mx := (OracleComp.liftComp hr.gen (Fork.wrappedSpec Chal) :
      OracleComp (Fork.wrappedSpec Chal) (Stmt × Wit)))
    (my := fun ps => forkLoggedVerifyBody (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT ps.1)
    (oc := fun ps =>
      Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) ps.1 >>=
        fun trace =>
          pure ((Fork.forkPoint (M := M) (Commit := Commit)
            (Resp := Resp) (Chal := Chal) qH trace).isSome))
    (q := fun b => b = true) (ε := 0) (by
      intro ps _hps
      simpa [probEvent_eq_eq_probOutput] using
        forkLogged_verify_prob_true_le_forkPoint_run (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) σ hr adv simT ps.1 hQ)
  let pointBody : OracleComp (Fork.wrappedSpec Chal) Bool := do
    let (pk, _) ← OracleComp.liftComp hr.gen (Fork.wrappedSpec Chal)
    let trace ← Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk
    pure (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH trace).isSome
  have hpoint :
      Pr[= true | pointBody] =
        Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH := by
    rw [← probOutput_simulateQ_forkWrappedUniformImpl (Chal := Chal) (oa := pointBody) true]
    simp [pointBody, forkWrappedUniformImpl, Fork.advantage, Fork.exp]
  have hbody :
      Pr[= true |
          forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ hr adv simT] ≤
        Pr[= true | pointBody] := by
    simpa [forkH5Body, forkLoggedVerifyBody, pointBody, probEvent_eq_eq_probOutput] using hbind
  exact hbody.trans_eq hpoint

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
/-- Native H4 hop: running the linked simulated CMA game from the direct initial
state is the same as running the NMA game on the `cmaToNma`-shifted adversary.

The initial direct CMA state decomposes into the empty signing log for
`cmaToNma` and the initial NMA state for `nma`. -/
theorem cmaSim_run_eq_nma_run_shiftLeft_cmaToNma
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {α : Type}
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) :
    (cmaSim M Commit Chal hr simT).run (cmaInit M Commit Chal Stmt Wit) A =
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).run
        (nmaInit M Commit Chal Stmt Wit)
        ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M) A) := by
  unfold QueryImpl.Stateful.run QueryImpl.Stateful.shiftLeft cmaSim
  rw [StateT.run'_eq, StateT.run'_eq, QueryImpl.Stateful.simulateQ_linkWith_run,
    QueryImpl.Stateful.run, StateT.run'_eq, simulateQ_map, StateT.run_map]
  simp [cmaInit, nmaInit, cmaFrame, cmaOuterLens, cmaNmaLens,
    Functor.map_map]

end FiatShamir.Stateful
