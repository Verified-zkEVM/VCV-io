/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Bridge
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Hops
import VCVio.CryptoFoundations.FiatShamir.Sigma.CmaToNma
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.HeapSSP.Composition

/-!
# HeapSSP Chain: H5 and the top-level EUF-CMA-to-Fork bound

Endpoint of the HeapSSP-style Fiat-Shamir EUF-CMA proof: chains
H1+H2+H3+H4+H5 to produce the EUF-CMA-to-`Fork.advantage` bound.

State access is heap-based. `cmaRealRun` packages the signed-message
log via `p.2 (Sum.inl .log)`; the `hProj` step in the final chain
reduction reads off the `.inl .log` cell verbatim. H4 is a direct
instance of `Package.run_link_eq_run_shiftLeft`, so no per-state
equivalence scaffolding is needed.

## Contents

* `nmaAdvFromCma` — reduction construction: from a CMA adversary and an
  HVZK simulator, build a managed-RO NMA adversary suitable as input
  to the replay-forking lemma (`Fork.replayForkingBound`).
* `nma_runProb_shiftLeft_signedFreshAdv_le_fork` — **H5 hop**: bounds the
  NMA-side probability of accepting a fresh forgery by
  `Fork.advantage σ hr M nmaAdv qH + δ_verify`.
* `cma_advantage_le_fork_bound` — **top-level chain**. Tight
  Pointcheval-Stern-with-HVZK bound assembled from H1+H2+H3+H4+H5.
-/

universe u

open ENNReal OracleSpec OracleComp ProbComp VCVio.StateSeparating
  OracleComp.ProgramLogic.Relational

namespace FiatShamir.HeapSSP

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
  [Finite Chal] [Inhabited Chal]

/-! ### H5 hop: NMA advantage ≤ `Fork.advantage + δ_verify` -/

/-- The CMA-to-NMA reduction at the managed-RO interface.

Builds a `SignatureAlg.managedRoNmaAdv` from a CMA adversary `adv` and
an HVZK simulator `simT`. Internally this runs `adv` against the
simulator-replacement signing oracle and the programming-tracking RO,
collecting the programmed cache entries in `advCache` and returning
the adversary's forgery.

Concretely, it is the composition `cmaToNma.shiftLeft (signedAdv …)`
re-routed from `nmaSpec = unifSpec + roSpec + progSpec + pkSpec` to
the managed-RO `FiatShamir` spec `unifSpec + (M × Commit →ₒ Chal)`:

* `unifSpec`, `roSpec` queries pass through unchanged;
* `progSpec (m, c, ch)` queries are absorbed into `advCache`
  (deterministic write, no side-effect on the live RO);
* `pkSpec ()` queries return the fixed `pk` input parameter.

The `advCache` output is the union of all entries installed by the
simulator across signing queries, packaged as the managed-RO cache
consumed by `managedRoNmaExp`.

Alias for `FiatShamir.simulatedNmaAdv` under the HeapSSP-namespace
spelling used by the chain theorem below. -/
noncomputable def nmaAdvFromCma
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M) :=
  FiatShamir.simulatedNmaAdv σ hr M simT adv

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Hash-query bound for the reduction `nmaAdvFromCma`.

The reduction forwards `qH` live hash queries from `adv`'s `roSpec`
channel plus `qS` live hash queries from sign-query simulator
transcripts (one per signing query, absorbed into `advCache` rather
than issued live). Net live `roSpec` query budget therefore stays at
`qH`.

This is the `nmaHashQueryBound` hypothesis consumed by
`Fork.replayForkingBound`. -/
theorem nmaAdvFromCma_nmaHashQueryBound
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (nmaAdvFromCma σ hr M adv simT).main pk) qH := by
  intro pk
  have hbase :=
    FiatShamir.simulatedNmaAdv_hashQueryBound σ hr M simT adv qS qH hQ pk
  simpa [nmaHashQueryBound, nmaAdvFromCma] using hbase

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq Commit]
  [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- Shifted H5 adversary factored at the candidate/verify boundary.

The H3 bound already uses this split to keep the final verifier query out of
the signing-replacement cost. H5 needs the same split for a different reason:
candidate production is the forkable managed-RO run, while `verifyFreshComp`
is the single final check that either hits the live query log or pays the
fresh-challenge `δ_verify` term. -/
theorem cmaToNma_shiftLeft_signedFreshAdv_eq_bind
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    (cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft
        (signedFreshAdv σ hr M adv) =
      (cmaToNma (Stmt := Stmt) M Commit Chal simT).init >>= fun h =>
        (simulateQ (cmaToNma (Stmt := Stmt) M Commit Chal simT).impl
          (signedCandidateAdv σ hr M adv)).run h >>= fun (p, h') =>
          Prod.fst <$> (simulateQ (cmaToNma (Stmt := Stmt) M Commit Chal simT).impl
            (verifyFreshComp (σ := σ) (hr := hr) (M := M)
              (Commit := Commit) (Chal := Chal) (Resp := Resp) p)).run h' := by
  rw [signedFreshAdv, Package.shiftLeft_bind]

/-! ### Fork-aware simulator state -/

private abbrev ForkBaseState (M Commit Chal : Type)
    [DecidableEq M] [DecidableEq Commit] :=
  (fsRoSpec M Commit Chal).QueryCache × Fork.simSt M Commit Chal

private noncomputable def forkBaseImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (ForkBaseState M Commit Chal) (OracleComp (Fork.wrappedSpec Chal))) :=
  ((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
    (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)).flattenStateT

private def forkSignLogAux
    (t : (cmaOracleSpec M Commit Chal Resp).Domain)
    (_s : ForkBaseState M Commit Chal)
    (_u : (cmaOracleSpec M Commit Chal Resp).Range t)
    (_s' : ForkBaseState M Commit Chal) (signed : List M) :
    List M :=
  match t with
  | .inl _ => signed
  | .inr m => signed ++ [m]

private noncomputable def forkLoggedImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (ForkBaseState M Commit Chal × List M)
        (OracleComp (Fork.wrappedSpec Chal))) :=
  QueryImpl.extendState
    (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (forkSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp))

private noncomputable def cmaSimLoggedImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (List M × Heap (CmaCells M Commit Chal Stmt Wit)) ProbComp) :=
  (((cmaSim M Commit Chal hr simT).impl).mapStateTBase
    (cmaSignLogImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt))).flattenStateT

private noncomputable def cmaSimLoggedLeftImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (List M × Heap (CmaCells M Commit Chal Stmt Wit)) ProbComp) :=
  fun t => cmaSimLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT (Sum.inl t)

private abbrev SimLoggedState (M Commit Chal : Type)
    [DecidableEq M] [DecidableEq Commit] :=
  (fsRoSpec M Commit Chal).QueryCache × List M

private noncomputable def fsUniformImpl :
    QueryImpl (fsRoSpec M Commit Chal) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (M × Commit →ₒ Chal)))

private def simSignLogAux
    (t : (cmaOracleSpec M Commit Chal Resp).Domain)
    (_s : (fsRoSpec M Commit Chal).QueryCache)
    (_u : (cmaOracleSpec M Commit Chal Resp).Range t)
    (_s' : (fsRoSpec M Commit Chal).QueryCache) (signed : List M) :
    List M :=
  match t with
  | .inl _ => signed
  | .inr m => signed ++ [m]

private noncomputable def simulatedNmaLoggedProbImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (SimLoggedState M Commit Chal) ProbComp) :=
  QueryImpl.extendState
    ((fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal)).mapStateTBase
      (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) simT pk))
    (simSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp))

private def cmaSimLoggedProj
    (s : List M × Heap (CmaCells M Commit Chal Stmt Wit)) :
    SimLoggedState M Commit Chal :=
  (fun t =>
    match t with
    | .inl _ => none
    | .inr mc => s.2 (Sum.inr .roCache) mc,
  s.1)

private def forkLoggedProj (s : ForkBaseState M Commit Chal × List M) :
    SimLoggedState M Commit Chal :=
  (s.1.1, s.2)

private def cmaSimFixedKeyInv (pk : Stmt) (sk : Wit)
    (s : List M × Heap (CmaCells M Commit Chal Stmt Wit)) : Prop :=
  s.2 (Sum.inr .keypair) = some (pk, sk)

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal]
  [Finite Chal] [Inhabited Chal] in
private lemma cmaSimLoggedProj_roCache_cacheQuery
    (signed : List M) (h : Heap (CmaCells M Commit Chal Stmt Wit))
    (mc : M × Commit) (ch : Chal) :
    cmaSimLoggedProj (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit)
      (signed, h.update (Sum.inr InnerCell.roCache)
        ((h (Sum.inr InnerCell.roCache)).cacheQuery mc ch)) =
      (((cmaSimLoggedProj (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) (signed, h)).1).cacheQuery
          (Sum.inr mc) ch, signed) := by
  ext t <;> cases t <;> simp [cmaSimLoggedProj, QueryCache.cacheQuery]

private noncomputable def simLoggedVerifyFreshComp
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (x : M × (Commit × Resp))
    (s : SimLoggedState M Commit Chal) :
    ProbComp Bool := do
  let msg := x.1
  let c := x.2.1
  let resp := x.2.2
  match s.1 (.inr (msg, c)) with
  | some ch => pure (!decide (msg ∈ s.2) && σ.verify pk c ch resp)
  | none => do
      let ch ← $ᵗ Chal
      pure (!decide (msg ∈ s.2) && σ.verify pk c ch resp)

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimLoggedImpl_liftAdv_run {α : Type}
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    (st : List M × Heap (CmaCells M Commit Chal Stmt Wit)) :
    (simulateQ (cmaSimLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT)
        (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run st =
      (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT)
        oa).run st := by
  simpa [cmaSimLoggedLeftImpl] using congrArg (fun x => x.run st)
    (QueryImpl.simulateQ_liftM_eq_of_query
      (impl := cmaSimLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT)
      (impl₁ := cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT)
      (h := fun t => by
        change simulateQ
            (cmaSimLoggedImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT)
            (liftM ((cmaSpec M Commit Chal Resp Stmt).query (Sum.inl t))) =
          cmaSimLoggedLeftImpl (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT t
        rw [simulateQ_spec_query]
        rfl)
      (oa := oa))

private def forkTraceOfBase
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (forgery : M × (Commit × Resp))
    (s : ForkBaseState M Commit Chal) :
    Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) :=
  let liveCache := s.2.1
  let queryLog := s.2.2
  let verified :=
    match forgery with
    | (msg, (c, r)) =>
        match liveCache (msg, c) with
        | some ω => σ.verify pk c ω r
        | none => false
  {
    forgery := forgery
    advCache := s.1
    roCache := liveCache
    queryLog := queryLog
    verified := verified
  }

private def forkFreshCacheInv (s : ForkBaseState M Commit Chal × List M) : Prop :=
  ∀ (mc : M × Commit) (ch : Chal),
    s.1.1 (.inr mc) = some ch → mc.1 ∉ s.2 → s.1.2.1 mc = some ch

private def forkLiveCacheLogInv (s : ForkBaseState M Commit Chal × List M) : Prop :=
  ∀ (mc : M × Commit) (ch : Chal), s.1.2.1 mc = some ch → mc ∈ s.1.2.2

private def forkLiveCacheAdvCacheInv (s : ForkBaseState M Commit Chal × List M) : Prop :=
  ∀ (mc : M × Commit) (ch : Chal), s.1.2.1 mc = some ch → s.1.1 (.inr mc) = some ch

private def forkAwareInv (s : ForkBaseState M Commit Chal × List M) : Prop :=
  forkFreshCacheInv (M := M) (Commit := Commit) (Chal := Chal) s ∧
    forkLiveCacheLogInv (M := M) (Commit := Commit) (Chal := Chal) s

private def forkLiveHashCost :
    (cmaOracleSpec M Commit Chal Resp).Domain → ℕ
  | .inl (.inr _) => 1
  | _ => 0

private def forkInitialState (M Commit Chal : Type)
    [DecidableEq M] [DecidableEq Commit] :
    ForkBaseState M Commit Chal × List M :=
  (((∅ : (fsRoSpec M Commit Chal).QueryCache),
      ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit)))),
    ([] : List M))

private def forkInitialBaseState (M Commit Chal : Type)
    [DecidableEq M] [DecidableEq Commit] :
    ForkBaseState M Commit Chal :=
  ((∅ : (fsRoSpec M Commit Chal).QueryCache),
    ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit))))

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma forkInitialState_inv :
    forkAwareInv (M := M) (Commit := Commit) (Chal := Chal)
      (forkInitialState M Commit Chal) := by
  constructor
  · intro mc ch hcache _hfresh
    simp [forkInitialState] at hcache
  · intro mc ch hcache
    simp [forkInitialState] at hcache

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma simulatedNmaUnifFork_flatten_preserves_state
    {α : Type} (A : ProbComp α)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.simSt M Commit Chal)
    {z : α × ((fsRoSpec M Commit Chal).QueryCache × Fork.simSt M Commit Chal)}
    (hz : z ∈ support
      ((simulateQ
        ((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
          (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))).flattenStateT
        A).run (advCache, liveSt))) :
    z.2 = (advCache, liveSt) := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := ((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
      (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))).flattenStateT)
    (inv := fun st => st = (advCache, liveSt))
    (hinv := by
      intro t st hst y hy
      subst hst
      have hy' := by
        simpa [QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          simulatedNmaUnifSim, simulatedNmaFwd, Fork.unifFwd] using hy
      rcases hy' with ⟨u, _hu, rfl⟩
      rfl)
    A (advCache, liveSt) rfl z hz

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma simulatedNmaUnifFork_nested_preserves_state
    {α : Type} (A : ProbComp α)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.simSt M Commit Chal)
    {z : (α × (fsRoSpec M Commit Chal).QueryCache) × Fork.simSt M Commit Chal}
    (hz : z ∈ support
      ((simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
        ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
          (Chal := Chal)) A).run advCache)).run liveSt)) :
    z.1.2 = advCache ∧ z.2 = liveSt := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (outer := Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
    (inner := simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))
    (oa := A) (s := advCache) (q := liveSt)] at hz
  rw [support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hstate := simulatedNmaUnifFork_flatten_preserves_state
    (M := M) (Commit := Commit) (Chal := Chal) A advCache liveSt hy
  rcases y with ⟨a, st⟩
  simp only at hstate
  subst st
  simp

omit [SampleableType Stmt] in
private lemma forkLoggedImpl_preserves_inv_step
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    ∀ (t : (cmaOracleSpec M Commit Chal Resp).Domain)
      (s : ForkBaseState M Commit Chal × List M),
      forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) s →
      ∀ z ∈ support ((forkLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk t).run s),
        forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) z.2 := by
  intro t s hs z hz
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  rcases hs with ⟨hfreshInv, hlogInv⟩
  rcases t with ((n | mc) | m)
  · have hz' := by
      simpa [forkLoggedImpl, forkBaseImpl, forkSignLogAux, QueryImpl.extendState,
        QueryImpl.flattenStateT, QueryImpl.mapStateTBase, simulatedNmaImpl,
        simulatedNmaBaseSim, simulatedNmaUnifSim, simulatedNmaFwd,
        Fork.unifFwd] using hz
    rcases hz' with ⟨u, _hu, rfl⟩
    exact ⟨hfreshInv, hlogInv⟩
  · by_cases hadv : advCache (.inr mc) = none
    · have hz' := by
        simpa [forkLoggedImpl, forkBaseImpl, forkSignLogAux, QueryImpl.extendState,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, simulatedNmaImpl,
          simulatedNmaBaseSim, simulatedNmaRoSim, simulatedNmaFwd,
          Fork.roImpl, hadv] using hz
      by_cases hlive : liveCache mc = none
      · have hz'' := by
          simpa [hlive] using hz'
        rcases hz'' with ⟨ch, hch, rfl⟩
        rcases hch with ⟨u, rfl⟩
        constructor
        · intro mc' ch' hcache hfresh
          by_cases hmc : mc' = mc
          · subst mc'
            simpa [QueryCache.cacheQuery_self] using hcache
          · have hcache_old : advCache (.inr mc') = some ch' := by
              simpa [QueryCache.cacheQuery_of_ne, hmc] using hcache
            have hlive_old := hfreshInv mc' ch' hcache_old hfresh
            simpa [QueryCache.cacheQuery_of_ne, hmc] using hlive_old
        · intro mc' ch' hcache
          by_cases hmc : mc' = mc
          · subst mc'
            simp
          · have hcache_old : liveCache mc' = some ch' := by
              simpa [QueryCache.cacheQuery_of_ne, hmc] using hcache
            exact List.mem_append_left [mc] (hlogInv mc' ch' hcache_old)
      · rcases hlive' : liveCache mc with _ | liveCh
        · exact (hlive hlive').elim
        · have hz'' := by
            simpa [hlive'] using hz'
          rcases hz'' with ⟨rfl, rfl⟩
          constructor
          · intro mc' ch' hcache hfresh
            by_cases hmc : mc' = mc
            · subst mc'
              simpa [hlive'] using hcache
            · exact hfreshInv mc' ch'
                (by simpa [QueryCache.cacheQuery_of_ne, hmc] using hcache) hfresh
          · intro mc' ch' hcache
            exact hlogInv mc' ch' hcache
    · rcases hadv' : advCache (.inr mc) with _ | advCh
      · exact (hadv hadv').elim
      · have hz' := by
          simpa [forkLoggedImpl, forkBaseImpl, forkSignLogAux, QueryImpl.extendState,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, simulatedNmaImpl,
          simulatedNmaBaseSim, simulatedNmaRoSim, simulatedNmaFwd,
          hadv'] using hz
        rcases hz' with ⟨hcache, rfl⟩
        constructor
        · intro mc' ch' hcache' hfresh
          exact hfreshInv mc' ch' hcache' hfresh
        · intro mc' ch' hcache'
          exact hlogInv mc' ch' hcache'
  · have hz' := by
      simpa [forkLoggedImpl, forkBaseImpl, forkSignLogAux, QueryImpl.extendState,
        QueryImpl.flattenStateT, QueryImpl.mapStateTBase, simulatedNmaImpl,
        simulatedNmaSigSim] using hz
    rcases hz' with ⟨x, _hx, hcache, rfl⟩
    have hxstate := simulatedNmaUnifFork_nested_preserves_state
      (M := M) (Commit := Commit) (Chal := Chal) (simT pk) advCache
      (liveCache, queryLog) _hx
    rcases hxstate with ⟨hxadv, hxlive⟩
    constructor
    · intro mc ch hcache' hfresh
      by_cases hmc : mc = (m, x.1.1.1)
      · subst mc
        simp at hfresh
      · have hcache_old : advCache (.inr mc) = some ch := by
          have hsum :
              (Sum.inr mc : (fsRoSpec M Commit Chal).Domain) ≠
                Sum.inr (m, x.1.1.1) := by
            intro hsum
            exact hmc (by simpa using Sum.inr.inj hsum)
          cases htarget : advCache (Sum.inr (m, x.1.1.1)) with
          | none =>
              simpa [hxadv, htarget, QueryCache.cacheQuery_of_ne _ _ hsum] using hcache'
          | some ch' =>
              simpa [hxadv, htarget] using hcache'
        have hfresh_old : mc.1 ∉ signed := by
          intro hmem
          exact hfresh (by simp [hmem])
        have hlive_old := hfreshInv mc ch hcache_old hfresh_old
        change x.2.1 mc = some ch
        simpa [hxlive] using hlive_old
    · intro mc ch hcache'
      have hcache_old : liveCache mc = some ch := by
        simpa [hxlive] using hcache'
      change mc ∈ x.2.2
      simpa [hxlive] using hlogInv mc ch hcache_old

omit [SampleableType Stmt] in
private lemma forkLoggedImpl_preserves_inv
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    {α : Type} (A : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    {z : α × (ForkBaseState M Commit Chal × List M)}
    (hz : z ∈ support ((simulateQ (forkLoggedImpl (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk) A).run
      (forkInitialState M Commit Chal))) :
    forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) z.2 := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (inv := forkAwareInv (M := M) (Commit := Commit) (Chal := Chal))
    (hinv := forkLoggedImpl_preserves_inv_step (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk)
    A (forkInitialState M Commit Chal)
    (forkInitialState_inv (M := M) (Commit := Commit) (Chal := Chal)) z hz

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma forkPoint_isSome_of_mem_verified_length
    {qH : ℕ}
    (trace : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal))
    (hverified : trace.verified = true)
    (hmem : trace.target ∈ trace.queryLog)
    (hlen : trace.queryLog.length ≤ qH) :
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH trace).isSome = true := by
  unfold Fork.forkPoint
  simp [hverified, hmem]
  have hidx_lt_len :
      trace.queryLog.findIdx (· == trace.target) < trace.queryLog.length := by
    exact List.findIdx_lt_length_of_exists ⟨trace.target, hmem, by simp⟩
  have hidx : trace.queryLog.findIdx (· == trace.target) ≤ qH := by
    omega
  simp [hidx]

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal]
  [Finite Chal] [Inhabited Chal] in
private lemma forkPoint_isSome_of_fresh_advCache_hit
    {qH : ℕ} {pk : Stmt} {x : M × (Commit × Resp)}
    {s : ForkBaseState M Commit Chal × List M} {ch : Chal}
    (hinv : forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) s)
    (hlen : s.1.2.2.length ≤ qH)
    (hfresh : x.1 ∉ s.2)
    (hcache : s.1.1 (.inr (x.1, x.2.1)) = some ch)
    (hverify : σ.verify pk x.2.1 ch x.2.2 = true) :
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH
      (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk x s.1)).isSome = true := by
  rcases hinv with ⟨hfreshInv, hlogInv⟩
  have hlive : s.1.2.1 (x.1, x.2.1) = some ch :=
    hfreshInv (x.1, x.2.1) ch hcache hfresh
  have hmem : (x.1, x.2.1) ∈ s.1.2.2 := hlogInv (x.1, x.2.1) ch hlive
  apply forkPoint_isSome_of_mem_verified_length
  · simp [forkTraceOfBase, hlive, hverify]
  · simpa [Fork.Trace.target, forkTraceOfBase] using hmem
  · simpa [forkTraceOfBase] using hlen

private noncomputable def forkVerifyFreshComp
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

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] in
private lemma forkVerifyFreshComp_prob_true_le
    [Fintype Chal]
    {qH : ℕ} {pk : Stmt} {x : M × (Commit × Resp)}
    {s : ForkBaseState M Commit Chal × List M}
    (hinv : forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) s)
    (hlen : s.1.2.2.length ≤ qH)
    {δ_verify : ENNReal}
    (hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify) :
    Pr[= true |
        forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x s]
      ≤ (if (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
            (Chal := Chal) qH
            (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) σ pk x s.1)).isSome then 1 else 0) + δ_verify := by
  classical
  rcases x with ⟨msg, c, resp⟩
  by_cases hsigned : msg ∈ s.2
  · rcases hcache : s.1.1 (Sum.inr (msg, c)) with _ | ch <;>
      simp [forkVerifyFreshComp, hcache, hsigned]
  · rcases hcache : s.1.1 (Sum.inr (msg, c)) with _ | ch
    · have hmiss_le :
          Pr[fun ch : Chal => σ.verify pk c ch resp = true |
              (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                OracleComp (Fork.wrappedSpec Chal) Chal)]
            ≤ δ_verify := by
        have hguess := hVerifyGuess pk c resp
        have hquery :
            Pr[fun ch : Chal => σ.verify pk c ch resp = true |
                (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                  OracleComp (Fork.wrappedSpec Chal) Chal)] =
              ↑(Finset.card {ch : Chal | σ.verify pk c ch resp = true}) /
                ↑(Fintype.card Chal) := by
          simpa [OracleSpec.query_def] using
            (probEvent_query (spec := Fork.wrappedSpec Chal) (t := Sum.inr ())
              (p := fun ch : Chal => σ.verify pk c ch resp = true))
        rw [hquery]
        simpa using hguess
      calc
        Pr[= true |
            forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) σ pk (msg, c, resp) s]
            = Pr[fun ch : Chal => σ.verify pk c ch resp = true |
                (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                  OracleComp (Fork.wrappedSpec Chal) Chal)] := by
              conv_lhs =>
                simp [forkVerifyFreshComp, hcache, hsigned]
              rw [← probEvent_eq_eq_probOutput, probEvent_map]
              rfl
        _ ≤ δ_verify := hmiss_le
        _ ≤ (if (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
              (Chal := Chal) qH
              (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp) σ pk (msg, c, resp) s.1)).isSome then 1 else 0) +
            δ_verify := by
              rw [add_comm]
              exact le_self_add
    · by_cases hverify : σ.verify pk c ch resp = true
      · have hfork :
            (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
              (Chal := Chal) qH
              (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp) σ pk (msg, c, resp) s.1)).isSome = true :=
          forkPoint_isSome_of_fresh_advCache_hit (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) σ hinv hlen hsigned hcache hverify
        simp [forkVerifyFreshComp, hcache, hsigned, hverify, hfork]
      · have hverify_false : σ.verify pk c ch resp = false := by
          cases hv : σ.verify pk c ch resp <;> simp_all
        simp [forkVerifyFreshComp, hcache, hsigned, hverify_false]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma forkBase_runTrace_eq
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) :
    Fork.runTrace σ hr M (nmaAdvFromCma σ hr M adv simT) pk =
      (fun z : (M × (Commit × Resp)) × ForkBaseState M Commit Chal =>
        forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk z.1 z.2) <$>
        (simulateQ (forkBaseImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
          (forkInitialBaseState M Commit Chal) := by
  unfold Fork.runTrace nmaAdvFromCma FiatShamir.simulatedNmaAdv forkBaseImpl
    forkInitialBaseState forkTraceOfBase
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (outer := Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
    (inner := simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (oa := adv.main pk)
    (s := (∅ : (fsRoSpec M Commit Chal).QueryCache))
    (q := ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit))))]
  conv_lhs =>
    simp only [map_eq_bind_pure_comp, bind_pure_comp, bind_assoc,
      Function.comp_apply, pure_bind]
  conv_rhs =>
    simp only [map_eq_bind_pure_comp, bind_pure_comp, bind_assoc,
      Function.comp_apply, pure_bind]
  refine bind_congr fun z => ?_
  rfl

private noncomputable def forkWrappedUniformImpl [Fintype Chal] :
    QueryImpl (Fork.wrappedSpec Chal) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (Unit →ₒ Chal)))

private noncomputable def forkLoggedProbImpl [Fintype Chal]
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (ForkBaseState M Commit Chal × List M) ProbComp) :=
  (forkWrappedUniformImpl (Chal := Chal)).mapStateTBase
    (forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)

omit [SampleableType Stmt] in
private lemma forkLoggedProbImpl_run [Fintype Chal]
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
private lemma simulatedNmaUnifSim_fsUniform_run
    {α : Type} (oa : ProbComp α)
    (cache : (fsRoSpec M Commit Chal).QueryCache) :
    simulateQ (fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal))
        ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
          (Chal := Chal)) oa).run cache) =
      (fun a => (a, cache)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x =>
      simp [fsUniformImpl]
  | query_bind n k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      simp only [fsUniformImpl, QueryImpl.ofLift_eq_id', simulatedNmaUnifSim,
        simulatedNmaFwd, QueryImpl.liftTarget_apply, add_apply_inl,
        HasQuery.toQueryImpl_apply, QueryImpl.toHasQuery_query, StateT.run_monadLift,
        monadLift_self, bind_pure_comp, simulateQ_map, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inl,
        QueryImpl.id'_apply, id_map, bind_map_left, map_bind]
      refine bind_congr (m := ProbComp) fun u => ?_
      exact ih u cache

omit [Finite Chal] [Inhabited Chal] in
private lemma simulatedNmaUnifSim_forkWrapped_run
    [Fintype Chal]
    {α : Type} (oa : ProbComp α)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.simSt M Commit Chal) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
          ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
            (Chal := Chal)) oa).run advCache)).run liveSt) =
      (fun a => ((a, advCache), liveSt)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing advCache liveSt with
  | pure x =>
      simp [forkWrappedUniformImpl]
  | query_bind n k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      simp only [forkWrappedUniformImpl, QueryImpl.ofLift_eq_id',
        simulatedNmaUnifSim, simulatedNmaFwd, QueryImpl.liftTarget_apply,
        add_apply_inl, HasQuery.toQueryImpl_apply, QueryImpl.toHasQuery_query,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, simulateQ_map,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        QueryImpl.add_apply_inl, Fork.unifFwd, id_map, StateT.run_map,
        Functor.map_map, QueryImpl.id'_apply, bind_map_left, map_bind]
      refine bind_congr (m := ProbComp) fun u => ?_
      exact ih u advCache liveSt

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma nma_impl_lift_unif_run
    {α : Type} (oa : ProbComp α)
    (h : Heap (InnerCell M Commit Chal Stmt Wit)) :
    (simulateQ (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).impl
        (liftM oa : OracleComp (nmaSpec M Commit Chal Stmt) α)).run h =
      (fun a => (a, h)) <$> oa := by
  let impl₁ : QueryImpl unifSpec
      (StateT (Heap (InnerCell M Commit Chal Stmt Wit)) ProbComp) :=
    fun n => StateT.mk fun h => (fun a => (a, h)) <$> (unifSpec.query n)
  have himpl₁ : (simulateQ impl₁ oa).run h = (fun a => (a, h)) <$> oa := by
    induction oa using OracleComp.inductionOn generalizing h with
    | pure x =>
        simp [impl₁]
    | query_bind n k ih =>
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        simp only [map_eq_bind_pure_comp, StateT.run_mk, bind_assoc,
          Function.comp_apply, pure_bind, impl₁]
        refine bind_congr (m := ProbComp) fun u => ?_
        exact ih u h
  have hsim := QueryImpl.simulateQ_liftM_eq_of_query
    (impl := (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).impl)
    (impl₁ := impl₁)
    (h := fun n => by
      funext h'
      change (((nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).impl
        (Sum.inl (Sum.inl (Sum.inl n)))).run h') =
          (impl₁ n).run h'
      simp [impl₁, nma])
    (oa := oa)
  rw [hsim]
  exact himpl₁

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma forkVerifyFreshComp_project
    [Fintype Chal]
    (pk : Stmt) (x : M × (Commit × Resp))
    (s : ForkBaseState M Commit Chal × List M) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x s) =
      simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk x
        (forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal) s) := by
  rcases x with ⟨msg, c, resp⟩
  rcases hcache : s.1.1 (.inr (msg, c)) with _ | ch
  · simp [forkVerifyFreshComp, simLoggedVerifyFreshComp, forkLoggedProj,
      hcache, forkWrappedUniformImpl, uniformSampleImpl]
    rfl
  · simp [forkVerifyFreshComp, simLoggedVerifyFreshComp, forkLoggedProj,
      hcache, forkWrappedUniformImpl]
    rfl

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaSimLoggedLeftImpl_project_step
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (sk : Wit)
    (t : (cmaOracleSpec M Commit Chal Resp).Domain)
    (s : List M × Heap (CmaCells M Commit Chal Stmt Wit))
    (hs : cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk s) :
    Prod.map id (cmaSimLoggedProj (M := M) (Commit := Commit)
      (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
        (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
          hr simT t).run s =
      (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk t).run
        (cmaSimLoggedProj (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit) s) := by
  rcases s with ⟨signed, h⟩
  simp only [cmaSimFixedKeyInv] at hs
  rcases t with ((n | mc) | m)
  · simp [cmaSimLoggedLeftImpl, cmaSimLoggedImpl, cmaSim, cmaToNma, nma,
      cmaSignLogImpl, simulatedNmaLoggedProbImpl, simSignLogAux,
      cmaSimLoggedProj, fsUniformImpl, QueryImpl.extendState,
      QueryImpl.flattenStateT, QueryImpl.mapStateTBase, Package.link,
      Package.linkReshape, simulatedNmaImpl, simulatedNmaBaseSim,
      simulatedNmaUnifSim, simulatedNmaFwd]
  · cases hcache : h (Sum.inr InnerCell.roCache) mc with
    | some ch =>
        simp [cmaSimLoggedLeftImpl, cmaSimLoggedImpl, cmaSim, cmaToNma, nma,
          cmaSignLogImpl, simulatedNmaLoggedProbImpl, simSignLogAux,
          cmaSimLoggedProj, fsUniformImpl, QueryImpl.extendState,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, Package.link,
          Package.linkReshape, simulatedNmaImpl, simulatedNmaBaseSim,
          simulatedNmaRoSim, simulatedNmaFwd, hcache]
    | none =>
        simp only [add_apply_inl, add_apply_inr, cmaSimLoggedLeftImpl,
          cmaSimLoggedImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          cmaSim, Package.link, nma, bind_pure_comp, Prod.mk.eta, cmaToNma,
          simulateQ_pure, StateT.run_pure, map_pure, cmaSignLogImpl, bind_pure,
          StateT.run_monadLift, monadLift_self, simulateQ_map, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, StateT.run_mk, id_map,
          StateT.run_map, Heap.split_apply_inr, Functor.map_map,
          Package.linkReshape, hcache, Heap.split_symm_update_inr,
          Equiv.symm_apply_apply, Prod.map_apply, id_eq, cmaSimLoggedProj,
          Heap.get_update_self, simulatedNmaLoggedProbImpl, QueryImpl.extendState,
          fsUniformImpl, QueryImpl.ofLift_eq_id', simulatedNmaImpl,
          simulatedNmaBaseSim, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
          simulatedNmaRoSim, simulatedNmaFwd, QueryImpl.liftTarget_apply,
          HasQuery.toQueryImpl_apply, QueryImpl.toHasQuery_query, StateT.run_bind,
          StateT.run_get, pure_bind, simSignLogAux, StateT.run_modifyGet,
          uniformSampleImpl]
        congr 1
        funext ch
        congr 1
        ext t <;> cases t <;> simp [QueryCache.cacheQuery]
  · simp only [add_apply_inr, cmaSimLoggedLeftImpl, cmaSimLoggedImpl,
      QueryImpl.flattenStateT, add_apply_inl, QueryImpl.mapStateTBase, cmaSim,
      Package.link, nma, bind_pure_comp, Prod.mk.eta, cmaToNma, simulateQ_pure,
      StateT.run_pure, map_pure, cmaSignLogImpl, StateT.run_bind,
      StateT.run_get, StateT.run_monadLift, monadLift_self, StateT.run_map,
      StateT.run_set, Functor.map_map, pure_bind, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, StateT.run_mk,
      Heap.split_apply_inl, simulateQ_bind, id_map, Heap.split_apply_inr,
      map_bind, Package.linkReshape, hs, Prod.map_apply, id_eq, cmaSimLoggedProj,
      Heap.split_symm_apply_inr, simulatedNmaLoggedProbImpl, QueryImpl.extendState,
      fsUniformImpl, QueryImpl.ofLift_eq_id', simulatedNmaImpl,
      QueryImpl.add_apply_inr, simulatedNmaSigSim, StateT.run_modifyGet,
      simSignLogAux]
    have hleft := nma_impl_lift_unif_run (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Stmt := Stmt) (Wit := Wit)
      (oa := simT pk)
      ((Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit) h).2)
    simp only [nma, add_apply_inl, bind_pure_comp, add_apply_inr, Prod.mk.eta] at hleft
    let cache : (fsRoSpec M Commit Chal).QueryCache := fun t =>
      match t with
      | Sum.inl _ => none
      | Sum.inr mc => h (Sum.inr InnerCell.roCache) mc
    have hright :
        simulateQ
            (((QueryImpl.id' unifSpec) +
              (uniformSampleImpl (spec := (M × Commit →ₒ Chal)))) :
              QueryImpl (fsRoSpec M Commit Chal) ProbComp)
            ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
              (Chal := Chal)) (simT pk)).run cache) =
          (fun a => (a, cache)) <$> simT pk := by
      simpa [fsUniformImpl] using
        (simulatedNmaUnifSim_fsUniform_run (M := M) (Commit := Commit)
          (Chal := Chal) (oa := simT pk) (cache := cache))
    rw [hleft]
    conv_rhs =>
      arg 2
      change simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
        ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
          (Chal := Chal)) (simT pk)).run cache)
      rw [hright]
    simp only [map_eq_bind_pure_comp, bind_pure_comp, bind_assoc,
      Function.comp_apply, pure_bind]
    refine bind_congr (m := ProbComp) fun x => ?_
    cases htarget : h (Sum.inr InnerCell.roCache) (m, x.1) with
    | some old =>
        simp [cache, htarget, Heap.update]
    | none =>
        simp only [Heap.split_apply_inr, htarget, Heap.update, QueryCache.cacheQuery,
          pure_bind, Function.comp_apply, Function.update_self, add_apply_inl,
          add_apply_inr, pure_inj, Prod.mk.injEq, and_true, true_and, cache]
        ext t
        cases t
        · simp only [add_apply_inl, reduceCtorEq, Function.update, ↓reduceDIte]
        · simp only [add_apply_inr, Function.update, eq_rec_constant, dite_eq_ite,
            Sum.inr.injEq]
          rename_i val out
          by_cases hval : val = (m, x.1)
          · subst val
            simp
          · simp [hval]

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimLoggedLeftImpl_preserves_fixedKey
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (sk : Wit)
    (t : (cmaOracleSpec M Commit Chal Resp).Domain)
    (s : List M × Heap (CmaCells M Commit Chal Stmt Wit))
    (hs : cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk s) :
    ∀ z ∈ support ((cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
      hr simT t).run s),
      cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) pk sk z.2 := by
  rcases s with ⟨signed, h⟩
  simp only [cmaSimFixedKeyInv] at hs ⊢
  rcases t with ((n | mc) | m)
  · intro z hz
    have hz' := by
      simpa [cmaSimLoggedLeftImpl, cmaSimLoggedImpl, cmaSim, cmaToNma, nma,
        cmaSignLogImpl, cmaOracleSpec, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        Package.link, Package.linkReshape, simulatedNmaImpl,
        simulatedNmaBaseSim, simulatedNmaUnifSim, simulatedNmaFwd] using hz
    rcases hz' with ⟨u, _hu, rfl⟩
    exact hs
  · intro z hz
    cases hcache : h (Sum.inr InnerCell.roCache) mc with
    | some ch =>
        have hz' := by
          simpa [cmaSimLoggedLeftImpl, cmaSimLoggedImpl, cmaSim, cmaToNma, nma,
            cmaSignLogImpl, cmaOracleSpec, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            Package.link, Package.linkReshape, hcache, simulatedNmaImpl,
            simulatedNmaBaseSim, simulatedNmaRoSim, simulatedNmaFwd] using hz
        rcases hz' with ⟨rfl, rfl⟩
        exact hs
    | none =>
        have hz' := by
          simpa [cmaSimLoggedLeftImpl, cmaSimLoggedImpl, cmaSim, cmaToNma, nma,
            cmaSignLogImpl, cmaOracleSpec, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            Package.link, Package.linkReshape, hcache, uniformSampleImpl,
            simulatedNmaImpl, simulatedNmaBaseSim, simulatedNmaRoSim,
            simulatedNmaFwd] using hz
        rcases hz' with ⟨ch, _hch, rfl⟩
        simpa [Heap.update] using hs
  · intro z hz
    have hz' := by
      simpa [cmaSimLoggedLeftImpl, cmaSimLoggedImpl, cmaSim, cmaToNma, nma,
        cmaSignLogImpl, cmaOracleSpec, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        Package.link, Package.linkReshape, hs, simulatedNmaImpl,
        simulatedNmaSigSim, simulatedNmaUnifSim, simulatedNmaFwd] using hz
    rcases Set.mem_iUnion₂.mp hz' with ⟨x, hxmem, hzimg⟩
    simp only [Set.mem_image] at hzimg
    rcases hzimg with ⟨a, ha, rfl⟩
    have hxinner : x.2 =
        (Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit) h).2 := by
      have hxmem_nma :
          x ∈ support ((simulateQ
            (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).impl
            (liftM (simT pk) :
              OracleComp (nmaSpec M Commit Chal Stmt) (Commit × Chal × Resp))).run
              ((Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit) h).2)) := by
        simpa [nma] using hxmem
      have hxmem' := hxmem_nma
      rw [nma_impl_lift_unif_run (hr := hr) (M := M) (Commit := Commit)
        (Chal := Chal) (Stmt := Stmt) (Wit := Wit)
        (oa := simT pk)
        ((Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit) h).2)] at hxmem'
      rw [support_map] at hxmem'
      rcases hxmem' with ⟨x', _hx', rfl⟩
      rfl
    have hinnerKey :
        ((Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit) h).2)
          InnerCell.keypair = some (pk, sk) := by
      simpa using hs
    cases htarget : x.2 InnerCell.roCache (m, x.1.1) with
    | some old =>
        have ha' : a = ((), x.2.update InnerCell.bad true) := by
          simpa [htarget] using ha
        subst a
        simpa [hxinner, Heap.update] using hinnerKey
    | none =>
        have ha' :
            a = ((), x.2.update InnerCell.roCache
              (QueryCache.cacheQuery (x.2 InnerCell.roCache) (m, x.1.1) x.1.2.1)) := by
          simpa [htarget] using ha
        subst a
        simpa [hxinner, Heap.update] using hinnerKey

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaSimLoggedLeftImpl_project_run
    {α : Type}
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    (st : List M × Heap (CmaCells M Commit Chal Stmt Wit))
    (hst : cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk st) :
    Prod.map id (cmaSimLoggedProj (M := M) (Commit := Commit)
      (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
        (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
          hr simT) oa).run st =
      (simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run
        (cmaSimLoggedProj (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit) st) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (impl₁ := cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
      hr simT)
    (impl₂ := simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk)
    (inv := cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk)
    (proj := cmaSimLoggedProj (M := M) (Commit := Commit)
      (Chal := Chal) (Stmt := Stmt) (Wit := Wit))
    (hinv := fun t s hs =>
      cmaSimLoggedLeftImpl_preserves_fixedKey (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp)
        (Stmt := Stmt) (Wit := Wit) simT pk sk t s hs)
    (hproj := fun t s hs =>
      cmaSimLoggedLeftImpl_project_step (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp)
        (Stmt := Stmt) (Wit := Wit) simT pk sk t s hs)
    oa st hst

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSim_impl_lift_ro_query_run
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (mc : M × Commit)
    (h : Heap (CmaCells M Commit Chal Stmt Wit)) :
    (simulateQ (cmaSim M Commit Chal hr simT).impl
      (liftM (liftM (((M × Commit →ₒ Chal).query mc) :
          OracleQuery (M × Commit →ₒ Chal) Chal) :
        OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run h =
      match h (Sum.inr InnerCell.roCache) mc with
      | some ch => pure (ch, h)
      | none => (fun ch => (ch, h.update (Sum.inr InnerCell.roCache)
          ((h (Sum.inr InnerCell.roCache)).cacheQuery mc ch))) <$> ($ᵗ Chal) := by
  change (simulateQ (cmaSim M Commit Chal hr simT).impl
      (OracleComp.liftComp
        (OracleComp.liftComp
          (OracleComp.liftComp
            (((M × Commit →ₒ Chal).query mc) :
              OracleComp (M × Commit →ₒ Chal) Chal)
            (unifSpec + (M × Commit →ₒ Chal)))
          (cmaOracleSpec M Commit Chal Resp))
        (cmaSpec M Commit Chal Resp Stmt))).run h = _
  let implCmaOracle :
      QueryImpl (cmaOracleSpec M Commit Chal Resp)
        (StateT (Heap (CmaCells M Commit Chal Stmt Wit)) ProbComp) :=
    fun t => (cmaSim M Commit Chal hr simT).impl (Sum.inl t)
  let implFs :
      QueryImpl (fsRoSpec M Commit Chal)
        (StateT (Heap (CmaCells M Commit Chal Stmt Wit)) ProbComp) :=
    fun t => implCmaOracle (Sum.inl t)
  let implRo :
      QueryImpl (M × Commit →ₒ Chal)
        (StateT (Heap (CmaCells M Commit Chal Stmt Wit)) ProbComp) :=
    fun mc => StateT.mk fun h =>
      match h (Sum.inr InnerCell.roCache) mc with
      | some ch => pure (ch, h)
      | none => (fun ch => (ch, h.update (Sum.inr InnerCell.roCache)
          ((h (Sum.inr InnerCell.roCache)).cacheQuery mc ch))) <$> ($ᵗ Chal)
  have houter := QueryImpl.simulateQ_liftComp_left_eq_of_apply
    (impl := (cmaSim M Commit Chal hr simT).impl)
    (impl₁ := implCmaOracle)
    (h := fun t => rfl)
    (oa := OracleComp.liftComp
      (OracleComp.liftComp
        (((M × Commit →ₒ Chal).query mc) :
          OracleComp (M × Commit →ₒ Chal) Chal)
        (unifSpec + (M × Commit →ₒ Chal)))
      (cmaOracleSpec M Commit Chal Resp))
  have hleft := QueryImpl.simulateQ_liftComp_left_eq_of_apply
    (impl := implCmaOracle)
    (impl₁ := implFs)
    (h := fun t => rfl)
    (oa := OracleComp.liftComp
      (((M × Commit →ₒ Chal).query mc) :
        OracleComp (M × Commit →ₒ Chal) Chal)
      (unifSpec + (M × Commit →ₒ Chal)))
  have hright_apply : ∀ mc, implFs (Sum.inr mc) = implRo mc := by
    intro mc'
    funext h'
    let hα : Heap (OuterCell M) :=
      (Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit) h').1
    let hβ : Heap (InnerCell M Commit Chal Stmt Wit) :=
      (Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit) h').2
    have h_split_symm :
        (Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit)).symm (hα, hβ)
          = h' :=
      (Heap.split (OuterCell M) (InnerCell M Commit Chal Stmt Wit)).left_inv h'
    have hβcache_eq : hβ .roCache = h' (Sum.inr .roCache) := rfl
    change (((cmaToNma (Stmt := Stmt) M Commit Chal simT).link
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)).impl
        (Sum.inl (Sum.inl (Sum.inr mc')))).run h' =
      (implRo mc').run h'
    conv_lhs => rw [← h_split_symm]
    rw [Package.link_impl_apply_run]
    simp only [cmaToNma, StateT.run_mk, bind_pure_comp,
      simulateQ_map, simulateQ_spec_query, StateT.run_map,
      Functor.map_map, Package.linkReshape]
    rcases hcache : h' (Sum.inr .roCache) mc' with _ | r
    · simp only [implRo, nma, StateT.run_mk, hβcache_eq, hcache,
        bind_pure_comp, Functor.map_map]
      congr 1
      funext a
      exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, by
        simpa [h_split_symm] using
          (Heap.split_symm_update_inr
            (α := OuterCell M) (β := InnerCell M Commit Chal Stmt Wit)
            (p := (hα, hβ)) .roCache ((h' (Sum.inr .roCache)).cacheQuery mc' a))⟩
    · simp only [implRo, nma, StateT.run_mk, hβcache_eq, hcache,
        map_pure, h_split_symm]
      rfl
  have hright := QueryImpl.simulateQ_liftComp_right_eq_of_apply
    (impl := implFs)
    (impl₂ := implRo)
    (h := hright_apply)
    (oa := (((M × Commit →ₒ Chal).query mc) :
      OracleComp (M × Commit →ₒ Chal) Chal))
  calc
    (simulateQ (cmaSim M Commit Chal hr simT).impl
        (OracleComp.liftComp
          (OracleComp.liftComp
            (OracleComp.liftComp
              (((M × Commit →ₒ Chal).query mc) :
                OracleComp (M × Commit →ₒ Chal) Chal)
              (unifSpec + (M × Commit →ₒ Chal)))
            (cmaOracleSpec M Commit Chal Resp))
          (cmaSpec M Commit Chal Resp Stmt))).run h
        = (simulateQ implCmaOracle
            (OracleComp.liftComp
              (OracleComp.liftComp
                (((M × Commit →ₒ Chal).query mc) :
                  OracleComp (M × Commit →ₒ Chal) Chal)
                (unifSpec + (M × Commit →ₒ Chal)))
              (cmaOracleSpec M Commit Chal Resp))).run h := by
          simpa [cmaSpec] using congrArg (fun c => c.run h) houter
    _ = (simulateQ implFs
          (OracleComp.liftComp
            (((M × Commit →ₒ Chal).query mc) :
              OracleComp (M × Commit →ₒ Chal) Chal)
            (unifSpec + (M × Commit →ₒ Chal)))).run h := by
          simpa using congrArg (fun c => c.run h) hleft
    _ = (simulateQ implRo
          (((M × Commit →ₒ Chal).query mc) :
            OracleComp (M × Commit →ₒ Chal) Chal)).run h := by
          simpa using congrArg (fun c => c.run h) hright
    _ = _ := by
          rw [simulateQ_spec_query]
          rfl

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimVerifyFreshComp_project
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (x : M × (Commit × Resp))
    (st : List M × Heap (CmaCells M Commit Chal Stmt Wit)) :
    (fun a => !decide (x.1 ∈ st.1) && a.1) <$>
        (simulateQ (cmaSim M Commit Chal hr simT).impl
          (liftM (((FiatShamir σ hr M).verify pk x.1 x.2) :
              OracleComp (unifSpec + (M × Commit →ₒ Chal)) Bool) :
            OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)).run st.2 =
      simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk x
        (cmaSimLoggedProj (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit) st) := by
  rcases x with ⟨msg, c, resp⟩
  rcases st with ⟨signed, h⟩
  rcases hcache : h (Sum.inr InnerCell.roCache) (msg, c) with _ | ch
  · simp [simLoggedVerifyFreshComp, cmaSimLoggedProj, FiatShamir, hcache,
      cmaSim_impl_lift_ro_query_run (hr := hr) (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        simT (msg, c) h]
    rfl
  · simp [simLoggedVerifyFreshComp, cmaSimLoggedProj, FiatShamir, hcache,
      cmaSim_impl_lift_ro_query_run (hr := hr) (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        simT (msg, c) h]
    rfl

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma forkInitialState_liveCacheAdvCacheInv :
    forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal)
      (forkInitialState M Commit Chal) := by
  intro mc ch hcache
  simp [forkInitialState] at hcache

omit [SampleableType Stmt] in
private lemma forkLoggedProbImpl_project_step
    [Fintype Chal]
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    (t : (cmaOracleSpec M Commit Chal Resp).Domain)
    (s : ForkBaseState M Commit Chal × List M)
    (hs : forkLiveCacheAdvCacheInv (M := M) (Commit := Commit)
      (Chal := Chal) s) :
    Prod.map id (forkLoggedProj (M := M) (Commit := Commit)
      (Chal := Chal)) <$>
        (forkLoggedProbImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT pk t).run s =
      (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk t).run
        (forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal) s) := by
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  rcases t with ((n | mc) | m)
  · simp [forkLoggedProbImpl, forkLoggedImpl, forkBaseImpl,
      simulatedNmaLoggedProbImpl, forkSignLogAux, simSignLogAux,
      forkLoggedProj, fsUniformImpl, forkWrappedUniformImpl,
      QueryImpl.extendState, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
      simulatedNmaImpl, simulatedNmaBaseSim, simulatedNmaUnifSim,
      simulatedNmaFwd, Fork.unifFwd]
  · cases hadv : advCache (.inr mc) with
    | some ch =>
        simp [forkLoggedProbImpl, forkLoggedImpl, forkBaseImpl,
          simulatedNmaLoggedProbImpl, forkSignLogAux, simSignLogAux,
          forkLoggedProj, fsUniformImpl, forkWrappedUniformImpl,
          QueryImpl.extendState, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, simulatedNmaImpl, simulatedNmaBaseSim,
          simulatedNmaRoSim, simulatedNmaFwd, hadv]
    | none =>
        cases hlive : liveCache mc with
        | some liveCh =>
            have hcontra : advCache (.inr mc) = some liveCh := hs mc liveCh hlive
            rw [hadv] at hcontra
            cases hcontra
        | none =>
            simp [forkLoggedProbImpl, forkLoggedImpl, forkBaseImpl,
              simulatedNmaLoggedProbImpl, forkSignLogAux, simSignLogAux,
              forkLoggedProj, fsUniformImpl, forkWrappedUniformImpl,
              QueryImpl.extendState, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, simulatedNmaImpl, simulatedNmaBaseSim,
              simulatedNmaRoSim, simulatedNmaFwd, Fork.roImpl, hadv, hlive,
              uniformSampleImpl]
  · simp only [add_apply_inr, forkLoggedProbImpl, QueryImpl.mapStateTBase,
      forkWrappedUniformImpl, QueryImpl.ofLift_eq_id', forkLoggedImpl,
      QueryImpl.extendState, forkBaseImpl, QueryImpl.flattenStateT,
      simulatedNmaImpl, QueryImpl.add_apply_inr, simulatedNmaSigSim,
      StateT.run_bind, StateT.run_modifyGet, Prod.mk.eta, bind_pure_comp,
      simulateQ_map, StateT.run_mk, StateT.run_map, Functor.map_map,
      forkSignLogAux, Prod.map_apply, id_eq, forkLoggedProj,
      simulatedNmaLoggedProbImpl, fsUniformImpl, simSignLogAux]
    have hleft :
        simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
            ((simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
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
    rw [hleft, hright]
    simp [Functor.map_map]

omit [SampleableType Stmt] in
private lemma forkLoggedProbImpl_preserves_liveCacheAdvCacheInv
    [Fintype Chal]
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    (t : (cmaOracleSpec M Commit Chal Resp).Domain)
    (s : ForkBaseState M Commit Chal × List M)
    (hs : forkLiveCacheAdvCacheInv (M := M) (Commit := Commit)
      (Chal := Chal) s) :
    ∀ z ∈ support ((forkLoggedProbImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk t).run s),
      forkLiveCacheAdvCacheInv (M := M) (Commit := Commit)
        (Chal := Chal) z.2 := by
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  rcases t with ((n | mc) | m)
  · intro z hz
    have hz' := by
      simpa [forkLoggedProbImpl, forkLoggedImpl, forkBaseImpl,
        forkSignLogAux, forkWrappedUniformImpl, QueryImpl.extendState,
        QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        simulatedNmaImpl, simulatedNmaBaseSim, simulatedNmaUnifSim,
        simulatedNmaFwd, Fork.unifFwd] using hz
    rcases hz' with ⟨u, _hu, rfl⟩
    exact hs
  · intro z hz
    cases hadv : advCache (.inr mc) with
    | some ch =>
        have hz' := by
          simpa [forkLoggedProbImpl, forkLoggedImpl, forkBaseImpl,
            forkSignLogAux, forkWrappedUniformImpl, QueryImpl.extendState,
            QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            simulatedNmaImpl, simulatedNmaBaseSim, simulatedNmaRoSim,
            simulatedNmaFwd, hadv] using hz
        rcases hz' with ⟨rfl, rfl⟩
        exact hs
    | none =>
        cases hlive : liveCache mc with
        | some liveCh =>
            have hcontra : advCache (.inr mc) = some liveCh := hs mc liveCh hlive
            rw [hadv] at hcontra
            cases hcontra
        | none =>
            have hz' := by
              simpa [forkLoggedProbImpl, forkLoggedImpl, forkBaseImpl,
                forkSignLogAux, forkWrappedUniformImpl, QueryImpl.extendState,
                QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
                simulatedNmaImpl, simulatedNmaBaseSim, simulatedNmaRoSim,
                simulatedNmaFwd, Fork.roImpl, hadv, hlive,
                uniformSampleImpl] using hz
            rcases hz' with ⟨ch, _hch, rfl⟩
            intro mc' ch' hcache'
            by_cases hmc : mc' = mc
            · subst mc'
              simpa [QueryCache.cacheQuery_self] using hcache'
            · have hcache_old : liveCache mc' = some ch' := by
                simpa [QueryCache.cacheQuery_of_ne, hmc] using hcache'
              have hadv_old := hs mc' ch' hcache_old
              simpa [QueryCache.cacheQuery_of_ne, hmc] using hadv_old
  · intro z hz
    have hz' := by
      simpa [forkLoggedProbImpl, forkLoggedImpl, forkBaseImpl,
        forkSignLogAux, forkWrappedUniformImpl, QueryImpl.extendState,
        QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        simulatedNmaImpl, simulatedNmaSigSim] using hz
    rcases hz' with ⟨x, _hx, hcache, rfl⟩
    have hrun :
        simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
            ((simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
              ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
                (Chal := Chal)) (simT pk)).run advCache)).run
              (liveCache, queryLog)) =
          (fun a => ((a, advCache), (liveCache, queryLog))) <$> simT pk := by
      simpa [forkWrappedUniformImpl] using
        (simulatedNmaUnifSim_forkWrapped_run (M := M) (Commit := Commit)
          (Chal := Chal) (oa := simT pk) (advCache := advCache)
          (liveSt := (liveCache, queryLog)))
    rw [hrun, support_map] at _hx
    rcases _hx with ⟨x', _hx', rfl⟩
    intro mc ch hcache'
    have hcache_old : liveCache mc = some ch := by
      simpa using hcache'
    have hadv_old := hs mc ch hcache_old
    have hadv_old' : advCache (.inr mc) = some ch := by
      simpa using hadv_old
    by_cases hmc : mc = (m, x'.1)
    · subst mc
      cases htarget : advCache (.inr (m, x'.1)) with
      | none =>
          rw [hadv_old'] at htarget
          cases htarget
      | some old =>
          simpa [htarget] using hadv_old'
    · have hsum :
          (Sum.inr mc : (fsRoSpec M Commit Chal).Domain) ≠
            Sum.inr (m, x'.1) := by
        intro hsum
        exact hmc (by simpa using Sum.inr.inj hsum)
      cases htarget : advCache (.inr (m, x'.1)) with
      | none =>
          simpa [htarget, QueryCache.cacheQuery_of_ne _ _ hsum] using hadv_old'
      | some old =>
          simpa [htarget] using hadv_old'

omit [SampleableType Stmt] in
private lemma forkLoggedProbImpl_project_run
    [Fintype Chal]
    {α : Type}
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) α) :
    Prod.map id (forkLoggedProj (M := M) (Commit := Commit)
      (Chal := Chal)) <$>
        (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT pk) oa).run
          (forkInitialState M Commit Chal) =
      (simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) := by
  have hrun := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (impl₁ := forkLoggedProbImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk)
    (impl₂ := simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk)
    (inv := forkLiveCacheAdvCacheInv (M := M) (Commit := Commit)
      (Chal := Chal))
    (proj := forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal))
    (hinv := fun t s hs =>
      forkLoggedProbImpl_preserves_liveCacheAdvCacheInv (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk t s hs)
    (hproj := fun t s hs =>
      forkLoggedProbImpl_project_step (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk t s hs)
    oa (forkInitialState M Commit Chal)
    (forkInitialState_liveCacheAdvCacheInv (M := M) (Commit := Commit)
      (Chal := Chal))
  simpa [forkLoggedProj, forkInitialState] using hrun

omit [Finite Chal] in
private lemma evalDist_simulateQ_forkWrappedUniformImpl [Fintype Chal]
    {α : Type} (oa : OracleComp (Fork.wrappedSpec Chal) α) :
    evalDist (simulateQ (forkWrappedUniformImpl (Chal := Chal)) oa) =
      evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [forkWrappedUniformImpl]
  | query_bind t mx ih =>
      rcases t with n | u
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map, evalDist_bind, ih]
        apply bind_congr
        simp
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, QueryImpl.add_apply_inr, forkWrappedUniformImpl,
          uniformSampleImpl, id_map, evalDist_bind]
        have heq :
            (evalDist ($ᵗ ((ofFn fun _ : Unit => Chal).Range u)) :
              SPMF ((ofFn fun _ : Unit => Chal).Range u)) =
            (evalDist (liftM
                (OracleSpec.query (Sum.inr u)) :
              OracleComp (Fork.wrappedSpec Chal) _) :
              SPMF ((Fork.wrappedSpec Chal).Range (Sum.inr u))) := by
          rw [evalDist_uniformSample, evalDist_query]
          rfl
        rw [← heq]
        apply bind_congr
        intro x
        exact ih x

omit [Finite Chal] in
private lemma probOutput_simulateQ_forkWrappedUniformImpl [Fintype Chal]
    {α : Type} (oa : OracleComp (Fork.wrappedSpec Chal) α) (x : α) :
    Pr[= x | simulateQ (forkWrappedUniformImpl (Chal := Chal)) oa] =
      Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ_forkWrappedUniformImpl oa)) x

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

private noncomputable def forkPointBody
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (qH : ℕ) :
    OracleComp (Fork.wrappedSpec Chal) Bool := do
  let (pk, _) ← OracleComp.liftComp hr.gen (Fork.wrappedSpec Chal)
  let trace ← Fork.runTrace σ hr M (nmaAdvFromCma σ hr M adv simT) pk
  pure (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
    (Chal := Chal) qH trace).isSome

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

private noncomputable def forkLoggedForkPointBody
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    (qH : ℕ) :
    OracleComp (Fork.wrappedSpec Chal) Bool := do
  let z ← (simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
    (forkInitialState M Commit Chal)
  pure ((Fork.forkPoint (M := M) (Commit := Commit)
    (Resp := Resp) (Chal := Chal) qH
    (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) σ pk z.1 z.2.1)).isSome)

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimRunState_signedCandidateAdv_eq
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    (cmaSim M Commit Chal hr simT).runState (signedCandidateAdv σ hr M adv) =
      (fun z : (Stmt × (M × (Commit × Resp))) ×
          (List M × Heap (CmaCells M Commit Chal Stmt Wit)) =>
        ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (cmaSimLoggedImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT)
          (candidateAdv σ hr M adv)).run
          (([] : List M), Heap.empty) := by
  unfold Package.runState signedCandidateAdv
  change ((pure (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)) :
      OracleComp unifSpec _) >>= fun h₀ =>
        (simulateQ (cmaSim M Commit Chal hr simT).impl
          ((simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
            (candidateAdv σ hr M adv)).run ([] : List M))).run h₀) = _
  simp only [pure_bind]
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (outer := (cmaSim M Commit Chal hr simT).impl)
    (inner := cmaSignLogImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (oa := candidateAdv σ hr M adv) (s := ([] : List M))
    (q := (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)))]
  rfl

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimLoggedImpl_pkSpec_run_empty
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    (cmaSimLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT (Sum.inr ())).run
        (([] : List M), Heap.empty) =
      (hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
        pure (ps.1,
          (([] : List M),
            (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)).update
              (Sum.inr .keypair) (some (ps.1, ps.2)))) := by
  simp only [add_apply_inr, cmaSimLoggedImpl, QueryImpl.flattenStateT,
    QueryImpl.mapStateTBase, cmaSim, Package.link, nma, add_apply_inl,
    bind_pure_comp, Prod.mk.eta, cmaToNma, simulateQ_pure, StateT.run_pure,
    map_pure, cmaSignLogImpl, bind_pure, StateT.run_monadLift, monadLift_self,
    simulateQ_map, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, StateT.run_mk, id_map, StateT.run_map,
    Heap.split_apply_inr, Functor.map_map, Package.linkReshape,
    Heap.split_empty, Heap.get_empty]
  refine congrArg
    (fun f : Stmt × Wit → Stmt × List M × Heap (CmaCells M Commit Chal Stmt Wit) =>
      f <$> (hr.gen : ProbComp (Stmt × Wit))) ?_
  funext ps
  congr 2
  ext i
  cases i with
  | inl i => rfl
  | inr i =>
      by_cases hi : i = InnerCell.keypair
      · subst i
        simp
      · simp [hi]

omit [SampleableType Stmt] [SampleableType Wit] in
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
    (aux := forkSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
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
            (forkSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp))) (adv.main pk)).run
            (forkInitialBaseState M Commit Chal, ([] : List M))) := by
    rw [support_map]
    exact ⟨z, by simpa [forkLoggedImpl, forkInitialState, forkInitialBaseState] using hz, by
      rcases z with ⟨out, st, log⟩
      rfl⟩
  simpa [forkLoggedImpl, forkInitialState, forkInitialBaseState] using
    (by rw [hproj] at hmem; exact hmem)

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma forkLogged_queryLog_length_le
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) {qS qH : ℕ}
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
        ((simulateQ (Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
          ((simulateQ (simulatedNmaImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
            (∅ : (fsRoSpec M Commit Chal).QueryCache))).run
          ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit)))) := by
    have hmap :
        ((z.1, z.2.1.1), z.2.1.2) ∈ support
          ((fun y : (M × (Commit × Resp)) ×
              ((fsRoSpec M Commit Chal).QueryCache × Fork.simSt M Commit Chal) =>
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
              ((fsRoSpec M Commit Chal).QueryCache × Fork.simSt M Commit Chal) =>
              ((y.1, y.2.1), y.2.2)) <$>
            (simulateQ
              ((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
                (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
                  (Resp := Resp) simT pk)).flattenStateT
              (adv.main pk)).run
              ((∅ : (fsRoSpec M Commit Chal).QueryCache),
                ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit))))) := by
      rw [support_map]
      exact ⟨(z.1, z.2.1), hmap_base, rfl⟩
    rw [← OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
      (outer := Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
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
private lemma forkLogged_forkPoint_prob_true_eq_runTrace
    [Fintype Chal]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) (qH : ℕ) :
    Pr[= true |
        forkLoggedForkPointBody (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT pk qH]
      =
    Pr[= true |
        Fork.runTrace σ hr M (nmaAdvFromCma σ hr M adv simT) pk >>= fun trace =>
          pure ((Fork.forkPoint (M := M) (Commit := Commit)
            (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
  unfold forkLoggedForkPointBody
  have hproj := OracleComp.extendState_run_proj_eq
    (so := forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (aux := forkSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp))
    (oa := adv.main pk)
    (s := forkInitialBaseState M Commit Chal)
    (q := ([] : List M))
  have hbase := forkBase_runTrace_eq (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) σ hr adv simT pk
  calc
    Pr[= true |
        ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
          (forkInitialState M Commit Chal) >>= fun z =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH
              (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp) σ pk z.1 z.2.1)).isSome))]
        =
      Pr[= true |
          (Prod.map id Prod.fst <$>
            (simulateQ (QueryImpl.extendState
              (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp) simT pk)
              (forkSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp))) (adv.main pk)).run
              (forkInitialBaseState M Commit Chal, ([] : List M))) >>= fun z =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH
              (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp) σ pk z.1 z.2)).isSome)] := by
          simp [forkLoggedImpl, forkInitialState, forkInitialBaseState,
            map_eq_bind_pure_comp, bind_assoc]
    _ =
      Pr[= true |
          (simulateQ (forkBaseImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
            (forkInitialBaseState M Commit Chal) >>= fun z =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH
              (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp) σ pk z.1 z.2)).isSome)] := by
          rw [hproj]
    _ =
      Pr[= true |
          ((fun z : (M × (Commit × Resp)) × ForkBaseState M Commit Chal =>
            forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) σ pk z.1 z.2) <$>
            (simulateQ (forkBaseImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
              (forkInitialBaseState M Commit Chal)) >>= fun trace =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
          simp [map_eq_bind_pure_comp, bind_assoc]
    _ =
      Pr[= true |
          Fork.runTrace σ hr M (nmaAdvFromCma σ hr M adv simT) pk >>= fun trace =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
          rw [← hbase]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma forkLogged_verify_prob_true_le_forkPoint_run
    [Fintype Chal]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    {qS qH : ℕ}
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit)
      (Chal := Chal) (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    {δ_verify : ENNReal}
    (hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify) :
    Pr[= true |
        forkLoggedVerifyBody (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT pk]
      ≤
    Pr[= true |
        Fork.runTrace σ hr M (nmaAdvFromCma σ hr M adv simT) pk >>= fun trace =>
          pure ((Fork.forkPoint (M := M) (Commit := Commit)
            (Resp := Resp) (Chal := Chal) qH trace).isSome)] + δ_verify := by
  let loggedRun :=
    ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
      (forkInitialState M Commit Chal))
  let verifyRun :=
    loggedRun >>= fun z =>
      forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk z.1 z.2
  let pointRun :=
    loggedRun >>= fun z =>
      pure ((Fork.forkPoint (M := M) (Commit := Commit)
        (Resp := Resp) (Chal := Chal) qH
        (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk z.1 z.2.1)).isSome)
  have hbind := probEvent_bind_congr_le_add
    (mx := loggedRun)
    (my := fun z => forkVerifyFreshComp (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) σ pk z.1 z.2)
    (oc := fun z => pure ((Fork.forkPoint (M := M) (Commit := Commit)
      (Resp := Resp) (Chal := Chal) qH
      (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk z.1 z.2.1)).isSome))
    (q := fun b => b = true) (ε := δ_verify) (by
      intro z hz
      have hinv := forkLoggedImpl_preserves_inv (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk (adv.main pk) hz
      have hlen := forkLogged_queryLog_length_le (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) σ hr adv simT pk hQ hz
      have hstep := forkVerifyFreshComp_prob_true_le (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) σ (qH := qH) (pk := pk) (x := z.1)
        (s := z.2) hinv hlen hVerifyGuess
      simpa [probEvent_eq_eq_probOutput] using hstep)
  have hbind' :
      Pr[= true | verifyRun] ≤ Pr[= true | pointRun] + δ_verify := by
    simpa [verifyRun, pointRun, probEvent_eq_eq_probOutput] using hbind
  have hpoint :
      Pr[= true | pointRun] =
        Pr[= true |
          Fork.runTrace σ hr M (nmaAdvFromCma σ hr M adv simT) pk >>= fun trace =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
    simpa [pointRun, loggedRun] using
      forkLogged_forkPoint_prob_true_eq_runTrace (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) σ hr adv simT pk qH
  change Pr[= true | verifyRun] ≤
    Pr[= true |
      Fork.runTrace σ hr M (nmaAdvFromCma σ hr M adv simT) pk >>= fun trace =>
        pure ((Fork.forkPoint (M := M) (Commit := Commit)
          (Resp := Resp) (Chal := Chal) qH trace).isSome)] + δ_verify
  calc
    Pr[= true | verifyRun]
        ≤ Pr[= true | pointRun] + δ_verify := hbind'
    _ ≤
      Pr[= true |
          Fork.runTrace σ hr M (nmaAdvFromCma σ hr M adv simT) pk >>= fun trace =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH trace).isSome)] + δ_verify := by
        rw [hpoint]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma forkH5Body_prob_true_le_forkPointBody
    [Fintype Chal]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {qS qH : ℕ}
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit)
      (Chal := Chal) (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    {δ_verify : ENNReal}
    (hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify) :
    Pr[= true |
        forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ hr adv simT]
      ≤
    Pr[= true |
        forkPointBody (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ hr adv simT qH] + δ_verify := by
  have hbind := probEvent_bind_congr_le_add
    (mx := (OracleComp.liftComp hr.gen (Fork.wrappedSpec Chal) :
      OracleComp (Fork.wrappedSpec Chal) (Stmt × Wit)))
    (my := fun ps => forkLoggedVerifyBody (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT ps.1)
    (oc := fun ps =>
      Fork.runTrace σ hr M (nmaAdvFromCma σ hr M adv simT) ps.1 >>= fun trace =>
        pure ((Fork.forkPoint (M := M) (Commit := Commit)
          (Resp := Resp) (Chal := Chal) qH trace).isSome))
    (q := fun b => b = true) (ε := δ_verify) (by
      intro ps _hps
      simpa [probEvent_eq_eq_probOutput] using
        forkLogged_verify_prob_true_le_forkPoint_run (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) σ hr adv simT ps.1 hQ hVerifyGuess)
  simpa [forkH5Body, forkPointBody, forkLoggedVerifyBody,
    probEvent_eq_eq_probOutput] using hbind

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma forkPointBody_prob_true_eq_fork_advantage
    [Fintype Chal]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (qH : ℕ) :
    Pr[= true |
        forkPointBody (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ hr adv simT qH]
      =
    Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH := by
  rw [← probOutput_simulateQ_forkWrappedUniformImpl
    (Chal := Chal)
    (oa := forkPointBody (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) σ hr adv simT qH) true]
  rfl

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma nma_runProb_shiftLeft_signedFreshAdv_eq_forkH5Body
    [Fintype Chal]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
        ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft
          (signedFreshAdv σ hr M adv))
      =
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
      (forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ hr adv simT) := by
  rw [← cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma
    (Stmt := Stmt) (Wit := Wit) M Commit Chal hr simT
    (A := signedFreshAdv σ hr M adv)]
  rw [show (cmaSim M Commit Chal hr simT).runProb (signedFreshAdv σ hr M adv) =
      (cmaSim M Commit Chal hr simT).run (signedFreshAdv σ hr M adv) from rfl]
  rw [signedFreshAdv]
  rw [Package.run_bind]
  rw [cmaSimRunState_signedCandidateAdv_eq (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT]
  simp only [bind_map_left]
  unfold candidateAdv
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, StateT.run_bind, bind_assoc]
  rw [cmaSimLoggedImpl_pkSpec_run_empty (hr := hr) (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) simT]
  simp only [add_apply_inr, Prod.mk.eta, bind_pure_comp, simulateQ_pure,
    StateT.run_pure, StateT.run'_eq, StateT.run_map, Functor.map_map, pure_bind,
    bind_map_left, forkWrappedUniformImpl, QueryImpl.ofLift_eq_id', forkH5Body,
    liftComp_eq_liftM, simulateQ_bind]
  let kg : ProbComp (Stmt × Wit) :=
    simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
      (liftM hr.gen : OracleComp (Fork.wrappedSpec Chal) (Stmt × Wit))
  have hkey :
      kg =
        (hr.gen : OracleComp unifSpec (Stmt × Wit)) := by
    have hlift :
        kg =
          simulateQ (QueryImpl.id' unifSpec)
            (hr.gen : OracleComp unifSpec (Stmt × Wit)) := by
      unfold kg
      exact QueryImpl.simulateQ_liftM_eq_of_query
        (impl := QueryImpl.id' unifSpec + uniformSampleImpl)
        (impl₁ := QueryImpl.id' unifSpec)
        (h := fun t => by
          change simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
              (liftM ((Fork.wrappedSpec Chal).query (Sum.inl t))) =
            (QueryImpl.id' unifSpec) t
          rw [simulateQ_spec_query]
          rfl)
        (oa := hr.gen)
    simpa using hlift
  conv_lhs => rw [← hkey]
  have hkeyR :
      simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
          (liftM hr.gen : OracleComp (Fork.wrappedSpec Chal) (Stmt × Wit)) = kg := by
    rfl
  have hkeyForkLift :
      simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
          (liftM (hr.gen : OracleComp unifSpec (Stmt × Wit)) :
            OracleComp (Fork.wrappedSpec Chal) (Stmt × Wit)) =
        (hr.gen : ProbComp (Stmt × Wit)) := by
    have hlift :
        simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
            (liftM (hr.gen : OracleComp unifSpec (Stmt × Wit)) :
              OracleComp (Fork.wrappedSpec Chal) (Stmt × Wit)) =
          simulateQ (QueryImpl.id' unifSpec)
            (hr.gen : OracleComp unifSpec (Stmt × Wit)) := by
      exact QueryImpl.simulateQ_liftM_eq_of_query
        (impl := QueryImpl.id' unifSpec + uniformSampleImpl)
        (impl₁ := QueryImpl.id' unifSpec)
        (h := fun t => by
          change simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
              (liftM ((Fork.wrappedSpec Chal).query (Sum.inl t))) =
            (QueryImpl.id' unifSpec) t
          rw [simulateQ_spec_query]
          rfl)
        (oa := (hr.gen : OracleComp unifSpec (Stmt × Wit)))
    simpa using hlift
  have hkeyLiftComp :
      simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
          (OracleComp.liftComp
            (hr.gen : OracleComp unifSpec (Stmt × Wit))
            (Fork.wrappedSpec Chal)) =
        (hr.gen : ProbComp (Stmt × Wit)) := by
    have hlift := QueryImpl.simulateQ_liftComp_left_eq_of_apply
      (impl := QueryImpl.id' unifSpec +
        (uniformSampleImpl (spec := (Unit →ₒ Chal))))
      (impl₁ := QueryImpl.id' unifSpec)
      (h := fun t => by rfl)
      (oa := (hr.gen : OracleComp unifSpec (Stmt × Wit)))
    simpa using hlift
  let f : Stmt × Wit → ProbComp Bool := fun ps =>
      (simulateQ (cmaSimLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT)
          (postKeygenCandidateAdv σ hr M adv ps.1)).run
        (([] : List M),
          (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)).update
            (Sum.inr InnerCell.keypair) (some ps)) >>=
        fun x =>
          (fun a_1 => !decide (x.1.1 ∈ x.2.1) && a_1.1) <$>
            (simulateQ (cmaSim M Commit Chal hr simT).impl
              (liftM (((FiatShamir σ hr M).verify ps.1 x.1.1 x.1.2) :
                  OracleComp (unifSpec + (M × Commit →ₒ Chal)) Bool) :
                OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)).run x.2.2
  let g : Stmt × Wit → ProbComp Bool := fun ps =>
      simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
        ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT ps.1)
          (adv.main ps.1)).run (forkInitialState M Commit Chal)) >>= fun x =>
        simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
          (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ ps.1 x.1 x.2)
  change (kg >>= f) = _
  calc
    kg >>= f = kg >>= g := by
      apply bind_congr
      intro ps
      change f ps = g ps
      let st0 : List M × Heap (CmaCells M Commit Chal Stmt Wit) :=
        (([] : List M),
          (Heap.empty : Heap (CmaCells M Commit Chal Stmt Wit)).update
            (Sum.inr InnerCell.keypair) (some ps))
      let common :
          (M × (Commit × Resp)) × SimLoggedState M Commit Chal → ProbComp Bool :=
        fun y => simLoggedVerifyFreshComp (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) σ ps.1 y.1 y.2
      have hfixed :
          cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
            (Stmt := Stmt) (Wit := Wit) ps.1 ps.2 st0 := by
        simp [st0, cmaSimFixedKeyInv, Heap.update]
      have hproj0 :
          cmaSimLoggedProj (M := M) (Commit := Commit) (Chal := Chal)
            (Stmt := Stmt) (Wit := Wit) st0 =
            ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) := by
        ext t <;> cases t <;> simp [st0, cmaSimLoggedProj, Heap.update]
      have hcmaRun :
          Prod.map id (cmaSimLoggedProj (M := M) (Commit := Commit)
            (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
              (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
                hr simT) (adv.main ps.1)).run st0 =
            (simulateQ (simulatedNmaLoggedProbImpl (M := M)
              (Commit := Commit) (Chal := Chal) (Resp := Resp) simT ps.1)
              (adv.main ps.1)).run
              ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) := by
        simpa [hproj0] using
          cmaSimLoggedLeftImpl_project_run (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp)
            (Stmt := Stmt) (Wit := Wit) simT ps.1 ps.2
            (adv.main ps.1) st0 hfixed
      have hforkRun :
          Prod.map id (forkLoggedProj (M := M) (Commit := Commit)
            (Chal := Chal)) <$>
              (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) simT ps.1)
                (adv.main ps.1)).run (forkInitialState M Commit Chal) =
            (simulateQ (simulatedNmaLoggedProbImpl (M := M)
              (Commit := Commit) (Chal := Chal) (Resp := Resp) simT ps.1)
              (adv.main ps.1)).run
              ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) :=
        forkLoggedProbImpl_project_run (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT ps.1 (adv.main ps.1)
      calc
        f ps =
            (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
              hr simT) (adv.main ps.1)).run st0 >>= fun x =>
              simLoggedVerifyFreshComp (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) σ ps.1 x.1
                (cmaSimLoggedProj (M := M) (Commit := Commit)
                  (Chal := Chal) (Stmt := Stmt) (Wit := Wit) x.2) := by
          dsimp [f, st0]
          rw [cmaSimLoggedImpl_liftAdv_run (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp)
            (Stmt := Stmt) (Wit := Wit) simT (adv.main ps.1) st0]
          refine bind_congr (m := ProbComp) fun x => ?_
          exact cmaSimVerifyFreshComp_project (σ := σ) (hr := hr)
            (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
            (Stmt := Stmt) (Wit := Wit) simT ps.1 x.1 x.2
        _ =
            (Prod.map id (cmaSimLoggedProj (M := M) (Commit := Commit)
              (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
                (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
                  (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
                  hr simT) (adv.main ps.1)).run st0) >>= common := by
          simp [common, map_eq_bind_pure_comp, bind_assoc]
        _ =
            (simulateQ (simulatedNmaLoggedProbImpl (M := M)
              (Commit := Commit) (Chal := Chal) (Resp := Resp) simT ps.1)
              (adv.main ps.1)).run
              ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>=
              common := by
          rw [hcmaRun]
        _ =
            (Prod.map id (forkLoggedProj (M := M) (Commit := Commit)
              (Chal := Chal)) <$>
                (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
                  (Chal := Chal) (Resp := Resp) simT ps.1)
                  (adv.main ps.1)).run (forkInitialState M Commit Chal)) >>=
              common := by
          rw [hforkRun]
        _ =
            (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) simT ps.1)
              (adv.main ps.1)).run (forkInitialState M Commit Chal) >>= fun x =>
              simLoggedVerifyFreshComp (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) σ ps.1 x.1
                (forkLoggedProj (M := M) (Commit := Commit)
                  (Chal := Chal) x.2) := by
          simp [common, map_eq_bind_pure_comp, bind_assoc]
        _ =
            simulateQ (forkWrappedUniformImpl (Chal := Chal))
              ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) simT ps.1)
                (adv.main ps.1)).run (forkInitialState M Commit Chal)) >>= fun x =>
              simLoggedVerifyFreshComp (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) σ ps.1 x.1
                (forkLoggedProj (M := M) (Commit := Commit)
                  (Chal := Chal) x.2) := by
          rw [forkLoggedProbImpl_run (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) simT ps.1 (adv.main ps.1)
            (forkInitialState M Commit Chal)]
        _ = g ps := by
          dsimp [g]
          refine bind_congr (m := ProbComp) fun x => ?_
          exact (forkVerifyFreshComp_project (σ := σ) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp)
            ps.1 x.1 x.2).symm
    _ =
        (simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
          (liftM (hr.gen : OracleComp unifSpec (Stmt × Wit)) :
            OracleComp (Fork.wrappedSpec Chal) (Stmt × Wit)) >>= g) :=
      (congrArg (fun mx => mx >>= g) (hkey.trans hkeyForkLift.symm))
    _ = _ := by
      dsimp [g]
      conv_lhs =>
        rw [hkeyForkLift]
      conv_rhs =>
        rw [← OracleComp.liftComp_eq_liftM
          (mx := (hr.gen : OracleComp unifSpec (Stmt × Wit)))
          (superSpec := Fork.wrappedSpec Chal)]
        rw [hkeyLiftComp]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- **H5 hop**: NMA-side fresh-forgery acceptance probability is bounded
by `Fork.advantage + δ_verify`.

Running `nma` against
`cmaToNma.shiftLeft (signedFreshAdv σ hr M adv)` returns a Boolean game
whose `true` event means both verification and freshness against the
adversary-side signing log. Its probability decomposes as:

* `Fork.advantage σ hr M (nmaAdvFromCma … adv simT) qH` — forgeries
  verifying through a challenge value present in the live query log
  (≤ qH entries), rewindable by the replay-forking lemma.
* `δ_verify` — residual event where the forgery's hash point was
  never queried live, so final verification lands on a fresh uniform
  challenge; bounded by `SigmaProtocol.verifyChallengePredictability σ
  δ_verify`.

Proof outline:

1. Split the event `verify = true` by whether the forgery's hash point
   `(msg, c)` was ever queried live during the simulation.
2. For the "queried live" branch, the verifying challenge matches the
   live cache entry at some index `s ≤ qH`; this is exactly the success
   event of `Fork.exp` (from `Sigma/Fork.lean`), so the branch's
   probability equals `Fork.advantage σ hr M (nmaAdvFromCma …) qH`.
3. For the "not queried live" branch, verification samples a fresh
   uniform `Chal`; acceptance probability at any fixed
   `(x, c, resp)` is at most `δ_verify` by
   `verifyChallengePredictability`.
4. The decomposition is tight: the two branches are disjoint, so the
   two bounds add without a union-bound factor. -/
theorem shiftedFreshAdv_nmaRunProb_le_fork
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    (δ_verify : ENNReal)
    (_hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify) :
    Pr[= true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft
            (signedFreshAdv σ hr M adv))]
      ≤ Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH + δ_verify := by
  letI : Fintype Chal := Fintype.ofFinite Chal
  have hbridge :
      Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft
              (signedFreshAdv σ hr M adv))]
        =
      Pr[= true |
          forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ hr adv simT] := by
    rw [nma_runProb_shiftLeft_signedFreshAdv_eq_forkH5Body (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT]
    exact probOutput_simulateQ_forkWrappedUniformImpl
      (Chal := Chal)
      (oa := forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ hr adv simT) true
  have hbody := forkH5Body_prob_true_le_forkPointBody (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) σ hr adv simT
    _hQ _hVerifyGuess
  have hpoint := forkPointBody_prob_true_eq_fork_advantage (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) σ hr adv simT qH
  calc
    Pr[= true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft
            (signedFreshAdv σ hr M adv))]
        = Pr[= true |
            forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) σ hr adv simT] := hbridge
    _ ≤ Pr[= true |
          forkPointBody (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ hr adv simT qH] + δ_verify := hbody
    _ = Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH +
        δ_verify := by
          rw [hpoint]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Public H5 wrapper used by the final chain. The proof obligation is isolated
in `shiftedFreshAdv_nmaRunProb_le_fork`, whose statement is the reusable
managed-RO/fresh-verifier boundary targeted by the replay-forking cutover. -/
theorem nma_runProb_shiftLeft_signedFreshAdv_le_fork
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    (δ_verify : ENNReal)
    (_hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify) :
    Pr[= true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft
            (signedFreshAdv σ hr M adv))]
      ≤ Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH + δ_verify := by
  exact shiftedFreshAdv_nmaRunProb_le_fork σ hr M adv simT qS qH _hQ δ_verify _hVerifyGuess

/-! ### Projecting transported CMA query bounds -/

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- Extract the H3 signing-query bound from the joint `cmaSpec` sign/hash
budget. -/
theorem cmaSignHashQueryBound_to_costly {α : Type}
    {A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α}
    {qS qH : ℕ}
    (hA : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) A qS qH) :
    OracleComp.IsQueryBound A qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b) := by
  refine OracleComp.IsQueryBound.proj
    (B := ℕ × ℕ) (B' := ℕ)
    (proj := fun b : ℕ × ℕ => b.1)
    (oa := A) (b := (qS, qH))
    (canQuery := cmaSignHashCanQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (cost := cmaSignHashCost (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (canQuery' := fun t b => if IsCostlyQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
    (cost' := fun t b => if IsCostlyQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) t then b - 1 else b)
    ?_ ?_ ?_
  · intro t b hcan
    rcases t with ((n | mc) | m) | u
    · trivial
    · trivial
    · simpa [IsCostlyQuery] using hcan
    · trivial
  · intro t b hcan
    rcases t with ((n | mc) | m) | u <;>
      simp [cmaSignHashCanQuery, cmaSignHashCost, IsCostlyQuery] at hcan ⊢
  · simpa [cmaSignHashQueryBound] using hA

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq M]
  [DecidableEq Commit] [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- Extract the H3 hash-query bound from the joint `cmaSpec` sign/hash
budget. -/
theorem cmaSignHashQueryBound_to_hash {α : Type}
    {A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α}
    {qS qH : ℕ}
    (hA : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) A qS qH) :
    OracleComp.IsQueryBound A qH
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b) := by
  refine OracleComp.IsQueryBound.proj
    (B := ℕ × ℕ) (B' := ℕ)
    (proj := fun b : ℕ × ℕ => b.2)
    (oa := A) (b := (qS, qH))
    (canQuery := cmaSignHashCanQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (cost := cmaSignHashCost (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
    (canQuery' := fun t b => if IsHashQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
    (cost' := fun t b => if IsHashQuery (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) t then b - 1 else b)
    ?_ ?_ ?_
  · intro t b hcan
    rcases t with ((n | mc) | m) | u
    · trivial
    · simpa [IsHashQuery] using hcan
    · trivial
    · trivial
  · intro t b hcan
    rcases t with ((n | mc) | m) | u <;>
      simp [cmaSignHashCanQuery, cmaSignHashCost, IsHashQuery] at hcan ⊢
  · simpa [cmaSignHashQueryBound] using hA

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq Commit]
  [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- The final freshness/verification continuation performs one random-oracle
query but no signing query, hence contributes zero cumulative H3 sign cost. -/
private lemma verifyFreshComp_expectedSCost_eq_zero
    (G : QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) × Bool)
        (OracleComp unifSpec)))
    (ε : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) → ℝ≥0∞)
    (p : (Stmt × (M × (Commit × Resp))) × List M)
    (qS : ℕ)
    (s : CmaInnerData M Commit Chal (Stmt := Stmt) (Wit := Wit) × Bool) :
    expectedSCost G
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      ε
      (verifyFreshComp (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) p)
      qS s = 0 := by
  rcases p with ⟨⟨pk, msg, sig⟩, signed⟩
  rcases sig with ⟨c, resp⟩
  rcases s with ⟨s, bad⟩
  cases bad
  · change expectedSCost G
        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        ε
        (liftM ((cmaSpec M Commit Chal Resp Stmt).query
            (Sum.inl (Sum.inl (Sum.inr (msg, c))))) >>= fun a =>
          pure (!decide (msg ∈ signed) && σ.verify pk c a resp))
        qS (s, false) = 0
    rw [expectedSCost_query_bind]
    rw [expectedSCostStep_free]
    · simp
    · simp [IsCostlyQuery]
  · simp [verifyFreshComp, expectedSCost_bad_eq_zero]

/-! ### Top-level chain: H1 + H2 + H3 + H4 + H5 -/

omit [SampleableType Stmt] [SampleableType Wit] in
/-- **Top-level HeapSSP chain** — tight EUF-CMA-to-Fork bound.

HeapSSP-native counterpart of `FiatShamir.euf_cma_to_nma`
(see `Sigma/Security.lean`). The chain is:

  `H1` (drop-fresh)                     +0
    ≤ `H2` (`unforgeableExpNoFresh = cmaReal.runProb signedAdv`)   +0
    ≤ `H3` (identical-until-bad, HVZK + cache-collision)
          +`qS · ζ_zk + qS · (qS + qH) · β`
    = `H4` (`cmaSim = cmaToNma.link nma`)           +0
    ≤ `H5` (fork + fresh-challenge)
          +`Fork.advantage σ hr M (nmaAdvFromCma …) qH + δ_verify`

Summing the per-hop slacks delivers the tight bound:

  `adv.advantage (runtime M)  ≤
    Fork.advantage σ hr M (nmaAdvFromCma …) qH
      + ENNReal.ofReal (qS · ζ_zk)
      + qS · (qS + qH) · β
      + δ_verify`.

The final Fiat-Shamir verification query is factored as a no-sign-cost
suffix (`verifyFreshComp`) after candidate production. It still executes in
the Boolean game consumed by H5, but it does not inflate the H3 cache-growth
budget for signing-query replacements.

Downstream, composing with `FiatShamir.euf_nma_bound` (the forking
lemma with special soundness) yields `FiatShamir.euf_cma_bound`. -/
theorem cma_advantage_le_fork_bound
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simT ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simT β)
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
          (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β +
          δ_verify := by
  refine ⟨nmaAdvFromCma σ hr M adv simT,
    nmaAdvFromCma_nmaHashQueryBound σ hr M adv simT qS qH hQ, ?_⟩
  set A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool :=
    signedFreshAdv σ hr M adv with hA_def
  set Apre : OracleComp (cmaSpec M Commit Chal Resp Stmt)
      ((Stmt × (M × (Commit × Resp))) × List M) :=
    signedCandidateAdv σ hr M adv with hApre_def
  have hA_bound : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) A qS (qH + 1) := by
    rw [hA_def]
    exact signedFreshAdv_cmaSignHashQueryBound (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv qS qH hQ
  have hApre_bound : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) Apre qS qH := by
    rw [hApre_def]
    exact signedCandidateAdv_cmaSignHashQueryBound (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv qS qH hQ
  have hQB : OracleComp.IsQueryBound A qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b) :=
    cmaSignHashQueryBound_to_costly (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (A := A) hA_bound
  have hQBpre : OracleComp.IsQueryBound Apre qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b) :=
    cmaSignHashQueryBound_to_costly (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (A := Apre) hApre_bound
  have hQBHpre : OracleComp.IsQueryBound Apre qH
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b) :=
    cmaSignHashQueryBound_to_hash (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (A := Apre) hApre_bound
  have hCommit : σ.simCommitPredictability simT β := hPredSim
  have hζ_zk_lt : ENNReal.ofReal ζ_zk < ∞ := ENNReal.ofReal_lt_top
  have hHVZK' : σ.HVZK simT (ENNReal.ofReal ζ_zk).toReal := by
    rwa [ENNReal.toReal_ofReal hζ_zk]
  have hH3_abs :
      ENNReal.ofReal
          (((cmaReal M Commit Chal σ hr).runProb A).boolDistAdvantage
            ((cmaSim M Commit Chal hr simT).runProb A))
        ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β := by
    set φ := cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit) with hφ
    set G := Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ with hG
    have h_cost_candidate :
        expectedSCost G
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) Apre qS
            (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
          ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
            + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β := by
      simpa [hG, hφ] using
        cmaSignEpsCore_expectedSCost_le M Commit Chal σ hr (ENNReal.ofReal ζ_zk) β
          Apre qS qH hQBpre hQBHpre
    have h_cost_bind :
        expectedSCost G
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) A qS
            (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
          =
        expectedSCost G
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) Apre qS
            (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false) := by
      rw [hA_def, hApre_def, signedFreshAdv]
      exact expectedSCost_bind_eq_of_right_zero G
        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β)
        (signedCandidateAdv σ hr M adv)
        (verifyFreshComp (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (fun x q p => verifyFreshComp_expectedSCost_eq_zero (σ := σ) (hr := hr)
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
          (G := G) (ε := cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) x q p)
        qS (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
    have h_cost_full :
        expectedSCost
            (Package.implConjugate (cmaReal M Commit Chal σ hr).impl
              (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)))
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) A qS
            (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
          ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
            + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β := by
      have hc :
          expectedSCost G
              (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp) (Stmt := Stmt))
              (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) A qS
              (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
            ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
              + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β := by
        rw [h_cost_bind]
        exact h_cost_candidate
      simpa [hG, hφ] using hc
    simpa [VCVio.HeapSSP.Package.advantage] using
      cmaReal_cmaSim_advantage_le_H3_bound_of_expectedSCost M Commit Chal σ hr simT
        (ENNReal.ofReal ζ_zk) β hζ_zk_lt hHVZK' hCommit A qS
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β)
        hQB h_cost_full
  have hH3_prob : Pr[= true | (cmaReal M Commit Chal σ hr).runProb A] ≤
      Pr[= true | (cmaSim M Commit Chal hr simT).runProb A] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
    le_trans
      (ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
        ((cmaReal M Commit Chal σ hr).runProb A)
        ((cmaSim M Commit Chal hr simT).runProb A))
      (add_le_add le_rfl hH3_abs)
  have hH4 := cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma M Commit Chal hr simT
    (A := A)
  have hH4_pr : Pr[= true | (cmaSim M Commit Chal hr simT).runProb A] =
      Pr[= true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A)] :=
    probOutput_congr rfl (congrArg evalDist hH4)
  have hH5' :
      Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A)] ≤
        Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH + δ_verify := by
    rw [hA_def]
    exact nma_runProb_shiftLeft_signedFreshAdv_le_fork σ hr M adv simT qS qH hQ
      δ_verify hVerifyGuess
  have hH1H2 : adv.advantage (FiatShamir.runtime M) ≤
      Pr[= true | (cmaReal M Commit Chal σ hr).runProb A] := by
    rw [hA_def]
    exact cma_advantage_le_runProb_cmaRealFresh (M := M) σ hr adv
  calc adv.advantage (FiatShamir.runtime M)
      ≤ Pr[= true | (cmaReal M Commit Chal σ hr).runProb A] := hH1H2
    _ ≤ Pr[= true | (cmaSim M Commit Chal hr simT).runProb A] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) := hH3_prob
    _ = Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A)] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) := by
        rw [hH4_pr]
    _ ≤ (Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH + δ_verify) +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
        add_le_add hH5' le_rfl
    _ = Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β +
          δ_verify := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (qS : ℝ)),
            show ENNReal.ofReal (qS : ℝ) = (qS : ENNReal) from
              ENNReal.ofReal_natCast _]
        ring

end FiatShamir.HeapSSP
