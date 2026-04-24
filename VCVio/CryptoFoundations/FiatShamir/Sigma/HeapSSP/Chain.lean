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
  `Fork.advantage σ hr M nmaAdv qH + δ_verify`; kept as `sorry` pending
  the forking-lemma reduction proof.
* `cma_advantage_le_fork_bound` — **top-level chain**. Tight
  Pointcheval-Stern-with-HVZK bound assembled from H1+H2+H3+H4+H5.
-/

universe u

open ENNReal OracleSpec OracleComp ProbComp VCVio.HeapSSP
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
  ((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal).stateTMapBase
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

private lemma forkInitialState_inv :
    forkAwareInv (M := M) (Commit := Commit) (Chal := Chal)
      (forkInitialState M Commit Chal) := by
  constructor
  · intro mc ch hcache _hfresh
    simp [forkInitialState] at hcache
  · intro mc ch hcache
    simp [forkInitialState] at hcache

private lemma simulatedNmaUnifFork_flatten_preserves_state
    {α : Type} (A : ProbComp α)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.simSt M Commit Chal)
    {z : α × ((fsRoSpec M Commit Chal).QueryCache × Fork.simSt M Commit Chal)}
    (hz : z ∈ support
      ((simulateQ
        ((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal).stateTMapBase
          (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))).flattenStateT
        A).run (advCache, liveSt))) :
    z.2 = (advCache, liveSt) := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := ((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal).stateTMapBase
      (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))).flattenStateT)
    (inv := fun st => st = (advCache, liveSt))
    (hinv := by
      intro t st hst y hy
      subst hst
      simp [QueryImpl.flattenStateT, QueryImpl.stateTMapBase,
        simulatedNmaUnifSim, simulatedNmaFwd, Fork.unifFwd] at hy
      rcases hy with ⟨u, _hu, rfl⟩
      rfl)
    A (advCache, liveSt) rfl z hz

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
  rw [OracleComp.simulateQ_stateTMapBase_run_eq_map_flattenStateT
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
  · simp [forkLoggedImpl, forkBaseImpl, forkSignLogAux, QueryImpl.extendState,
      QueryImpl.flattenStateT, QueryImpl.stateTMapBase, simulatedNmaImpl,
      simulatedNmaBaseSim, simulatedNmaUnifSim, simulatedNmaFwd,
      Fork.unifFwd] at hz ⊢
    rcases hz with ⟨u, _hu, rfl⟩
    exact ⟨hfreshInv, hlogInv⟩
  · by_cases hadv : advCache (.inr mc) = none
    · simp [forkLoggedImpl, forkBaseImpl, forkSignLogAux, QueryImpl.extendState,
        QueryImpl.flattenStateT, QueryImpl.stateTMapBase, simulatedNmaImpl,
        simulatedNmaBaseSim, simulatedNmaRoSim, simulatedNmaFwd,
        Fork.roImpl, hadv] at hz ⊢
      by_cases hlive : liveCache mc = none
      · simp [hlive] at hz
        rcases hz with ⟨ch, hch, rfl⟩
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
        · simp [hlive'] at hz
          rcases hz with ⟨rfl, rfl⟩
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
      · simp [forkLoggedImpl, forkBaseImpl, forkSignLogAux, QueryImpl.extendState,
          QueryImpl.flattenStateT, QueryImpl.stateTMapBase, simulatedNmaImpl,
          simulatedNmaBaseSim, simulatedNmaRoSim, simulatedNmaFwd,
          Fork.roImpl, hadv'] at hz ⊢
        rcases hz with ⟨hcache, rfl⟩
        constructor
        · intro mc' ch' hcache' hfresh
          exact hfreshInv mc' ch' hcache' hfresh
        · intro mc' ch' hcache'
          exact hlogInv mc' ch' hcache'
  · simp [forkLoggedImpl, forkBaseImpl, forkSignLogAux, QueryImpl.extendState,
      QueryImpl.flattenStateT, QueryImpl.stateTMapBase, simulatedNmaImpl,
      simulatedNmaSigSim, simulatedNmaUnifSim, simulatedNmaFwd, Fork.unifFwd] at hz ⊢
    rcases hz with ⟨x, _hx, hcache, rfl⟩
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
              simp [forkVerifyFreshComp, hcache, hsigned]
              rw [← probEvent_eq_eq_probOutput, probEvent_map]
              rfl
        _ ≤ δ_verify := hmiss_le
        _ ≤ (if (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
              (Chal := Chal) qH
              (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp) σ pk (msg, c, resp) s.1)).isSome then 1 else 0) +
            δ_verify := by
              simpa [add_comm] using
                (le_self_add δ_verify
                  (if (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
                    (Chal := Chal) qH
                    (forkTraceOfBase (M := M) (Commit := Commit) (Chal := Chal)
                      (Resp := Resp) σ pk (msg, c, resp) s.1)).isSome then 1 else 0))
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
  rw [OracleComp.simulateQ_stateTMapBase_run_eq_map_flattenStateT
    (outer := Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
    (inner := simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (oa := adv.main pk)
    (s := (∅ : (fsRoSpec M Commit Chal).QueryCache))
    (q := ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit))))]
  simp [map_eq_bind_pure_comp]
  refine bind_congr fun z => ?_
  rfl

private noncomputable def forkWrappedUniformImpl [Fintype Chal] :
    QueryImpl (Fork.wrappedSpec Chal) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (Unit →ₒ Chal)))

private lemma evalDist_simulateQ_forkWrappedUniformImpl [Fintype Chal]
    {α : Type} (oa : OracleComp (Fork.wrappedSpec Chal) α) :
    evalDist (simulateQ (forkWrappedUniformImpl (Chal := Chal)) oa) =
      evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [forkWrappedUniformImpl]
  | query_bind t mx ih =>
      rcases t with n | u
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
          id_map, evalDist_bind, ih]
        apply bind_congr
        simp
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, QueryImpl.add_apply_inr, forkWrappedUniformImpl,
          uniformSampleImpl, id_map, evalDist_bind, ih]
        have heq :
            (evalDist ($ᵗ ((ofFn fun _ : Unit => Chal).Range u)) :
              SPMF ((ofFn fun _ : Unit => Chal).Range u)) =
            (evalDist (liftM (query (Sum.inr u)) :
              OracleComp (Fork.wrappedSpec Chal) _) :
              SPMF ((Fork.wrappedSpec Chal).Range (Sum.inr u))) := by
          rw [evalDist_uniformSample, evalDist_query]
          rfl
        rw [← heq]
        apply bind_congr
        intro x
        exact ih x

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
    simp [forkBaseImpl, forkInitialBaseState] at hmap
    have hmap' :
        ((z.1, z.2.1.1), z.2.1.2) ∈ support
          ((fun y : (M × (Commit × Resp)) ×
              ((fsRoSpec M Commit Chal).QueryCache × Fork.simSt M Commit Chal) =>
              ((y.1, y.2.1), y.2.2)) <$>
            (simulateQ
              ((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal).stateTMapBase
                (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
                  (Resp := Resp) simT pk)).flattenStateT
              (adv.main pk)).run
              ((∅ : (fsRoSpec M Commit Chal).QueryCache),
                ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit))))) := by
      rw [support_map]
      exact ⟨(z.1, z.2.1), hmap, rfl⟩
    rw [← OracleComp.simulateQ_stateTMapBase_run_eq_map_flattenStateT
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
  rw [cmaToNma_shiftLeft_signedFreshAdv_eq_bind (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT]
  -- Remaining semantic bridge: factor the NMA package's lazy keypair heap
  -- execution into the fixed-key fork-logged body under `forkWrappedUniformImpl`.
  sorry

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
