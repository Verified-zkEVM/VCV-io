/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Hops
import VCVio.CryptoFoundations.FiatShamir.Sigma.CmaToNma
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Native stateful Fiat-Shamir CMA-to-NMA chain

This file assembles the non-heap Fiat-Shamir EUF-CMA chain. The top-level
statement is factored so the H1/H2/H3 arithmetic is native immediately, while
the H5 replay-forking boundary can be ported as a focused lemma.
-/

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

/-! ## CMA-to-NMA adversary -/

/-- The CMA-to-NMA reduction at the managed random-oracle interface. -/
noncomputable def nmaAdvFromCma
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    SignatureAlg.managedRoNmaAdv
      (SourceSigAlg (σ := σ) (hr := hr) (M := M)) :=
  FiatShamir.simulatedNmaAdv σ hr M simT adv

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Hash-query bound for `nmaAdvFromCma`. -/
theorem nmaAdvFromCma_nmaHashQueryBound
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
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

/-- Wrapper around `nmaAdvFromCma` that issues one explicit live random-oracle
query for the forgery's hash point `(msg, commit)` after the source adversary
returns. The extra query makes the verification challenge part of the forkable
transcript: `Fork.runTrace` always sees `(msg, commit)` in the live `queryLog`,
so the replay-forking lemma can rewind at the verification position without any
auxiliary "fresh challenge accepts" assumption on the verifier.

The wrapped adversary issues `qH + 1` random-oracle queries (the source's `qH`
plus the appended verifier-point query). The H5 chain calls `Fork.advantage`
on this wrapper at slot parameter `qH`: `Fork.forkPoint qH` indexes
`Fin (qH + 1)`, which is exactly the right number of slots for `qH + 1`
queries (the framework's structural `+1` is precisely the wrapper's verifier
slot). The replay-forking denominator is therefore `qH + 1`, not `qH + 2`. -/
noncomputable def nmaAdvFromCmaWithFinalQuery
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    SignatureAlg.managedRoNmaAdv
      (SourceSigAlg (σ := σ) (hr := hr) (M := M)) where
  main pk := do
    let result ← (nmaAdvFromCma σ hr M adv simT).main pk
    let _ ← (((unifSpec + (M × Commit →ₒ Chal)).query
      (.inr (result.1.1, result.1.2.1))) :
      OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal)
    pure result

/-! ## Shifted CMA-to-NMA normal forms -/

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq Commit]
  [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- The stateful shifted form of `signedFreshAdv` splits at the
candidate/verifier boundary, preserving the `cmaToNma` signing log between the
two pieces. -/
theorem cmaToNma_shiftLeft_signedFreshAdv_eq_bind
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    (cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
        (signedFreshAdv σ hr M adv) =
      (simulateQ (cmaToNma M Commit Chal simT)
        (signedCandidateAdv σ hr M adv)).run ([] : List M) >>= fun (p, log') =>
          Prod.fst <$> (simulateQ (cmaToNma M Commit Chal simT)
            (verifyFreshComp (σ := σ) (hr := hr) (M := M)
              (Commit := Commit) (Chal := Chal) (Resp := Resp) p)).run log' := by
  unfold QueryImpl.Stateful.shiftLeft QueryImpl.Stateful.run signedFreshAdv
  rw [StateT.run'_eq, simulateQ_bind, StateT.run_bind]
  simp [map_eq_bind_pure_comp, bind_assoc]

/-! ## H5 fork-side infrastructure -/

private abbrev ForkBaseState (M Commit Chal : Type)
    [DecidableEq M] [DecidableEq Commit] :=
  (fsRoSpec M Commit Chal).QueryCache × Fork.simSt M Commit Chal

@[fs_simp] private noncomputable def forkBaseImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (ForkBaseState M Commit Chal) (OracleComp (Fork.wrappedSpec Chal))) :=
  ((Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
    (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)).flattenStateT

@[fs_simp] private def cmaOracleSignLogAux
    {S : Type}
    (t : (cmaOracleSpec M Commit Chal Resp).Domain)
    (_s : S)
    (_u : (cmaOracleSpec M Commit Chal Resp).Range t)
    (_s' : S) (signed : List M) :
    List M :=
  match t with
  | .inl _ => signed
  | .inr m => signed ++ [m]

@[fs_simp] private noncomputable def forkLoggedImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (ForkBaseState M Commit Chal × List M)
        (OracleComp (Fork.wrappedSpec Chal))) :=
  QueryImpl.extendState
    (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp))


private abbrev SimLoggedState (M Commit Chal : Type)
    [DecidableEq M] [DecidableEq Commit] :=
  (fsRoSpec M Commit Chal).QueryCache × List M

@[fs_simp] private noncomputable def simLoggedVerifyFreshComp
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (x : M × (Commit × Resp))
    (s : SimLoggedState M Commit Chal) : ProbComp Bool := do
  let msg := x.1
  let c := x.2.1
  let resp := x.2.2
  match s.1 (.inr (msg, c)) with
  | some ch => pure (!decide (msg ∈ s.2) && σ.verify pk c ch resp)
  | none => do
      let ch ← ($ᵗ Chal : ProbComp Chal)
      pure (!decide (msg ∈ s.2) && σ.verify pk c ch resp)

@[fs_simp] private noncomputable def fsUniformImpl :
    QueryImpl (fsRoSpec M Commit Chal) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (M × Commit →ₒ Chal)))

@[fs_simp] private noncomputable def simulatedNmaLoggedProbImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (SimLoggedState M Commit Chal) ProbComp) :=
  QueryImpl.extendState
    ((fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal)).mapStateTBase
      (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) simT pk))
    (cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp))

@[fs_simp] private noncomputable def cmaSimLoggedImpl
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (List M × CmaState M Commit Chal Stmt Wit) ProbComp) :=
  ((cmaSim M Commit Chal hr simT).mapStateTBase
    (cmaSignLogImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt))).flattenStateT

@[fs_simp] private noncomputable def cmaSimLoggedLeftImpl
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (List M × CmaState M Commit Chal Stmt Wit) ProbComp)
  | .inl (.inl n) =>
      cmaSimLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT (.unif n)
  | .inl (.inr mc) =>
      cmaSimLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT (.ro mc)
  | .inr m =>
      cmaSimLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT (.sign m)

@[fs_simp] private def cmaSimLoggedProj
    (s : List M × CmaState M Commit Chal Stmt Wit) :
    SimLoggedState M Commit Chal :=
  (fun t =>
    match t with
    | .inl _ => none
    | .inr mc => s.2.1.2.1 mc,
    s.1)

private def cmaSimFixedKeyInv
    (pk : Stmt) (sk : Wit)
    (s : List M × CmaState M Commit Chal Stmt Wit) : Prop :=
  s.2.1.2.2 = some (pk, sk)

private def cmaSimFixedKeyInitialState
    (ps : Stmt × Wit) : List M × CmaState M Commit Chal Stmt Wit :=
  (([] : List M), ((([] : List M), (∅ : RoCache M Commit Chal), some ps), false))

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimLoggedImpl_liftAdv_run
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {α : Type} (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    (st : List M × CmaState M Commit Chal Stmt Wit) :
    (simulateQ (cmaSimLoggedImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
      hr simT)
      (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run st =
    (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
      hr simT) oa).run st := by
  simpa [cmaSimLoggedLeftImpl] using congrArg (fun x => x.run st)
    (QueryImpl.simulateQ_liftM_eq_of_query
      (impl := cmaSimLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT)
      (impl₁ := cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT)
      (h := fun t => by
        rcases t with ((n | mc) | m)
        · change simulateQ
            (cmaSimLoggedImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
              hr simT)
            (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.unif n))) = _
          rw [simulateQ_spec_query]
          rfl
        · change simulateQ
            (cmaSimLoggedImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
              hr simT)
            (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.ro mc))) = _
          rw [simulateQ_spec_query]
          rfl
        · change simulateQ
            (cmaSimLoggedImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
              hr simT)
            (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.sign m))) = _
          rw [simulateQ_spec_query]
          rfl)
      (oa := oa))

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimLoggedImpl_liftAdv_run_expanded
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {α : Type} (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    (st : CmaState M Commit Chal Stmt Wit) :
    (simulateQ (cmaSim M Commit Chal hr simT)
      ((simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
        (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run
        ([] : List M))).run st =
    (fun z : α × (List M × CmaState M Commit Chal Stmt Wit) =>
      ((z.1, z.2.1), z.2.2)) <$>
    (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
      hr simT) oa).run (([] : List M), st) := by
  calc
    (simulateQ (cmaSim M Commit Chal hr simT)
        ((simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
          (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run
          ([] : List M))).run st
        =
      (fun z : α × (List M × CmaState M Commit Chal Stmt Wit) =>
        ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (cmaSimLoggedImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
          hr simT)
          (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run
          (([] : List M), st) := by
        simpa [cmaSimLoggedImpl] using
          OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
            (outer := cmaSim M Commit Chal hr simT)
            (inner := cmaSignLogImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
            (oa := (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α))
            (s := ([] : List M)) (q := st)
    _ =
      (fun z : α × (List M × CmaState M Commit Chal Stmt Wit) =>
        ((z.1, z.2.1), z.2.2)) <$>
      (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT) oa).run (([] : List M), st) := by
        rw [cmaSimLoggedImpl_liftAdv_run (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
          hr simT oa (([] : List M), st)]

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma nma_lift_unif_run
    (hr : GenerableRelation Stmt Wit rel)
    {α : Type} (oa : ProbComp α)
    (s : NmaState M Commit Chal Stmt Wit) :
    (simulateQ (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)
        (liftM oa : OracleComp (nmaSpec M Commit Chal Stmt) α)).run s =
      (fun a => (a, s)) <$> oa := by
  let impl₁ : QueryImpl unifSpec
      (StateT (NmaState M Commit Chal Stmt Wit) ProbComp) :=
    fun n => StateT.mk fun s => (fun a => (a, s)) <$> (unifSpec.query n)
  have himpl₁ : (simulateQ impl₁ oa).run s = (fun a => (a, s)) <$> oa := by
    induction oa using OracleComp.inductionOn generalizing s with
    | pure x =>
        simp [impl₁]
    | query_bind n k ih =>
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        simp only [map_eq_bind_pure_comp, StateT.run_mk, bind_assoc,
          Function.comp_apply, pure_bind, impl₁]
        refine bind_congr (m := ProbComp) fun u => ?_
        exact ih u s
  have hsim := QueryImpl.simulateQ_liftM_eq_of_query
    (impl := nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)
    (impl₁ := impl₁)
    (h := fun n => by
      funext s'
      change ((nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr
        (.unif n)).run s') = (impl₁ n).run s'
      simp [impl₁, nma, nmaPublic])
    (oa := oa)
  rw [hsim]
  exact himpl₁

omit [Finite Chal] [Inhabited Chal] in
private lemma simulatedNmaUnifSim_fsUniform_run_for_cma
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

omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] [Finite Chal] in
private def cmaSimLoggedLeftOrnament
    [Finite Chal]
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (sk : Wit) :
    QueryImpl.StateOrnament
      (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT)
      (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) where
  inv := cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
    (Stmt := Stmt) (Wit := Wit) pk sk
  proj := cmaSimLoggedProj (M := M) (Commit := Commit)
    (Chal := Chal) (Stmt := Stmt) (Wit := Wit)
  preserves_inv := fun t s hs => by
    letI : Fintype Chal := Fintype.ofFinite Chal
    rcases s with ⟨signed, ⟨⟨log, cache, keypair⟩, bad⟩⟩
    simp only [cmaSimFixedKeyInv] at hs ⊢
    rcases t with ((n | mc) | m)
    · intro z hz
      have hz' := by
        simpa [fs_simp, cmaOracleSpec, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
          QueryImpl.Stateful.linkWith] using hz
      rcases hz' with ⟨u, _hu, rfl⟩
      exact hs
    · intro z hz
      cases hcache : cache mc with
      | some ch =>
          have hz' := by
            simpa [fs_simp, cmaOracleSpec, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, hcache] using hz
          rcases hz' with ⟨rfl, rfl⟩
          exact hs
      | none =>
          have hz' := by
            simpa [fs_simp, cmaOracleSpec, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, hcache, uniformSampleImpl] using hz
          rcases hz' with ⟨ch, _hch, rfl⟩
          simpa [QueryCache.cacheQuery] using hs
    · subst keypair
      intro z hz
      have hz' := by
        simpa [fs_simp, cmaOracleSpec, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
          QueryImpl.Stateful.linkWith, StateT.run_bind, StateT.run_mk,
          StateT.run_map, StateT.run_monadLift, monadLift_self, simulateQ_bind,
          simulateQ_map, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, bind_assoc, bind_pure_comp, pure_bind,
          map_bind, Functor.map_map, Prod.map_apply, id_eq] using hz
      rcases Set.mem_iUnion₂.mp hz' with ⟨x, hxmem, hzimg⟩
      simp only [Set.mem_image] at hzimg
      rcases hzimg with ⟨a, ha, rfl⟩
      have hxinner : x.2 = (cache, some (pk, sk), bad) := by
        have hxmem_nma :
            x ∈ support ((simulateQ
              (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)
              (liftM (simT pk) :
                OracleComp (nmaSpec M Commit Chal Stmt) (Commit × Chal × Resp))).run
                (cache, some (pk, sk), bad)) := by
          simpa [nma] using hxmem
        have hxmem' := hxmem_nma
        rw [nma_lift_unif_run (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit) hr (simT pk)
          (cache, some (pk, sk), bad)] at hxmem'
        rw [support_map] at hxmem'
        rcases hxmem' with ⟨x', _hx', rfl⟩
        rfl
      cases htarget : x.2.1 (m, x.1.1) with
      | some old =>
          have ha' : a = ((), x.2.1, x.2.2.1, true) := by
            simpa [htarget] using ha
          subst a
          simp [hxinner]
      | none =>
          have ha' :
              a = ((), QueryCache.cacheQuery x.2.1 (m, x.1.1) x.1.2.1, x.2.2) := by
            simpa [htarget] using ha
          subst a
          simp [hxinner]
  project_step := fun t s hs => by
    letI : Fintype Chal := Fintype.ofFinite Chal
    rcases s with ⟨signed, ⟨⟨log, cache, keypair⟩, bad⟩⟩
    simp only [cmaSimFixedKeyInv] at hs
    rcases t with ((n | mc) | m)
    · simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
        QueryImpl.Stateful.linkWith, QueryImpl.liftTarget_apply]
    · cases hcache : cache mc with
      | some ch =>
          simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
            QueryImpl.Stateful.linkWith, QueryImpl.liftTarget_apply, hcache]
      | none =>
          conv_lhs =>
            simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, QueryImpl.liftTarget_apply,
              uniformSampleImpl, QueryCache.cacheQuery, hcache]
          conv_rhs =>
            simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, QueryImpl.liftTarget_apply,
              uniformSampleImpl, QueryCache.cacheQuery, hcache]
          congr 1
          funext ch
          congr 1
          ext t <;> cases t <;> simp
    · subst keypair
      conv_lhs =>
        simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
          QueryImpl.Stateful.linkWith,
          StateT.run_bind, StateT.run_mk, StateT.run_map, StateT.run_monadLift,
          monadLift_self, simulateQ_bind, simulateQ_map, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, id_map,
          bind_pure_comp, pure_bind, map_bind, Functor.map_map, Prod.map_apply,
          id_eq]
      conv_rhs =>
        simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
          QueryImpl.Stateful.linkWith,
          StateT.run_bind, StateT.run_mk, StateT.run_map, StateT.run_monadLift,
          monadLift_self, simulateQ_bind, simulateQ_map, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, id_map,
          bind_pure_comp, pure_bind, map_bind, Functor.map_map, Prod.map_apply,
          id_eq]
      have hleft := nma_lift_unif_run (M := M) (Commit := Commit)
        (Chal := Chal) (Stmt := Stmt) (Wit := Wit) hr (simT pk)
        (cache, some (pk, sk), bad)
      let advCache : (fsRoSpec M Commit Chal).QueryCache := fun t =>
        match t with
        | Sum.inl _ => none
        | Sum.inr mc => cache mc
      have hright :
          simulateQ (fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal))
              ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
                (Chal := Chal)) (simT pk)).run advCache) =
            (fun a => (a, advCache)) <$> simT pk := by
        exact simulatedNmaUnifSim_fsUniform_run_for_cma (M := M)
          (Commit := Commit) (Chal := Chal) (oa := simT pk) (cache := advCache)
      rw [hleft]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      conv_rhs =>
        lhs
        change simulateQ (fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal))
          ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
            (Chal := Chal)) (simT pk)).run advCache)
        rw [hright]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      refine bind_congr (m := ProbComp) fun x => ?_
      cases htarget : cache (m, x.1) with
      | some old =>
          simp [advCache, htarget]
      | none =>
          simp only [htarget, QueryCache.cacheQuery, pure_bind, Function.comp_apply,
            add_apply_inl, add_apply_inr, advCache]
          simp only [pure_inj, Prod.mk.injEq, and_true, true_and]
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

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Stmt] [SampleableType Wit]
  [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma cmaToNma_lift_ro_query_run
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (mc : M × Commit) (log : OuterState M) :
    (simulateQ (cmaToNma M Commit Chal simT)
      (liftM (liftM (((M × Commit →ₒ Chal).query mc) :
          OracleQuery (M × Commit →ₒ Chal) Chal) :
        OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run log =
      (fun ch => (ch, log)) <$>
        (((nmaSpec M Commit Chal Stmt).query (.ro mc)) :
          OracleComp (nmaSpec M Commit Chal Stmt) Chal) := by
  change (simulateQ (cmaToNma M Commit Chal simT)
      (((cmaSpec M Commit Chal Resp Stmt).query (.ro mc)) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run log =
      (fun ch => (ch, log)) <$>
        (((nmaSpec M Commit Chal Stmt).query (.ro mc)) :
          OracleComp (nmaSpec M Commit Chal Stmt) Chal)
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, cmaToNma,
    StateT.run_mk, StateT.run_bind, map_eq_bind_pure_comp,
    Function.comp_apply]
  simp [map_eq_bind_pure_comp]

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSim_lift_ro_query_run
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (mc : M × Commit) (s : CmaState M Commit Chal Stmt Wit) :
    (simulateQ (cmaSim M Commit Chal hr simT)
      (liftM (liftM (((M × Commit →ₒ Chal).query mc) :
          OracleQuery (M × Commit →ₒ Chal) Chal) :
        OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run s =
      match s.1.2.1 mc with
      | some ch => pure (ch, s)
      | none => (fun ch =>
          (ch, ((s.1.1, s.1.2.1.cacheQuery mc ch, s.1.2.2), s.2))) <$> ($ᵗ Chal) := by
  rcases s with ⟨⟨log, cache, keypair⟩, bad⟩
  unfold cmaSim
  rw [QueryImpl.Stateful.simulateQ_linkWith_run]
  change (cmaFrame M Commit Chal Stmt Wit).linkReshape
        ((log, cache, keypair), bad) <$>
      (simulateQ (nma M Commit Chal hr)
          ((simulateQ (cmaToNma M Commit Chal simT)
            (liftM (liftM (((M × Commit →ₒ Chal).query mc) :
              OracleQuery (M × Commit →ₒ Chal) Chal) :
              OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run log)).run
        (cache, keypair, bad) =
      match cache mc with
      | some ch => pure (ch, (log, cache, keypair), bad)
      | none => (fun ch =>
          (ch, (log, cache.cacheQuery mc ch, keypair), bad)) <$> ($ᵗ Chal)
  rw [cmaToNma_lift_ro_query_run (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt) simT mc log]
  cases hcache : cache mc with
  | none =>
      simp [simulateQ_map, StateT.run_map, nma, nmaPublic, cmaFrame,
        cmaOuterLens, cmaNmaLens, QueryImpl.Stateful.Frame.linkReshape,
        hcache, QueryCache.cacheQuery, Functor.map_map]
  | some ch =>
      simp [simulateQ_map, StateT.run_map, nma, nmaPublic, cmaFrame,
        cmaOuterLens, cmaNmaLens, QueryImpl.Stateful.Frame.linkReshape,
        hcache]

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimVerifyFreshComp_project
    [Finite Chal]
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (x : M × (Commit × Resp))
    (st : List M × CmaState M Commit Chal Stmt Wit) :
    (fun a => !decide (x.1 ∈ st.1) && a.1) <$>
        (simulateQ (cmaSim M Commit Chal hr simT)
          (liftM (((FiatShamir σ hr M).verify pk x.1 x.2) :
              OracleComp (unifSpec + (M × Commit →ₒ Chal)) Bool) :
            OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)).run st.2 =
      simLoggedVerifyFreshComp (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) σ pk x
        (cmaSimLoggedProj (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit) st) := by
  letI : Fintype Chal := Fintype.ofFinite Chal
  rcases x with ⟨msg, c, resp⟩
  rcases st with ⟨signed, ⟨⟨log, cache, keypair⟩, bad⟩⟩
  cases hcache : cache (msg, c) with
  | none =>
      simp [simLoggedVerifyFreshComp, cmaSimLoggedProj, _root_.FiatShamir,
        hcache, cmaSim_lift_ro_query_run (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
          hr simT (msg, c) ((log, cache, keypair), bad)]
      rfl
  | some ch =>
      simp [simLoggedVerifyFreshComp, cmaSimLoggedProj, _root_.FiatShamir,
        hcache, cmaSim_lift_ro_query_run (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
          hr simT (msg, c) ((log, cache, keypair), bad)]
      rfl

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

@[fs_simp] private def forkLoggedProj (s : ForkBaseState M Commit Chal × List M) :
    SimLoggedState M Commit Chal :=
  (s.1.1, s.2)

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
      simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, Fork.unifFwd] using hz
    rcases hz' with ⟨u, _hu, rfl⟩
    exact ⟨hfreshInv, hlogInv⟩
  · by_cases hadv : advCache (.inr mc) = none
    · have hz' := by
        simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, Fork.roImpl, hadv] using hz
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
          simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, hadv'] using hz
        rcases hz' with ⟨hcache, rfl⟩
        constructor
        · intro mc' ch' hcache' hfresh
          exact hfreshInv mc' ch' hcache' hfresh
        · intro mc' ch' hcache'
          exact hlogInv mc' ch' hcache'
  · have hz' := by
      simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase] using hz
    rcases hz' with ⟨x, _hx, hsigCache, rfl⟩
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

omit [SampleableType Stmt] in
private lemma forkLoggedImpl_preserves_live_adv_inv_step
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    ∀ (t : (cmaOracleSpec M Commit Chal Resp).Domain)
      (s : ForkBaseState M Commit Chal × List M),
      forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal) s →
      ∀ z ∈ support ((forkLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk t).run s),
        forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal) z.2 := by
  intro t s hs z hz
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  rcases t with ((n | mc) | m)
  · have hz' := by
      simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, Fork.unifFwd] using hz
    rcases hz' with ⟨u, _hu, rfl⟩
    exact hs
  · cases hadv : advCache (.inr mc) with
    | some ch =>
        have hz' := by
          simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, hadv] using hz
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
              simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
                QueryImpl.mapStateTBase, Fork.roImpl, hadv, hlive] using hz
            rcases hz' with ⟨ch, _hch, rfl⟩
            intro mc' ch' hcache'
            by_cases hmc : mc' = mc
            · subst mc'
              simpa [QueryCache.cacheQuery_self] using hcache'
            · have hcache_old : liveCache mc' = some ch' := by
                simpa [QueryCache.cacheQuery_of_ne, hmc] using hcache'
              have hadv_old := hs mc' ch' hcache_old
              simpa [QueryCache.cacheQuery_of_ne, hmc] using hadv_old
  · have hz' := by
      simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase] using hz
    rcases hz' with ⟨x, _hx, hsigCache, rfl⟩
    have hxstate := simulatedNmaUnifFork_nested_preserves_state
      (M := M) (Commit := Commit) (Chal := Chal) (simT pk) advCache
      (liveCache, queryLog) _hx
    rcases hxstate with ⟨hxadv, hxlive⟩
    intro mc ch hcache'
    have hcache_old : liveCache mc = some ch := by
      simpa [hxlive] using hcache'
    have hadv_old := hs mc ch hcache_old
    have hadv_old' : advCache (.inr mc) = some ch := by
      simpa using hadv_old
    by_cases hmc : mc = (m, x.1.1.1)
    · subst mc
      cases htarget : advCache (.inr (m, x.1.1.1)) with
      | none =>
          rw [hadv_old'] at htarget
          cases htarget
      | some old =>
          simpa [hxadv, htarget] using hadv_old'
    · have hsum :
          (Sum.inr mc : (fsRoSpec M Commit Chal).Domain) ≠
            Sum.inr (m, x.1.1.1) := by
        intro hsum
        exact hmc (by simpa using Sum.inr.inj hsum)
      cases htarget : advCache (.inr (m, x.1.1.1)) with
      | none =>
          simpa [hxadv, htarget, QueryCache.cacheQuery_of_ne _ _ hsum] using hadv_old'
      | some old =>
          simpa [hxadv, htarget] using hadv_old'

omit [SampleableType Stmt] in
private lemma forkLoggedImpl_preserves_live_adv_inv
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    {α : Type} (A : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    {z : α × (ForkBaseState M Commit Chal × List M)}
    (hz : z ∈ support ((simulateQ (forkLoggedImpl (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk) A).run
      (forkInitialState M Commit Chal))) :
    forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal) z.2 := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (inv := forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal))
    (hinv := forkLoggedImpl_preserves_live_adv_inv_step (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
    A (forkInitialState M Commit Chal)
    (by
      intro mc ch hcache
      simp [forkInitialState] at hcache)
    z hz

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma forkPoint_isSome_of_mem_verified_findIdx_le
    {qH : ℕ}
    (trace : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal))
    (hverified : trace.verified = true)
    (hmem : trace.target ∈ trace.queryLog)
    (hidx : trace.queryLog.findIdx (· == trace.target) ≤ qH) :
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH trace).isSome = true := by
  unfold Fork.forkPoint
  simp [hverified, hmem, hidx]

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- Convenience corollary: if the queryLog itself fits within `qH`, then the
target's `findIdx` is automatically `≤ qH` and `forkPoint qH trace` is some. -/
private lemma forkPoint_isSome_of_mem_verified_length
    {qH : ℕ}
    (trace : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal))
    (hverified : trace.verified = true)
    (hmem : trace.target ∈ trace.queryLog)
    (hlen : trace.queryLog.length ≤ qH) :
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH trace).isSome = true := by
  have hlt : trace.queryLog.findIdx (· == trace.target) < trace.queryLog.length :=
    List.findIdx_lt_length_of_exists ⟨trace.target, hmem, by simp⟩
  exact forkPoint_isSome_of_mem_verified_findIdx_le (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) trace hverified hmem (by omega)

@[fs_simp] private noncomputable def forkWrappedUniformImpl [Fintype Chal] :
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
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  cases hcache : advCache (.inr (msg, c)) with
  | some ch =>
      simp [forkVerifyFreshComp, simLoggedVerifyFreshComp, forkLoggedProj, hcache]
      rfl
  | none =>
      simp [forkVerifyFreshComp, simLoggedVerifyFreshComp, forkLoggedProj,
        forkWrappedUniformImpl, hcache]
      rfl

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
  · cases hcache : advCache (.inr (msg, c)) with
    | none =>
        simp [forkVerifyFreshComp, hcache, hsigned]
    | some ch =>
        simp [forkVerifyFreshComp, hcache, hsigned]
  · cases hcache : advCache (.inr (msg, c)) with
    | some ch =>
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
        · have hverify_false : σ.verify pk c ch resp = false := by
            cases hv : σ.verify pk c ch resp <;> simp_all
          simp [forkVerifyFreshComp, hcache, hsigned, hverify_false]
    | none =>
        cases hlive : liveCache (msg, c) with
        | some liveCh =>
            have hcontra : advCache (.inr (msg, c)) = some liveCh :=
              hliveAdv (msg, c) liveCh hlive
            rw [hcache] at hcontra
            cases hcontra
        | none =>
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
                  rfl
              _ ≤
                Pr[= true |
                    forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal)
                      (Resp := Resp) σ pk (msg, (c, resp))
                      (((advCache, (liveCache, queryLog)), signed)) >>= fun trace =>
                        pure ((Fork.forkPoint (M := M) (Commit := Commit)
                          (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
                  simp only [forkFinalQueryTrace, Fork.roImpl, StateT.run_bind,
                    StateT.run_get, hlive, StateT.run_monadLift, StateT.run_set,
                    StateT.run_pure, monadLift_self, bind_assoc, pure_bind]
                  change
                    Pr[fun ch : Chal => σ.verify pk c ch resp = true |
                      (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                        OracleComp (Fork.wrappedSpec Chal) Chal)] ≤
                    Pr[= true |
                    ((fun ch : Chal =>
                        (Fork.forkPoint (M := M) (Commit := Commit)
                          (Resp := Resp) (Chal := Chal) qH
                          { forgery := (msg, (c, resp))
                            advCache := advCache
                            roCache := liveCache.cacheQuery (msg, c) ch
                            queryLog := queryLog ++ [(msg, c)]
                            verified := σ.verify pk c ch resp }).isSome) <$>
                      (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                        OracleComp (Fork.wrappedSpec Chal) Chal))]
                  conv_rhs =>
                    rw [← probEvent_eq_eq_probOutput]
                    rw [probEvent_map]
                  change
                    Pr[fun ch : Chal => σ.verify pk c ch resp = true |
                      (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                        OracleComp (Fork.wrappedSpec Chal) Chal)] ≤
                    Pr[fun ch : Chal =>
                        (Fork.forkPoint (M := M) (Commit := Commit)
                          (Resp := Resp) (Chal := Chal) qH
                          { forgery := (msg, (c, resp))
                            advCache := advCache
                            roCache := liveCache.cacheQuery (msg, c) ch
                            queryLog := queryLog ++ [(msg, c)]
                            verified := σ.verify pk c ch resp }).isSome = true |
                      (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                        OracleComp (Fork.wrappedSpec Chal) Chal)]
                  refine _root_.probEvent_mono
                    (mx := (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
                      OracleComp (Fork.wrappedSpec Chal) Chal)) ?_
                  intro ch _hch hverify
                  have hmem : (msg, c) ∈ queryLog ++ [(msg, c)] := by simp
                  have hlt :
                      (queryLog ++ [(msg, c)]).findIdx (· == (msg, c)) <
                        (queryLog ++ [(msg, c)]).length :=
                    List.findIdx_lt_length_of_exists ⟨(msg, c), hmem, by simp⟩
                  have hidx : (queryLog ++ [(msg, c)]).findIdx (· == (msg, c)) ≤ qH := by
                    have hlen_eq : (queryLog ++ [(msg, c)]).length = queryLog.length + 1 := by
                      simp
                    omega
                  have hfork := forkPoint_isSome_of_mem_verified_findIdx_le
                    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
                    (qH := qH)
                    ({ forgery := (msg, (c, resp))
                       advCache := advCache
                       roCache := liveCache.cacheQuery (msg, c) ch
                       queryLog := queryLog ++ [(msg, c)]
                       verified := σ.verify pk c ch resp } :
                      Fork.Trace (M := M) (Commit := Commit) (Resp := Resp)
                        (Chal := Chal))
                    (by simp [hverify]) (by simp [Fork.Trace.target, hmem])
                    (by simp [Fork.Trace.target, hidx])
                  simp [hfork]

omit [SampleableType Stmt] [SampleableType Wit] in
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
    (outer := Fork.unifFwd M Commit Chal + Fork.roImpl M Commit Chal)
    (inner := simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (oa := adv.main pk)
    (s := (∅ : (fsRoSpec M Commit Chal).QueryCache))
    (q := ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit))))]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro z
  rcases z with ⟨⟨msg, c, resp⟩, advCache, liveCache, queryLog⟩
  cases hcache : liveCache (msg, c) with
  | some ch =>
      simp [Fork.roImpl, hcache]
  | none =>
      simp [Fork.roImpl, hcache]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Lift `forkBase_finalQuery_runTrace_eq` through the signing-log auxiliary:
running the source adversary under `forkLoggedImpl` and then issuing the
verifier-point query via `forkFinalQueryTrace` produces the same distribution
as `Fork.runTrace` of the verifier-point-wrapped adversary. -/
private lemma forkLogged_finalQuery_eq_runTrace
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk) (adv.main pk)).run
      (forkInitialState M Commit Chal) >>= fun z =>
        forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk z.1 z.2) =
      Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk := by
  rw [forkBase_finalQuery_runTrace_eq (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) σ hr adv simT pk]
  have hproj := OracleComp.extendState_run_proj_eq
    (so := forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (aux := cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp))
    (oa := adv.main pk)
    (s := forkInitialBaseState M Commit Chal)
    (q := ([] : List M))
  simp only [forkLoggedImpl, forkInitialState, forkInitialBaseState,
    map_eq_bind_pure_comp, bind_assoc] at hproj ⊢
  rw [hproj]
  simp [bind_assoc]

@[fs_simp] private noncomputable def forkLoggedProbImpl [Fintype Chal]
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
omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma forkInitialState_liveCacheAdvCacheInv :
    forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal)
      (forkInitialState M Commit Chal) := by
  intro mc ch hcache
  simp [forkInitialState] at hcache

omit [SampleableType Stmt] in
private def forkLoggedProbOrnament
    [Fintype Chal]
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl.StateOrnament
      (forkLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk)
      (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) where
  inv := forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal)
  proj := forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal)
  preserves_inv := fun t s hs => by
    rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
    rcases t with ((n | mc) | m)
    · intro z hz
      have hz' := by
        simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, Fork.unifFwd] using hz
      rcases hz' with ⟨u, _hu, rfl⟩
      exact hs
    · intro z hz
      cases hadv : advCache (.inr mc) with
      | some ch =>
          have hz' := by
            simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, hadv] using hz
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
                simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
                  QueryImpl.mapStateTBase, Fork.roImpl, hadv, hlive,
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
        simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase] using hz
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
  project_step := fun t s hs => by
    rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
    rcases t with ((n | mc) | m)
    · simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, Fork.unifFwd]
    · cases hadv : advCache (.inr mc) with
      | some ch =>
          simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, hadv]
      | none =>
          cases hlive : liveCache mc with
          | some liveCh =>
              have hcontra : advCache (.inr mc) = some liveCh := hs mc liveCh hlive
              rw [hadv] at hcontra
              cases hcontra
          | none =>
              simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
                QueryImpl.mapStateTBase, Fork.roImpl, hadv, hlive,
                uniformSampleImpl]
    · simp only [add_apply_inr, fs_simp, QueryImpl.mapStateTBase,
        QueryImpl.ofLift_eq_id', QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_modifyGet,
        Prod.mk.eta, bind_pure_comp, simulateQ_map, StateT.run_mk, StateT.run_map,
        Functor.map_map, Prod.map_apply, id_eq]
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

omit [Finite Chal] in
private lemma evalDist_simulateQ_forkWrappedUniformImpl [Fintype Chal]
    {α : Type} (oa : OracleComp (Fork.wrappedSpec Chal) α) :
    𝒟[simulateQ (forkWrappedUniformImpl (Chal := Chal)) oa] =
      𝒟[oa] := by
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
            (𝒟[$ᵗ ((ofFn fun _ : Unit => Chal).Range u)] :
              SPMF ((ofFn fun _ : Unit => Chal).Range u)) =
            (𝒟[(liftM
                (OracleSpec.query (Sum.inr u)) :
              OracleComp (Fork.wrappedSpec Chal) _)] :
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
/-- The H5 verify body's success probability is bounded by the live `forkPoint`
event for the verify-wrapped adversary. The fork slot parameter is `qH`:
`Fork.forkPoint qH` indexes `Fin (qH + 1)`, accommodating the wrapped
adversary's source-`qH` plus verifier-point query. -/
private lemma forkLogged_verify_prob_true_le_forkPoint_run
    [Fintype Chal]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    {qS qH : ℕ}
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
  have hpoint :
      Pr[= true | finalRun] =
        Pr[= true |
          Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk
            >>= fun trace =>
              pure ((Fork.forkPoint (M := M) (Commit := Commit)
                (Resp := Resp) (Chal := Chal) qH trace).isSome)] := by
    simp only [finalRun, ← bind_assoc,
      forkLogged_finalQuery_eq_runTrace (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT pk]
  calc
    Pr[= true |
        forkLoggedVerifyBody (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv simT pk]
        ≤ Pr[= true | finalRun] := hbind'
    _ =
      Pr[= true |
        Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk
          >>= fun trace =>
            pure ((Fork.forkPoint (M := M) (Commit := Commit)
              (Resp := Resp) (Chal := Chal) qH trace).isSome)] := hpoint

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The H5 body's success probability is bounded by the wrapped adversary's
fork advantage at slot parameter `qH`. The framework's `Fin (qH + 1)` indexing
provides exactly enough slots for the wrapped adversary's source-`qH` plus
verifier-point query. -/
private lemma forkH5Body_prob_true_le_fork_advantage
    [Fintype Chal]
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {qS qH : ℕ}
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
    rfl
  have hbody :
      Pr[= true |
          forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ hr adv simT] ≤
        Pr[= true | pointBody] := by
    simpa [forkH5Body, forkLoggedVerifyBody, pointBody, probEvent_eq_eq_probOutput] using hbind
  calc
    Pr[= true |
        forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ hr adv simT]
        ≤ Pr[= true | pointBody] := hbody
    _ = Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH := hpoint

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSim_run_eq_nma_run_shiftLeft_cmaToNma_private
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {α : Type}
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) :
    (cmaSim M Commit Chal hr simT).run (cmaInit M Commit Chal Stmt Wit) A =
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).run
        (nmaInit M Commit Chal Stmt Wit)
        ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M) A) := by
  unfold QueryImpl.Stateful.run QueryImpl.Stateful.shiftLeft cmaSim
  rw [StateT.run'_eq, StateT.run'_eq]
  rw [QueryImpl.Stateful.simulateQ_linkWith_run]
  rw [QueryImpl.Stateful.run, StateT.run'_eq, simulateQ_map, StateT.run_map]
  simp [cmaInit, nmaInit, cmaFrame, cmaOuterLens, cmaNmaLens,
    Functor.map_map]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma nma_runProb_shiftLeft_signedFreshAdv_eq_forkH5Body
    [Fintype Chal]
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
        (nmaInit M Commit Chal Stmt Wit)
        ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
          (signedFreshAdv σ hr M adv))
      =
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
      (forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ hr adv simT) := by
  unfold QueryImpl.Stateful.runProb
  rw [← cmaSim_run_eq_nma_run_shiftLeft_cmaToNma_private (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) simT (signedFreshAdv σ hr M adv)]
  unfold QueryImpl.Stateful.run signedFreshAdv signedCandidateAdv candidateAdv
  rw [StateT.run'_eq]
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    OracleQuery.input_query, id_map, StateT.run_bind, bind_assoc]
  conv_lhs =>
    simp [cmaSim, cmaToNma, nma, nmaPublic, postKeygenCandidateAdv,
      SourceSigAlg, _root_.FiatShamir, forkH5Body, forkWrappedUniformImpl,
      forkLoggedImpl, forkInitialState, forkVerifyFreshComp, forkBaseImpl,
      simulatedNmaImpl, simulatedNmaBaseSim, cmaInit, cmaDataInit, cmaFrame,
      cmaOuterLens, cmaNmaLens, QueryImpl.Stateful.Frame.linkReshape,
      Functor.map_map]
  conv_rhs =>
    simp [cmaSim, cmaToNma, nma, nmaPublic, postKeygenCandidateAdv,
      SourceSigAlg, _root_.FiatShamir, forkH5Body, forkWrappedUniformImpl,
      forkLoggedImpl, forkInitialState, forkVerifyFreshComp, forkBaseImpl,
      simulatedNmaImpl, simulatedNmaBaseSim, cmaInit, cmaDataInit, cmaFrame,
      cmaOuterLens, cmaNmaLens, QueryImpl.Stateful.Frame.linkReshape,
      Functor.map_map]
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
  rw (occs := .pos [1]) [← hkeyLiftComp]
  change (simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
      (OracleComp.liftComp
        (hr.gen : OracleComp unifSpec (Stmt × Wit))
        (Fork.wrappedSpec Chal)) >>= fun ps => _) =
    (simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
      (OracleComp.liftComp
        (hr.gen : OracleComp unifSpec (Stmt × Wit))
        (Fork.wrappedSpec Chal)) >>= fun ps => _)
  apply bind_congr
  intro ps
  change _ =
    ((simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
          (forkInitialState M Commit Chal))) >>= fun x =>
      simulateQ (forkWrappedUniformImpl (Chal := Chal))
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ ps.1 x.1 x.2))
  rw [forkLoggedProbImpl_run (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) simT ps.1 (adv.main ps.1) (forkInitialState M Commit Chal)]
  have hfork :
      ((simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
          (forkInitialState M Commit Chal) >>= fun x =>
        simulateQ (forkWrappedUniformImpl (Chal := Chal))
          (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ ps.1 x.1 x.2)) =
      ((simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
          ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>= fun x =>
        simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ ps.1 x.1 x.2) := by
    calc
      ((simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
          (forkInitialState M Commit Chal) >>= fun x =>
        simulateQ (forkWrappedUniformImpl (Chal := Chal))
          (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ ps.1 x.1 x.2))
          =
        (Prod.map id (forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal)) <$>
          (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
            (forkInitialState M Commit Chal)) >>= fun x =>
          simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ ps.1 x.1 x.2 := by
            simp only [bind_map_left, Prod.map_fst, id_eq, Prod.map_snd]
            refine bind_congr fun x => ?_
            exact forkVerifyFreshComp_project (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) σ ps.1 x.1 x.2
      _ =
        ((simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
          ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>= fun x =>
        simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ ps.1 x.1 x.2) := by
          rw [show
            Prod.map id (forkLoggedProj (M := M) (Commit := Commit)
              (Chal := Chal)) <$>
                (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
                  (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
                  (forkInitialState M Commit Chal) =
              (simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
                ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) by
            have hrun := (forkLoggedProbOrnament (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) simT ps.1).run_eq (adv.main ps.1)
              (forkInitialState M Commit Chal)
              (forkInitialState_liveCacheAdvCacheInv (M := M) (Commit := Commit)
                (Chal := Chal))
            simpa [forkLoggedProj, forkInitialState, forkLoggedProbOrnament] using hrun]
  rw [hfork]
  let st0 : List M × CmaState M Commit Chal Stmt Wit :=
    cmaSimFixedKeyInitialState (M := M) (Commit := Commit)
      (Chal := Chal) (Stmt := Stmt) (Wit := Wit) ps
  let common :
      (M × (Commit × Resp)) × SimLoggedState M Commit Chal → ProbComp Bool :=
    fun y => simLoggedVerifyFreshComp (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) σ ps.1 y.1 y.2
  have hfixed :
      cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) ps.1 ps.2 st0 := by
    simp [st0, cmaSimFixedKeyInitialState, cmaSimFixedKeyInv]
  have hproj0 :
      cmaSimLoggedProj (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) st0 =
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) := by
    ext t <;> cases t <;> simp [st0, cmaSimLoggedProj, cmaSimFixedKeyInitialState]
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
    letI : Fintype Chal := Fintype.ofFinite Chal
    simpa [hproj0, cmaSimLoggedLeftOrnament] using
      (cmaSimLoggedLeftOrnament (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT ps.1 ps.2).run_eq (adv.main ps.1) st0 hfixed
  have hrunExpanded :
      (simulateQ (QueryImpl.Stateful.linkWith
          (cmaFrame M Commit Chal Stmt Wit)
          (cmaToNma M Commit Chal simT)
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr))
        ((simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
          (liftM (adv.main ps.1) :
            OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)))).run
          ([] : List M))).run
          ((([] : List M), (∅ : RoCache M Commit Chal), some ps), false) =
        (fun z : (M × (Commit × Resp)) ×
            (List M × CmaState M Commit Chal Stmt Wit) => ((z.1, z.2.1), z.2.2)) <$>
          (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
            hr simT) (adv.main ps.1)).run st0 := by
    simpa [cmaSim, st0, cmaSimFixedKeyInitialState] using
      cmaSimLoggedImpl_liftAdv_run_expanded (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT (adv.main ps.1) st0.2
  unfold cmaFrame cmaOuterLens cmaNmaLens at hrunExpanded
  rw [hrunExpanded]
  calc
    _ =
      (Prod.map id (cmaSimLoggedProj (M := M) (Commit := Commit)
        (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
          (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
            hr simT) (adv.main ps.1)).run st0) >>= common := by
        simp only [bind_map_left]
        refine bind_congr fun x => ?_
        simpa [cmaSim, _root_.FiatShamir, map_eq_bind_pure_comp] using
          cmaSimVerifyFreshComp_project (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp)
          (Stmt := Stmt) (Wit := Wit) simT ps.1 x.1 x.2
    _ =
      ((simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>=
        common) := by
        rw [hcmaRun]
    _ =
      ((simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT ps.1) (adv.main ps.1)).run
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>= fun x =>
        simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ ps.1 x.1 x.2) := by
        rfl

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] in
/-- H5 boundary in shifted-NMA form. This is the fork-side statement after the
native H4 normalization has moved `cmaSim` to `nma ∘ cmaToNma`. The bound is in
terms of the verify-wrapped adversary `nmaAdvFromCmaWithFinalQuery` at fork
slot parameter `qH` (the framework's `Fin (qH + 1)` indexing accommodates the
wrapper's verifier-point query). -/
theorem nma_runProb_shiftLeft_signedFreshAdv_le_fork
    [Finite Chal]
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit)
      (Chal := Chal) (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    Pr[= true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          (nmaInit M Commit Chal Stmt Wit)
          ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
            (signedFreshAdv σ hr M adv))]
      ≤ Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT)
          qH := by
  letI : Fintype Chal := Fintype.ofFinite Chal
  have hbridge :
      Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            (nmaInit M Commit Chal Stmt Wit)
            ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
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
  have hbody := forkH5Body_prob_true_le_fork_advantage (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    adv simT hQ
  calc
    Pr[= true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          (nmaInit M Commit Chal Stmt Wit)
          ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
            (signedFreshAdv σ hr M adv))]
        = Pr[= true |
            forkH5Body (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) σ hr adv simT] := hbridge
    _ ≤ Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT)
          qH := hbody

/-! ## H3 cost factoring -/

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq Commit]
  [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- The final freshness/verification continuation performs no signing queries,
hence contributes zero cumulative H3 signing cost. -/
private lemma verifyFreshComp_expectedQuerySlack_eq_zero
    (G : QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (CmaData M Commit Chal Stmt Wit × Bool) (OracleComp unifSpec)))
    (ε : CmaData M Commit Chal Stmt Wit → ℝ≥0∞)
    (p : (Stmt × (M × (Commit × Resp))) × List M)
    (qS : ℕ)
    (s : CmaData M Commit Chal Stmt Wit × Bool) :
    expectedQuerySlack G
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
  · change expectedQuerySlack G
        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        ε
        (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.ro (msg, c))) >>= fun a =>
          pure (!decide (msg ∈ signed) && σ.verify pk c a resp))
        qS (s, false) = 0
    rw [expectedQuerySlack_query_bind]
    rw [expectedQuerySlackStep_free]
    · simp
    · simp [IsCostlyQuery]
  · simp [verifyFreshComp, expectedQuerySlack_bad_eq_zero]

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
/-- Tight native H3 bound for the freshness-preserving adversary, using the
candidate/verifier split so the final verifier hash query is not charged to H3
signing replacement. -/
private theorem signedFreshAdv_H3_bound
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ENNReal.ofReal (cmaH3Advantage M Commit Chal σ hr simT
      (signedFreshAdv σ hr M adv)) ≤
      (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β := by
  let A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool :=
    signedFreshAdv σ hr M adv
  let Apre : OracleComp (cmaSpec M Commit Chal Resp Stmt)
      ((Stmt × (M × (Commit × Resp))) × List M) :=
    signedCandidateAdv σ hr M adv
  have h_cost_candidate :
      cmaH3ExpectedLoss M Commit Chal σ hr ζ_zk β Apre qS ≤
        (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β :=
    cmaH3ExpectedLoss_le_queryBounds M Commit Chal σ hr ζ_zk β Apre
      (signedCandidateAdv_isQueryBoundP_costly (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        adv qS qH hQ)
      (signedCandidateAdv_isQueryBoundP_hash (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        adv qS qH hQ)
  have h_cost_bind :
      cmaH3ExpectedLoss M Commit Chal σ hr ζ_zk β A qS =
        cmaH3ExpectedLoss M Commit Chal σ hr ζ_zk β Apre qS := by
    simp only [A, Apre, signedFreshAdv, cmaH3ExpectedLoss]
    exact expectedQuerySlack_bind_eq_of_right_zero
      (cmaReal M Commit Chal σ hr)
      (cmaH3Costly (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      (cmaSignEpsCore M Commit Chal ζ_zk β)
      (signedCandidateAdv σ hr M adv)
      (verifyFreshComp (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (fun x q p => verifyFreshComp_expectedQuerySlack_eq_zero (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        (G := cmaReal M Commit Chal σ hr)
        (ε := cmaSignEpsCore M Commit Chal ζ_zk β) x q p)
      qS (cmaInit M Commit Chal Stmt Wit)
  exact cmaReal_cmaSim_advantage_le_H3_bound_of_expectedQuerySlack
    M Commit Chal σ hr simT ζ_zk β A qS
    ((qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β)
    (cmaH3StepFacts_of_hvzk_predictability M Commit Chal σ hr simT
      ζ_zk β hζ_zk hHVZK hCommit)
    (cmaH3RunFacts_of_queryBound_expectedLoss M Commit Chal σ hr ζ_zk β A qS
      ((qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β)
      (by
        simpa [A] using signedFreshAdv_isQueryBoundP_costly (σ := σ) (hr := hr)
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
          adv qS qH hQ)
      (by
        rw [h_cost_bind]
        exact h_cost_candidate))

/-! ## Top-level chain factored over H5 -/

/-! ## H4: linked simulation as shifted NMA execution -/

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
  rw [StateT.run'_eq, StateT.run'_eq]
  rw [QueryImpl.Stateful.simulateQ_linkWith_run]
  rw [QueryImpl.Stateful.run, StateT.run'_eq, simulateQ_map, StateT.run_map]
  simp [cmaInit, nmaInit, cmaFrame, cmaOuterLens, cmaNmaLens,
    Functor.map_map]

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
/-- Native H4 hop in probability form. -/
theorem cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool) :
    (cmaSim M Commit Chal hr simT).runProb
        (cmaInit M Commit Chal Stmt Wit) A =
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
        (nmaInit M Commit Chal Stmt Wit)
        ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M) A) := by
  exact cmaSim_run_eq_nma_run_shiftLeft_cmaToNma (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) simT A

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Convert the shifted-NMA H5 boundary into the linked simulated-CMA form used
by the top-level chain. -/
theorem cmaSim_signedFreshAdv_le_fork_of_shifted_h5
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qH : ℕ)
    (hH5 :
      Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            (nmaInit M Commit Chal Stmt Wit)
            ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
              (signedFreshAdv σ hr M adv))] ≤
        Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT)
          qH) :
    Pr[= true |
        (cmaSim M Commit Chal hr simT).runProb
          (cmaInit M Commit Chal Stmt Wit)
          (signedFreshAdv σ hr M adv)] ≤
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT)
        qH := by
  rw [cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) simT (signedFreshAdv σ hr M adv)]
  exact hH5

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] in
/-- Native H5 boundary in the linked simulated-CMA form used by the top-level
chain. -/
theorem cmaSim_signedFreshAdv_le_fork
    [Finite Chal]
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit)
      (Chal := Chal) (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    Pr[= true |
        (cmaSim M Commit Chal hr simT).runProb
          (cmaInit M Commit Chal Stmt Wit)
          (signedFreshAdv σ hr M adv)] ≤
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT)
        qH := by
  letI : Fintype Chal := Fintype.ofFinite Chal
  exact cmaSim_signedFreshAdv_le_fork_of_shifted_h5 (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) adv simT qH
    (nma_runProb_shiftLeft_signedFreshAdv_le_fork (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (Stmt := Stmt) (Wit := Wit) adv simT qS qH hQ)

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Native stateful top-level chain, assuming the H5 replay-forking boundary.

This theorem carries the H1/H2/H3/H4 arithmetic directly in the stateful chain.
The bound is in terms of the verify-wrapped adversary
`nmaAdvFromCmaWithFinalQuery` at fork slot parameter `qH`. -/
theorem cma_advantage_le_fork_bound_of_h5
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simT ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simT β)
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    (hH1H2 :
      adv.advantage (FiatShamir.runtime M) ≤
        Pr[= true | (cmaReal M Commit Chal σ hr).runProb
          (cmaInit M Commit Chal Stmt Wit) (signedFreshAdv σ hr M adv)])
    (hH5 :
      Pr[= true |
          (cmaSim M Commit Chal hr simT).runProb
            (cmaInit M Commit Chal Stmt Wit)
            (signedFreshAdv σ hr M adv)] ≤
        Fork.advantage σ hr M
          (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH) :
    adv.advantage (FiatShamir.runtime M) ≤
      Fork.advantage σ hr M
          (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
        ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
        (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β := by
  let A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool :=
    signedFreshAdv σ hr M adv
  have hζ_zk_lt : ENNReal.ofReal ζ_zk < ∞ := ENNReal.ofReal_lt_top
  have hHVZK' : σ.HVZK simT (ENNReal.ofReal ζ_zk).toReal := by
    rwa [ENNReal.toReal_ofReal hζ_zk]
  have hH3_abs :
      ENNReal.ofReal
          (((cmaReal M Commit Chal σ hr).runProb
              (cmaInit M Commit Chal Stmt Wit) A).boolDistAdvantage
            ((cmaSim M Commit Chal hr simT).runProb
              (cmaInit M Commit Chal Stmt Wit) A))
        ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β := by
    simpa [A, cmaH3Advantage, QueryImpl.Stateful.advantage] using
      signedFreshAdv_H3_bound (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp)
        adv simT (ENNReal.ofReal ζ_zk) β hζ_zk_lt hHVZK' hPredSim qS qH hQ
  have hH3_prob :
      Pr[= true | (cmaReal M Commit Chal σ hr).runProb
        (cmaInit M Commit Chal Stmt Wit) A] ≤
      Pr[= true | (cmaSim M Commit Chal hr simT).runProb
        (cmaInit M Commit Chal Stmt Wit) A] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
    le_trans
      (ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
        ((cmaReal M Commit Chal σ hr).runProb
          (cmaInit M Commit Chal Stmt Wit) A)
        ((cmaSim M Commit Chal hr simT).runProb
          (cmaInit M Commit Chal Stmt Wit) A))
      (add_le_add le_rfl hH3_abs)
  calc
    adv.advantage (FiatShamir.runtime M)
        ≤ Pr[= true | (cmaReal M Commit Chal σ hr).runProb
          (cmaInit M Commit Chal Stmt Wit) A] := by
            simpa [A] using hH1H2
    _ ≤ Pr[= true | (cmaSim M Commit Chal hr simT).runProb
          (cmaInit M Commit Chal Stmt Wit) A] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) := hH3_prob
    _ ≤ Fork.advantage σ hr M
          (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
        add_le_add hH5 le_rfl
    _ = Fork.advantage σ hr M
            (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg qS)]
        rw [ENNReal.ofReal_natCast]
        ring_nf

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Native stateful chain with H5 discharged by the replay-forking boundary,
leaving only the public-to-stateful H1/H2 compatibility premise. -/
theorem cma_advantage_le_fork_bound_of_h1h2
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simT ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simT β)
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH)
    (hH1H2 :
      adv.advantage (FiatShamir.runtime M) ≤
        Pr[= true | (cmaReal M Commit Chal σ hr).runProb
          (cmaInit M Commit Chal Stmt Wit) (signedFreshAdv σ hr M adv)]) :
    adv.advantage (FiatShamir.runtime M) ≤
      Fork.advantage σ hr M
          (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
        ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
        (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β := by
  letI : Fintype Chal := Fintype.ofFinite Chal
  exact cma_advantage_le_fork_bound_of_h5 (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) simT ζ_zk hζ_zk hHVZK β hPredSim
    adv qS qH hQ hH1H2
    (cmaSim_signedFreshAdv_le_fork (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (Stmt := Stmt) (Wit := Wit) adv simT qS qH hQ)

end FiatShamir.Stateful
