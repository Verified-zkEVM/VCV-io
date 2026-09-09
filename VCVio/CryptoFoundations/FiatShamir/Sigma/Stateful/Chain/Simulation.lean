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

/-!
# Stateful Fiat-Shamir simulation and cache invariants
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

noncomputable local instance instIsUniformSpecChalSingleton [Fintype Chal] :
    IsUniformSpec ((Unit →ₒ Chal) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

private lemma simulateQ_id_add_uniform_query_inl
    {ι : Type*} (spec : OracleSpec ι) [∀ i, SampleableType (spec.Range i)]
    (n : unifSpec.Domain) :
    simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl (spec := spec))
        (liftM ((unifSpec + spec).query (Sum.inl n))) =
      liftM (unifSpec.query n) := by
  rw [simulateQ_spec_query]
  change (QueryImpl.id' unifSpec n) = _
  exact QueryImpl.id'_apply n

private lemma simulateQ_id_add_uniform_query_inr
    {ι : Type*} (spec : OracleSpec ι) [∀ i, SampleableType (spec.Range i)]
    (t : spec.Domain) :
    simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl (spec := spec))
        (liftM ((unifSpec + spec).query (Sum.inr t))) =
      $ᵗ spec.Range t := by
  rw [simulateQ_spec_query]
  change uniformSampleImpl (spec := spec) t = _
  exact uniformSampleImpl_apply t

/-! ## CMA-to-NMA adversary -/

/-- The CMA-to-NMA reduction at the managed random-oracle interface. -/
@[expose]
def nmaAdvFromCma
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    SignatureAlg.managedRoNmaAdv
      (SourceSigAlg (σ := σ) (hr := hr) (M := M)) :=
  FiatShamir.simulatedNmaAdv σ hr M simT adv

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Hash-query bound for `nmaAdvFromCma`. -/
theorem nmaAdvFromCma_nmaHashQueryBound
    [Finite Commit] [Finite Resp]
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (nmaAdvFromCma σ hr M adv simT).main pk) qH := fun pk => by
  simpa [nmaHashQueryBound, nmaAdvFromCma] using
    FiatShamir.simulatedNmaAdv_hashQueryBound σ hr M simT adv qS qH hQ pk

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
@[expose]
def nmaAdvFromCmaWithFinalQuery
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
  simp [QueryImpl.Stateful.shiftLeft, QueryImpl.Stateful.run, signedFreshAdv,
    StateT.run'_eq, simulateQ_bind, StateT.run_bind, monad_norm]

/-! ## H5 fork-side infrastructure -/

private abbrev ForkBaseState (M Commit Chal : Type)
      :=
  (fsRoSpec M Commit Chal).QueryCache × Fork.SimState M Commit Chal

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma mem_support_forkSim_pure_nested_iff
    {α : Type} (x : α) (cache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.SimState M Commit Chal)
    (z : (α × (fsRoSpec M Commit Chal).QueryCache) × Fork.SimState M Commit Chal) :
    z ∈ support
      ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
        ((pure x : StateT (fsRoSpec M Commit Chal).QueryCache
          (OracleComp (unifSpec + (M × Commit →ₒ Chal))) α).run cache)).run liveSt) ↔
      z = ((x, cache), liveSt) := by
  rw [StateT.run_pure, simulateQ_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff]

@[fs_simp] private noncomputable def forkBaseImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (ForkBaseState M Commit Chal) (OracleComp (Fork.wrappedSpec Chal))) :=
  ((Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
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
      :=
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
  ((s.2.1.2.1.inr : (fsRoSpec M Commit Chal).QueryCache), s.1)

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
  simpa [cmaSimLoggedLeftImpl] using congrArg (fun x ↦ x.run st)
    (QueryImpl.simulateQ_liftM_eq_of_query
      (impl := cmaSimLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT)
      (impl₁ := cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT)
      (h := fun t ↦ by
        rcases t with ((n | mc) | m) <;>
          · change simulateQ _ (liftM ((cmaSpec M Commit Chal Resp Stmt).query _)) = _
            simp [cmaSimLoggedLeftImpl])
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
  rw [← cmaSimLoggedImpl_liftAdv_run (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
    hr simT oa (([] : List M), st)]
  simpa [cmaSimLoggedImpl] using
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
      (outer := cmaSim M Commit Chal hr simT)
      (inner := cmaSignLogImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
      (oa := (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α))
      (s := ([] : List M)) (q := st)

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
        simp only [monad_norm, StateT.run_mk, impl₁]
        refine bind_congr (m := ProbComp) fun u => ?_
        simpa only [impl₁, pure_bind, map_eq_bind_pure_comp, Function.comp_apply] using ih u s
  exact QueryImpl.simulateQ_liftM_eq_of_query
    (impl := nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)
    (impl₁ := impl₁)
    (h := fun n => by
      funext s'
      change ((nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr
        (.unif n)).run s') = (impl₁ n).run s'
      simp [impl₁, nma, nmaPublic])
    (oa := oa) ▸ himpl₁

omit [Finite Chal] [Inhabited Chal] in
private lemma simulatedNmaUnifSim_fsUniform_run
    {α : Type} (oa : ProbComp α)
    (cache : (fsRoSpec M Commit Chal).QueryCache) :
    simulateQ (fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal))
        ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
          (Chal := Chal)) oa).run cache) =
      (fun a ↦ (a, cache)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x =>
      simp [fsUniformImpl]
  | query_bind n k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      simp only [fsUniformImpl, QueryImpl.ofLift_eq_id', simulatedNmaUnifSim,
        simulatedNmaFwd, QueryImpl.liftTarget_apply, add_apply_inl,
        HasQuery.toQueryImpl_apply, QueryImpl.toHasQuery_query, StateT.run_monadLift,
        monadLift_self, bind_pure_comp, simulateQ_map, bind_map_left, map_bind]
      exact bind_congr (m := ProbComp) fun u ↦ ih u cache

omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimLoggedLeft_preserves_inv
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (sk : Wit) : ∀ t s,
    cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk s →
    ∀ z ∈ support (m := ProbComp)
      ((cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT t).run s),
      cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) pk sk z.2 := by
    intro t s hs
    rcases s with ⟨signed, ⟨⟨log, cache, keypair⟩, bad⟩⟩
    simp only [cmaSimFixedKeyInv] at hs ⊢
    rcases t with ((n | mc) | m)
    · intro z hz
      obtain ⟨u, _hu, rfl⟩ := by
        simpa [fs_simp, cmaOracleSpec, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
          QueryImpl.Stateful.linkWith] using hz
      exact hs
    · intro z hz
      cases hcache : cache mc with
      | some ch =>
          obtain ⟨rfl, rfl⟩ := by
            simpa [fs_simp, cmaOracleSpec, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, hcache] using hz
          exact hs
      | none =>
          obtain ⟨ch, _hch, rfl⟩ := by
            simpa [fs_simp, cmaOracleSpec, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, hcache, uniformSampleImpl] using hz
          simpa [QueryCache.cacheQuery] using hs
    · subst keypair
      intro z hz
      have hz' := by
        simpa only [cmaOracleSpec, add_apply_inr, cmaSimLoggedLeftImpl, cmaSimLoggedImpl,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, cmaSim, cmaFrame, cmaOuterLens,
          Prod.mk.eta, cmaNmaLens, cmaSignLogImpl, bind_pure_comp, StateT.run_bind,
          StateT.run_get, StateT.run_monadLift, monadLift_self, StateT.run_map, StateT.run_set,
          map_pure, Functor.map_map, pure_bind, simulateQ_map, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.Stateful.linkWith,
          cmaToNma, cmaSignSim, liftComp_eq_liftM, PFunctor.Lens.State.mk_get, StateT.run_mk,
          simulateQ_bind, nma, nmaPublic, id_map, nmaProgram, map_bind,
          QueryImpl.Stateful.Frame.linkReshape, PFunctor.Lens.State.mk_put, support_bind,
          support_map, Set.mem_iUnion, Set.mem_image, Prod.exists, Bool.exists_bool, exists_prop]
          using hz
      rcases hz' with ⟨xCommit, xChal, xResp, xCache, xKeypair, hx⟩
      have state_eq (xBad : Bool)
          (hxmem : ((xCommit, xChal, xResp), xCache, xKeypair, xBad) ∈
            support ((simulateQ
              (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)
              (liftM (simT pk))).run (cache, some (pk, sk), bad))) :
          (xCache, xKeypair, xBad) = (cache, some (pk, sk), bad) := by
        have hxmem' := hxmem
        rw [nma_lift_unif_run (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit) hr (simT pk)
          (cache, some (pk, sk), bad), support_map] at hxmem'
        rcases hxmem' with ⟨x', _hx', hx'⟩
        exact congrArg Prod.snd hx'.symm
      rcases hx with ⟨hxmem, hnext⟩ | ⟨hxmem, hnext⟩
      · have hxinner := state_eq false hxmem
        have hxkey : xKeypair = some (pk, sk) :=
          congrArg (fun state => state.2.1) hxinner
        rcases hnext with ⟨u, nextCache, nextKeypair, hnext⟩
        rcases hnext with ⟨hu, rfl⟩ | ⟨hu, rfl⟩
        all_goals
          cases htarget : xCache (m, xCommit)
          all_goals
            simp only [htarget, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
              Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, true_and] at hu
          all_goals exact hu.2.trans hxkey
      · have hxinner := state_eq true hxmem
        have hxkey : xKeypair = some (pk, sk) :=
          congrArg (fun state => state.2.1) hxinner
        rcases hnext with ⟨u, nextCache, nextKeypair, hnext⟩
        rcases hnext with ⟨hu, rfl⟩ | ⟨hu, rfl⟩
        all_goals
          cases htarget : xCache (m, xCommit)
          all_goals
            simp only [htarget, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
              Bool.false_eq_true, and_false, and_true, true_and] at hu
          all_goals exact hu.2.trans hxkey
omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private lemma cmaSimLoggedLeft_project_step
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (sk : Wit) : ∀ t s,
    cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk s →
    Prod.map id (cmaSimLoggedProj (M := M) (Commit := Commit)
        (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
      (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT t).run s =
      (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk t).run
        (cmaSimLoggedProj (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit) s) := by
    intro t s hs
    rcases s with ⟨signed, ⟨⟨log, cache, keypair⟩, bad⟩⟩
    simp only [cmaSimFixedKeyInv] at hs
    rcases t with ((n | mc) | m)
    · simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
        QueryImpl.Stateful.linkWith]
    · cases hcache : cache mc with
      | some ch =>
          simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
            QueryImpl.Stateful.linkWith, hcache]
      | none =>
          conv_lhs =>
            simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, QueryImpl.liftTarget_apply,
              QueryImpl.simulateQ_add_query_left, QueryImpl.simulateQ_add_query_right,
              QueryImpl.id'_apply, uniformSampleImpl, hcache]
          conv_rhs =>
            simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, QueryImpl.liftTarget_apply,
              QueryImpl.simulateQ_add_query_left, QueryImpl.simulateQ_add_query_right,
              QueryImpl.id'_apply, uniformSampleImpl, hcache]
    · subst keypair
      conv_lhs =>
        simp only [add_apply_inr, cmaSimLoggedLeftImpl, cmaSimLoggedImpl,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, cmaSim, cmaFrame,
          cmaOuterLens, Prod.mk.eta, cmaNmaLens, cmaSignLogImpl, bind_pure_comp,
          StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
          StateT.run_map, StateT.run_set, map_pure, Functor.map_map, pure_bind,
          simulateQ_map, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, QueryImpl.Stateful.linkWith, cmaToNma,
          cmaSignSim, liftComp_eq_liftM, PFunctor.Lens.State.mk_get,
          StateT.run_mk, simulateQ_bind, nma, nmaPublic, id_map, nmaProgram,
          map_bind, QueryImpl.Stateful.Frame.linkReshape,
          PFunctor.Lens.State.mk_put, Prod.map_apply, id_eq, cmaSimLoggedProj]
      conv_rhs =>
        simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
          QueryImpl.Stateful.linkWith,
          StateT.run_bind, StateT.run_mk, StateT.run_map, StateT.run_monadLift,
          monadLift_self, simulateQ_bind, simulateQ_map, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, id_map,
          bind_pure_comp, pure_bind, map_bind, Functor.map_map, Prod.map_apply,
          id_eq]
      let advCache : (fsRoSpec M Commit Chal).QueryCache := cache.inr
      have hright :
          simulateQ (fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal))
              ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
                (Chal := Chal)) (simT pk)).run advCache) =
            (fun a ↦ (a, advCache)) <$> simT pk :=
        simulatedNmaUnifSim_fsUniform_run (M := M)
          (Commit := Commit) (Chal := Chal) (oa := simT pk) (cache := advCache)
      rw [nma_lift_unif_run (M := M) (Commit := Commit)
        (Chal := Chal) (Stmt := Stmt) (Wit := Wit) hr (simT pk)
        (cache, some (pk, sk), bad)]
      simp only [monad_norm]
      conv_rhs =>
        lhs
        change simulateQ (fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal))
          ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
            (Chal := Chal)) (simT pk)).run advCache)
        rw [hright]
      simp only [monad_norm]
      refine bind_congr (m := ProbComp) fun x => ?_
      cases htarget : cache (m, x.1) with
      | some old =>
          simp [advCache, htarget]
      | none =>
          simp [advCache, htarget]

omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private def cmaSimLoggedLeftOrnament
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
  preserves_inv := cmaSimLoggedLeft_preserves_inv (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT pk sk
  project_step := cmaSimLoggedLeft_project_step (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT pk sk

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
  simp [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, cmaToNma,
    StateT.run_mk, map_eq_bind_pure_comp]

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
  | none | some ch =>
      simp [nma, nmaPublic, cmaFrame,
        cmaOuterLens, cmaNmaLens, QueryImpl.Stateful.Frame.linkReshape,
        hcache, QueryCache.cacheQuery, monad_norm]

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
  let : Fintype Chal := Fintype.ofFinite Chal
  rcases x with ⟨msg, c, resp⟩
  rcases st with ⟨signed, ⟨⟨log, cache, keypair⟩, bad⟩⟩
  cases hcache : cache (msg, c) with
  | some ch =>
      change Chal at ch
      simp [simLoggedVerifyFreshComp, cmaSimLoggedProj, _root_.FiatShamir,
        hcache, cmaSim_lift_ro_query_run (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
          hr simT (msg, c) ((log, cache, keypair), bad)]
      congr 1
  | none =>
      simp [simLoggedVerifyFreshComp, cmaSimLoggedProj, _root_.FiatShamir,
        hcache, cmaSim_lift_ro_query_run (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
          hr simT (msg, c) ((log, cache, keypair), bad)]
      congr 1

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
      :
    ForkBaseState M Commit Chal × List M :=
  (((∅ : (fsRoSpec M Commit Chal).QueryCache),
      ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit)))),
    ([] : List M))

private def forkInitialBaseState (M Commit Chal : Type)
      :
    ForkBaseState M Commit Chal :=
  ((∅ : (fsRoSpec M Commit Chal).QueryCache),
    ((∅ : (M × Commit →ₒ Chal).QueryCache), ([] : List (M × Commit))))

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
omit [DecidableEq M] [DecidableEq Commit] in
private lemma forkInitialState_inv :
    forkAwareInv (M := M) (Commit := Commit) (Chal := Chal)
      (forkInitialState M Commit Chal) := by
  constructor <;> intro mc ch hcache <;> simp [forkInitialState] at hcache

omit [SampleableType Chal] in
private lemma simulatedNmaUnifFork_flatten_preserves_state
    {α : Type} (A : ProbComp α)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.SimState M Commit Chal)
    {z : α × ((fsRoSpec M Commit Chal).QueryCache × Fork.SimState M Commit Chal)}
    (hz : z ∈ support
      ((simulateQ
        ((Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
          (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))).flattenStateT
        A).run (advCache, liveSt))) :
    z.2 = (advCache, liveSt) := by
  let : Fintype Chal := Fintype.ofFinite Chal
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := ((Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
      (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))).flattenStateT)
    (inv := fun st => st = (advCache, liveSt))
    (hinv := by
      intro t st hst y hy
      subst hst
      have hy' := by
        simpa [QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          simulatedNmaUnifSim, simulatedNmaFwd, Fork.unifForward] using hy
      rcases hy' with ⟨u, _hu, b, hb, rfl⟩
      rfl)
    A (advCache, liveSt) rfl z hz

omit [SampleableType Chal] in
private lemma simulatedNmaUnifFork_nested_preserves_state
    {α : Type} (A : ProbComp α)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.SimState M Commit Chal)
    {z : (α × (fsRoSpec M Commit Chal).QueryCache) × Fork.SimState M Commit Chal}
    (hz : z ∈ support
      ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
        ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
          (Chal := Chal)) A).run advCache)).run liveSt)) :
    z.1.2 = advCache ∧ z.2 = liveSt := by
  let : Fintype Chal := Fintype.ofFinite Chal
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (outer := Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
    (inner := simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))
    (oa := A) (s := advCache) (q := liveSt), support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hstate := simulatedNmaUnifFork_flatten_preserves_state
    (M := M) (Commit := Commit) (Chal := Chal) A advCache liveSt hy
  rcases y with ⟨a, st⟩
  simp only at hstate
  subst st
  simp

omit [SampleableType Stmt] [Inhabited Chal] in
private lemma forkLoggedImpl_sign_support
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) (m : M)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveCache : (M × Commit →ₒ Chal).QueryCache)
    (queryLog : List (M × Commit)) (signed : List M)
    {z : (Commit × Resp) × (ForkBaseState M Commit Chal × List M)}
    (hz : z ∈ support ((forkLoggedImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk (.inr m)).run
        ((advCache, liveCache, queryLog), signed))) :
    ∃ xCommit xChal xResp xAdvCache xLiveCache xQueryLog,
      ((((xCommit, xChal, xResp), xAdvCache), (xLiveCache, xQueryLog)) ∈ support
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
          ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
            (Chal := Chal)) (simT pk)).run advCache)).run (liveCache, queryLog))) ∧
      ((match xAdvCache (.inr (m, xCommit)) with
        | some _ => ((xCommit, xResp), xAdvCache)
        | none => ((xCommit, xResp),
            xAdvCache.cacheQuery (.inr (m, xCommit)) xChal)).1,
        ((match xAdvCache (.inr (m, xCommit)) with
          | some _ => ((xCommit, xResp), xAdvCache)
          | none => ((xCommit, xResp),
              xAdvCache.cacheQuery (.inr (m, xCommit)) xChal)).2,
          xLiveCache, xQueryLog),
        signed ++ [m]) = z := by
  have hz' := by
    simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
      QueryImpl.mapStateTBase] using hz
  rcases hz' with ⟨xCommit, xChal, xResp, xAdvCache, xLiveCache,
    xQueryLog, hxmem, hout⟩
  refine ⟨xCommit, xChal, xResp, xAdvCache, xLiveCache, xQueryLog, hxmem, ?_⟩
  convert hout using 1
  congr 4
  all_goals
    cases xAdvCache (.inr (m, xCommit)) <;> rfl

/-! ## Structural fork-state transitions -/

/-- State changes possible in one logged fork-handler step. The relation records only
cache and log effects, independently of the answer distribution. -/
private inductive ForkStateStep (s : ForkBaseState M Commit Chal × List M) :
    ForkBaseState M Commit Chal × List M → Prop
  | unchanged : ForkStateStep s s
  | cached (mc : M × Commit) (ch : Chal) (h : s.1.2.1 mc = some ch) :
      ForkStateStep s ((s.1.1.cacheQuery (.inr mc) ch, s.1.2), s.2)
  | fresh (mc : M × Commit) (ch : Chal) :
      ForkStateStep s ((s.1.1.cacheQuery (.inr mc) ch,
        s.1.2.1.cacheQuery mc ch, s.1.2.2 ++ [mc]), s.2)
  | signed (m : M) : ForkStateStep s (s.1, s.2 ++ [m])
  | signedFresh (mc : M × Commit) (ch : Chal) (h : s.1.1 (.inr mc) = none) :
      ForkStateStep s ((s.1.1.cacheQuery (.inr mc) ch, s.1.2), s.2 ++ [mc.1])

omit [SampleableType Stmt] in
/-- Normalize one handler outcome to its cache/log state transition. -/
private lemma forkLoggedImpl_state_step
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    (t : (cmaOracleSpec M Commit Chal Resp).Domain)
    (s : ForkBaseState M Commit Chal × List M)
    (z : (cmaOracleSpec M Commit Chal Resp).Range t × (ForkBaseState M Commit Chal × List M))
    (hz : z ∈ support ((forkLoggedImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk t).run s)) : ForkStateStep (M := M) s z.2 := by
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  rcases t with ((n | mc) | m)
  · have hz' := by
      simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase] using hz
    rcases hz' with ⟨w, hw, rfl⟩
    exact .unchanged
  · cases hadv : advCache (.inr mc) with
    | some ch =>
        have hz' := by
          simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, hadv] using hz
        rcases hz' with ⟨w, hw, rfl⟩
        exact .unchanged
    | none =>
        have hz' := by
          simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, hadv] using hz
        rcases hz' with ⟨ch, liveCache', queryLog', hw, rfl⟩
        cases hlive : liveCache mc with
        | none =>
            rw [Fork.roImpl_run_none (M := M) (Commit := Commit) (Chal := Chal)
                mc liveCache queryLog hlive,
              ← Fork.simulateQ_unifForward_add_roImpl_query_inr_run_none
                (M := M) (Commit := Commit) (Chal := Chal)
                mc liveCache queryLog hlive] at hw
            obtain ⟨v, heq⟩ :=
              (Fork.mem_support_simulateQ_unifForward_add_roImpl_query_inr_run_none_iff
                (M := M) (Commit := Commit) (Chal := Chal)
                mc liveCache queryLog hlive (ch, (liveCache', queryLog'))).mp hw
            rcases Prod.mk.inj heq with ⟨rfl, hst⟩
            rcases Prod.mk.inj hst with ⟨rfl, rfl⟩
            exact .fresh mc _
        | some liveCh =>
            rw [Fork.roImpl_run_some (M := M) (Commit := Commit) (Chal := Chal)
                mc liveCache queryLog liveCh hlive,
              ← Fork.simulateQ_unifForward_add_roImpl_query_inr_run_some
                (M := M) (Commit := Commit) (Chal := Chal)
                mc liveCache queryLog liveCh hlive] at hw
            have heq :=
              (Fork.mem_support_simulateQ_unifForward_add_roImpl_query_inr_run_some_iff
                (M := M) (Commit := Commit) (Chal := Chal)
                mc liveCache queryLog liveCh hlive (ch, (liveCache', queryLog'))).mp hw
            rcases Prod.mk.inj heq with ⟨rfl, hst⟩
            rcases Prod.mk.inj hst with ⟨rfl, rfl⟩
            exact .cached mc _ hlive
  · obtain ⟨xCommit, xChal, xResp, xAdvCache, xLiveCache, xQueryLog, hxmem, rfl⟩ :=
      forkLoggedImpl_sign_support (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk m advCache liveCache queryLog signed hz
    obtain ⟨hadv, hlive⟩ := simulatedNmaUnifFork_nested_preserves_state
      (M := M) (Commit := Commit) (Chal := Chal) (simT pk) advCache
      (liveCache, queryLog) hxmem
    dsimp only at hadv hlive
    subst xAdvCache
    rcases Prod.mk.inj hlive with ⟨rfl, rfl⟩
    cases htarget : advCache (.inr (m, xCommit)) with
    | none =>
        exact .signedFresh (m, xCommit) xChal htarget
    | some ch =>
        exact .signed m

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- Fresh-cache coherence and live-log coverage are preserved by every structural transition. -/
private lemma ForkStateStep.preserves_aware
    {s s' : ForkBaseState M Commit Chal × List M} (step : ForkStateStep (M := M) s s')
    (hs : forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) s) :
    forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) s' := by
  rcases hs with ⟨hfresh, hlog⟩
  cases step with
  | unchanged => exact ⟨hfresh, hlog⟩
  | cached mc ch hlive =>
      refine ⟨?_, hlog⟩
      intro mc' ch' hcache hnew
      by_cases heq : mc' = mc
      · subst mc'
        have hv : ch = ch' := by simpa using hcache
        simpa [hv] using hlive
      · apply hfresh mc' ch' _ hnew
        simpa [QueryCache.cacheQuery_of_ne, heq] using hcache
  | fresh mc ch =>
      constructor
      · intro mc' ch' hcache hnew
        by_cases heq : mc' = mc
        · subst mc'
          have hv : ch = ch' := by simpa using hcache
          simp [hv]
        · have hold : s.1.1 (.inr mc') = some ch' := by
            simpa [QueryCache.cacheQuery_of_ne, heq] using hcache
          simpa [QueryCache.cacheQuery_of_ne, heq] using hfresh mc' ch' hold hnew
      · intro mc' ch' hcache
        by_cases heq : mc' = mc
        · subst mc'; simp
        · have hold : s.1.2.1 mc' = some ch' := by
            simpa [QueryCache.cacheQuery_of_ne, heq] using hcache
          exact List.mem_append_left [mc] (hlog mc' ch' hold)
  | signed m =>
      refine ⟨?_, hlog⟩
      intro mc ch hcache hnew
      exact hfresh mc ch hcache (fun hm => hnew (List.mem_append_left [m] hm))
  | signedFresh mc ch hnone =>
      refine ⟨?_, hlog⟩
      intro mc' ch' hcache hnew
      have heq : mc' ≠ mc := by rintro rfl; simp at hnew
      apply hfresh mc' ch' _ (fun hm => hnew (List.mem_append_left [mc.1] hm))
      simpa [QueryCache.cacheQuery_of_ne, heq] using hcache

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- Agreement of live and adversary caches is preserved by every structural transition. -/
private lemma ForkStateStep.preserves_live_adv
    {s s' : ForkBaseState M Commit Chal × List M} (step : ForkStateStep (M := M) s s')
    (hs : forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal) s) :
    forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal) s' := by
  cases step with
  | unchanged => exact hs
  | signed m => exact hs
  | cached mc ch hlive =>
      intro mc' ch' hcache
      by_cases heq : mc' = mc
      · subst mc'
        have hv : ch = ch' := Option.some.inj (hlive.symm.trans hcache)
        simp [hv]
      · simpa [QueryCache.cacheQuery_of_ne, heq] using hs mc' ch' hcache
  | fresh mc ch =>
      intro mc' ch' hcache
      by_cases heq : mc' = mc
      · subst mc'
        have hv : ch = ch' := by simpa using hcache
        simp [hv]
      · have hold : s.1.2.1 mc' = some ch' := by
          simpa [QueryCache.cacheQuery_of_ne, heq] using hcache
        simpa [QueryCache.cacheQuery_of_ne, heq] using hs mc' ch' hold
  | signedFresh mc ch hnone =>
      intro mc' ch' hcache
      have heq : mc' ≠ mc := by
        rintro rfl
        have h := hs _ ch' hcache
        rw [hnone] at h
        cases h
      simpa [QueryCache.cacheQuery_of_ne, heq] using hs mc' ch' hcache

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
  exact ForkStateStep.preserves_aware (M := M)
    (forkLoggedImpl_state_step (M := M) simT pk t s z hz) hs

omit [SampleableType Stmt] in
private lemma forkLoggedImpl_preserves_inv
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    {α : Type} (A : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    {z : α × (ForkBaseState M Commit Chal × List M)}
    (hz : z ∈ support ((simulateQ (forkLoggedImpl (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk) A).run
      (forkInitialState M Commit Chal))) :
    forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) z.2 := by
  let : Fintype Chal := Fintype.ofFinite Chal
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
  exact ForkStateStep.preserves_live_adv (M := M)
    (forkLoggedImpl_state_step (M := M) simT pk t s z hz) hs

omit [SampleableType Stmt] in
private lemma forkLoggedImpl_preserves_live_adv_inv
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    {α : Type} (A : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    {z : α × (ForkBaseState M Commit Chal × List M)}
    (hz : z ∈ support ((simulateQ (forkLoggedImpl (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk) A).run
      (forkInitialState M Commit Chal))) :
    forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal) z.2 := by
  let : Fintype Chal := Fintype.ofFinite Chal
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
private lemma forkPoint_isSome_of_mem_verified_findIdx_le {qH : ℕ}
    (trace : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (hverified : trace.verified = true) (hmem : trace.target ∈ trace.queryLog)
    (hidx : trace.queryLog.findIdx (· == trace.target) ≤ qH) :
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH trace).isSome = true := by
  simp [Fork.forkPoint, hverified, hmem, hidx]

omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- Convenience corollary: if the queryLog itself fits within `qH`, then the
target's `findIdx` is automatically `≤ qH` and `forkPoint qH trace` is some. -/
private lemma forkPoint_isSome_of_mem_verified_length {qH : ℕ}
    (trace : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (hverified : trace.verified = true) (hmem : trace.target ∈ trace.queryLog)
    (hlen : trace.queryLog.length ≤ qH) :
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH trace).isSome = true := by
  refine forkPoint_isSome_of_mem_verified_findIdx_le (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) trace hverified hmem ?_
  exact (List.findIdx_lt_length_of_exists ⟨trace.target, hmem, by simp⟩).le.trans hlen

end FiatShamir.Stateful
