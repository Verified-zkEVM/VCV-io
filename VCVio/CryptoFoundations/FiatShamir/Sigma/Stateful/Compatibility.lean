/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Bridge
import VCVio.StateSeparating.Advantage

/-!
# Compatibility endpoints for the stateful Fiat-Shamir CMA proof

The main stateful proof path uses the full `CmaState` game definitions from
`Stateful.Games` and the full-state post-keygen normal form in
`Stateful.Bridge`.

The generic `SignatureAlg.unforgeableExp` experiment is still a useful public
API, but it interprets signing queries through a `WriterT` query log. Any theorem
equating that legacy public experiment with the full-state CMA game necessarily
relates two interpreters. Such theorems belong here, not in the main stateful
bridge.
-/

universe u v

open OracleSpec OracleComp ProbComp

namespace FiatShamir.Stateful

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit]
variable [SampleableType Chal]

/-! ## Public and stateful endpoints -/

/-- The legacy public EUF-CMA advantage exposed by `SignatureAlg`.

This endpoint uses `SignatureAlg.unforgeableExp`, which logs signing queries via
`WriterT`. It is kept separate from the full-state stateful proof path. -/
noncomputable def publicUnforgeableAdvantage
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) : ENNReal :=
  adv.advantage (_root_.FiatShamir.runtime M)

/-- The full-state post-keygen CMA advantage used by the stateful proof path.

This is the key-generation wrapper around `postKeygenFreshProb`; the fixed-key
body runs through `cmaRealSourceFullSum` on `CmaState`. -/
noncomputable def statefulPostKeygenFreshAdvantage
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) : ENNReal :=
  Pr[= true | ((hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
    postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2)]

/-- The full-state CMA run as a Boolean freshness experiment.

This packages `cmaRealRun` with the same final freshness predicate as the
post-keygen normal form. -/
noncomputable def statefulCmaFreshExperiment
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) : ProbComp Bool := do
  let z ← cmaRealRun σ hr M adv
  let out := z.1
  let verified := z.2.1
  let signed := z.2.2
  pure (!decide (out.1 ∈ signed) && verified)

/-- The full-state CMA advantage obtained directly from `cmaRealRun`.

This endpoint is equivalent to `statefulPostKeygenFreshAdvantage` by unfolding
the public-key query in `signedAdv`; the equality is a stateful-game normal-form
fact and does not mention `SignatureAlg.unforgeableExp`. -/
noncomputable def statefulCmaFreshAdvantage
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) : ENNReal :=
  Pr[= true | statefulCmaFreshExperiment σ hr M adv]

/-! ## Compatibility boundary -/

/-- Compatibility proposition between the legacy public experiment and the
full-state stateful experiment.

The main stateful proof path should assume or prove facts about
`statefulCmaFreshAdvantage`. If a caller needs the historical
`SignatureAlg.unforgeableAdv.advantage` API, the required normalization theorem
should target this proposition in this quarantined module. -/
def PublicCompatible
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) : Prop :=
  publicUnforgeableAdvantage σ hr M adv =
    statefulCmaFreshAdvantage σ hr M adv

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Interpreting a lifted source-CMA computation through the named real-CMA
handler is the same as interpreting it through the source-query full-state
handler. -/
private lemma simulateQ_cmaReal_liftM_sourceCma_eq
    {α : Type}
    (oa : SourceCmaComp (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) α) :
    simulateQ (cmaReal M Commit Chal σ hr)
      (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) =
    simulateQ (cmaRealSourceFullSum M Commit Chal σ hr) oa := by
  apply QueryImpl.simulateQ_liftM_eq_of_query
  intro t
  rcases t with (n | mc) | m
  · rfl
  · change simulateQ (cmaReal M Commit Chal σ hr)
      (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.ro mc))) = _
    rw [simulateQ_spec_query]
    rfl
  · change simulateQ (cmaReal M Commit Chal σ hr)
      (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.sign m))) = _
    rw [simulateQ_spec_query]
    rfl

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The Fiat-Shamir public random-oracle interface has the same real-CMA
semantics whether it is embedded directly into the named CMA interface or first
through the source-CMA interface. -/
private lemma simulateQ_cmaReal_liftM_fsRo_eq_sourceCma
    {α : Type}
    (oa : OracleComp (unifSpec + roSpec M Commit Chal) α) :
    simulateQ (cmaReal M Commit Chal σ hr)
      (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) =
    simulateQ (cmaRealSourceFullSum M Commit Chal σ hr)
      (liftM oa : SourceCmaComp (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) α) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      rw [liftM_bind, liftM_bind, simulateQ_bind, simulateQ_bind]
      rcases t with n | mc
      · simp only [add_apply_inl]
        exact bind_congr ih
      · simp only [add_apply_inr]
        exact bind_congr ih

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Fixed-key `postKeygenAdv` over the named CMA interface is the source
post-keygen computation interpreted by the full-state source handler. -/
private lemma postKeygenAdv_runState_eq_postKeygenAdvBase_run
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) (s : CmaState M Commit Chal Stmt Wit) :
    (cmaReal M Commit Chal σ hr).runState s (postKeygenAdv σ hr M adv pk) =
      (simulateQ (cmaRealSourceFullSum M Commit Chal σ hr)
        (postKeygenAdvBase (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk)).run s := by
  unfold QueryImpl.Stateful.runState postKeygenAdv postKeygenAdvBase
    postKeygenCandidateAdv postVerifyComp
  simp only [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_cmaReal_liftM_sourceCma_eq (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (oa := adv.main pk)]
  apply bind_congr
  intro a
  rw [simulateQ_cmaReal_liftM_fsRo_eq_sourceCma (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt)
    (oa := (SourceSigAlg (σ := σ) (hr := hr) (M := M)).verify pk a.1.1 a.1.2)]
  simp

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The direct `cmaRealRun` endpoint and the fixed-key post-keygen endpoint are
the same full-state freshness experiment. -/
theorem statefulCmaFreshAdvantage_eq_statefulPostKeygenFreshAdvantage
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    statefulCmaFreshAdvantage σ hr M adv =
      statefulPostKeygenFreshAdvantage σ hr M adv := by
  unfold statefulCmaFreshAdvantage statefulCmaFreshExperiment
    statefulPostKeygenFreshAdvantage
  rw [cmaRealRun_eq_keygen_bind (σ := σ) (hr := hr) (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) adv]
  simp only [bind_assoc]
  apply congrArg (fun p => Pr[= true | p])
  apply bind_congr
  intro ps
  unfold postKeygenFreshProb
  rw [postKeygenAdv_runState_eq_postKeygenAdvBase_run (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    adv ps.1 ((([] : List M), (∅ : RoCache M Commit Chal),
      (some (ps.1, ps.2) : Option (Stmt × Wit))), false)]
  simp [StateT.run_bind]

/-! ## Public WriterT compatibility -/

/-- Fixed-key public signing-query handler in the generic `appendInputLog` form. -/
@[reducible, fs_simp] private noncomputable def postKeygenAppendImpl
    (pk : Stmt) (sk : Wit) :
    QueryImpl (SourceCmaSpec (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (StateT (List M) (StateT (RoCache M Commit Chal) ProbComp)) := by
  letI : HasQuery (unifSpec + roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp) :=
    (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).toHasQuery
  let baseS : QueryImpl (unifSpec + roSpec M Commit Chal)
      (StateT (List M) (StateT (RoCache M Commit Chal) ProbComp)) :=
    (HasQuery.toQueryImpl (spec := unifSpec + roSpec M Commit Chal)
      (m := StateT (RoCache M Commit Chal) ProbComp)).liftTarget _
  exact baseS +
    QueryImpl.appendInputLog
      (cmaRealFixedSign (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ hr pk sk)

private abbrev postKeygenState (M Commit Chal : Type) :=
  List M × RoCache M Commit Chal

/-- Product-state version of `postKeygenAppendImpl`, used to compare with the
full `CmaState` handler by projection. -/
@[fs_simp] private noncomputable def postKeygenAppendProdImpl (pk : Stmt) (sk : Wit) :
    QueryImpl (SourceCmaSpec (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (StateT (postKeygenState M Commit Chal) ProbComp) := fun t =>
  StateT.mk fun (signed, cache) =>
    match t with
    | Sum.inl (Sum.inl n) => do
        let r ← (unifSpec.query n : ProbComp (Fin (n + 1)))
        pure (r, (signed, cache))
    | Sum.inl (Sum.inr mc) => do
        let (r, cache') ←
          ((randomOracle : QueryImpl (roSpec M Commit Chal)
            (StateT (RoCache M Commit Chal) ProbComp)) mc).run cache
        pure (r, (signed, cache'))
    | Sum.inr m => do
        let (sig, cache') ←
          (cmaRealFixedSign (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ hr pk sk m).run cache
        pure (sig, (signed ++ [m], cache'))

@[fs_simp] private def cmaPostKeygenProj
    (s : CmaState M Commit Chal Stmt Wit) :
    postKeygenState M Commit Chal :=
  (s.1.1, s.1.2.1)

private def cmaPostKeygenInv
    (pk : Stmt) (sk : Wit)
    (s : CmaState M Commit Chal Stmt Wit) : Prop :=
  s.1.2.2 = some (pk, sk) ∧ s.2 = false

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealSourceFullSum_lift_ro_query_run
    (mc : M × Commit) (s : CmaState M Commit Chal Stmt Wit) :
    (simulateQ (cmaRealSourceFullSum M Commit Chal σ hr)
      (liftM (liftM ((roSpec M Commit Chal).query mc) :
        OracleComp (unifSpec + roSpec M Commit Chal) Chal) :
        SourceCmaComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) Chal)).run s =
    (cmaRealSourceFullSum M Commit Chal σ hr (.inl (.inr mc))).run s := by
  change (simulateQ (cmaRealSourceFullSum M Commit Chal σ hr)
      (liftM ((SourceCmaSpec (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp)).query (.inl (.inr mc))))).run s = _
  rw [simulateQ_spec_query]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealSourceFullSum_sign_run_some
    (pk : Stmt) (sk : Wit) (m : M)
    (signed : List M) (cache : RoCache M Commit Chal) :
    (cmaRealSourceFullSum M Commit Chal σ hr (.inr m)).run
        (((signed, cache, some (pk, sk)), false) :
          CmaState M Commit Chal Stmt Wit) =
      (do
        let cp ← σ.commit pk sk
        match cache (m, cp.1) with
        | some ch => do
            let π ← σ.respond pk sk cp.2 ch
            pure ((cp.1, π), ((signed ++ [m], cache, some (pk, sk)), false))
        | none => do
            let ch ← (($ᵗ Chal) : OracleComp unifSpec Chal)
            let π ← σ.respond pk sk cp.2 ch
            pure ((cp.1, π), ((signed ++ [m],
              cache.cacheQuery (m, cp.1) ch, some (pk, sk)), false))) := by
  dsimp [cmaRealSourceFullSum, cmaRealSourceFull]
  refine bind_congr (m := ProbComp) fun cp => ?_
  rcases cp with ⟨c, prv⟩
  cases hcache : cache (m, c) with
  | some ch =>
      simp [map_eq_bind_pure_comp]
  | none =>
      simp [map_eq_bind_pure_comp]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealSourceFullSum_project_step
    (pk : Stmt) (sk : Wit)
    (t : (SourceCmaSpec (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)).Domain)
    (st : CmaState M Commit Chal Stmt Wit)
    (hst : cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk st) :
    Prod.map id (cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit)) <$>
        (cmaRealSourceFullSum M Commit Chal σ hr t).run st =
      (postKeygenAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk t).run
        (cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
          (Stmt := Stmt) (Wit := Wit) st) := by
  rcases st with ⟨⟨signed, cache, keypair⟩, bad⟩
  simp only [cmaPostKeygenInv] at hst
  rcases hst with ⟨hkp, hbad⟩
  subst keypair
  subst bad
  rcases t with (n | mc) | m
  · simp [fs_simp]
  · cases hcache : cache mc with
    | some ch =>
        simp [fs_simp, hcache]
    | none =>
        simp [fs_simp, hcache, uniformSampleImpl]
  · simp only [add_apply_inr, fs_simp, bind_pure_comp,
      map_eq_bind_pure_comp, Prod.mk.eta, StateT.run_mk, bind_assoc,
      FiatShamir, QueryImpl.toHasQuery_query,
      randomOracle, QueryImpl.withCaching_apply, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_get, Function.comp_apply, StateT.run_pure, pure_bind]
    refine bind_congr (m := ProbComp) fun cp => ?_
    rcases cp with ⟨c, prv⟩
    cases hcache : cache (m, c) with
    | some ch =>
        simp [fs_simp, map_eq_bind_pure_comp]
    | none =>
        simp [fs_simp, uniformSampleImpl, StateT.run_modifyGet,
          map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealSourceFullSum_preserves_inv
    (pk : Stmt) (sk : Wit)
    (t : (SourceCmaSpec (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)).Domain)
    (st : CmaState M Commit Chal Stmt Wit)
    (hst : cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk st) :
    ∀ z ∈ support ((cmaRealSourceFullSum M Commit Chal σ hr t).run st),
      cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) pk sk z.2 := by
  rcases st with ⟨⟨signed, cache, keypair⟩, bad⟩
  simp only [cmaPostKeygenInv] at hst ⊢
  rcases hst with ⟨hkp, hbad⟩
  subst keypair
  subst bad
  rcases t with (n | mc) | m
  · intro z hz
    have hz' := by
      simpa [fs_simp] using hz
    rcases hz' with ⟨r, _hr, rfl⟩
    exact ⟨rfl, rfl⟩
  · intro z hz
    cases hcache : cache mc with
    | some ch =>
        have hz' := by
          simpa [fs_simp, hcache] using hz
        subst hz'
        exact ⟨rfl, rfl⟩
    | none =>
        have hz' := by
          simpa [fs_simp, hcache] using hz
        rcases hz' with ⟨ch, _hch, rfl⟩
        exact ⟨rfl, rfl⟩
  · intro z hz
    rw [cmaRealSourceFullSum_sign_run_some (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (Stmt := Stmt) (Wit := Wit) pk sk m signed cache] at hz
    have hz' := hz
    rw [support_bind] at hz'
    simp only [Set.mem_iUnion] at hz'
    rcases hz' with ⟨cp, _hcp, hz⟩
    rcases cp with ⟨c, prv⟩
    cases hcache : cache (m, c) with
    | some ch =>
        simp only [hcache, support_bind, support_pure, Set.mem_iUnion,
          Set.mem_singleton_iff] at hz
        rcases hz with ⟨π, _hπ, rfl⟩
        exact ⟨rfl, rfl⟩
    | none =>
        simp only [hcache, support_bind, Set.mem_iUnion] at hz
        rcases hz with ⟨ch, _hch, hz⟩
        rcases hz with ⟨π, _hπ, hz⟩
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨rfl, rfl⟩

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealSourceFullSum_project_run {α : Type}
    (pk : Stmt) (sk : Wit)
    (oa : SourceCmaComp (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) α)
    (st : CmaState M Commit Chal Stmt Wit)
    (hst : cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk st) :
    Prod.map id (cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit)) <$>
        (simulateQ (cmaRealSourceFullSum M Commit Chal σ hr) oa).run st =
      (simulateQ (postKeygenAppendProdImpl (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk) oa).run
        (cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
          (Stmt := Stmt) (Wit := Wit) st) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (impl₁ := cmaRealSourceFullSum M Commit Chal σ hr)
    (impl₂ := postKeygenAppendProdImpl (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
    (inv := cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk)
    (proj := cmaPostKeygenProj (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit))
    (hinv := fun t s hs =>
      cmaRealSourceFullSum_preserves_inv (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        pk sk t s hs)
    (hproj := fun t s hs =>
      cmaRealSourceFullSum_project_step (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        pk sk t s hs)
    oa st hst

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma postKeygenAppendProdImpl_eq_flattenStateT
    (pk : Stmt) (sk : Wit) :
    postKeygenAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk =
      (postKeygenAppendImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk).flattenStateT := by
  funext t
  rcases t with (n | mc) | m
  · ext st
    rcases st with ⟨signed, cache⟩
    conv_lhs =>
      simp [postKeygenAppendProdImpl]
    conv_rhs =>
      simp [postKeygenAppendImpl, QueryImpl.add_apply_inl]
    change _ =
      (((fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).liftTarget
          (StateT (List M) (StateT (RoCache M Commit Chal) ProbComp))).flattenStateT
        (.inl n)).run (signed, cache)
    rw [QueryImpl.flattenStateT_liftTarget_apply_run]
    simp [fsBaseImpl, unifFwdImpl, map_eq_bind_pure_comp]
  · ext st
    rcases st with ⟨signed, cache⟩
    conv_lhs =>
      simp [postKeygenAppendProdImpl]
    conv_rhs =>
      simp [postKeygenAppendImpl, QueryImpl.add_apply_inl]
    change _ =
      (((fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).liftTarget
          (StateT (List M) (StateT (RoCache M Commit Chal) ProbComp))).flattenStateT
        (.inr mc)).run (signed, cache)
    rw [QueryImpl.flattenStateT_liftTarget_apply_run]
    simp [fsBaseImpl, unifFwdImpl, randomOracle, map_eq_bind_pure_comp]
  · ext st
    rcases st with ⟨signed, cache⟩
    simp [postKeygenAppendProdImpl, postKeygenAppendImpl,
      QueryImpl.flattenStateT, QueryImpl.add_apply_inr, QueryImpl.appendInputLog_apply,
      StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift,
      map_eq_bind_pure_comp, bind_assoc]

/-- Fixed-key public post-keygen experiment after WriterT logging has been
converted to an input log. This is split at the candidate/log boundary. -/
private noncomputable def postKeygenFreshAppendProb
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) (sk : Wit) : ProbComp Bool :=
  letI : HasQuery (roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp) :=
    (randomOracle : QueryImpl (roSpec M Commit Chal) _).toHasQuery
  (((simulateQ (postKeygenAppendImpl (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
      (adv.main pk)).run ([] : List M)) >>= fun z => do
        let msg := z.1.1
        let sig := z.1.2
        let signed := z.2
        let verified ←
          (FiatShamir (m := StateT (RoCache M Commit Chal) ProbComp) σ hr M).verify
            pk msg sig
        pure (!decide (msg ∈ signed) && verified)).run' (∅ : RoCache M Commit Chal)

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma postKeygenAppendImpl_run_eq_cmaRealSourceFullSum_run
    {α : Type}
    (oa : SourceCmaComp (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) α)
    (pk : Stmt) (sk : Wit) (signed : List M)
    (cache : RoCache M Commit Chal) :
    ((simulateQ (postKeygenAppendImpl (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk) oa).run signed).run cache =
      (fun z : α × CmaState M Commit Chal Stmt Wit =>
        ((z.1, z.2.1.1), z.2.1.2.1)) <$>
        (simulateQ (cmaRealSourceFullSum M Commit Chal σ hr) oa).run
          (((signed, cache, some (pk, sk)), false)) := by
  let impl := postKeygenAppendImpl (σ := σ) (hr := hr) (M := M)
    (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk
  let st : CmaState M Commit Chal Stmt Wit :=
    (((signed, cache, some (pk, sk)), false))
  have hst :
      cmaPostKeygenInv (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) pk sk st := by
    simp [st, cmaPostKeygenInv]
  have hproj :=
    cmaRealSourceFullSum_project_run (σ := σ) (hr := hr)
      (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
      (Stmt := Stmt) (Wit := Wit) pk sk oa st hst
  rw [postKeygenAppendProdImpl_eq_flattenStateT (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk] at hproj
  have hflat :=
    OracleComp.simulateQ_flattenStateT_run (impl := impl) oa signed cache
  calc
    ((simulateQ impl oa).run signed).run cache =
        (fun z : α × (List M × RoCache M Commit Chal) => ((z.1, z.2.1), z.2.2)) <$>
          (simulateQ impl.flattenStateT oa).run (signed, cache) := by
        rw [hflat]
        simp [map_eq_bind_pure_comp, bind_assoc]
    _ =
        (fun z : α × CmaState M Commit Chal Stmt Wit =>
          ((z.1, z.2.1.1), z.2.1.2.1)) <$>
          (simulateQ (cmaRealSourceFullSum M Commit Chal σ hr) oa).run st := by
        have hreassoc :=
          congrArg
            (fun p : ProbComp (α × (postKeygenState M Commit Chal)) =>
              (fun z : α × (List M × RoCache M Commit Chal) =>
                ((z.1, z.2.1), z.2.2)) <$> p)
            hproj.symm
        simpa [impl, st, cmaPostKeygenProj, Functor.map_map] using hreassoc

omit [SampleableType Stmt] [SampleableType Wit] in
private theorem postKeygenFreshAppendProb_eq_statefulPostKeygenFreshProb
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) (sk : Wit) :
    postKeygenFreshAppendProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk =
    postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk := by
  unfold postKeygenFreshAppendProb postKeygenFreshProb
  simp only [FiatShamir, HasQuery.instOfMonadLift_query, QueryImpl.toHasQuery_query,
    QueryImpl.withCaching_apply, bind_pure_comp, bind_assoc, map_bind, Functor.map_map,
    StateT.run'_eq, StateT.run_bind, StateT.run_get, StateT.run_map, pure_bind,
    postKeygenAdvBase, SourceSigAlg, liftM_map, Prod.mk.eta, simulateQ_bind, simulateQ_map]
  rw [postKeygenAppendImpl_run_eq_cmaRealSourceFullSum_run (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (oa := adv.main pk)
    pk sk ([] : List M) (∅ : RoCache M Commit Chal)]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr (m := ProbComp) fun z => ?_
  rcases z with ⟨out, st⟩
  rcases out with ⟨msg, sig⟩
  rcases sig with ⟨c, resp⟩
  rcases st with ⟨⟨signed, cache, keypair⟩, bad⟩
  rw [cmaRealSourceFullSum_lift_ro_query_run (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) (mc := (msg, c))]
  cases hcache : cache (msg, c) with
  | some ch =>
      simp [cmaRealSourceFullSum, cmaRealSourceFull, hcache]
  | none =>
      simp [cmaRealSourceFullSum, cmaRealSourceFull, hcache, uniformSampleImpl]

@[fs_simp] private noncomputable def cmaRealAppendProdImpl :
    QueryImpl (SourceCmaSpec (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (StateT (List M × CmaState M Commit Chal Stmt Wit) ProbComp) := fun t =>
  StateT.mk fun (signed, st) =>
    match t with
    | Sum.inl (Sum.inl n) =>
        Prod.map id (fun st' => (signed, st')) <$>
          (cmaRealSourceFullSum M Commit Chal σ hr (.inl (.inl n))).run st
    | Sum.inl (Sum.inr mc) =>
        Prod.map id (fun st' => (signed, st')) <$>
          (cmaRealSourceFullSum M Commit Chal σ hr (.inl (.inr mc))).run st
    | Sum.inr m =>
        Prod.map id (fun st' => (signed ++ [m], st')) <$>
          (cmaRealSourceFullSum M Commit Chal σ hr (.inr m)).run st

@[fs_simp] private noncomputable def cmaRealLoggedProdImpl :
    QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (List M × CmaState M Commit Chal Stmt Wit) ProbComp) :=
  ((cmaReal M Commit Chal σ hr).mapStateTBase
    (cmaSignLogImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt))).flattenStateT

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealLoggedProdImpl_lift_query_eq_cmaRealAppendProdImpl
    (t : (SourceCmaSpec (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp)).Domain) :
    simulateQ (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (liftM ((SourceCmaSpec (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp)).query t) :
        OracleComp (cmaSpec M Commit Chal Resp Stmt)
          ((SourceCmaSpec (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp)).Range t)) =
      cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) t := by
  rcases t with (n | mc) | m
  · change simulateQ
        (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.unif n))) =
      cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) (.inl (.inl n))
    rw [simulateQ_spec_query]
    ext st
    rcases st with ⟨signed, st⟩
    simp [fs_simp, QueryImpl.mapStateTBase, QueryImpl.flattenStateT,
      map_eq_bind_pure_comp]
  · change simulateQ
        (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.ro mc))) =
      cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) (.inl (.inr mc))
    rw [simulateQ_spec_query]
    ext st
    rcases st with ⟨signed, st⟩
    cases hcache : st.1.2.1 mc with
    | some ch =>
        simp [fs_simp, QueryImpl.mapStateTBase, QueryImpl.flattenStateT, hcache]
    | none =>
        simp [fs_simp, QueryImpl.mapStateTBase, QueryImpl.flattenStateT, hcache]
  · change simulateQ
        (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.sign m))) =
      cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) (.inr m)
    rw [simulateQ_spec_query]
    ext st
    rcases st with ⟨signed, st⟩
    simp [fs_simp, QueryImpl.mapStateTBase, QueryImpl.flattenStateT,
      StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]
    rfl

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealLoggedProdImpl_liftAdv_run {α : Type}
    (oa : SourceCmaComp (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) α)
    (st : List M × CmaState M Commit Chal Stmt Wit) :
    (simulateQ (cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run st =
      (simulateQ (cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp)) oa).run st := by
  simpa using congrArg (fun x => x.run st)
    (QueryImpl.simulateQ_liftM_eq_of_query
      (impl := cmaRealLoggedProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (impl₁ := cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (h := fun t => by
        exact cmaRealLoggedProdImpl_lift_query_eq_cmaRealAppendProdImpl
          (σ := σ) (hr := hr) (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) t)
      (oa := oa))

@[fs_simp] private def cmaRealAppendProj
    (st : CmaState M Commit Chal Stmt Wit) :
    List M × CmaState M Commit Chal Stmt Wit :=
  (st.1.1, st)

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaRealAppendProdImpl_project_step
    (t : (SourceCmaSpec (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)).Domain)
    (st : CmaState M Commit Chal Stmt Wit) :
    Prod.map id (cmaRealAppendProj (M := M) (Commit := Commit)
      (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
        (cmaRealSourceFullSum M Commit Chal σ hr t).run st =
      (cmaRealAppendProdImpl (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) t).run
        (cmaRealAppendProj (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit) st) := by
  rcases st with ⟨⟨signed, cache, keypair⟩, bad⟩
  rcases t with (n | mc) | m
  · simp [fs_simp, map_eq_bind_pure_comp]
  · cases hcache : cache mc with
    | some ch =>
        simp [fs_simp, hcache, map_eq_bind_pure_comp]
    | none =>
        simp [fs_simp, hcache, map_eq_bind_pure_comp]
  · cases hkp : keypair with
    | none =>
        simp only [add_apply_inr, fs_simp,
          bind_pure_comp, map_eq_bind_pure_comp, Prod.mk.eta, StateT.run_mk,
          bind_assoc]
        refine bind_congr (m := ProbComp) fun ps => ?_
        refine bind_congr (m := ProbComp) fun cp => ?_
        rcases cp with ⟨c, prv⟩
        cases hcache : cache (m, c) with
        | some ch =>
            simp [fs_simp, map_eq_bind_pure_comp]
        | none =>
            simp [fs_simp, map_eq_bind_pure_comp, bind_assoc]
    | some ps =>
        rcases ps with ⟨pk, sk⟩
        simp only [add_apply_inr, fs_simp,
          bind_pure_comp, map_eq_bind_pure_comp, Prod.mk.eta, StateT.run_mk,
          bind_assoc]
        refine bind_congr (m := ProbComp) fun cp => ?_
        rcases cp with ⟨c, prv⟩
        cases hcache : cache (m, c) with
        | some ch =>
            simp [fs_simp, map_eq_bind_pure_comp, bind_assoc]
        | none =>
            simp [fs_simp, map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma cmaReal_cmaSignLog_liftM_run_eq_cmaRealSourceFullSum_run
    {α : Type}
    (oa : SourceCmaComp (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) α)
    (pk : Stmt) (sk : Wit) (signed : List M)
    (cache : RoCache M Commit Chal) :
    (simulateQ (cmaReal M Commit Chal σ hr)
        ((simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
          (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run
          signed)).run
        (((signed, cache, some (pk, sk)), false) :
          CmaState M Commit Chal Stmt Wit) =
      (fun z : α × CmaState M Commit Chal Stmt Wit =>
        ((z.1, z.2.1.1), z.2)) <$>
        (simulateQ (cmaRealSourceFullSum M Commit Chal σ hr) oa).run
          (((signed, cache, some (pk, sk)), false) :
            CmaState M Commit Chal Stmt Wit) := by
  let st : CmaState M Commit Chal Stmt Wit :=
    (((signed, cache, some (pk, sk)), false))
  have hlogged :
      (simulateQ (cmaReal M Commit Chal σ hr)
          ((simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
            (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run
            signed)).run st =
        (fun z : α × (List M × CmaState M Commit Chal Stmt Wit) =>
          ((z.1, z.2.1), z.2.2)) <$>
          (simulateQ (cmaRealLoggedProdImpl (σ := σ) (hr := hr)
            (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
            (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run
            (signed, st) := by
    simpa [cmaRealLoggedProdImpl] using
      OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
        (outer := cmaReal M Commit Chal σ hr)
        (inner := cmaSignLogImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
        (oa := (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α))
        (s := signed) (q := st)
  have happend :
      (simulateQ (cmaRealAppendProdImpl (σ := σ) (hr := hr)
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)) oa).run
          (signed, st) =
        Prod.map id (cmaRealAppendProj (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
          (simulateQ (cmaRealSourceFullSum M Commit Chal σ hr) oa).run st := by
    have hrun :=
      OracleComp.map_run_simulateQ_eq_of_query_map_eq
        (impl₁ := cmaRealSourceFullSum M Commit Chal σ hr)
        (impl₂ := cmaRealAppendProdImpl (σ := σ) (hr := hr)
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (proj := cmaRealAppendProj (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit))
        (hproj := fun t s =>
          cmaRealAppendProdImpl_project_step (σ := σ) (hr := hr)
            (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
            (Stmt := Stmt) (Wit := Wit) t s)
        (oa := oa) (s := st)
    simpa [st, cmaRealAppendProj] using hrun.symm
  rw [hlogged]
  rw [cmaRealLoggedProdImpl_liftAdv_run (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (oa := oa) (st := (signed, st))]
  rw [happend]
  simp [st, cmaRealAppendProj, Functor.map_map]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- The post-keygen freshness endpoint is the same Boolean experiment as running
`signedFreshAdv` in the direct stateful CMA game. -/
theorem statefulPostKeygenFreshAdvantage_eq_cmaRealRunProb_signedFreshAdv
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    statefulPostKeygenFreshAdvantage σ hr M adv =
      Pr[= true | (cmaReal M Commit Chal σ hr).runProb
        (cmaInit M Commit Chal Stmt Wit) (signedFreshAdv σ hr M adv)] := by
  unfold statefulPostKeygenFreshAdvantage
  have hpost :
      ((hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
        postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2) =
      ((hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
        postKeygenFreshAppendProb (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2) := by
    apply bind_congr
    intro ps
    exact (postKeygenFreshAppendProb_eq_statefulPostKeygenFreshProb (σ := σ)
      (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) adv ps.1 ps.2).symm
  rw [hpost]
  apply congrArg (fun p => Pr[= true | p])
  unfold QueryImpl.Stateful.runProb QueryImpl.Stateful.run signedFreshAdv
    signedCandidateAdv candidateAdv postKeygenFreshAppendProb postKeygenCandidateAdv
  simp only [StateT.run'_eq, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind,
    bind_assoc]
  simp only [postKeygenAppendImpl, StateT.run_pure,
    bind_pure_comp, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind,
    cmaSignLogImpl, bind_pure, CompTriple.comp_eq, StateT.run_monadLift, monadLift_self,
    simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    cmaReal, Prod.mk.eta, simulateQ_pure, cmaInit, StateT.run_bind, StateT.run_mk]
  apply bind_congr
  intro ps
  rw [postKeygenAppendImpl_run_eq_cmaRealSourceFullSum_run (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (oa := adv.main ps.1) ps.1 ps.2 ([] : List M) (∅ : RoCache M Commit Chal)]
  rw [cmaReal_cmaSignLog_liftM_run_eq_cmaRealSourceFullSum_run (σ := σ)
    (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) (oa := adv.main ps.1) ps.1 ps.2
    ([] : List M) (∅ : RoCache M Commit Chal)]
  simp only [Prod.mk.eta, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr (m := ProbComp) fun z => ?_
  rcases z with ⟨out, st⟩
  rcases out with ⟨msg, sig⟩
  rcases sig with ⟨c, resp⟩
  rcases st with ⟨⟨signed, cache, keypair⟩, bad⟩
  letI : HasQuery (roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp) :=
    (randomOracle : QueryImpl (roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp)).toHasQuery
  rw [simulateQ_cmaReal_liftM_fsRo_eq_sourceCma (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt)
    (oa := (SourceSigAlg (σ := σ) (hr := hr) (M := M)).verify ps.1 msg (c, resp))]
  cases hcache : cache (msg, c) with
  | some ch =>
      have hleft :
          (((_root_.FiatShamir
              (m := StateT (RoCache M Commit Chal) ProbComp) σ hr M).verify
              ps.1 msg (c, resp)).run cache >>=
            fun a => pure (!decide (msg ∈ signed) && a.1)) =
            pure (!decide (msg ∈ signed) && σ.verify ps.1 c ch resp) := by
        simp [FiatShamir, hcache]
      have hright :
          ((simulateQ (cmaRealSourceFullSum M Commit Chal σ hr)
              ((SourceSigAlg (σ := σ) (hr := hr) (M := M)).verify
                ps.1 msg (c, resp))).run
            (((signed, cache, keypair), bad) :
              CmaState M Commit Chal Stmt Wit) >>=
            fun a => pure (!decide (msg ∈ signed) && a.1)) =
            pure (!decide (msg ∈ signed) && σ.verify ps.1 c ch resp) := by
        have hrun :
            (simulateQ (cmaRealSourceFullSum M Commit Chal σ hr)
              ((SourceSigAlg (σ := σ) (hr := hr) (M := M)).verify
                ps.1 msg (c, resp))).run
              (((signed, cache, keypair), bad) :
                CmaState M Commit Chal Stmt Wit) =
              pure (σ.verify ps.1 c ch resp,
                (((signed, cache, keypair), bad) :
                  CmaState M Commit Chal Stmt Wit)) := by
          simp only [SourceSigAlg, FiatShamir, HasQuery.instOfMonadLift_query,
            bind_pure_comp, liftM_map, simulateQ_map, StateT.run_map]
          rw [cmaRealSourceFullSum_lift_ro_query_run (σ := σ) (hr := hr)
            (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
            (Stmt := Stmt) (Wit := Wit) (mc := (msg, c))]
          simp [cmaRealSourceFullSum, cmaRealSourceFull, hcache]
        rw [hrun]
        simp
      simpa [map_eq_bind_pure_comp] using hleft.trans hright.symm
  | none =>
      have hleft :
          (((_root_.FiatShamir
              (m := StateT (RoCache M Commit Chal) ProbComp) σ hr M).verify
              ps.1 msg (c, resp)).run cache >>=
            fun a => pure (!decide (msg ∈ signed) && a.1)) =
            (($ᵗ Chal) >>= fun ch =>
              pure (!decide (msg ∈ signed) && σ.verify ps.1 c ch resp)) := by
        simp [FiatShamir, hcache, uniformSampleImpl, map_eq_bind_pure_comp,
          bind_assoc]
      have hright :
          ((simulateQ (cmaRealSourceFullSum M Commit Chal σ hr)
              ((SourceSigAlg (σ := σ) (hr := hr) (M := M)).verify
                ps.1 msg (c, resp))).run
            (((signed, cache, keypair), bad) :
              CmaState M Commit Chal Stmt Wit) >>=
            fun a => pure (!decide (msg ∈ signed) && a.1)) =
            (($ᵗ Chal) >>= fun ch =>
              pure (!decide (msg ∈ signed) && σ.verify ps.1 c ch resp)) := by
        simp only [SourceSigAlg, FiatShamir, HasQuery.instOfMonadLift_query,
          bind_pure_comp, map_eq_bind_pure_comp, liftM_bind, Function.comp_apply, liftM_pure,
          simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc,
          pure_bind]
        rw [cmaRealSourceFullSum_lift_ro_query_run (σ := σ) (hr := hr)
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
          (Stmt := Stmt) (Wit := Wit) (mc := (msg, c))]
        simp [cmaRealSourceFullSum, cmaRealSourceFull, hcache,
          map_eq_bind_pure_comp, bind_assoc]
      simpa [map_eq_bind_pure_comp] using hleft.trans hright.symm

/-- Fixed-key public post-keygen experiment in the WriterT signing-log form. -/
@[reducible] private noncomputable def postKeygenFreshWriterComp
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) (sk : Wit) :
    OracleComp (unifSpec + roSpec M Commit Chal) Bool := by
  letI : DecidableEq (Commit × Resp) := Classical.decEq _
  let so := (SourceSigAlg (σ := σ) (hr := hr) (M := M)).signingOracle pk sk
  let baseW : QueryImpl (unifSpec + roSpec M Commit Chal)
      (WriterT (QueryLog (signSpec M Commit Resp))
        (OracleComp (unifSpec + roSpec M Commit Chal))) :=
    (HasQuery.toQueryImpl (spec := unifSpec + roSpec M Commit Chal)
      (m := OracleComp (unifSpec + roSpec M Commit Chal))).liftTarget _
  let implW : QueryImpl (SourceCmaSpec (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp))
      (WriterT (QueryLog (signSpec M Commit Resp))
        (OracleComp (unifSpec + roSpec M Commit Chal))) :=
    baseW + so
  exact do
    let ((msg, sig), log) ← (simulateQ implW (adv.main pk)).run
    let verified ← (SourceSigAlg (σ := σ) (hr := hr) (M := M)).verify pk msg sig
    pure (!log.wasQueried msg && verified)

@[reducible] private noncomputable def postKeygenFreshWriterProb
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) (sk : Wit) : ProbComp Bool := by
  let runtime := fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
  letI : HasQuery (unifSpec + roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp) := runtime.toHasQuery
  let so := cmaRealFixedSign (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) σ hr pk sk
  let baseW : QueryImpl (unifSpec + roSpec M Commit Chal)
      (WriterT (QueryLog (signSpec M Commit Resp))
        (StateT (RoCache M Commit Chal) ProbComp)) :=
    runtime.liftTarget _
  let implW : QueryImpl (SourceCmaSpec (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp))
      (WriterT (QueryLog (signSpec M Commit Resp))
        (StateT (RoCache M Commit Chal) ProbComp)) :=
    baseW + QueryImpl.withLogging so
  letI : HasQuery (roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp) :=
    (randomOracle : QueryImpl (roSpec M Commit Chal) _).toHasQuery
  exact
    (((fun z : (M × (Commit × Resp)) × QueryLog (signSpec M Commit Resp) =>
        (z.1, z.2.map (fun e => e.1))) <$>
        ((simulateQ implW (adv.main pk)).run :
          StateT (RoCache M Commit Chal) ProbComp
            ((M × (Commit × Resp)) × QueryLog (signSpec M Commit Resp)))) >>= fun z => do
        let msg := z.1.1
        let sig := z.1.2
        let signed := z.2
        let verified ←
          (FiatShamir (m := StateT (RoCache M Commit Chal) ProbComp) σ hr M).verify
            pk msg sig
        pure (!decide (msg ∈ signed) && verified)).run' ∅

omit [SampleableType Stmt] [SampleableType Wit] in
private theorem postKeygenWriterLog_eq_inputLog
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) (sk : Wit) :
    let runtime := fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
    letI : HasQuery (unifSpec + roSpec M Commit Chal)
        (StateT (RoCache M Commit Chal) ProbComp) := runtime.toHasQuery
    let so := cmaRealFixedSign (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) σ hr pk sk
    let baseW : QueryImpl (unifSpec + roSpec M Commit Chal)
        (WriterT (QueryLog (signSpec M Commit Resp))
          (StateT (RoCache M Commit Chal) ProbComp)) :=
      (HasQuery.toQueryImpl (spec := unifSpec + roSpec M Commit Chal)
        (m := StateT (RoCache M Commit Chal) ProbComp)).liftTarget _
    let implW : QueryImpl (SourceCmaSpec (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp))
        (WriterT (QueryLog (signSpec M Commit Resp))
          (StateT (RoCache M Commit Chal) ProbComp)) :=
      baseW + QueryImpl.withLogging so
    ((fun z : (M × (Commit × Resp)) × QueryLog (signSpec M Commit Resp) =>
        (z.1, z.2.map (fun e => e.1))) <$>
        ((simulateQ implW (adv.main pk)).run :
          StateT (RoCache M Commit Chal) ProbComp
            ((M × (Commit × Resp)) × QueryLog (signSpec M Commit Resp)))) =
      ((simulateQ
          (postKeygenAppendImpl (σ := σ) (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
          (adv.main pk)).run [] :
        StateT (RoCache M Commit Chal) ProbComp
          ((M × (Commit × Resp)) × List M)) := by
  let runtime := fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
  letI : HasQuery (unifSpec + roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp) := runtime.toHasQuery
  let so := cmaRealFixedSign (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) σ hr pk sk
  simpa [runtime, so, postKeygenAppendImpl] using
    (QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
      (spec₀ := unifSpec + roSpec M Commit Chal)
      (loggedSpec := signSpec M Commit Resp)
      (m₀ := StateT (RoCache M Commit Chal) ProbComp)
      so (adv.main pk) ([] : List M))

omit [SampleableType Stmt] [SampleableType Wit] in
private theorem postKeygenFreshWriterProb_eq_postKeygenFreshProb
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) (sk : Wit) :
    postKeygenFreshWriterProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk =
    postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk := by
  unfold postKeygenFreshWriterProb
  let runtime := fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
  letI : HasQuery (unifSpec + roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp) := runtime.toHasQuery
  let so := cmaRealFixedSign (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) σ hr pk sk
  letI : HasQuery (roSpec M Commit Chal)
      (StateT (RoCache M Commit Chal) ProbComp) :=
    (randomOracle : QueryImpl (roSpec M Commit Chal) _).toHasQuery
  let baseW : QueryImpl (unifSpec + roSpec M Commit Chal)
      (WriterT (QueryLog (signSpec M Commit Resp))
        (StateT (RoCache M Commit Chal) ProbComp)) :=
    (HasQuery.toQueryImpl (spec := unifSpec + roSpec M Commit Chal)
      (m := StateT (RoCache M Commit Chal) ProbComp)).liftTarget _
  let implW : QueryImpl (SourceCmaSpec (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp))
      (WriterT (QueryLog (signSpec M Commit Resp))
        (StateT (RoCache M Commit Chal) ProbComp)) :=
    baseW + QueryImpl.withLogging so
  let mappedW : StateT (RoCache M Commit Chal) ProbComp
      ((M × (Commit × Resp)) × List M) :=
    (fun z : (M × (Commit × Resp)) × QueryLog (signSpec M Commit Resp) =>
      (z.1, z.2.map (fun e => e.1))) <$> ((simulateQ implW (adv.main pk)).run :
        StateT (RoCache M Commit Chal) ProbComp
          ((M × (Commit × Resp)) × QueryLog (signSpec M Commit Resp)))
  let appendS : StateT (RoCache M Commit Chal) ProbComp
      ((M × (Commit × Resp)) × List M) :=
    (simulateQ (postKeygenAppendImpl (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
      (adv.main pk)).run []
  let kont : ((M × (Commit × Resp)) × List M) →
      StateT (RoCache M Commit Chal) ProbComp Bool := fun z => do
    let msg := z.1.1
    let sig := z.1.2
    let signed := z.2
    let verified ←
      (FiatShamir (m := StateT (RoCache M Commit Chal) ProbComp) σ hr M).verify
        pk msg sig
    pure (!decide (msg ∈ signed) && verified)
  have hlog : mappedW = appendS := by
    simpa [mappedW, appendS, implW, baseW, postKeygenAppendImpl, runtime, so] using
      (postKeygenWriterLog_eq_inputLog (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk)
  have hprod :
      (appendS >>= kont).run' (∅ : RoCache M Commit Chal) =
        postKeygenFreshAppendProb (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk := by
    unfold postKeygenFreshAppendProb
    simp [appendS, kont]
  change (mappedW >>= kont).run' (∅ : RoCache M Commit Chal) =
    postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk
  rw [hlog, hprod]
  exact postKeygenFreshAppendProb_eq_statefulPostKeygenFreshProb (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma fsBaseImpl_writerTMapBase_signingOracle_eq
    (pk : Stmt) (sk : Wit) :
    let baseW : QueryImpl (unifSpec + roSpec M Commit Chal)
        (WriterT (QueryLog (signSpec M Commit Resp))
          (OracleComp (unifSpec + roSpec M Commit Chal))) :=
      (HasQuery.toQueryImpl (spec := unifSpec + roSpec M Commit Chal)
        (m := OracleComp (unifSpec + roSpec M Commit Chal))).liftTarget _
    let implW : QueryImpl (SourceCmaSpec (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp))
        (WriterT (QueryLog (signSpec M Commit Resp))
          (OracleComp (unifSpec + roSpec M Commit Chal))) :=
      baseW + (SourceSigAlg (σ := σ) (hr := hr) (M := M)).signingOracle pk sk
    let baseS : QueryImpl (unifSpec + roSpec M Commit Chal)
        (WriterT (QueryLog (signSpec M Commit Resp))
          (StateT (RoCache M Commit Chal) ProbComp)) :=
      (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).liftTarget _
    let implS : QueryImpl (SourceCmaSpec (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp))
        (WriterT (QueryLog (signSpec M Commit Resp))
          (StateT (RoCache M Commit Chal) ProbComp)) :=
      baseS +
        QueryImpl.withLogging
          (cmaRealFixedSign (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ hr pk sk)
    (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).writerTMapBase implW =
      implS := by
  funext t
  rcases t with (n | mc) | m
  · ext cache
    simp [QueryImpl.writerTMapBase, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, fsBaseImpl, unifFwdImpl]
  · ext cache
    simp [QueryImpl.writerTMapBase, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, fsBaseImpl, unifFwdImpl, randomOracle]
  · ext cache
    simp [QueryImpl.writerTMapBase, SignatureAlg.signingOracle,
      QueryImpl.withLogging_apply, cmaRealFixedSign, SourceSigAlg, FiatShamir,
      fsBaseImpl, randomOracle, StateT.run_bind, roSim.run_liftM]

omit [SampleableType Stmt] [SampleableType Wit] in
private theorem simulateQ_fsBaseImpl_postKeygenFreshWriterComp_run'_eq
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) (sk : Wit) :
    (simulateQ (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal))
        (postKeygenFreshWriterComp (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk)).run'
        (∅ : RoCache M Commit Chal) =
      postKeygenFreshWriterProb (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk := by
  unfold postKeygenFreshWriterComp postKeygenFreshWriterProb
  let baseW : QueryImpl (unifSpec + roSpec M Commit Chal)
      (WriterT (QueryLog (signSpec M Commit Resp))
        (OracleComp (unifSpec + roSpec M Commit Chal))) :=
    (HasQuery.toQueryImpl (spec := unifSpec + roSpec M Commit Chal)
      (m := OracleComp (unifSpec + roSpec M Commit Chal))).liftTarget _
  let implW : QueryImpl (SourceCmaSpec (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp))
      (WriterT (QueryLog (signSpec M Commit Resp))
        (OracleComp (unifSpec + roSpec M Commit Chal))) :=
    baseW + (SourceSigAlg (σ := σ) (hr := hr) (M := M)).signingOracle pk sk
  let baseS : QueryImpl (unifSpec + roSpec M Commit Chal)
      (WriterT (QueryLog (signSpec M Commit Resp))
        (StateT (RoCache M Commit Chal) ProbComp)) :=
    (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).liftTarget _
  let implS : QueryImpl (SourceCmaSpec (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp))
      (WriterT (QueryLog (signSpec M Commit Resp))
        (StateT (RoCache M Commit Chal) ProbComp)) :=
    baseS +
      QueryImpl.withLogging
        (cmaRealFixedSign (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ hr pk sk)
  have hmap :
      (fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal)).writerTMapBase implW =
        implS := by
    simpa [baseW, implW, baseS, implS] using
      (fsBaseImpl_writerTMapBase_signingOracle_eq (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) pk sk)
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  rw [QueryImpl.simulateQ_writerTMapBase_run
    (outer := fsBaseImpl (M := M) (Commit := Commit) (Chal := Chal))
    (inner := implW) (oa := adv.main pk)]
  rw [hmap]
  letI : DecidableEq (Commit × Resp) := Classical.decEq _
  conv_lhs =>
    simp [implS, baseS, fsBaseImpl, cmaRealFixedSign, SourceSigAlg, FiatShamir,
      randomOracle, QueryLog.wasQueried_eq_decide_mem_map_fst, StateT.run_bind]
  conv_rhs =>
    simp [implS, baseS, fsBaseImpl, cmaRealFixedSign, SourceSigAlg, FiatShamir,
      randomOracle, QueryLog.wasQueried_eq_decide_mem_map_fst, StateT.run_bind]
omit [SampleableType Stmt] [SampleableType Wit] in
private theorem runtime_evalDist_postKeygenFreshWriterComp_eq
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (pk : Stmt) (sk : Wit) :
    (_root_.FiatShamir.runtime M).evalDist
        (postKeygenFreshWriterComp (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk) =
      𝒟[postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk] := by
  rw [_root_.FiatShamir.runtime_eq_runtimeWithCache_empty (M := M)]
  rw [runtimeWithCache_evalDist_eq_fsBaseImpl (M := M) (Commit := Commit)
    (Chal := Chal) (cache := (∅ : RoCache M Commit Chal))]
  rw [simulateQ_fsBaseImpl_postKeygenFreshWriterComp_run'_eq (σ := σ)
    (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) adv pk sk]
  rw [postKeygenFreshWriterProb_eq_postKeygenFreshProb (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv pk sk]

omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq Commit] in
/-- The public EUF-CMA experiment factors into keygen followed by the fixed-key
WriterT post-keygen computation. -/
private theorem unforgeableExp_eq_runtime_bind_postKeygenFreshWriterComp
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    SignatureAlg.unforgeableExp (_root_.FiatShamir.runtime M) adv =
      (_root_.FiatShamir.runtime M).evalDist
        ((liftM (hr.gen : ProbComp (Stmt × Wit))) >>= fun ps =>
          postKeygenFreshWriterComp (σ := σ) (hr := hr) (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2) := by
  unfold SignatureAlg.unforgeableExp postKeygenFreshWriterComp
  simp only [runtime_eq_runtimeWithCache_empty, FiatShamir, HasQuery.instOfMonadLift_query,
    liftM, bind_pure_comp, Functor.map_map, roSpec, signSpec]
  congr 1
  refine bind_congr (m := OracleComp (unifSpec + roSpec M Commit Chal)) fun ps => ?_
  rcases ps with ⟨pk, sk⟩
  simp only [QueryLog.wasQueried_eq_decide_mem_map_fst, List.mem_map, Sigma.exists,
    exists_and_right, Prod.exists, exists_eq_right]
  refine bind_congr (m := OracleComp (unifSpec + roSpec M Commit Chal)) fun z => ?_
  congr
  funext a
  congr

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Public EUF-CMA advantage in the shared fixed-key post-keygen normal form. -/
theorem publicUnforgeableAdvantage_eq_statefulPostKeygenFreshAdvantage
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    publicUnforgeableAdvantage σ hr M adv =
      statefulPostKeygenFreshAdvantage σ hr M adv := by
  unfold publicUnforgeableAdvantage SignatureAlg.unforgeableAdv.advantage
    statefulPostKeygenFreshAdvantage
  rw [unforgeableExp_eq_runtime_bind_postKeygenFreshWriterComp (σ := σ)
    (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) adv]
  rw [_root_.FiatShamir.runtime_evalDist_bind_liftComp (M := M)
    (oa := (hr.gen : ProbComp (Stmt × Wit)))
    (rest := fun ps =>
      postKeygenFreshWriterComp (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2)]
  change
    Pr[= true | (𝒟[(hr.gen : ProbComp (Stmt × Wit))] >>= fun ps =>
      (_root_.FiatShamir.runtime M).evalDist
        (postKeygenFreshWriterComp (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2))] =
    Pr[= true | 𝒟[(((hr.gen : ProbComp (Stmt × Wit)) >>= fun ps =>
      postKeygenFreshProb (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2) :
      ProbComp Bool)]]
  rw [evalDist_bind]
  apply congrArg (fun p => Pr[= true | p])
  refine bind_congr fun ps => ?_
  rw [runtime_evalDist_postKeygenFreshWriterComp_eq (σ := σ) (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv ps.1 ps.2]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Public compatibility for the legacy `SignatureAlg` endpoint. -/
theorem publicCompatible
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) :
    PublicCompatible σ hr M adv := by
  unfold PublicCompatible
  rw [publicUnforgeableAdvantage_eq_statefulPostKeygenFreshAdvantage (σ := σ)
    (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) adv]
  rw [← statefulCmaFreshAdvantage_eq_statefulPostKeygenFreshAdvantage (σ := σ)
    (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) adv]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Public compatibility, in inequality form, against the direct stateful
freshness experiment. -/
theorem publicUnforgeableAdvantage_le_statefulCmaFresh
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (hCompat : PublicCompatible σ hr M adv) :
    adv.advantage (_root_.FiatShamir.runtime M) ≤
      statefulCmaFreshAdvantage σ hr M adv := by
  rw [← hCompat]
  rfl

end FiatShamir.Stateful
