/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.Defs

/-!
# PRF Tag/Reader Protocol — Authentication

The auth→PRF reduction and authentication security for the tag/reader protocol. Defines the
distinguisher `authToPRFReduction` that turns an authentication adversary into a PRF adversary,
the random-function authentication experiment `authRFExp`, and proves:

- the authentication adversary's success probability is bounded by PRF advantage plus the
  random-function world (`authExp_le_prfAdvantage_add_authRF`);
- the look-up-only ideal world is unwinnable (`authIdealExp_eq_zero`);
- `authRFExp` equals the directly-defined random-function experiment `authRFDirectExp`
  (`authRFExp_eq_authRFDirectExp`).
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section AuthReduction

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest]

/-- Query the PRF oracle on `(tag, nonce)` to obtain its digest. -/
private def authPRFQuery (tag : TagId) (nonce : Nonce) :
    OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest :=
  (unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr (tag, nonce))

/-- Tag-oracle implementation that samples a nonce uniformly and queries the PRF oracle for
the authenticator. Models `authTagQueryImpl` with the hash replaced by a PRF oracle call. -/
def authToPRFTagImpl :
    QueryImpl (TagId →ₒ TagTranscript Nonce Digest)
      (StateT (AuthState TagId Nonce Digest)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) := fun tag => do
  let st ← get
  let nonce ← (OracleComp.liftComp (spec := unifSpec)
    (superSpec := unifSpec + ((TagId × Nonce) →ₒ Digest)) ($ᵗ Nonce) :
    OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Nonce)
  let auth ← authPRFQuery (TagId := TagId) (Nonce := Nonce) (Digest := Digest) tag nonce
  let transcript : TagTranscript Nonce Digest := ⟨nonce, auth⟩
  set { st with honestOutputs := insert (tag, transcript) st.honestOutputs }
  return transcript

/-- Reader-oracle implementation that queries the PRF oracle for every tag at the transcript's
nonce in order to identify the matching tags. Models `authReaderQueryImpl` with the hash
replaced by a PRF oracle call. -/
noncomputable def authToPRFReaderImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (AuthState TagId Nonce Digest)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) := fun transcript => do
  let st ← get
  let pairs ←
    (Finset.univ : Finset TagId).toList.mapM
      (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
      (fun tag => do
        let d ← authPRFQuery (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          tag transcript.nonce
        return (tag, d))
  let accepted : Bool := decide (∃ p ∈ pairs, p.2 = transcript.auth)
  let newForged : Finset TagId :=
    ((pairs.filter fun p => decide (p.2 = transcript.auth ∧
        (p.1, transcript) ∉ st.honestOutputs)).map Prod.fst).toFinset
  set { st with readerForged := st.readerForged ∪ (newForged.image (·, transcript)) }
  return ReaderReply.ofBool accepted

/-- Combined oracle implementation that simulates the authentication game while hashing through
the PRF oracle. -/
noncomputable def authToPRFQueryImpl :
    QueryImpl (AuthOracleSpec TagId Nonce Digest)
      (StateT (AuthState TagId Nonce Digest)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) :=
  authToPRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest) +
    authToPRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)

/-- PRF distinguisher derived from an authentication adversary. The reduction runs the auth game
with every call to `prfs.evalMultiple k tag nonce` replaced by a query to the PRF oracle on
`(tag, nonce)`. It returns `true` exactly when the reader records a forged acceptance during the
simulation. -/
noncomputable def authToPRFReduction
    (adversary : AuthAdversary TagId Nonce Digest) :
    PRFScheme.PRFAdversary (TagId × Nonce) Digest :=
  ((simulateQ (authToPRFQueryImpl (TagId := TagId)) adversary).run AuthState.init >>=
    fun p => pure (decide (p.2.readerForged ≠ ∅)) :
    OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Bool)

end AuthReduction

section Theorems

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- Random-function authentication experiment. Defined as the ideal PRF experiment applied to the
`authToPRFReduction` distinguisher: every call to `prfs.evalMultiple` in `authExp` is replaced by a
lazy random oracle on `(tag, nonce)` consistent across both tag and reader oracle queries.

This is the natural PRF-replacement ideal world (in contrast to the look-up-only `authIdealExp`,
which is the stronger ideal world where the reader cannot make oracle queries). Random-function
matches against an adversary-submitted transcript contribute to `Pr[authRFExp]`, so it is generally
nonzero. -/
noncomputable def authRFExp
    (adversary : AuthAdversary TagId Nonce Digest) : ProbComp Bool :=
  PRFScheme.prfIdealExp (authToPRFReduction adversary)

omit [Fintype TagId] [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Per-tag-query equivalence: running the reduction's tag-oracle implementation through the real
PRF simulator produces the same distribution and final state as the real auth-game tag oracle
parameterised by `prfs.evalMultiple k`. -/
private lemma simulateQ_prfReal_authToPRFTagImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (tag : TagId) (s : AuthState TagId Nonce Digest) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((authToPRFTagImpl (TagId := TagId) tag).run s) =
      (authTagQueryImpl (fun tag nonce => prfs.evalMultiple k tag nonce) tag).run s := by
  let so : QueryImpl ((TagId × Nonce) →ₒ Digest) ProbComp :=
    fun d => pure (prfs.multiplePRFScheme.eval k d)
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp :=
    HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + so
  have hleft : ∀ {α : Type} (oa : ProbComp α),
      simulateQ impl (liftComp oa (unifSpec + ((TagId × Nonce) →ₒ Digest))) = oa := by
    intro α oa
    simp [impl, QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_toQueryImpl]
  unfold authToPRFTagImpl authTagQueryImpl authPRFQuery
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    bind_pure_comp, pure_bind]
  change @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
  simp only [simulateQ_bind, simulateQ_map, monadLift_eq_self,
    hleft]
  rfl

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Per-reader-query equivalence: running the reduction's reader-oracle implementation through the
real PRF simulator produces the same distribution and final state as the real auth-game reader
oracle parameterised by `prfs.evalMultiple k`. -/
private lemma simulateQ_prfReal_authToPRFReaderImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (transcript : TagTranscript Nonce Digest) (s : AuthState TagId Nonce Digest) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((authToPRFReaderImpl (TagId := TagId) transcript).run s) =
      (authReaderQueryImpl (fun tag nonce => prfs.evalMultiple k tag nonce) transcript).run s := by
  let so : QueryImpl ((TagId × Nonce) →ₒ Digest) ProbComp :=
    fun d => pure (prfs.multiplePRFScheme.eval k d)
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp :=
    HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + so
  have hquery : ∀ (d : TagId × Nonce),
      simulateQ impl
        (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr d)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) _) =
      (pure (prfs.evalMultiple k d.1 d.2) : ProbComp Digest) := by
    intro d
    rw [simulateQ_spec_query]
    change impl (Sum.inr d) = _
    simp [impl, so, QueryImpl.add_apply_inr, TagReaderPRFs.multiplePRFScheme]
  have hquery_pair : ∀ (tag : TagId),
      simulateQ impl
        (Prod.mk tag <$> authPRFQuery (TagId := TagId) tag transcript.nonce :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) (TagId × Digest)) =
        pure (tag, prfs.evalMultiple k tag transcript.nonce) := by
    intro tag
    change @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
    rw [simulateQ_map, show @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _
      impl _ (authPRFQuery (TagId := TagId) tag transcript.nonce) =
      pure (prfs.evalMultiple k tag transcript.nonce) from hquery (tag, transcript.nonce)]
    rfl
  have hmapM :
      simulateQ impl
        ((Finset.univ : Finset TagId).toList.mapM
          (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
          (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) tag transcript.nonce)) =
      pure ((Finset.univ : Finset TagId).toList.map
        fun tag => (tag, prfs.evalMultiple k tag transcript.nonce)) := by
    change @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
    rw [simulateQ_list_mapM]
    induction (Finset.univ : Finset TagId).toList with
    | nil => rfl
    | cons t ts ih =>
      rw [List.mapM_cons, hquery_pair, pure_bind, ih, pure_bind]
      rfl
  have hForged :
      ((((Finset.univ : Finset TagId).toList.map
              fun tag => (tag, prfs.evalMultiple k tag transcript.nonce)).filter
            fun p => decide (p.2 = transcript.auth ∧ (p.1, transcript) ∉ s.honestOutputs)).map
          Prod.fst).toFinset =
        (Finset.univ : Finset TagId).filter fun tag =>
          prfs.evalMultiple k tag transcript.nonce = transcript.auth ∧
            (tag, transcript) ∉ s.honestOutputs := by
    ext tag
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_toList, Prod.exists]
    aesop
  have hAccept :
      decide (∃ p ∈ (Finset.univ : Finset TagId).toList.map
        fun tag => (tag, prfs.evalMultiple k tag transcript.nonce),
        p.2 = transcript.auth) =
      decide (∃ tag, prfs.evalMultiple k tag transcript.nonce = transcript.auth) := by
    congr 1
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    aesop
  unfold authToPRFReaderImpl authReaderQueryImpl
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    bind_pure_comp, pure_bind]
  change @simulateQ _ (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp _ impl _ _ = _
  simp only [simulateQ_bind, simulateQ_map, monadLift_eq_self,
    hmapM, pure_bind, map_pure]
  rw [hForged, hAccept]
  rfl

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Inductive helper: simulating the auth-game adversary through the reduction's query
implementation and then through the real PRF query implementation is the same, state-by-state,
as simulating it directly through the real authentication query implementation with the hash set
to `prfs.evalMultiple k`. Each tag/reader query case follows by unfolding both sides and noting
that `prfRealQueryImpl prfs.multiplePRFScheme k` returns `prfs.evalMultiple k tag nonce` on the
`Sum.inr (tag, nonce)` query. -/
private theorem simulateQ_prfReal_authToPRFQueryImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (adversary : AuthAdversary TagId Nonce Digest)
    (s : AuthState TagId Nonce Digest) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((simulateQ (authToPRFQueryImpl (TagId := TagId)) adversary).run s) =
      (simulateQ (authRealQueryImpl (fun tag nonce => prfs.evalMultiple k tag nonce))
        adversary).run s :=
  simulateQ_StateT_compose (authToPRFQueryImpl (TagId := TagId))
    (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
    (authRealQueryImpl (fun tag nonce => prfs.evalMultiple k tag nonce))
    (fun q s' => by
      rcases q with tag | transcript
      · exact simulateQ_prfReal_authToPRFTagImpl_run prfs k tag s'
      · exact simulateQ_prfReal_authToPRFReaderImpl_run prfs k transcript s')
    adversary s

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The PRF reduction faithfully reproduces the real authentication experiment: under the real
PRF, each oracle query at `(tag, nonce)` returns `prfs.evalMultiple k tag nonce`, so the reduction
runs exactly the same game as `authExp`. -/
theorem prfRealExp_authToPRFReduction_eq_authExp
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest) :
    Pr[= true | PRFScheme.prfRealExp prfs.multiplePRFScheme
        (authToPRFReduction adversary)] =
      Pr[= true | authExp prfs adversary] := by
  suffices h : PRFScheme.prfRealExp prfs.multiplePRFScheme (authToPRFReduction adversary) =
      authExp prfs adversary by rw [h]
  unfold PRFScheme.prfRealExp authExp authToPRFReduction
  refine bind_congr (m := ProbComp) fun k => ?_
  change simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
      ((simulateQ authToPRFQueryImpl adversary).run AuthState.init >>=
        fun p => pure (decide (p.2.readerForged ≠ ∅))) = _
  rw [simulateQ_bind,
    simulateQ_prfReal_authToPRFQueryImpl_run prfs k adversary AuthState.init]
  refine bind_congr fun p => ?_
  rw [simulateQ_pure]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Authentication reduction statement: the success probability of the active-authentication
adversary is bounded by the PRF distinguishing advantage of the canonical reduction plus the
"random-function" experiment's success probability `authRFExp`.

The conceptually simpler look-up-only ideal world `authIdealExp` is provably zero
(`authIdealExp_eq_zero`), but it is too restrictive to serve as the RHS of this kind of PRF
reduction: when the PRF oracle is replaced by a lazy random function, the reader's queries
on unseen `(tag, nonce)` pairs land on uniformly random digests that may coincide with the
adversary's submitted authenticator. `authRFExp` captures exactly that contribution. -/
theorem authExp_le_prfAdvantage_add_authRF
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest) :
    (Pr[= true | authExp prfs adversary]).toReal ≤
      PRFScheme.prfAdvantage prfs.multiplePRFScheme (authToPRFReduction adversary) +
      (Pr[= true | authRFExp adversary]).toReal := by
  have hreal := prfRealExp_authToPRFReduction_eq_authExp prfs adversary
  have hRF : authRFExp adversary = PRFScheme.prfIdealExp (authToPRFReduction adversary) := rfl
  rw [← hreal, hRF]
  unfold PRFScheme.prfAdvantage
  set a := (Pr[= true | PRFScheme.prfRealExp prfs.multiplePRFScheme
    (authToPRFReduction adversary)]).toReal
  set b := (Pr[= true | PRFScheme.prfIdealExp (authToPRFReduction adversary)]).toReal
  have : a - b ≤ |a - b| := le_abs_self _
  linarith

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Existential form of the authentication reduction: there is a PRF adversary whose
distinguishing advantage, added to the random-function world's success probability
`authRFExp`, bounds the authentication adversary's success probability. The witness is
`authToPRFReduction adversary`. -/
theorem exists_prfAdv_authExp_le_prfAdvantage_add_authRF
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : AuthAdversary TagId Nonce Digest) :
    ∃ prfAdv : PRFScheme.PRFAdversary (TagId × Nonce) Digest,
      (Pr[= true | authExp prfs adversary]).toReal ≤
        PRFScheme.prfAdvantage prfs.multiplePRFScheme prfAdv +
        (Pr[= true | authRFExp adversary]).toReal :=
  ⟨authToPRFReduction adversary, authExp_le_prfAdvantage_add_authRF prfs adversary⟩

omit [Nonempty TagId] in
/-- In the ideal authentication world, a forged reader acceptance never occurs. -/
theorem authIdealExp_eq_zero
    (adversary : AuthAdversary TagId Nonce Digest) :
    Pr[= true | authIdealExp adversary] = 0 := by
  let ForgedInv : AuthIdealState TagId Nonce Digest → Prop := fun st => st.readerForged = ∅
  let CacheInv : AuthIdealState TagId Nonce Digest → Prop := fun st =>
    ∀ tag nonce auth, st.responses (tag, nonce) = some auth →
      (tag, ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest)) ∈ st.honestOutputs
  have htagForged :
      QueryImpl.PreservesInv (authIdealTagQueryImpl (TagId := TagId)) ForgedInv := by
    intro tag st hst z hz
    unfold authIdealTagQueryImpl at hz
    simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_eq_self, bind_map_left, support_bind, support_uniformSample, Set.mem_univ,
      Set.iUnion_true, Set.mem_iUnion] at hz
    rcases hz with ⟨i, hz⟩
    cases hresp : st.responses (tag, i) with
    | none =>
      simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
        StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
        support_uniformSample, Set.image_univ, Set.mem_range] at hz
      grind
    | some out =>
      simp only [hresp, StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      grind
  have htagCached :
      QueryImpl.PreservesInv (authIdealTagQueryImpl (TagId := TagId)) CacheInv := by
    intro tag st hst z hz
    unfold authIdealTagQueryImpl at hz
    simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      monadLift_eq_self, bind_map_left, support_bind, support_uniformSample, Set.mem_univ,
      Set.iUnion_true, Set.mem_iUnion] at hz
    rcases hz with ⟨nonce, hz⟩
    cases hresp : st.responses (tag, nonce) with
    | none =>
      simp only [hresp, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self, bind_pure_comp,
        StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
        support_uniformSample, Set.image_univ, Set.mem_range] at hz
      rcases hz with ⟨auth, rfl⟩
      intro tag' nonce' auth' hlookup
      by_cases hkey : (tag', nonce') = (tag, nonce)
      · cases hkey
        simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hlookup
        subst auth'
        simp
      · have hlookup' : st.responses (tag', nonce') = some auth' := by
          simpa [QueryCache.cacheQuery_of_ne (cache := st.responses) auth hkey] using hlookup
        exact Finset.mem_insert_of_mem (hst tag' nonce' auth' hlookup')
    | some out =>
      simp only [hresp, StateT.run_map, StateT.run_set, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      rcases hz with rfl
      intro tag' nonce' auth' hlookup
      exact Finset.mem_insert_of_mem (hst tag' nonce' auth' hlookup)
  have hreaderForged :
      ∀ transcript st, ForgedInv st ∧ CacheInv st →
        ∀ z ∈ support (((authIdealReaderQueryImpl (TagId := TagId)) transcript).run st),
          ForgedInv z.2 := by
    intro transcript st hst z hz
    have hz' := hz
    have hcached := hst.2
    unfold authIdealReaderQueryImpl at hz'
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set,
      map_pure, support_pure, Set.mem_singleton_iff] at hz'
    rcases hz' with rfl
    unfold ForgedInv at *
    have hnewForged :
        ((Finset.univ.filter fun tag =>
          st.responses (tag, transcript.nonce) = some transcript.auth).filter fun tag =>
            (tag, transcript) ∉ st.honestOutputs) = ∅ := by
      ext tag
      constructor
      · intro hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        rcases hmem with ⟨hmatch, hnotmem⟩
        simpa using (False.elim (hnotmem (hcached tag transcript.nonce transcript.auth hmatch)))
      · intro hmem
        simp at hmem
    rw [hst.1, hnewForged, Finset.image_empty, Finset.empty_union]
  have hreaderCached :
      QueryImpl.PreservesInv (authIdealReaderQueryImpl (TagId := TagId)) CacheInv := by
    intro transcript st hst z hz
    unfold authIdealReaderQueryImpl at hz
    simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_map, StateT.run_set,
      map_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with rfl
    exact hst
  have himpl :
      QueryImpl.PreservesInv (authIdealQueryImpl (TagId := TagId))
        (fun st => ForgedInv st ∧ CacheInv st) := by
    intro t st hst z hz
    cases t with
    | inl tag =>
        exact (QueryImpl.PreservesInv.and htagForged htagCached) tag st hst z hz
    | inr transcript =>
        exact ⟨hreaderForged transcript st hst z hz, hreaderCached transcript st hst.2 z hz⟩
  have hfinal :
      ∀ z ∈ support ((simulateQ (authIdealQueryImpl (TagId := TagId))
            adversary).run AuthIdealState.init),
        z.2.readerForged = ∅ := by
    intro z hz
    have hz' :=
      OracleComp.simulateQ_run_preservesInv (authIdealQueryImpl (TagId := TagId))
        (fun st => ForgedInv st ∧ CacheInv st) himpl adversary AuthIdealState.init
        (by simp [ForgedInv, CacheInv, AuthIdealState.init]) z hz
    grind
  refine (probOutput_eq_zero_iff (mx := authIdealExp adversary) (x := true)).mpr ?_
  intro hmem
  rw [authIdealExp, mem_support_bind_iff] at hmem
  grind

/-- Bundle a reduction state `AuthState × QueryCache` into the corresponding `AuthIdealState`:
the lazy random-oracle cache becomes the `responses` table, and the observable logs carry
through unchanged. -/
private def authRFBundle
    (p : AuthState TagId Nonce Digest × ((TagId × Nonce) →ₒ Digest).QueryCache) :
    AuthIdealState TagId Nonce Digest where
  responses := p.2
  honestOutputs := p.1.honestOutputs
  readerForged := p.1.readerForged

omit [Fintype TagId] [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Per-tag-query equivalence (ideal side): simulating the reduction's tag oracle through the lazy
random oracle, threaded through the cache, matches the ideal auth-game tag oracle. -/
private lemma simulateQ_prfIdeal_authToPRFTagImpl_run
    (tag : TagId) (s : AuthState TagId Nonce Digest)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((authToPRFTagImpl (TagId := TagId) tag).run s)).run c) =
      (authIdealTagQueryImpl (TagId := TagId) tag).run (authRFBundle (s, c)) := by
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest))
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) +
      ((TagId × Nonce) →ₒ Digest).randomOracle
  have hImplEq : impl = PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest) := rfl
  have hleft : ∀ {α : Type} (oa : ProbComp α),
      simulateQ impl (liftComp oa (unifSpec + ((TagId × Nonce) →ₒ Digest))) =
        (liftM oa : StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp α) := by
    intro α oa
    simp [impl, QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_toQueryImpl]
  have hquery : ∀ (d : TagId × Nonce),
      simulateQ impl
        (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr d)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest) =
      (((TagId × Nonce) →ₒ Digest).randomOracle d :
        StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp Digest) := by
    intro d
    simp only [simulateQ_query]
    change id <$> impl (Sum.inr d) = _
    rw [id_map]
    rfl
  -- Per-step equality, packaged so the simulator only ever sees explicit `simulateQ_*` shapes.
  have hstep : ∀ (st : AuthState TagId Nonce Digest),
      simulateQ impl ((authToPRFTagImpl (TagId := TagId) tag).run st) =
        ((($ᵗ Nonce : ProbComp Nonce) : StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp _)
            >>= fun nonce =>
          (((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce) :
              StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp Digest) >>= fun auth =>
            pure (TagTranscript.mk nonce auth,
              AuthState.mk
                (insert (tag, TagTranscript.mk nonce auth) st.honestOutputs)
                st.readerForged)) := by
    intro st
    have hbody :
        ((authToPRFTagImpl (TagId := TagId) tag).run st) =
          ((liftComp ($ᵗ Nonce) (unifSpec + ((TagId × Nonce) →ₒ Digest))) >>= fun nonce =>
            (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr (tag, nonce))) :
                OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest) >>= fun auth =>
              pure (TagTranscript.mk nonce auth,
                AuthState.mk
                  (insert (tag, TagTranscript.mk nonce auth) st.honestOutputs)
                  st.readerForged)) := by
      unfold authToPRFTagImpl authPRFQuery
      simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
        StateT.run_map, StateT.run_set, bind_pure_comp, pure_bind, map_pure,
        bind_map_left]
      rfl
    rw [hbody, simulateQ_bind, hleft]
    refine bind_congr fun nonce => ?_
    rw [simulateQ_bind, hquery]
    refine bind_congr fun auth => ?_
    rw [simulateQ_pure]
  have hgoal : (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((authToPRFTagImpl (TagId := TagId) tag).run s)).run c) =
      (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        (((($ᵗ Nonce : ProbComp Nonce) :
              StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp _)
              >>= fun nonce =>
            (((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce) :
                StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp Digest) >>= fun auth =>
              pure (TagTranscript.mk nonce auth,
                AuthState.mk
                  (insert (tag, TagTranscript.mk nonce auth) s.honestOutputs)
                  s.readerForged)).run c) := by
    rw [← hImplEq]
    exact congrArg _ (congrArg (StateT.run · c) (hstep s))
  rw [hgoal]
  unfold authIdealTagQueryImpl
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
    StateT.run_map, bind_pure_comp, pure_bind, map_bind,
    bind_map_left, Functor.map_map]
  refine bind_congr fun nonce => ?_
  simp only [OracleSpec.randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
    StateT.run_get, map_bind]
  cases hc : c (tag, nonce) with
  | some out =>
    simp only [authRFBundle, hc, map_pure, pure_bind, StateT.run_pure,
      StateT.run_map, StateT.run_set]
  | none =>
    simp only [authRFBundle, hc, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
      bind_pure_comp, StateT.run_modifyGet, StateT.run_map, StateT.run_set,
      pure_bind, Functor.map_map, map_pure, uniformSampleImpl]

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- Generalized per-tag-list equivalence used by the reader helper: simulating the reduction's
per-tag PRF queries through the lazy random oracle, threaded through the cache, matches mapping
`authRFLookup` over the same tag list with the cache bundled into the ideal state. -/
private lemma simulateQ_prfIdeal_authToPRFReader_mapM
    (nonce : Nonce) (tags : List TagId) :
    ∀ (st : AuthState TagId Nonce Digest)
      (c : ((TagId × Nonce) →ₒ Digest).QueryCache),
      (fun p => (p.1, authRFBundle (st, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          (tags.mapM (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
            (fun tag => Prod.mk tag <$>
              authPRFQuery (TagId := TagId) tag nonce))).run c) =
        ((tags.mapM (fun tag => do
            let d ← authRFLookup (TagId := TagId) tag nonce
            pure (tag, d))).run (authRFBundle (st, c))) := by
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest))
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) +
      ((TagId × Nonce) →ₒ Digest).randomOracle
  have hImplEq : impl = PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest) := rfl
  have hquery : ∀ (d : TagId × Nonce),
      simulateQ impl
        (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr d)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest) =
      (((TagId × Nonce) →ₒ Digest).randomOracle d :
        StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp Digest) := by
    intro d
    simp only [simulateQ_query]
    change id <$> impl (Sum.inr d) = _
    rw [id_map]
    rfl
  -- Per-tag step: simulating `Prod.mk tag <$> authPRFQuery tag nonce` is the cached random oracle.
  have hstep : ∀ (tag : TagId),
      simulateQ impl (Prod.mk tag <$> authPRFQuery (TagId := TagId) tag nonce) =
        (Prod.mk tag <$> ((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce) :
          StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp (TagId × Digest)) := by
    intro tag
    unfold authPRFQuery
    rw [simulateQ_map]
    congr 1
    exact hquery (tag, nonce)
  -- One `authRFLookup` step on a bundled state factors as the cached random oracle on the cache.
  have hlookup : ∀ (tag : TagId) (st : AuthState TagId Nonce Digest)
      (c : ((TagId × Nonce) →ₒ Digest).QueryCache),
      ((do
          let d ← authRFLookup (TagId := TagId) tag nonce
          pure (tag, d)).run (authRFBundle (st, c))) =
        (fun p => ((tag, p.1), authRFBundle (st, p.2))) <$>
          ((((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce) :
            StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp Digest).run c) := by
    intro tag st c
    unfold authRFLookup
    simp only [OracleSpec.randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
      StateT.run_get, bind_pure_comp, StateT.run_map, map_bind]
    cases hc : c (tag, nonce) with
    | some out =>
      simp only [authRFBundle, hc, map_pure, pure_bind, StateT.run_pure]
    | none =>
      simp only [authRFBundle, hc, StateT.run_bind, StateT.run_monadLift, monadLift_eq_self,
        bind_pure_comp, StateT.run_modifyGet, StateT.run_map, StateT.run_set,
        pure_bind, Functor.map_map, map_pure, uniformSampleImpl]
  -- The simulated `mapM` is the `mapM` of the cached random oracle (per-tag step `hstep`).
  have hmapM : ∀ (ts : List TagId), simulateQ impl
        (ts.mapM (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
          (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) tag nonce)) =
      ts.mapM (fun tag => Prod.mk tag <$>
        ((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce)) := by
    intro ts
    induction ts with
    | nil => simp only [List.mapM_nil, simulateQ_pure]
    | cons t ts ih =>
      rw [List.mapM_cons, List.mapM_cons, simulateQ_bind, hstep t]
      refine bind_congr fun p => ?_
      rw [simulateQ_bind, ih]
      refine bind_congr fun ps => ?_
      rw [simulateQ_pure]
  intro st c
  -- Push `simulateQ` through `mapM` and the per-tag step, leaving a pure `StateT` list-fold.
  have hgoal : (fun p => (p.1, authRFBundle (st, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          (tags.mapM (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
            (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId) tag nonce))).run c) =
      (fun p => (p.1, authRFBundle (st, p.2))) <$>
        ((tags.mapM (fun tag => Prod.mk tag <$>
          ((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce))).run c) := by
    rw [← hImplEq]
    exact congrArg _ (congrArg (StateT.run · c) (hmapM tags))
  rw [hgoal]
  clear hgoal hmapM hstep hquery hImplEq
  -- Induct on the tag list: each `randomOracle` step matches an `authRFLookup` step.
  induction tags generalizing c with
  | nil =>
    simp only [List.mapM_nil, StateT.run_pure, map_pure]
  | cons t ts ih =>
    rw [List.mapM_cons, List.mapM_cons]
    have hhead := hlookup t st c
    -- Expose the head/tail binds on both sides via `StateT.run_bind`.
    simp only [StateT.run_bind, StateT.run_map, map_bind, bind_pure_comp, bind_map_left,
      Functor.map_map] at *
    -- Factor the RHS head bind through `((t, ·.1), ·.2) <$> authRFLookup.run`, then use `hhead`.
    rw [show (do
          let p ← (authRFLookup (TagId := TagId) t nonce).run (authRFBundle (st, c))
          (fun p_1 => (((t, p.1) :: p_1.1 : List (TagId × Digest)), p_1.2)) <$>
            (List.mapM (fun tag => Prod.mk tag <$>
              authRFLookup (TagId := TagId) tag nonce) ts).run p.2) =
        ((fun p => (((t, p.1) : TagId × Digest), p.2)) <$>
            (authRFLookup (TagId := TagId) t nonce).run (authRFBundle (st, c))) >>= fun q =>
          (fun p_1 => ((q.1 :: p_1.1 : List (TagId × Digest)), p_1.2)) <$>
            (List.mapM (fun tag => Prod.mk tag <$>
              authRFLookup (TagId := TagId) tag nonce) ts).run q.2
      from by rw [bind_map_left]]
    rw [hhead, bind_map_left]
    refine bind_congr fun p => ?_
    have ihp := ih p.2
    rw [show (fun a => (((t, p.1) :: a.1 : List (TagId × Digest)),
            authRFBundle (st, a.2))) <$>
          (List.mapM (fun tag => Prod.mk tag <$>
            ((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce)) ts).run p.2 =
        (fun q => (((t, p.1) :: q.1 : List (TagId × Digest)), q.2)) <$>
          ((fun a => ((a.1 : List (TagId × Digest)), authRFBundle (st, a.2))) <$>
            (List.mapM (fun tag => Prod.mk tag <$>
              ((TagId × Nonce) →ₒ Digest).randomOracle (tag, nonce)) ts).run p.2)
      from by rw [Functor.map_map]]
    rw [ihp]

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- Per-reader-query equivalence (ideal side): simulating the reduction's reader oracle through the
lazy random oracle, threaded through the cache, matches the random-function auth-game reader. -/
private lemma simulateQ_prfIdeal_authToPRFReaderImpl_run
    (transcript : TagTranscript Nonce Digest) (s : AuthState TagId Nonce Digest)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((authToPRFReaderImpl (TagId := TagId) transcript).run s)).run c) =
      (authRFReaderQueryImpl (TagId := TagId) transcript).run (authRFBundle (s, c)) := by
  have hmapM := simulateQ_prfIdeal_authToPRFReader_mapM (TagId := TagId)
    transcript.nonce (Finset.univ : Finset TagId).toList s c
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest))
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT ((TagId × Nonce) →ₒ Digest).QueryCache ProbComp) +
      ((TagId × Nonce) →ₒ Digest).randomOracle
  have hImplEq : impl = PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest) := rfl
  -- The reduction's reader oracle is a `Functor.map` of the per-tag `mapM` (no nested binds).
  have hbody :
      ((authToPRFReaderImpl (TagId := TagId) transcript).run s) =
        ((fun pairs => (ReaderReply.ofBool (decide (∃ p ∈ pairs, p.2 = transcript.auth)),
            AuthState.mk s.honestOutputs
              (s.readerForged ∪ ((((pairs.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ s.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript)))))) <$>
          ((Finset.univ : Finset TagId).toList.mapM
            (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
            (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId)
              tag transcript.nonce))) := by
    unfold authToPRFReaderImpl authPRFQuery
    simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_eq_self,
      StateT.run_map, StateT.run_set, bind_pure_comp, pure_bind, map_pure,
      Functor.map_map]
  -- Push `simulateQ` through the `Functor.map`.
  have hsimQ :
      simulateQ impl ((authToPRFReaderImpl (TagId := TagId) transcript).run s) =
        (fun pairs => (ReaderReply.ofBool (decide (∃ p ∈ pairs, p.2 = transcript.auth)),
            AuthState.mk s.honestOutputs
              (s.readerForged ∪ ((((pairs.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ s.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript)))))) <$>
          simulateQ impl
            ((Finset.univ : Finset TagId).toList.mapM
              (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
              (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId)
                tag transcript.nonce)) := by
    rw [hbody, simulateQ_map]
  -- Rewrite the goal's `simulateQ` body through `hsimQ`, then through `hmapM`.
  have hgoal : (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((authToPRFReaderImpl (TagId := TagId) transcript).run s)).run c) =
      (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        (((fun pairs => (ReaderReply.ofBool (decide (∃ p ∈ pairs, p.2 = transcript.auth)),
            AuthState.mk s.honestOutputs
              (s.readerForged ∪ ((((pairs.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ s.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript)))))) <$>
          simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
            ((Finset.univ : Finset TagId).toList.mapM
              (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
              (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId)
                tag transcript.nonce))).run c) := by
    rw [← hImplEq]
    exact congrArg _ (congrArg (StateT.run · c) hsimQ)
  rw [hgoal]
  simp only [StateT.run_map, Functor.map_map]
  -- Factor the reader's post-processing through the bundling map `(·.1, authRFBundle (s, ·.2))`,
  -- so the simulated per-tag `mapM` can be replaced by the `authRFLookup`-`mapM` via `hmapM`.
  rw [show (fun a : List (TagId × Digest) × ((TagId × Nonce) →ₒ Digest).QueryCache =>
          ((ReaderReply.ofBool (decide (∃ p ∈ a.1, p.2 = transcript.auth)),
            authRFBundle (AuthState.mk s.honestOutputs
              (s.readerForged ∪ ((((a.1.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ s.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript)))), a.2)) :
            ReaderReply × AuthIdealState TagId Nonce Digest)) =
        (fun q : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
          ((ReaderReply.ofBool (decide (∃ p ∈ q.1, p.2 = transcript.auth)),
            AuthIdealState.mk q.2.responses q.2.honestOutputs
              (q.2.readerForged ∪ ((((q.1.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ q.2.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript))))) :
            ReaderReply × AuthIdealState TagId Nonce Digest)) ∘
          (fun p : List (TagId × Digest) × ((TagId × Nonce) →ₒ Digest).QueryCache =>
            ((p.1, authRFBundle (s, p.2)) :
            List (TagId × Digest) × AuthIdealState TagId Nonce Digest))
      from by funext a; simp only [Function.comp_apply, authRFBundle]]
  rw [show ((fun q : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
          ((ReaderReply.ofBool (decide (∃ p ∈ q.1, p.2 = transcript.auth)),
            AuthIdealState.mk q.2.responses q.2.honestOutputs
              (q.2.readerForged ∪ ((((q.1.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ q.2.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript))))) :
            ReaderReply × AuthIdealState TagId Nonce Digest)) ∘
        (fun p : List (TagId × Digest) × ((TagId × Nonce) →ₒ Digest).QueryCache =>
          ((p.1, authRFBundle (s, p.2)) :
          List (TagId × Digest) × AuthIdealState TagId Nonce Digest))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((Finset.univ : Finset TagId).toList.mapM
            (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
            (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId)
              tag transcript.nonce))).run c) =
      (fun q : List (TagId × Digest) × AuthIdealState TagId Nonce Digest =>
          ((ReaderReply.ofBool (decide (∃ p ∈ q.1, p.2 = transcript.auth)),
            AuthIdealState.mk q.2.responses q.2.honestOutputs
              (q.2.readerForged ∪ ((((q.1.filter fun p => decide (p.2 = transcript.auth ∧
                  (p.1, transcript) ∉ q.2.honestOutputs)).map Prod.fst).toFinset).image
                (fun x => (x, transcript))))) :
            ReaderReply × AuthIdealState TagId Nonce Digest)) <$>
        ((fun p : List (TagId × Digest) × ((TagId × Nonce) →ₒ Digest).QueryCache =>
          ((p.1, authRFBundle (s, p.2)) :
          List (TagId × Digest) × AuthIdealState TagId Nonce Digest)) <$>
          (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
            ((Finset.univ : Finset TagId).toList.mapM
              (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
              (fun tag => Prod.mk tag <$> authPRFQuery (TagId := TagId)
                tag transcript.nonce))).run c)
    from by rw [Functor.map_map]; rfl]
  rw [hmapM]
  -- Both sides are now the per-tag `mapM` followed by the same reader bookkeeping.
  unfold authRFReaderQueryImpl
  simp only [StateT.run_bind, StateT.run_get,
    StateT.run_map, StateT.run_set, bind_pure_comp, map_pure, authRFBundle]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Inductive helper (ideal side): simulating the auth-game adversary through the reduction's
query implementation and then through the lazy random oracle, threaded through the cache, is the
same as simulating it directly through the random-function auth query implementation, with the
cache bundled into the ideal state. -/
private theorem simulateQ_prfIdeal_authToPRFQueryImpl_run
    (adversary : AuthAdversary TagId Nonce Digest)
    (s : AuthState TagId Nonce Digest)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          ((simulateQ (authToPRFQueryImpl (TagId := TagId)) adversary).run s)).run c) =
      (simulateQ (authRFQueryImpl (TagId := TagId)) adversary).run (authRFBundle (s, c)) := by
  induction adversary using OracleComp.inductionOn generalizing s c with
  | pure x =>
    change (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
          (pure (x, s))).run c) =
      (simulateQ (authRFQueryImpl (TagId := TagId)) (pure x)).run (authRFBundle (s, c))
    rw [simulateQ_pure, simulateQ_pure]
    simp only [StateT.run_pure, map_pure]
  | query_bind t f ih =>
    rcases t with tag | transcript
    · -- Tag query: use the per-tag-query ideal helper, then the induction hypothesis.
      have hstep := simulateQ_prfIdeal_authToPRFTagImpl_run (TagId := TagId) tag s c
      change (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
          ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
            (((authToPRFTagImpl tag).run s) >>= fun p =>
              (simulateQ authToPRFQueryImpl (f p.1)).run p.2)).run c) =
        ((authIdealTagQueryImpl tag).run (authRFBundle (s, c))) >>= fun p =>
          (simulateQ (authRFQueryImpl (TagId := TagId)) (f p.1)).run p.2
      rw [simulateQ_bind]
      simp only [StateT.run_bind, map_bind]
      rw [show (do
            let a ← (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
              ((authToPRFTagImpl tag).run s)).run c
            (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((simulateQ authToPRFQueryImpl (f a.1.1)).run a.1.2)).run a.2) =
          ((fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((authToPRFTagImpl tag).run s)).run c) >>= fun q =>
            (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((simulateQ authToPRFQueryImpl (f q.1)).run
                  (AuthState.mk q.2.honestOutputs q.2.readerForged))).run q.2.responses
        from by rw [bind_map_left]; rfl]
      refine Eq.trans (congrArg
        (fun (x : ProbComp (TagTranscript Nonce Digest × AuthIdealState TagId Nonce Digest)) =>
          x >>= fun q =>
          (fun p : (Unit × AuthState TagId Nonce Digest) ×
              ((TagId × Nonce) →ₒ Digest).QueryCache =>
            (p.1.1, authRFBundle (p.1.2, p.2))) <$>
            (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
              ((simulateQ authToPRFQueryImpl (f q.1)).run
                (AuthState.mk q.2.honestOutputs q.2.readerForged))).run q.2.responses) hstep) ?_
      refine bind_congr fun p => ?_
      exact ih p.1 (AuthState.mk p.2.honestOutputs p.2.readerForged) p.2.responses
    · -- Reader query: use the per-reader-query ideal helper, then the induction hypothesis.
      have hstep := simulateQ_prfIdeal_authToPRFReaderImpl_run (TagId := TagId) transcript s c
      change (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
          ((simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
            (((authToPRFReaderImpl transcript).run s) >>= fun p =>
              (simulateQ authToPRFQueryImpl (f p.1)).run p.2)).run c) =
        ((authRFReaderQueryImpl transcript).run (authRFBundle (s, c))) >>= fun p =>
          (simulateQ (authRFQueryImpl (TagId := TagId)) (f p.1)).run p.2
      rw [simulateQ_bind]
      simp only [StateT.run_bind, map_bind]
      rw [show (do
            let a ← (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
              ((authToPRFReaderImpl transcript).run s)).run c
            (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((simulateQ authToPRFQueryImpl (f a.1.1)).run a.1.2)).run a.2) =
          ((fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((authToPRFReaderImpl transcript).run s)).run c) >>= fun q =>
            (fun p => (p.1.1, authRFBundle (p.1.2, p.2))) <$>
              (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
                ((simulateQ authToPRFQueryImpl (f q.1)).run
                  (AuthState.mk q.2.honestOutputs q.2.readerForged))).run q.2.responses
        from by rw [bind_map_left]; rfl]
      refine Eq.trans (congrArg
        (fun (x : ProbComp (ReaderReply × AuthIdealState TagId Nonce Digest)) =>
          x >>= fun q =>
          (fun p : (Unit × AuthState TagId Nonce Digest) ×
              ((TagId × Nonce) →ₒ Digest).QueryCache =>
            (p.1.1, authRFBundle (p.1.2, p.2))) <$>
            (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
              ((simulateQ authToPRFQueryImpl (f q.1)).run
                (AuthState.mk q.2.honestOutputs q.2.readerForged))).run q.2.responses) hstep) ?_
      refine bind_congr fun p => ?_
      exact ih p.1 (AuthState.mk p.2.honestOutputs p.2.readerForged) p.2.responses

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The random-function authentication experiment coincides with its direct form: running the PRF
reduction against a lazy random oracle (`authRFExp`) produces the same distribution as running the
adversary against the directly-defined random-function oracle `authRFQueryImpl` (`authRFDirectExp`).

The lazy random oracle answering the reduction's PRF queries at `(tag, nonce)` is exactly the
`responses` table threaded by `authRFQueryImpl`. -/
theorem authRFExp_eq_authRFDirectExp
    (adversary : AuthAdversary TagId Nonce Digest) :
    authRFExp adversary = authRFDirectExp adversary := by
  unfold authRFExp authRFDirectExp PRFScheme.prfIdealExp authToPRFReduction
  have hquery :=
    simulateQ_prfIdeal_authToPRFQueryImpl_run (TagId := TagId) adversary AuthState.init ∅
  -- `authRFBundle (AuthState.init, ∅)` is `AuthIdealState.init`.
  have hinit : authRFBundle (AuthState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest),
      (∅ : ((TagId × Nonce) →ₒ Digest).QueryCache)) = AuthIdealState.init := rfl
  rw [hinit] at hquery
  -- Reduce the reduction's `simulateQ … >>= pure (decide …)` and apply the inductive helper.
  change (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
      (((simulateQ authToPRFQueryImpl adversary).run AuthState.init) >>=
        fun p => pure (decide (p.2.readerForged ≠ ∅)))).run' ∅ =
    (do
      let (_, st) ← (simulateQ (authRFQueryImpl (TagId := TagId)) adversary).run
        AuthIdealState.init
      return decide (st.readerForged ≠ ∅))
  rw [simulateQ_bind]
  simp only [StateT.run'_eq, StateT.run_bind, map_bind]
  rw [← hquery]
  simp only [Functor.map_map, simulateQ_pure, StateT.run_pure,
    bind_pure_comp, map_pure, authRFBundle]


end Theorems

end PRFTagReader
