/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.Defs
import Examples.PRFTagReader.BadEvent
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# PRF reductions and composed ideal handlers for the tag/reader unlinkability game

PRF reductions for the multiple-session and single-session unlinkability worlds, the composed
ideal-world handlers `multipleIdealQueryImpl`, `singleIdealQueryImpl`, and `unlinkBadQueryImpl`,
their per-query and `query_bind` reduction lemmas, and the pairwise-distinct-reader-nonce
predicate `HasDistinctUnlinkReaderNonces`.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ## Multiple-session reduction

The multiple-session world hashes through a single per-tag secret. Replacing that secret by a PRF
oracle on `(TagId × Nonce)` turns the game into a PRF distinguisher.
-/

/-- Tag-oracle implementation of the multiple-session reduction: sample a nonce uniformly and
query the PRF oracle on `(tag, nonce)` for the authenticator. Models `unlinkTagQueryImpl` under the
`multiplePattern` with the hash replaced by a PRF oracle call. -/
def unlinkToMultiplePRFTagImpl :
    QueryImpl (TagId →ₒ Option (TagTranscript Nonce Digest))
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) := fun tag => do
  let st ← get
  if _h : st.sessionsUsed tag < sessionsPerTag then
    let nonce ← (OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + ((TagId × Nonce) →ₒ Digest)) ($ᵗ Nonce) :
      OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Nonce)
    let auth ← ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr (tag, nonce)) :
      OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest)
    set { st with
      sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1) }
    return some (⟨nonce, auth⟩ : TagTranscript Nonce Digest)
  else
    return none

/-- Reader-oracle implementation of the multiple-session reduction: query the PRF oracle on
`(tag, transcript.nonce)` for every tag and accept when some digest matches the submitted
authenticator. Models `unlinkReaderQueryImpl` under the `multiplePattern`. -/
noncomputable def unlinkToMultiplePRFReaderImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) := fun transcript => do
  let digests ← (Finset.univ : Finset TagId).toList.mapM
    (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
    (fun tag => ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query
      (Sum.inr (tag, transcript.nonce)) :
      OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest))
  return ReaderReply.ofBool (decide (∃ d ∈ digests, d = transcript.auth))

/-- Combined oracle implementation of the multiple-session reduction. -/
noncomputable def unlinkToMultiplePRFQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))) :=
  unlinkToMultiplePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) +
    unlinkToMultiplePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)

/-- PRF distinguisher against `prfs.multiplePRFScheme` derived from an unlinkability adversary.
It runs the unlinkability game with every `prfs.evalMultiple k tag nonce` replaced by a PRF oracle
query on `(tag, nonce)`, and returns the adversary's distinguishing bit. -/
noncomputable def unlinkToMultiplePRFReduction
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    PRFScheme.PRFAdversary (TagId × Nonce) Digest :=
  (simulateQ (unlinkToMultiplePRFQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' UnlinkState.init

/-! ## Single-session reduction

The single-session world hashes through an independent secret per session. Replacing it by a PRF
oracle on `((TagId × Fin sessionsPerTag) × Nonce)` turns the game into a PRF distinguisher. -/

/-- Tag-oracle implementation of the single-session reduction: sample a nonce uniformly and query
the PRF oracle on `((tag, sid), nonce)` for the authenticator, where `sid` is the current session
index. Models `unlinkTagQueryImpl` under the `singlePattern`. -/
def unlinkToSinglePRFTagImpl :
    QueryImpl (TagId →ₒ Option (TagTranscript Nonce Digest))
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec +
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))) := fun tag => do
  let st ← get
  if h : st.sessionsUsed tag < sessionsPerTag then
    let sid : Fin sessionsPerTag := ⟨st.sessionsUsed tag, h⟩
    let nonce ← (OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) ($ᵗ Nonce) :
      OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) Nonce)
    let auth ← ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
      (Sum.inr ((tag, sid), nonce)) :
      OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) Digest)
    set { st with
      sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1) }
    return some (⟨nonce, auth⟩ : TagTranscript Nonce Digest)
  else
    return none

/-- Reader-oracle implementation of the single-session reduction: query the PRF oracle on
`((tag, sid), transcript.nonce)` for every tag/session slot and accept when some digest matches
the submitted authenticator. Models `unlinkReaderQueryImpl` under the `singlePattern`. -/
noncomputable def unlinkToSinglePRFReaderImpl :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec +
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))) := fun transcript => do
  let digests ← (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.mapM
    (m := OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))
    (fun slot => ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
      (Sum.inr (slot, transcript.nonce)) :
      OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) Digest))
  return ReaderReply.ofBool (decide (∃ d ∈ digests, d = transcript.auth))

/-- Combined oracle implementation of the single-session reduction. -/
noncomputable def unlinkToSinglePRFQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId)
        (OracleComp (unifSpec +
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))) :=
  unlinkToSinglePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
    (sessionsPerTag := sessionsPerTag) +
    unlinkToSinglePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)

/-- PRF distinguisher against `prfs.singlePRFScheme` derived from an unlinkability adversary.
It runs the unlinkability game with every `prfs.evalSingle k tag sid nonce` replaced by a PRF
oracle query on `((tag, sid), nonce)`, and returns the adversary's distinguishing bit. -/
noncomputable def unlinkToSinglePRFReduction
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    PRFScheme.PRFAdversary ((TagId × Fin sessionsPerTag) × Nonce) Digest :=
  (simulateQ (unlinkToSinglePRFQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' UnlinkState.init

/-! ## Bridge lemmas

PRF-real faithfulness for the multiple- and single-session reductions, proved by the same
simulation-collapse argument as the auth-side `prfRealExp_authToPRFReduction_eq_authExp`.
-/

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Per-tag-query equivalence, multiple-session world: running the reduction's tag-oracle
implementation through the real PRF simulator produces the same distribution and final state as
the real multiple-session unlinkability tag oracle parameterised by `prfs.evalMultiple k`. -/
lemma simulateQ_prfReal_unlinkToMultiplePRFTagImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (tag : TagId) (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((unlinkToMultiplePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) tag).run s) =
      (unlinkTagQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
        (fun tag nonce => prfs.evalMultiple k tag nonce)
        (multiplePattern (TagId := TagId) sessionsPerTag) tag).run s := by
  let so : QueryImpl ((TagId × Nonce) →ₒ Digest) ProbComp :=
    fun d => pure (prfs.multiplePRFScheme.eval k d)
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp :=
    HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + so
  have hleft : ∀ {α : Type} (oa : ProbComp α),
      simulateQ impl (liftComp oa (unifSpec + ((TagId × Nonce) →ₒ Digest))) = oa := fun oa =>
    (QueryImpl.simulateQ_add_liftComp_left _ _ oa).trans (simulateQ_ofLift_eq_self _)
  have hquery : ∀ (d : TagId × Nonce),
      simulateQ impl
        (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr d)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) _) =
      (pure (prfs.evalMultiple k d.1 d.2) : ProbComp Digest) := fun d => by
    simp [impl, so, QueryImpl.add_apply_inr, TagReaderPRFs.multiplePRFScheme]
  unfold unlinkToMultiplePRFTagImpl unlinkTagQueryImpl
  by_cases hs : s.sessionsUsed tag < sessionsPerTag
  · simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      bind_pure_comp, pure_bind, dif_pos hs]
    change simulateQ impl _ = _
    simp only [simulateQ_bind, simulateQ_map, monadLift_eq_self, hleft]
    refine bind_congr fun nonce => ?_
    erw [hquery (tag, nonce.1)]
    rfl
  · simp [hs]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- Per-reader-query equivalence, multiple-session world: running the reduction's reader-oracle
implementation through the real PRF simulator produces the same distribution and final state as
the real multiple-session unlinkability reader oracle parameterised by `prfs.evalMultiple k`. -/
lemma simulateQ_prfReal_unlinkToMultiplePRFReaderImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((unlinkToMultiplePRFReaderImpl
            (TagId := TagId) (Nonce := Nonce) (Digest := Digest) transcript).run s) =
      (unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
        (fun tag nonce => prfs.evalMultiple k tag nonce)
        (multiplePattern (TagId := TagId) sessionsPerTag) transcript).run s := by
  let so : QueryImpl ((TagId × Nonce) →ₒ Digest) ProbComp :=
    fun d => pure (prfs.multiplePRFScheme.eval k d)
  let impl : QueryImpl (unifSpec + ((TagId × Nonce) →ₒ Digest)) ProbComp :=
    HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + so
  have hquery : ∀ (d : TagId × Nonce),
      simulateQ impl
        (liftM ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr d)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) _) =
      (pure (prfs.evalMultiple k d.1 d.2) : ProbComp Digest) := fun d => by
    simp [impl, so, QueryImpl.add_apply_inr, TagReaderPRFs.multiplePRFScheme]
  have hmapM :
      simulateQ impl
        ((Finset.univ : Finset TagId).toList.mapM
          (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
          (fun tag => ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query
            (Sum.inr (tag, transcript.nonce)) :
            OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest))) =
      pure ((Finset.univ : Finset TagId).toList.map
        fun tag => prfs.evalMultiple k tag transcript.nonce) := by
    show simulateQ impl _ = _
    rw [simulateQ_list_mapM]
    induction (Finset.univ : Finset TagId).toList with
    | nil => rfl
    | cons t ts ih =>
      rw [List.mapM_cons]
      erw [hquery (t, transcript.nonce)]
      rw [pure_bind, ih, pure_bind]
      rfl
  have hAccept :
      decide (∃ d ∈ (Finset.univ : Finset TagId).toList.map
        fun tag => prfs.evalMultiple k tag transcript.nonce, d = transcript.auth) =
      unlinkReaderAccepts (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
        (fun tag nonce => prfs.evalMultiple k tag nonce)
        (multiplePattern (TagId := TagId) sessionsPerTag) transcript := by
    unfold unlinkReaderAccepts tagAccepts
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, multiplePattern,
      decide_eq_decide, decide_eq_true_eq]
    constructor
    · rintro ⟨d, ⟨tag, rfl⟩, hd⟩
      exact ⟨tag, ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne sessionsPerTag)⟩, hd⟩⟩
    · rintro ⟨tag, _, hd⟩
      exact ⟨_, ⟨tag, rfl⟩, hd⟩
  unfold unlinkToMultiplePRFReaderImpl unlinkReaderQueryImpl
  simp only [bind_pure_comp]
  change simulateQ impl _ = _
  simp only [StateT.run_map, StateT.run_monadLift, simulateQ_bind, simulateQ_map,
    monadLift_eq_self, hmapM, pure_bind, simulateQ_pure, map_pure]
  rw [hAccept]
  rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] in
/-- Multiple-session compose: simulating the unlinkability adversary through the reduction's query
implementation and then through the real PRF query implementation matches, state-by-state, the
direct simulation through the real multiple-session query implementation with the hash set to
`prfs.evalMultiple k`. -/
theorem simulateQ_prfReal_unlinkToMultiplePRFQueryImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((simulateQ
          (unlinkToMultiplePRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag))
          adversary).run s) =
      (simulateQ
        (unlinkMultipleQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          prfs k)
        adversary).run s :=
  simulateQ_StateT_compose unlinkToMultiplePRFQueryImpl
    (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k) (unlinkMultipleQueryImpl prfs k)
    (fun q s' => by
      rcases q with tag | transcript
      · exact simulateQ_prfReal_unlinkToMultiplePRFTagImpl_run prfs k tag s'
      · exact simulateQ_prfReal_unlinkToMultiplePRFReaderImpl_run prfs k transcript s')
    adversary s

/-- PRF-real faithfulness, multiple-session world: under the real PRF, each oracle query at
`(tag, nonce)` returns `prfs.evalMultiple k tag nonce`, so the reduction runs exactly the
multiple-session unlinkability game. -/
theorem prfRealExp_unlinkToMultiplePRFReduction_eq_unlinkMultipleExp
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | PRFScheme.prfRealExp prfs.multiplePRFScheme
        (unlinkToMultiplePRFReduction (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary)] =
      Pr[= true | unlinkMultipleExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary] := by
  congr 1
  unfold PRFScheme.prfRealExp unlinkMultipleExp unlinkToMultiplePRFReduction
  refine bind_congr (m := ProbComp) fun k => ?_
  change simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
      ((simulateQ unlinkToMultiplePRFQueryImpl adversary).run UnlinkState.init >>=
        fun p => pure p.1) = _
  rw [simulateQ_bind,
    simulateQ_prfReal_unlinkToMultiplePRFQueryImpl_run prfs k adversary UnlinkState.init]
  rfl

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Per-tag-query equivalence, single-session world: running the reduction's tag-oracle
implementation through the real PRF simulator produces the same distribution and final state as
the real single-session unlinkability tag oracle parameterised by `prfs.evalSingle k`. -/
lemma simulateQ_prfReal_unlinkToSinglePRFTagImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (tag : TagId) (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
        ((unlinkToSinglePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) tag).run s) =
      (unlinkTagQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag) (Nonce := Nonce)
        (Digest := Digest)
        (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
        (singlePattern (TagId := TagId) sessionsPerTag) tag).run s := by
  let so : QueryImpl (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest) ProbComp :=
    fun d => pure (prfs.singlePRFScheme.eval k d)
  let impl : QueryImpl (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) ProbComp :=
    HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + so
  have hleft : ∀ {α : Type} (oa : ProbComp α),
      simulateQ impl
        (liftComp oa (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))) = oa :=
    fun oa => (QueryImpl.simulateQ_add_liftComp_left _ _ oa).trans (simulateQ_ofLift_eq_self _)
  have hquery : ∀ (d : (TagId × Fin sessionsPerTag) × Nonce),
      simulateQ impl
        (liftM ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
            (Sum.inr d)) :
          OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) _) =
      (pure (prfs.evalSingle k d.1.1 d.1.2 d.2) : ProbComp Digest) := fun d => by
    simp [impl, so, QueryImpl.add_apply_inr, TagReaderPRFs.singlePRFScheme]
  unfold unlinkToSinglePRFTagImpl unlinkTagQueryImpl
  by_cases hs : s.sessionsUsed tag < sessionsPerTag
  · simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift,
      bind_pure_comp, pure_bind, dif_pos hs]
    change simulateQ impl _ = _
    simp only [simulateQ_bind, simulateQ_map, monadLift_eq_self, hleft]
    refine bind_congr fun nonce => ?_
    erw [hquery ((tag, ⟨s.sessionsUsed tag, hs⟩), nonce.1)]
    rfl
  · simp [hs]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Per-reader-query equivalence, single-session world: running the reduction's reader-oracle
implementation through the real PRF simulator produces the same distribution and final state as
the real single-session unlinkability reader oracle parameterised by `prfs.evalSingle k`. -/
lemma simulateQ_prfReal_unlinkToSinglePRFReaderImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
        ((unlinkToSinglePRFReaderImpl
            (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) transcript).run s) =
      (unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId × Fin sessionsPerTag) (Nonce := Nonce)
        (Digest := Digest)
        (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
        (singlePattern (TagId := TagId) sessionsPerTag) transcript).run s := by
  let so : QueryImpl (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest) ProbComp :=
    fun d => pure (prfs.singlePRFScheme.eval k d)
  let impl : QueryImpl (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) ProbComp :=
    HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + so
  have hquery : ∀ (d : (TagId × Fin sessionsPerTag) × Nonce),
      simulateQ impl
        (liftM ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
            (Sum.inr d)) :
          OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)) _) =
      (pure (prfs.evalSingle k d.1.1 d.1.2 d.2) : ProbComp Digest) := fun d => by
    simp [impl, so, QueryImpl.add_apply_inr, TagReaderPRFs.singlePRFScheme]
  have hmapM :
      simulateQ impl
        ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.mapM
          (m := OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))
          (fun slot => ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
            (Sum.inr (slot, transcript.nonce)) :
            OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))
              Digest))) =
      pure ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
        (fun slot : TagId × Fin sessionsPerTag =>
          prfs.evalSingle k slot.1 slot.2 transcript.nonce)) := by
    show simulateQ impl _ = _
    rw [simulateQ_list_mapM]
    induction (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList with
    | nil => rfl
    | cons t ts ih =>
      rw [List.mapM_cons]
      erw [hquery (t, transcript.nonce)]
      rw [pure_bind, ih, pure_bind]
      rfl
  have hAccept :
      decide (∃ d ∈ (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
        (fun slot : TagId × Fin sessionsPerTag =>
          prfs.evalSingle k slot.1 slot.2 transcript.nonce), d = transcript.auth) =
      unlinkReaderAccepts (TagId := TagId) (Slot := TagId × Fin sessionsPerTag) (Nonce := Nonce)
        (Digest := Digest)
        (fun slot nonce => prfs.evalSingle k slot.1 slot.2 nonce)
        (singlePattern (TagId := TagId) sessionsPerTag) transcript := by
    unfold unlinkReaderAccepts tagAccepts
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, singlePattern,
      decide_eq_decide, decide_eq_true_eq]
    constructor
    · rintro ⟨d, ⟨⟨tag, sid⟩, hslot⟩, hd⟩
      exact ⟨tag, ⟨sid, by rw [hslot]; exact hd⟩⟩
    · rintro ⟨tag, ⟨sid, hd⟩⟩
      exact ⟨_, ⟨(tag, sid), rfl⟩, hd⟩
  unfold unlinkToSinglePRFReaderImpl unlinkReaderQueryImpl
  simp only [bind_pure_comp]
  change simulateQ impl _ = _
  simp only [StateT.run_map, StateT.run_monadLift, simulateQ_bind, simulateQ_map,
    monadLift_eq_self, hmapM, pure_bind, simulateQ_pure, map_pure]
  rw [hAccept]
  rfl

omit [Nonempty TagId] [DecidableEq Nonce] [SampleableType Digest] in
/-- Single-session compose: simulating the unlinkability adversary through the reduction's query
implementation and then through the real PRF query implementation matches, state-by-state, the
direct simulation through the real single-session query implementation with the hash set to
`prfs.evalSingle k`. -/
theorem simulateQ_prfReal_unlinkToSinglePRFQueryImpl_run
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
        ((simulateQ
          (unlinkToSinglePRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag))
          adversary).run s) =
      (simulateQ
        (unlinkSingleQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          prfs k)
        adversary).run s :=
  simulateQ_StateT_compose unlinkToSinglePRFQueryImpl
    (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k) (unlinkSingleQueryImpl prfs k)
    (fun q s' => by
      rcases q with tag | transcript
      · exact simulateQ_prfReal_unlinkToSinglePRFTagImpl_run prfs k tag s'
      · exact simulateQ_prfReal_unlinkToSinglePRFReaderImpl_run prfs k transcript s')
    adversary s

/-- PRF-real faithfulness, single-session world: under the real PRF, each oracle query at
`((tag, sid), nonce)` returns `prfs.evalSingle k tag sid nonce`, so the reduction runs exactly the
single-session unlinkability game. -/
theorem prfRealExp_unlinkToSinglePRFReduction_eq_unlinkSingleExp
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag)
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | PRFScheme.prfRealExp prfs.singlePRFScheme
        (unlinkToSinglePRFReduction (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary)] =
      Pr[= true | unlinkSingleExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) prfs adversary] := by
  congr 1
  unfold PRFScheme.prfRealExp unlinkSingleExp unlinkToSinglePRFReduction
  refine bind_congr (m := ProbComp) fun k => ?_
  change simulateQ (PRFScheme.prfRealQueryImpl prfs.singlePRFScheme k)
      ((simulateQ unlinkToSinglePRFQueryImpl adversary).run UnlinkState.init >>=
        fun p => pure p.1) = _
  rw [simulateQ_bind,
    simulateQ_prfReal_unlinkToSinglePRFQueryImpl_run prfs k adversary UnlinkState.init]
  rfl

/-! ### Composed ideal-world handlers

`multipleIdealQueryImpl` and `singleIdealQueryImpl` package the nested simulation of each ideal-PRF
experiment as a single stateful handler over the unlinkability oracle interface, with state
`UnlinkState TagId × QueryCache`. The `simulateQ_*Ideal_collapse` lemmas identify the composed
handler with the nested simulation up to reassociation of the product state.
-/

/-- Composed multiple-session ideal handler: run the reduction's query implementation, then
interpret the resulting PRF-oracle queries through the lazy random oracle. -/
noncomputable def multipleIdealQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) ProbComp) :=
  fun q => fun p => do
    let r ← (simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToMultiplePRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) q).run p.1)).run p.2
    return (r.1.1, (r.1.2, r.2))

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The nested simulation defining the multiple-session ideal experiment collapses to a single
`simulateQ` of `multipleIdealQueryImpl`, up to reassociating the product state. -/
lemma simulateQ_multipleIdeal_collapse
    (adv : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ PRFScheme.prfIdealQueryImpl
        ((simulateQ (unlinkToMultiplePRFQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run s)).run c =
      (fun r : (Bool × UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) =>
        ((r.1, r.2.1), r.2.2)) <$>
        (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run (s, c) :=
  simulateQ_StateT_StateT_compose unlinkToMultiplePRFQueryImpl
    PRFScheme.prfIdealQueryImpl multipleIdealQueryImpl
    (fun q s' c' => by
      simp [multipleIdealQueryImpl])
    adv s c

/-- Composed single-session ideal handler: run the reduction's query implementation, then
interpret the resulting PRF-oracle queries through the lazy random oracle. -/
noncomputable def singleIdealQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId ×
        (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) ProbComp) :=
  fun q => fun p => do
    let r ← (simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToSinglePRFQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) q).run p.1)).run p.2
    return (r.1.1, (r.1.2, r.2))

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The nested simulation defining the single-session ideal experiment collapses to a single
`simulateQ` of `singleIdealQueryImpl`, up to reassociating the product state. -/
lemma simulateQ_singleIdeal_collapse
    (adv : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ PRFScheme.prfIdealQueryImpl
        ((simulateQ (unlinkToSinglePRFQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run s)).run c =
      (fun r : (Bool × UnlinkState TagId ×
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) =>
        ((r.1, r.2.1), r.2.2)) <$>
        (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run (s, c) :=
  simulateQ_StateT_StateT_compose unlinkToSinglePRFQueryImpl
    PRFScheme.prfIdealQueryImpl singleIdealQueryImpl
    (fun q s' c' => by
      simp [singleIdealQueryImpl])
    adv s c

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The multiple-session ideal-PRF experiment is the composed handler `multipleIdealQueryImpl`
simulated over the adversary from the initial state. -/
lemma prfIdealExp_unlinkToMultiplePRFReduction_eq_run'
    (adv : UnlinkAdversary TagId Nonce Digest) :
    PRFScheme.prfIdealExp (unlinkToMultiplePRFReduction (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adv) =
      (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run' (UnlinkState.init, ∅) := by
  unfold PRFScheme.prfIdealExp unlinkToMultiplePRFReduction
  rw [StateT.run']
  change (simulateQ PRFScheme.prfIdealQueryImpl
      ((simulateQ unlinkToMultiplePRFQueryImpl adv).run UnlinkState.init >>=
        fun p => pure p.1)).run' ∅ = _
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    simulateQ_multipleIdeal_collapse adv UnlinkState.init ∅, map_bind, bind_map_left]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The single-session ideal-PRF experiment is the composed handler `singleIdealQueryImpl`
simulated over the adversary from the initial state. -/
lemma prfIdealExp_unlinkToSinglePRFReduction_eq_run'
    (adv : UnlinkAdversary TagId Nonce Digest) :
    PRFScheme.prfIdealExp (unlinkToSinglePRFReduction (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adv) =
      (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run' (UnlinkState.init, ∅) := by
  unfold PRFScheme.prfIdealExp unlinkToSinglePRFReduction
  rw [StateT.run']
  change (simulateQ PRFScheme.prfIdealQueryImpl
      ((simulateQ unlinkToSinglePRFQueryImpl adv).run UnlinkState.init >>=
        fun p => pure p.1)).run' ∅ = _
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    simulateQ_singleIdeal_collapse adv UnlinkState.init ∅, map_bind, bind_map_left]
  rfl

/-! ### Per-query reduction lemmas for the composed ideal handlers

Explicit reduced forms of `*IdealQueryImpl` on each oracle query. The lazy-random-oracle lookup at
a domain point is exposed via `QueryCache` operations.
-/

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the multiple-session reduction tag handler when the slot budget is exhausted. -/
lemma unlinkToMultiplePRFTagImpl_run_of_not_lt (tag : TagId) (s : UnlinkState TagId)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (unlinkToMultiplePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run s = pure (none, s) := by
  unfold unlinkToMultiplePRFTagImpl
  simp [hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the multiple-session reduction tag handler when a slot is available: sample a
nonce, query the PRF oracle at `(tag, nonce)`, advance the session counter. -/
lemma unlinkToMultiplePRFTagImpl_run_of_lt (tag : TagId) (s : UnlinkState TagId)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (unlinkToMultiplePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run s =
      (OracleComp.liftComp (spec := unifSpec)
          (superSpec := unifSpec + ((TagId × Nonce) →ₒ Digest)) ($ᵗ Nonce)) >>= fun nonce =>
        ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query (Sum.inr (tag, nonce))) >>= fun auth =>
          pure (some (⟨nonce, auth⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }) := by
  unfold unlinkToMultiplePRFTagImpl
  simp [hslot]

/-- The lazy-random-oracle answer to a PRF-oracle query on domain point `d` against cache `c`:
return the cached digest, or sample a fresh one and insert it. -/
noncomputable def idealCacheStep {D : Type} [DecidableEq D]
    (c : (D →ₒ Digest).QueryCache) (d : D) :
    ProbComp (Digest × (D →ₒ Digest).QueryCache) :=
  match c d with
  | some u => pure (u, c)
  | none => ($ᵗ Digest) >>= fun u => pure (u, c.cacheQuery d u)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Simulating a left-injected (uniform-sampling) query through `prfIdealQueryImpl` discards the
cache and reduces to the plain probabilistic computation. -/
lemma simulateQ_prfIdeal_liftComp {D : Type} [DecidableEq D] {α : Type}
    (oa : ProbComp α) (c : (D →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Digest))
        (OracleComp.liftComp oa (unifSpec + (D →ₒ Digest)))).run c =
      oa >>= fun a => pure (a, c) := by
  have h := QueryImpl.simulateQ_add_liftComp_left
    ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (D →ₒ Digest).QueryCache ProbComp)) randomOracle oa
  exact (congrArg (StateT.run · c) (h.trans ((simulateQ_liftTarget _ oa).trans
    (congrArg liftM (simulateQ_ofLift_eq_self oa))))).trans (StateT.run_monadLift oa c)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Simulating a right-injected (PRF-function) query through `prfIdealQueryImpl` consults the
lazy random oracle: `idealCacheStep`. -/
lemma simulateQ_prfIdeal_query_inr {D : Type} [DecidableEq D]
    (d : D) (c : (D →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Digest))
        (liftM ((PRFScheme.PRFOracleSpec D Digest).query (Sum.inr d)) :
          OracleComp (PRFScheme.PRFOracleSpec D Digest) Digest)).run c =
      idealCacheStep c d := by
  rw [simulateQ_query]
  change ((fun x => x) <$> PRFScheme.prfIdealQueryImpl (Sum.inr d)).run c = _
  rw [id_map']
  change (uniformSampleImpl.withCaching d).run c = _
  unfold idealCacheStep
  cases hc : c d with
  | none => rw [QueryImpl.withCaching_run_none uniformSampleImpl hc]; rfl
  | some u => rw [QueryImpl.withCaching_run_some uniformSampleImpl hc]

/-- Folding the lazy-random-oracle lookup `idealCacheStep` over a list of domain points, threading
the cache: this is the reader-oracle's behaviour under `prfIdealQueryImpl`. -/
noncomputable def idealCacheMapM {D : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache) :
    ProbComp (List Digest × (D →ₒ Digest).QueryCache) :=
  match l with
  | [] => pure ([], c)
  | d :: ds => idealCacheStep c d >>= fun r =>
      idealCacheMapM ds r.2 >>= fun rs => pure (r.1 :: rs.1, rs.2)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Simulating a `mapM` of right-injected PRF-oracle queries (with domain points `f a`) through
`prfIdealQueryImpl` folds the lazy random oracle over `l.map f`: `idealCacheMapM`. -/
lemma simulateQ_prfIdeal_run_mapM {D α : Type} [DecidableEq D]
    (f : α → D) (l : List α) (c : (D →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Digest))
        (l.mapM (m := OracleComp (PRFScheme.PRFOracleSpec D Digest))
          (fun a => (liftM ((PRFScheme.PRFOracleSpec D Digest).query (Sum.inr (f a))) :
            OracleComp (PRFScheme.PRFOracleSpec D Digest) Digest)))).run c =
      idealCacheMapM (l.map f) c := by
  induction l generalizing c with
  | nil => simp [idealCacheMapM]
  | cons a as ih =>
    rw [List.mapM_cons, List.map_cons]
    erw [simulateQ_bind, StateT.run_bind, simulateQ_prfIdeal_query_inr]
    rw [idealCacheMapM]
    refine bind_congr fun r => ?_
    erw [simulateQ_bind, StateT.run_bind, ih]
    refine bind_congr fun rs => ?_
    erw [simulateQ_pure, StateT.run_pure]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the multiple-session reduction reader handler: query the PRF oracle at
`(tag, transcript.nonce)` for every tag, then return acceptance; the state is untouched. -/
lemma unlinkToMultiplePRFReaderImpl_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    (unlinkToMultiplePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      transcript).run s =
      ((Finset.univ : Finset TagId).toList.mapM
        (m := OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)))
        (fun tag => ((unifSpec + ((TagId × Nonce) →ₒ Digest)).query
          (Sum.inr (tag, transcript.nonce)) :
          OracleComp (unifSpec + ((TagId × Nonce) →ₒ Digest)) Digest))) >>= fun digests =>
        pure (ReaderReply.ofBool (decide (∃ d ∈ digests, d = transcript.auth)), s) := by
  unfold unlinkToMultiplePRFReaderImpl
  simp

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Multiple-session ideal handler on a tag query whose slot budget is exhausted: returns `none`,
state unchanged. -/
lemma multipleIdealQueryImpl_tag_run_of_not_lt (tag : TagId) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) (s, c) =
      pure ((none, s, c)) := by
  unfold multipleIdealQueryImpl unlinkToMultiplePRFQueryImpl
  rw [QueryImpl.add_apply_inl unlinkToMultiplePRFTagImpl unlinkToMultiplePRFReaderImpl tag]
  change (do let r ← (simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToMultiplePRFTagImpl tag).run s)).run c; pure (r.1.1, r.1.2, r.2)) = _
  rw [unlinkToMultiplePRFTagImpl_run_of_not_lt tag s hslot]
  rfl

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Running the multiple-session reduction tag handler (slot available) through the lazy random
oracle: sample a nonce, consult the cache at `(tag, nonce)` via `idealCacheStep`, and advance the
session counter. -/
lemma simulateQ_prfIdeal_unlinkToMultiplePRFTagImpl_run_of_lt
    (tag : TagId) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
        ((unlinkToMultiplePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) tag).run s)).run c =
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep c (tag, nonce) >>= fun r =>
          pure ((some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }), r.2) := by
  rw [unlinkToMultiplePRFTagImpl_run_of_lt tag s hslot]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_prfIdeal_liftComp, bind_assoc]
  refine bind_congr fun nonce => ?_
  rw [pure_bind]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_prfIdeal_query_inr]
  refine bind_congr fun r => ?_
  erw [simulateQ_pure, StateT.run_pure]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Multiple-session ideal handler on a tag query with a free slot: sample a nonce, consult the
random-oracle cache at `(tag, nonce)` via `idealCacheStep`, advance the session counter. -/
lemma multipleIdealQueryImpl_tag_run_of_lt (tag : TagId) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) (s, c) =
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep c (tag, nonce) >>= fun r =>
          pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            ({ sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } :
              UnlinkState TagId), r.2) := by
  unfold multipleIdealQueryImpl unlinkToMultiplePRFQueryImpl
  rw [QueryImpl.add_apply_inl unlinkToMultiplePRFTagImpl unlinkToMultiplePRFReaderImpl tag]
  change ((simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToMultiplePRFTagImpl tag).run s)).run c) >>=
      (fun r => pure (r.1.1, r.1.2, r.2)) = _
  simp [simulateQ_prfIdeal_unlinkToMultiplePRFTagImpl_run_of_lt tag s c hslot]

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- Running the multiple-session reduction reader handler through the lazy random oracle: fold
`idealCacheStep` over the `(tag, transcript.nonce)` domain points, then return acceptance. -/
lemma simulateQ_prfIdeal_unlinkToMultiplePRFReaderImpl_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := TagId × Nonce) (R := Digest))
        ((unlinkToMultiplePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript).run s)).run c =
      idealCacheMapM ((Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, transcript.nonce))) c >>= fun rs =>
        pure ((ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s), rs.2) := by
  rw [unlinkToMultiplePRFReaderImpl_run transcript s]
  erw [simulateQ_bind, StateT.run_bind,
    simulateQ_prfIdeal_run_mapM (fun tag => (tag, transcript.nonce))]
  refine bind_congr fun rs => ?_
  erw [simulateQ_pure, StateT.run_pure]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Multiple-session ideal handler on a reader query: fold `idealCacheStep` over the
`(tag, transcript.nonce)` domain points and return reader acceptance. -/
lemma multipleIdealQueryImpl_reader_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) (s, c) =
      idealCacheMapM ((Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, transcript.nonce))) c >>= fun rs =>
        pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2) := by
  unfold multipleIdealQueryImpl unlinkToMultiplePRFQueryImpl
  rw [QueryImpl.add_apply_inr unlinkToMultiplePRFTagImpl unlinkToMultiplePRFReaderImpl transcript]
  change ((simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToMultiplePRFReaderImpl transcript).run s)).run c) >>=
      (fun r => pure (r.1.1, r.1.2, r.2)) = _
  simp [simulateQ_prfIdeal_unlinkToMultiplePRFReaderImpl_run transcript s c]

/-! ### Per-query reduction lemmas, single-session ideal handler -/

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the single-session reduction tag handler when the slot budget is exhausted. -/
lemma unlinkToSinglePRFTagImpl_run_of_not_lt (tag : TagId) (s : UnlinkState TagId)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (unlinkToSinglePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run s = pure (none, s) := by
  unfold unlinkToSinglePRFTagImpl
  simp [hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the single-session reduction tag handler when a slot is available: sample a
nonce, query the PRF oracle at `((tag, sid), nonce)`, advance the session counter. -/
lemma unlinkToSinglePRFTagImpl_run_of_lt (tag : TagId) (s : UnlinkState TagId)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (unlinkToSinglePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) tag).run s =
      (OracleComp.liftComp (spec := unifSpec)
          (superSpec := unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))
          ($ᵗ Nonce)) >>= fun nonce =>
        ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
          (Sum.inr ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce))) >>= fun auth =>
          pure (some (⟨nonce, auth⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }) := by
  unfold unlinkToSinglePRFTagImpl
  simp [hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Running the single-session reduction tag handler (slot available) through the lazy random
oracle: sample a nonce, consult the cache at `((tag, sid), nonce)` via `idealCacheStep`, advance
the session counter. -/
lemma simulateQ_prfIdeal_unlinkToSinglePRFTagImpl_run_of_lt
    (tag : TagId) (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := (TagId × Fin sessionsPerTag) × Nonce)
        (R := Digest))
        ((unlinkToSinglePRFTagImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) tag).run s)).run c =
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep c ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce) >>= fun r =>
          pure ((some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }), r.2) := by
  rw [unlinkToSinglePRFTagImpl_run_of_lt tag s hslot]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_prfIdeal_liftComp, bind_assoc]
  refine bind_congr fun nonce => ?_
  rw [pure_bind]
  erw [simulateQ_bind, StateT.run_bind, simulateQ_prfIdeal_query_inr]
  refine bind_congr fun r => ?_
  erw [simulateQ_pure, StateT.run_pure]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Single-session ideal handler on a tag query whose slot budget is exhausted: returns `none`,
state unchanged. -/
lemma singleIdealQueryImpl_tag_run_of_not_lt (tag : TagId) (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) (s, c) =
      pure ((none, s, c)) := by
  unfold singleIdealQueryImpl unlinkToSinglePRFQueryImpl
  rw [QueryImpl.add_apply_inl unlinkToSinglePRFTagImpl unlinkToSinglePRFReaderImpl tag]
  change (do let r ← (simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToSinglePRFTagImpl tag).run s)).run c; pure (r.1.1, r.1.2, r.2)) = _
  rw [unlinkToSinglePRFTagImpl_run_of_not_lt tag s hslot]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Single-session ideal handler on a tag query with a free slot: sample a nonce, consult the
random-oracle cache at `((tag, sid), nonce)` via `idealCacheStep`, advance the session counter. -/
lemma singleIdealQueryImpl_tag_run_of_lt (tag : TagId) (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) (s, c) =
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep c ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce) >>= fun r =>
          pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            { s with sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) }, r.2) := by
  unfold singleIdealQueryImpl unlinkToSinglePRFQueryImpl
  rw [QueryImpl.add_apply_inl unlinkToSinglePRFTagImpl unlinkToSinglePRFReaderImpl tag]
  change ((simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToSinglePRFTagImpl tag).run s)).run c) >>=
      (fun r => pure (r.1.1, r.1.2, r.2)) = _
  simp [simulateQ_prfIdeal_unlinkToSinglePRFTagImpl_run_of_lt tag s c hslot]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Reduced form of the single-session reduction reader handler: query the PRF oracle at
`(slot, transcript.nonce)` for every tag/session slot, then return acceptance; state untouched. -/
lemma unlinkToSinglePRFReaderImpl_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    (unlinkToSinglePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) transcript).run s =
      ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.mapM
        (m := OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)))
        (fun slot => ((unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest)).query
          (Sum.inr (slot, transcript.nonce)) :
          OracleComp (unifSpec + (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest))
            Digest))) >>= fun digests =>
        pure (ReaderReply.ofBool (decide (∃ d ∈ digests, d = transcript.auth)), s) := by
  unfold unlinkToSinglePRFReaderImpl
  simp

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- Running the single-session reduction reader handler through the lazy random oracle: fold
`idealCacheStep` over the `(slot, transcript.nonce)` domain points, then return acceptance. -/
lemma simulateQ_prfIdeal_unlinkToSinglePRFReaderImpl_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := (TagId × Fin sessionsPerTag) × Nonce)
        (R := Digest))
        ((unlinkToSinglePRFReaderImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) transcript).run s)).run c =
      idealCacheMapM ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
          (fun slot => (slot, transcript.nonce))) c >>= fun rs =>
        pure ((ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s), rs.2) := by
  rw [unlinkToSinglePRFReaderImpl_run transcript s]
  erw [simulateQ_bind, StateT.run_bind,
    simulateQ_prfIdeal_run_mapM (fun slot => (slot, transcript.nonce))]
  refine bind_congr fun rs => ?_
  erw [simulateQ_pure, StateT.run_pure]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Single-session ideal handler on a reader query: fold `idealCacheStep` over the
`(slot, transcript.nonce)` domain points and return reader acceptance. -/
lemma singleIdealQueryImpl_reader_run
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) (s, c) =
      idealCacheMapM ((Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
          (fun slot => (slot, transcript.nonce))) c >>= fun rs =>
        pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2) := by
  unfold singleIdealQueryImpl unlinkToSinglePRFQueryImpl
  rw [QueryImpl.add_apply_inr unlinkToSinglePRFTagImpl unlinkToSinglePRFReaderImpl transcript]
  change ((simulateQ PRFScheme.prfIdealQueryImpl
      ((unlinkToSinglePRFReaderImpl transcript).run s)).run c) >>=
      (fun r => pure (r.1.1, r.1.2, r.2)) = _
  simp [simulateQ_prfIdeal_unlinkToSinglePRFReaderImpl_run transcript s c]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Pure-adversary base case of `multipleIdeal_le_singleIdeal_add_bad`: on a `pure b` adversary the
multiple- and single-session ideal handlers return `b`, so the multiple-world success probability
is bounded by the single-world one plus the bad-event probability for arbitrary initial states. -/
lemma multipleIdeal_le_singleIdeal_add_bad_pure (b : Bool)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (pure b)).run' sM] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (pure b)).run' sS] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (pure b)).run sB] := by
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
  exact le_add_right (le_refl _)

/-! ### Structural reductions of the composed ideal handlers on a `query_bind`

`simulateQ … (query_bind t f)` run from a state is a single monadic `bind`: the per-query handler
applied to the head, then the recursive `simulateQ` of the continuation threaded through the
resulting state. These rewrites turn a coupling induction into `bind`-decomposition steps for
`probEvent_bind_le_add` / `probEvent_bind_congr_le_add`.
-/

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ multipleIdealQueryImpl` of a `query_bind`, run from a state and projected to its
output bit, is the per-query handler followed by the recursive simulation of the continuation. -/
lemma multipleIdeal_run'_query_bind
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t → UnlinkAdversary TagId Nonce Digest)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sM =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sM) >>= fun p =>
        (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ singleIdealQueryImpl` of a `query_bind`, run from a state and projected to its
output bit, is the per-query handler followed by the recursive simulation of the continuation. -/
lemma singleIdeal_run'_query_bind
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t → UnlinkAdversary TagId Nonce Digest)
    (sS : UnlinkState TagId × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sS =
      (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sS) >>= fun p =>
        (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ unlinkBadQueryImpl` of a `query_bind`, run from a state, is the per-query handler
followed by the recursive simulation of the continuation threaded through the resulting state. -/
lemma unlinkBad_run_query_bind
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t → UnlinkAdversary TagId Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run sB =
      (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sB) >>= fun p =>
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `unlinkBadQueryImpl` on a tag query with the slot budget exhausted: returns `none`, state
unchanged. -/
lemma unlinkBadQueryImpl_tag_run_of_not_lt (tag : TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hslot : ¬ sB.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sB = pure (none, sB) := by
  unfold unlinkBadQueryImpl
  rw [QueryImpl.add_apply_inl]
  change (unlinkBadTagQueryImpl tag).run sB = _
  unfold unlinkBadTagQueryImpl
  simp [hslot]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `unlinkBadQueryImpl` on a tag query with a free slot: sample a nonce and a fresh digest,
record the digest under `(tag, nonce)`, set the `bad` flag if `(tag, nonce)` was already cached,
and advance the session counter. -/
lemma unlinkBadQueryImpl_tag_run_of_lt (tag : TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hslot : sB.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sB =
      ($ᵗ Nonce) >>= fun nonce =>
        ($ᵗ Digest) >>= fun auth =>
          pure (some (⟨nonce, auth⟩ : TagTranscript Nonce Digest),
            ({ sessionsUsed :=
                Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1)
               responses := sB.responses.cacheQuery (tag, nonce)
                 (auth :: Option.getD (sB.responses (tag, nonce)) [])
               bad := sB.bad || (sB.responses (tag, nonce)).isSome } :
              UnlinkBadState TagId Nonce Digest)) := by
  unfold unlinkBadQueryImpl
  rw [QueryImpl.add_apply_inl]
  change (unlinkBadTagQueryImpl tag).run sB = _
  unfold unlinkBadTagQueryImpl
  simp [hslot]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `unlinkBadQueryImpl` on a reader query: deterministic acceptance against the recorded
random-function responses, state untouched. -/
lemma unlinkBadQueryImpl_reader_run (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) sB =
      pure (ReaderReply.ofBool (decide (∃ tag ∈ (Finset.univ : Finset TagId),
        transcript.auth ∈ ((sB.responses (tag, transcript.nonce)).getD []))), sB) := by
  unfold unlinkBadQueryImpl
  rw [QueryImpl.add_apply_inr]
  change (unlinkBadReaderQueryImpl transcript).run sB = _
  unfold unlinkBadReaderQueryImpl
  simp

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The `bad` flag of `unlinkBadQueryImpl` is monotone: a single per-query step started from a
state with `bad = true` keeps `bad = true`. -/
lemma unlinkBadQueryImpl_step_preserves_bad
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (sB : UnlinkBadState TagId Nonce Digest) (hbad : sB.bad = true) :
    ∀ z ∈ support ((unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t) sB), z.2.bad = true := by
  cases t with
  | inl tag =>
    by_cases hslot : sB.sessionsUsed tag < sessionsPerTag
    · have key : ∀ z : Option (TagTranscript Nonce Digest) × UnlinkBadState TagId Nonce Digest,
          z ∈ support
            ((unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sB) → z.2.bad = true := by
        intro z hz
        rw [unlinkBadQueryImpl_tag_run_of_lt tag sB hslot] at hz
        obtain ⟨nonce, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
        obtain ⟨auth, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
        rw [mem_support_pure_iff] at hz
        subst hz; simp [hbad]
      exact key
    · intro z hz
      rw [unlinkBadQueryImpl_tag_run_of_not_lt tag sB hslot] at hz
      have hz' := (mem_support_pure_iff _ _).mp hz
      subst hz'; exact hbad
  | inr transcript =>
    intro z hz
    rw [unlinkBadQueryImpl_reader_run transcript sB] at hz
    have hz' := (mem_support_pure_iff _ _).mp hz
    subst hz'; exact hbad

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The `bad` flag of a full `simulateQ unlinkBadQueryImpl` run is monotone: started from a state
with `bad = true` the run keeps `bad = true`. -/
lemma simulateQ_unlinkBad_preserves_bad
    (adv : UnlinkAdversary TagId Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) (hbad : sB.bad = true) :
    ∀ z ∈ support ((simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run sB), z.2.bad = true := by
  induction adv using OracleComp.inductionOn generalizing sB with
  | pure b =>
    intro z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz; exact hbad
  | query_bind t f ih =>
    intro z hz
    rw [unlinkBad_run_query_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    exact ih p.1 p.2 (unlinkBadQueryImpl_step_preserves_bad t sB hbad p hp) z hz

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Once the `bad` flag is set, the `Pr[bad]` of the residual `unlinkBadQueryImpl` run is `1`. -/
lemma probEvent_unlinkBad_bad_eq_one_of_bad
    (adv : UnlinkAdversary TagId Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) (hbad : sB.bad = true) :
    Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run sB] = 1 := by
  rw [probEvent_eq_one_iff]
  exact ⟨by simp, fun z hz => simulateQ_unlinkBad_preserves_bad adv sB hbad z hz⟩

/-! ### Pairwise-distinct reader nonces

`HasDistinctUnlinkReaderNonces` bounds, for every nonce `n`, the number of reader queries carrying
`n` by `1`. It is the unlinkability analogue of `PRFTagReader.HasDistinctReaderNonces` from the
authentication collision proof, and underpins the reader-slack half of the multiple-vs-single
coupling: a reader query at nonce `n` programs an entire column of the random oracle, which the
coupling can charge only once.
-/

/-- Per-nonce reader-query predicate on the unlinkability oracle interface. `pReaderNonce n` holds
of a reader query exactly when its transcript carries the nonce `n`, and never holds of a tag
query. Bounding the number of `pReaderNonce n`-queries by `1` for every `n` expresses that the
adversary's reader queries use pairwise-distinct nonces. -/
def pReaderNonce (n : Nonce) : (UnlinkOracleSpec TagId Nonce Digest).Domain → Prop :=
  fun i => match i with
    | Sum.inr tr => tr.nonce = n
    | Sum.inl _ => False

instance pReaderNonceDecidable (n : Nonce) :
    DecidablePred (pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n) := by
  intro i
  cases i with
  | inr tr => exact (inferInstance : Decidable (tr.nonce = n))
  | inl _ => exact (inferInstance : Decidable False)

/-- The adversary's reader queries use pairwise-distinct nonces: every nonce `n` is carried by at
most one reader query. This is the public hypothesis under which the reader-slack half of the
unlinkability coupling is sound; it rules out the shared-column obstruction that an unrestricted
multiple-vs-single coupling would face. -/
def HasDistinctUnlinkReaderNonces (adversary : UnlinkAdversary TagId Nonce Digest) : Prop :=
  ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pReaderNonce n) 1

/-- `HasDistinctUnlinkReaderNonces` unfolds definitionally to a per-nonce reader-query bound: it
holds exactly when, for every nonce `n`, at most one reader query carries `n`. -/
lemma hasDistinctUnlinkReaderNonces_iff (adversary : UnlinkAdversary TagId Nonce Digest) :
    HasDistinctUnlinkReaderNonces adversary ↔
      ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pReaderNonce n) 1 :=
  Iff.rfl

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest]
  [NeZero sessionsPerTag] in
/-- Every `pReaderNonce n`-query is a reader query: `pReaderNonce n` is false on tag (`Sum.inl`)
queries and, on reader (`Sum.inr`) queries, refines `Sum.isRight`. -/
lemma pReaderNonce_imp_isRight (n : Nonce)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain) :
    pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n t → t.isRight := by
  cases t with
  | inl x => exact fun h => (h : (False : Prop)).elim
  | inr tr => exact fun _ => rfl

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest]
  [NeZero sessionsPerTag] in
/-- An adversary making at most one reader query has pairwise-distinct reader nonces: a single
reader query cannot collide with itself. Adversaries with no reader queries also qualify. -/
theorem hasDistinctUnlinkReaderNonces_of_readerBound
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) 1) :
    HasDistinctUnlinkReaderNonces adversary := fun n =>
  OracleComp.IsQueryBoundP.of_imp (pReaderNonce_imp_isRight n) hq


end UnlinkReduction

end PRFTagReader
