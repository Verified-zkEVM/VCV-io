/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# PRF Tag/Reader Protocol — Reductions and Bridge Lemmas

PRF distinguishers derived from an unlinkability adversary, in both the multiple-session and
single-session worlds, together with the PRF-real faithfulness lemmas
(`prfRealExp_unlinkToMultiplePRFReduction_eq_unlinkMultipleExp` and
`prfRealExp_unlinkToSinglePRFReduction_eq_unlinkSingleExp`).
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
oracle on `(TagId × Nonce)` turns the game into a PRF distinguisher. -/

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

The three lemmas below are the analytic content of the reduction. The first two are PRF-real
faithfulness lemmas (each provable by the same simulation-collapse argument as the auth-side
`prfRealExp_authToPRFReduction_eq_authExp`); the third is the identical-until-bad coupling. -/

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
/-- Inductive helper, multiple-session world: simulating the unlinkability adversary through the
reduction's query implementation and then through the real PRF query implementation is the same,
state-by-state, as simulating it directly through the real multiple-session query implementation
with the hash set to `prfs.evalMultiple k`. -/
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
/-- Inductive helper, single-session world: simulating the unlinkability adversary through the
reduction's query implementation and then through the real PRF query implementation is the same,
state-by-state, as simulating it directly through the real single-session query implementation
with the hash set to `prfs.evalSingle k`. -/
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

end UnlinkReduction

end PRFTagReader
