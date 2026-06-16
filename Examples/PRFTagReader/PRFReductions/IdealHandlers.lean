/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.PRFReductions.Reductions

/-!
# PRF Tag/Reader Protocol — Composed Ideal Handlers

The two ideal-PRF experiments collapsed into single stateful handlers `multipleIdealQueryImpl` /
`singleIdealQueryImpl` over the unlinkability oracle interface, with their per-query reduction
lemmas exposing the lazy-random-oracle behaviour via `idealCacheStep` / `idealCacheMapM`.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ### Composed ideal-world handlers

The two ideal-PRF experiments are each a `simulateQ` of the lazy random oracle applied to the
output of a `simulateQ` of the reduction's query implementation. The `*IdealQueryImpl` definitions
below package that nested simulation as a single stateful handler over the unlinkability oracle
interface, with state `UnlinkState TagId × QueryCache`. The `simulateQ_*Ideal_collapse` lemmas show
that simulating the adversary through the composed handler reproduces the nested simulation up to
the obvious reassociation of the product state. -/

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

The `*IdealQueryImpl` handlers are `simulateQ`-wrappers; the lemmas below give their explicit
reduced forms on each oracle query, so that a coupling induction can reason about them concretely.
The lazy-random-oracle lookup at a domain point is exposed via `QueryCache` operations. -/

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
session counter. The proof uses `erw` to bridge the reducible-defeq gap between the unfolded spec
`unifSpec + ((TagId × Nonce) →ₒ Digest)` and `PRFScheme.PRFOracleSpec (TagId × Nonce) Digest`. -/
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
/-- Base case of the multiple-vs-single ideal-world coupling induction: on a `pure`
adversary the multiple- and single-session ideal handlers return the same bit, so the
multiple-world success probability is trivially bounded by the single-world one plus the
bad-event probability. Holds for arbitrary (not necessarily coupled) initial states. -/
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

end UnlinkReduction

end PRFTagReader
