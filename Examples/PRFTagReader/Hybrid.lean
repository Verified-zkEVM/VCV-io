/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.Table

/-!
# PRF Tag/Reader Protocol — Hybrid Handler

Milestone 5 of the unlinkability reduction: the hybrid table handler `hybridTableHandler`, its
state `HybridState`, and the lazy-form companion `hybridLazyHandler`. The hybrid world is the
intermediate game between the multiple-session ideal world (per-tag PRF cell) and the
single-session ideal world (per-session PRF cell): tag oracles run on the single-session table
keyed on `(tag, sid, nonce)`, but the reader oracle inspects only cells that the tag oracle has
already touched, via the recorded `sessionNonce` map.

This file also introduces the spare-fed hop-A hybrid handler `hybridSpareHandler` and the
`HybridCacheConsistent` invariant connecting `hybridLazyHandler` runs to
`hybridCacheAccepts`-based reader decisions.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]
  [SampleableType ((TagId × Fin sessionsPerTag) × Nonce → Digest)]

/-! #### Milestone 5: the hybrid table handler

The 2-hop hybrid game closing the unlinkability reduction. The hybrid world `H` runs on the
*single-session* random-oracle table `gS : (TagId × Fin sessionsPerTag) × Nonce → Digest`, with:

* a tag oracle identical to the single-session world's — session `i` of `tag` reads
  `gS ((tag, i), nonce)`, so tag queries are *per-session fresh*;
* a *session-nonce-based* reader oracle. The hybrid state carries, beside the session counters, a
  `sessionNonce : TagId × Fin sessionsPerTag → Option Nonce` recording, for each `(tag, sid)`, the
  nonce that session `sid` of `tag` drew. On a reader query at transcript `(n, v)`, the reader
  accepts when some session `(tag, sid)` has a recorded draw `sessionNonce (tag, sid) = some n`
  with `gS ((tag, sid), n) = v` — i.e. it inspects exactly the cells that honest tag queries
  actually produced.

The `sessionNonce` map is *write-once*: each session `(tag, sid)` draws exactly once (the tag
oracle writes `sessionNonce (tag, sessionsUsed tag)` and strictly increments `sessionsUsed tag`),
so a tag drawing the same nonce twice records *both* draws on distinct keys, never orphaning a
cell. This is what makes the reader sound against the within-tag nonce-collision case, and what
makes the column-freshness invariant of hop B step-stable.

Because its tag oracle matches the single world's, `H` and Single can be coupled on one shared
table `gS` and differ only in the reader (hop B): `H`'s reader checks only the drawn cells, a
subset of the single reader's all-cells check, paying the reader-slack term. -/

/-- Per-session nonce map: records, for each session `(tag, sid)`, the nonce that session drew in
its tag query, or `none` if that session has not been used yet. The hybrid world threads a
`HybridSessionNonce` beside its session counters so that its reader can inspect exactly the cells
that honest tag queries produced. The map is write-once: each `(tag, sid)` is set exactly once. -/
def HybridSessionNonce (TagId Nonce : Type) (sessionsPerTag : ℕ) : Type :=
  TagId × Fin sessionsPerTag → Option Nonce

/-- Empty session-nonce map: no session has drawn a nonce yet. -/
def HybridSessionNonce.init {TagId Nonce : Type} {sessionsPerTag : ℕ} :
    HybridSessionNonce TagId Nonce sessionsPerTag := fun _ => none

/-- Hybrid-world handler state: the session counters together with the session-nonce map. -/
structure HybridState (TagId Nonce : Type) (sessionsPerTag : ℕ) where
  sessionsUsed : TagId → ℕ
  sessionNonce : HybridSessionNonce TagId Nonce sessionsPerTag

/-- Initial hybrid-world state: no sessions used, empty session-nonce map. -/
def HybridState.init {TagId Nonce : Type} {sessionsPerTag : ℕ} :
    HybridState TagId Nonce sessionsPerTag where
  sessionsUsed := fun _ => 0
  sessionNonce := HybridSessionNonce.init

/-- Reader acceptance for the hybrid world at session-nonce map `sn` and single-session table `gS`:
accept the transcript when some session `(tag, sid)` has a recorded draw
`sn (tag, sid) = some nonce` whose cell `gS ((tag, sid), nonce)` matches the authenticator. Only
the cells that honest tag queries actually produced are inspected. -/
def hybridReaderAccepts (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (transcript : TagTranscript Nonce Digest) : Bool :=
  decide (∃ tag : TagId, ∃ sid : Fin sessionsPerTag,
    sn (tag, sid) = some transcript.nonce ∧
      gS ((tag, sid), transcript.nonce) = transcript.auth)

/-- Hybrid-world tag oracle keyed on the single-session table `gS`: identical to the
single-session tag oracle on the session counter, additionally recording the drawn nonce in the
session-nonce map. Session `sid := sessionsUsed tag` of `tag` samples `nonce`, sets
`sessionNonce (tag, sid) := some nonce`, and returns `⟨nonce, gS ((tag, sid), nonce)⟩`. -/
noncomputable def hybridTagHandler (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) :
    QueryImpl (TagId →ₒ Option (TagTranscript Nonce Digest))
      (StateT (HybridState TagId Nonce sessionsPerTag) ProbComp) := fun tag => do
  let st ← get
  if h : st.sessionsUsed tag < sessionsPerTag then
    let sid : Fin sessionsPerTag := ⟨st.sessionsUsed tag, h⟩
    let nonce ← ($ᵗ Nonce : ProbComp Nonce)
    set
      ({ sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1)
         sessionNonce := Function.update st.sessionNonce (tag, sid) (some nonce) } :
        HybridState TagId Nonce sessionsPerTag)
    return some (⟨nonce, gS ((tag, sid), nonce)⟩ : TagTranscript Nonce Digest)
  else
    return none

/-- Hybrid-world reader oracle keyed on the single-session table `gS`: deterministic session-nonce
acceptance against `gS`, with the state untouched. -/
noncomputable def hybridReaderHandler (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) :
    QueryImpl ((TagTranscript Nonce Digest) →ₒ ReaderReply)
      (StateT (HybridState TagId Nonce sessionsPerTag) ProbComp) := fun transcript => fun s =>
  pure (ReaderReply.ofBool (hybridReaderAccepts gS s.sessionNonce transcript), s)

/-- Deterministic hybrid handler keyed on a single-session random-oracle table
`gS : (TagId × Fin sessionsPerTag) × Nonce → Digest`: the session-nonce-recording single-session
tag oracle paired with the session-nonce-consulting reader oracle. -/
noncomputable def hybridTableHandler (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (HybridState TagId Nonce sessionsPerTag) ProbComp) :=
  hybridTagHandler gS + hybridReaderHandler gS

/-- `simulateQ hybridTableHandler` of a `query_bind`, run from a state and projected to its
output: the per-query handler followed by the recursive simulation of the continuation. -/
lemma hybridTable_run'_query_bind' {α : Type}
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : HybridState TagId Nonce sessionsPerTag) :
    (simulateQ (hybridTableHandler gS) (liftM (OracleSpec.query t) >>= f)).run' s =
      (hybridTableHandler gS t s) >>= fun p =>
        (simulateQ (hybridTableHandler gS) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- `hybridTableHandler` on a tag query with the slot budget exhausted: returns `none`, state
unchanged. -/
lemma hybridTableHandler_tag_run_of_not_lt
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (s : HybridState TagId Nonce sessionsPerTag)
    (hslot : ¬ s.sessionsUsed tag < sessionsPerTag) :
    (hybridTableHandler gS (Sum.inl tag) s) = pure (none, s) := by
  unfold hybridTableHandler
  rw [QueryImpl.add_apply_inl]
  change (hybridTagHandler gS tag).run s = _
  unfold hybridTagHandler
  simp [StateT.run_bind, StateT.run_get, hslot]

/-- `hybridTableHandler` on a tag query with a free slot: sample a nonce, look up the table at
`((tag, sid), nonce)`, advance the session counter, and record the draw in the session-nonce map. -/
lemma hybridTableHandler_tag_run_of_lt
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (tag : TagId) (s : HybridState TagId Nonce sessionsPerTag)
    (hslot : s.sessionsUsed tag < sessionsPerTag) :
    (hybridTableHandler gS (Sum.inl tag) s) =
      ($ᵗ Nonce) >>= fun nonce =>
        pure (some (⟨nonce, gS ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce)⟩ :
            TagTranscript Nonce Digest),
          ({ sessionsUsed :=
              Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)
             sessionNonce := Function.update s.sessionNonce (tag, ⟨s.sessionsUsed tag, hslot⟩)
              (some nonce) } :
            HybridState TagId Nonce sessionsPerTag)) := by
  unfold hybridTableHandler
  rw [QueryImpl.add_apply_inl]
  change (hybridTagHandler gS tag).run s = _
  unfold hybridTagHandler
  simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    hslot, bind_pure_comp]

/-- `hybridTableHandler` on a reader query: deterministic session-nonce acceptance against the
table, state untouched. -/
lemma hybridTableHandler_reader_run
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (transcript : TagTranscript Nonce Digest) (s : HybridState TagId Nonce sessionsPerTag) :
    (hybridTableHandler gS (Sum.inr transcript) s) =
      pure (ReaderReply.ofBool (hybridReaderAccepts gS s.sessionNonce transcript), s) := by
  simp [hybridTableHandler, QueryImpl.add_apply_inr, hybridReaderHandler]

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] in
/-- Hybrid session-nonce acceptance is monotone in the table-cell agreement: whenever the hybrid
reader accepts a transcript at session-nonce map `sn` and table `gS`, the single-session reader
`unlinkReaderAccepts … singlePattern` at the same table also accepts it — `H`'s accept condition
inspects a *subset* of the cells the single reader checks (only the drawn ones). -/
lemma hybridReaderAccepts_imp_singleReaderAccepts
    (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (transcript : TagTranscript Nonce Digest)
    (h : hybridReaderAccepts gS sn transcript = true) :
    unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
      (fun slot nonce => gS (slot, nonce))
      (singlePattern (TagId := TagId) sessionsPerTag) transcript = true := by
  unfold hybridReaderAccepts at h
  unfold unlinkReaderAccepts tagAccepts singlePattern
  simp only [decide_eq_true_eq] at h ⊢
  obtain ⟨tag, sid, _, hcell⟩ := h
  exact ⟨tag, sid, hcell⟩

/-! #### Hybrid-to-single: the lazy hybrid handler and its eager-table equivalence

`hybridTableHandler` runs the hybrid world `H` against a *pre-sampled* single-session table `gS`.
For the hop-B coupling we instead need `H` and `Single` to share a *lazily-sampled* random-oracle
cache, so that the cells the single reader inspects but the hybrid reader does not are genuinely
fresh at each reader query. `hybridLazyHandler` is that lazy form: its state is
`HybridState × QueryCache` over the single-session domain `(TagId × Fin sessionsPerTag) × Nonce`,
its tag oracle samples a nonce and consults the cache via `idealCacheStep` (recording the draw in
the session-nonce map), and its reader oracle inspects only the drawn cache cells. -/

/-- Reader acceptance for the lazy hybrid world, read directly off the random-oracle cache `c`:
accept the transcript when some session `(tag, sid)` has a recorded draw
`sn (tag, sid) = some nonce` whose cached cell `c ((tag, sid), nonce)` equals the authenticator.
This is `hybridReaderAccepts` with the table lookup replaced by a cache lookup. -/
def hybridCacheAccepts
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (transcript : TagTranscript Nonce Digest) : Bool :=
  decide (∃ tag : TagId, ∃ sid : Fin sessionsPerTag,
    sn (tag, sid) = some transcript.nonce ∧
      c ((tag, sid), transcript.nonce) = some transcript.auth)

/-- Lazy hybrid handler: the hybrid world `H` run against a lazily-sampled random-oracle cache
rather than a pre-sampled table. The tag oracle samples a nonce, consults the cache at
`((tag, sid), nonce)` via `idealCacheStep`, advances the session counter, and records the draw in
the session-nonce map. The reader oracle inspects only the drawn cache cells via
`hybridCacheAccepts`. -/
noncomputable def hybridLazyHandler :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (HybridState TagId Nonce sessionsPerTag ×
        (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag => do
        let s := p.1
        if h : s.sessionsUsed tag < sessionsPerTag then
          let sid : Fin sessionsPerTag := ⟨s.sessionsUsed tag, h⟩
          let nonce ← ($ᵗ Nonce : ProbComp Nonce)
          let r ← idealCacheStep p.2 ((tag, sid), nonce)
          pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            ({ sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)
               sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } :
              HybridState TagId Nonce sessionsPerTag), r.2)
        else
          pure (none, p)
    | Sum.inr transcript =>
        pure (ReaderReply.ofBool (hybridCacheAccepts p.2 p.1.sessionNonce transcript), p)

/-- `simulateQ hybridLazyHandler` of a `query_bind`, run from a state and projected to its
output: the per-query handler followed by the recursive simulation of the continuation. -/
lemma hybridLazy_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ hybridLazyHandler (liftM (OracleSpec.query t) >>= f)).run' sH =
      (hybridLazyHandler t sH) >>= fun p =>
        (simulateQ hybridLazyHandler (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridLazyHandler` on a tag query whose slot budget is exhausted: returns `none`, state
unchanged. -/
lemma hybridLazyHandler_tag_run_of_not_lt (tag : TagId)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hslot : ¬ sH.1.sessionsUsed tag < sessionsPerTag) :
    (hybridLazyHandler (Sum.inl tag)) sH = pure (none, sH) := by
  change dite _ _ _ = _; exact dif_neg hslot

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridLazyHandler` on a tag query with a free slot: sample a nonce, consult the cache at
`((tag, sid), nonce)` via `idealCacheStep`, advance the session counter, record the draw. -/
lemma hybridLazyHandler_tag_run_of_lt (tag : TagId)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hslot : sH.1.sessionsUsed tag < sessionsPerTag) :
    (hybridLazyHandler (Sum.inl tag)) sH =
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep sH.2 ((tag, ⟨sH.1.sessionsUsed tag, hslot⟩), nonce) >>= fun r =>
          pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
            ({ sessionsUsed :=
                Function.update sH.1.sessionsUsed tag (sH.1.sessionsUsed tag + 1)
               sessionNonce := Function.update sH.1.sessionNonce
                (tag, ⟨sH.1.sessionsUsed tag, hslot⟩) (some nonce) } :
              HybridState TagId Nonce sessionsPerTag), r.2) := by
  show (if h : sH.1.sessionsUsed tag < sessionsPerTag then
      ($ᵗ Nonce) >>= fun nonce =>
        idealCacheStep sH.2 ((tag, ⟨sH.1.sessionsUsed tag, h⟩), nonce) >>= fun r =>
          pure (_, _, r.2)
      else pure (none, sH)) = _
  rw [dif_pos hslot]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridLazyHandler` on a reader query: deterministic session-nonce acceptance read off the
cache, state untouched. -/
lemma hybridLazyHandler_reader_run (transcript : TagTranscript Nonce Digest)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (hybridLazyHandler (Sum.inr transcript)) sH =
      pure (ReaderReply.ofBool (hybridCacheAccepts sH.2 sH.1.sessionNonce transcript), sH) := by
  rfl

/-- Session-nonce / cache consistency invariant for the lazy hybrid handler: every cell recorded in
the session-nonce map is already present in the random-oracle cache. The lazy hybrid tag oracle
maintains this invariant — it records `sessionNonce (tag, sid) := some nonce` exactly when it
caches the cell `((tag, sid), nonce)` — and it is what lets the lazy reader (which reads only
cached cells) agree with the table reader (which reads the overlaid table `tableExtending c g`). -/
def HybridCacheConsistent
    (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) : Prop :=
  ∀ (tag : TagId) (sid : Fin sessionsPerTag) (n : Nonce),
    s.sessionNonce (tag, sid) = some n → (c ((tag, sid), n)).isSome

omit [Fintype TagId] [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The initial hybrid state with the empty cache is session-nonce / cache consistent: the empty
session-nonce map records nothing. -/
lemma hybridCacheConsistent_init :
    HybridCacheConsistent (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) HybridState.init ∅ := by
  intro tag sid n h
  simp [HybridState.init, HybridSessionNonce.init] at h

omit [Fintype TagId] [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The lazy hybrid tag oracle preserves session-nonce / cache consistency: a tag query at `tag`
with a free slot caches the freshly drawn cell `((tag, sid), nonce)` and records exactly that draw,
while leaving every previously recorded draw both still recorded and still cached. The write is to
the fresh key `(tag, sid)`, never overwriting an existing record. -/
lemma hybridCacheConsistent_tag_step
    (tag : TagId) (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hcons : HybridCacheConsistent s c)
    (hslot : s.sessionsUsed tag < sessionsPerTag) (nonce : Nonce)
    (r : Digest × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheStep c ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce))) :
    HybridCacheConsistent
      ({ sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)
         sessionNonce := Function.update s.sessionNonce (tag, ⟨s.sessionsUsed tag, hslot⟩)
          (some nonce) } : HybridState TagId Nonce sessionsPerTag)
      r.2 := by
  classical
  intro tag' sid' n' hsn
  dsimp only [HybridState.sessionNonce] at hsn
  by_cases hkey : (tag', sid') = (tag, ⟨s.sessionsUsed tag, hslot⟩)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hkey
    rw [Function.update_self] at hsn
    obtain rfl := Option.some.injEq .. ▸ hsn
    exact idealCacheStep_cache_self c _ r hr ▸ rfl
  · rw [Function.update_of_ne hkey] at hsn
    have hcell := hcons tag' sid' n' hsn
    by_cases hcellkey : ((tag', sid'), n') = ((tag, ⟨s.sessionsUsed tag, hslot⟩), nonce)
    · rw [hcellkey, idealCacheStep_cache_self c _ r hr]; rfl
    · rw [idealCacheStep_cache_off c _ r hr _ hcellkey]; exact hcell

omit [SampleableType Nonce] [SampleableType Digest] in
/-- Under session-nonce / cache consistency, the lazy hybrid reader (reading only cached cells)
agrees with the table hybrid reader run against the overlaid table `tableExtending c g`: every
drawn cell is cached, so its cached value equals its `tableExtending` value, and the two acceptance
tests coincide. -/
lemma hybridCacheAccepts_eq_hybridReaderAccepts_tableExtending
    (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (g : (TagId × Fin sessionsPerTag) × Nonce → Digest)
    (hcons : HybridCacheConsistent s c)
    (transcript : TagTranscript Nonce Digest) :
    hybridCacheAccepts c s.sessionNonce transcript =
      hybridReaderAccepts (OracleComp.tableExtending c g) s.sessionNonce transcript := by
  unfold hybridCacheAccepts hybridReaderAccepts
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · rintro ⟨tag, sid, hsn, hcv⟩
    refine ⟨tag, sid, hsn, ?_⟩
    simp only [OracleComp.tableExtending, hcv, Option.getD_some]
  · rintro ⟨tag, sid, hsn, hcv⟩
    refine ⟨tag, sid, hsn, ?_⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hcons tag sid transcript.nonce hsn)
    rw [OracleComp.tableExtending, hv, Option.getD_some] at hcv
    rw [hv, hcv]

/-- **Hybrid-to-single, Step 1.** Running the lazy hybrid handler from a session-nonce / cache consistent
state `(s, c)` has the same output distribution as sampling a full single-session random-oracle
table `g`, overlaying the cache `c`, and running the deterministic table hybrid handler
`hybridTableHandler (tableExtending c g)` from `s`. The hybrid analogue of
`evalDist_simulateQ_singleIdealQueryImpl_run'_eq_tableExtending`. -/
lemma evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hcons : HybridCacheConsistent s c) :
    𝒟[(simulateQ hybridLazyHandler oa).run' (s, c)] =
      𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (simulateQ (hybridTableHandler (OracleComp.tableExtending c g)) oa).run' s] := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [hybridLazy_run'_query_bind']
    have hrhs : 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
          (simulateQ (hybridTableHandler (OracleComp.tableExtending c g))
            (liftM (OracleSpec.query t) >>= f)).run' s]
        = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (hybridTableHandler (OracleComp.tableExtending c g) t s) >>= fun p =>
              (simulateQ (hybridTableHandler (OracleComp.tableExtending c g))
                (f p.1)).run' p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [hybridTable_run'_query_bind']
    rw [hrhs]
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · rw [hybridLazyHandler_tag_run_of_lt tag (s, c) hslot]
        set sid := (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag)
        set adv : Nonce → HybridState TagId Nonce sessionsPerTag := fun nonce =>
          { sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1),
            sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) }
        have hlhs_reassoc :
            ((($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), adv nonce, r.2))
              >>= fun p =>
              (simulateQ hybridLazyHandler (f p.1)).run' p.2)
            = (($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                (simulateQ hybridLazyHandler
                  (f (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv nonce, r.2)) := by
          simp only [bind_assoc, pure_bind]
        refine (congrArg evalDist hlhs_reassoc).trans ?_
        have hlhs_inner : ∀ (n : Nonce),
            𝒟[idealCacheStep c ((tag, sid), n) >>= fun r =>
              (simulateQ hybridLazyHandler
                (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv n, r.2)]
            = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                  (simulateQ (hybridTableHandler (OracleComp.tableExtending c g))
                    (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                      TagTranscript Nonce Digest)))).run' (adv n)] := by
          intro n
          set Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun g' =>
            (simulateQ (hybridTableHandler g')
              (f (some (⟨n, g' ((tag, sid), n)⟩ : TagTranscript Nonce Digest)))).run' (adv n)
            with hMψ
          refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp c ((tag, sid), n) Mψ)
          refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
          rw [ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) (adv n) r.2
            (hybridCacheConsistent_tag_step tag s c hcons hslot n r hr)]
          refine congrArg _ (congrArg _ (funext fun g => ?_))
          have hcell : OracleComp.tableExtending r.2 g ((tag, sid), n) = r.1 := by
            simp only [OracleComp.tableExtending,
              idealCacheStep_cache_self c ((tag, sid), n) r hr, Option.getD_some]
          rw [hMψ]
          simp only [hcell]
        simp only [hybridTableHandler_tag_run_of_lt _ tag s hslot]
        have hrhs_swap :
            (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
              (($ᵗ Nonce) >>= fun nonce =>
                pure (some (⟨nonce, OracleComp.tableExtending c g ((tag, sid), nonce)⟩ :
                  TagTranscript Nonce Digest), adv nonce)) >>= fun p =>
                (simulateQ (hybridTableHandler (OracleComp.tableExtending c g))
                  (f p.1)).run' p.2)
            = (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                ($ᵗ Nonce) >>= fun n =>
                (simulateQ (hybridTableHandler (OracleComp.tableExtending c g))
                  (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                    TagTranscript Nonce Digest)))).run' (adv n)) := by
          simp only [bind_assoc, pure_bind]
        refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
        rw [evalDist_probComp_bind_comm ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
          ($ᵗ Nonce)]
        refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        exact hlhs_inner n
      · rw [hybridLazyHandler_tag_run_of_not_lt tag (s, c) hslot]
        change 𝒟[(simulateQ hybridLazyHandler (f none)).run' (s, c)] = _
        rw [ih none s c hcons]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hybridTableHandler_tag_run_of_not_lt _ tag s hslot]
        rfl
    | inr transcript =>
      rw [hybridLazyHandler_reader_run transcript (s, c)]
      change 𝒟[(simulateQ hybridLazyHandler
          (f (ReaderReply.ofBool (hybridCacheAccepts c s.sessionNonce
            transcript)))).run' (s, c)] = _
      rw [ih _ s c hcons]
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [hybridTableHandler_reader_run _ transcript s,
        hybridCacheAccepts_eq_hybridReaderAccepts_tableExtending s c g hcons transcript]
      rfl

/-- **Hybrid-to-single, deliverable 1.** Eager form of the hybrid-world success probability: running the
lazy hybrid handler from the initial state has the same success probability as sampling a full
single-session random-oracle table `gS` up front and running the deterministic table hybrid
handler. The hybrid analogue of `probOutput_singleIdeal_run'_eq_tableSample`. -/
lemma probOutput_hybrid_run'_eq_tableSample [Fintype Nonce] [Finite Digest]
    (adv : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | (simulateQ (hybridLazyHandler (sessionsPerTag := sessionsPerTag)) adv).run'
        (HybridState.init, ∅)] =
      Pr[= true | ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gS =>
        (simulateQ (hybridTableHandler gS) adv).run' HybridState.init] := by
  rw [probOutput_def, probOutput_def,
    evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending adv HybridState.init ∅
      hybridCacheConsistent_init]
  simp only [OracleComp.tableExtending_empty]

/-! #### Multiple-to-hybrid: the spare-fed hybrid handler

The hop-A coupling pairs the multiple world against the hybrid world. The multiple world's reader
queries *write* random-oracle cells keyed on `(TagId × Nonce)` that a later multiple tag query may
reuse; the hybrid world's reader is read-only, so there is no cell for the coupling to align with.
`hybridSpareHandler` is a distribution-preserving reformulation of `hybridLazyHandler` carrying an
extra **spare reservoir** — a `((TagId × Nonce) →ₒ Digest).QueryCache` with the same key shape as
the multiple world's cache. Its reader, beyond the read-only session-cache acceptance test of
`hybridLazyHandler`, folds `idealCacheStep` over `(tag, transcript.nonce)` for every tag, drawing
fresh uniform digests into the reservoir (write-once: `idealCacheStep` skips cells already cached).
Its tag oracle draws a nonce `n` and, if the reservoir already holds `(tag, n)`, consumes that
spare as the tag digest; otherwise it draws fresh exactly as `hybridLazyHandler` does. -/

/-- Spare-fed hybrid handler: `hybridLazyHandler` augmented with a spare reservoir keyed on
`(TagId × Nonce)`. The reader additionally populates the reservoir with fresh uniform digests at
`(tag, transcript.nonce)` for every tag (write-once via `idealCacheStep`), leaving the read-only
output bit unchanged. The tag oracle draws a nonce `n`; if the reservoir holds a spare at
`(tag, n)` it consumes it as the tag digest, recording it in the session cell `((tag, sid), n)` and
*clearing* the reservoir cell so the spare is consumed at most once; otherwise it draws fresh via
`idealCacheStep` on the session cache. -/
noncomputable def hybridSpareHandler :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (HybridState TagId Nonce sessionsPerTag ×
        (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache ×
        ((TagId × Nonce) →ₒ Digest).QueryCache) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag => do
        let s := p.1
        if h : s.sessionsUsed tag < sessionsPerTag then
          let sid : Fin sessionsPerTag := ⟨s.sessionsUsed tag, h⟩
          let nonce ← ($ᵗ Nonce : ProbComp Nonce)
          match p.2.2 (tag, nonce) with
          | some d =>
              pure (some (⟨nonce, d⟩ : TagTranscript Nonce Digest),
                ({ sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)
                   sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } :
                  HybridState TagId Nonce sessionsPerTag),
                p.2.1.cacheQuery ((tag, sid), nonce) d,
                Function.update p.2.2 (tag, nonce) none)
          | none => do
              let r ← idealCacheStep p.2.1 ((tag, sid), nonce)
              pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
                ({ sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1)
                   sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } :
                  HybridState TagId Nonce sessionsPerTag),
                r.2, p.2.2)
        else
          pure (none, p)
    | Sum.inr transcript => do
        let rs ← idealCacheMapM ((Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, transcript.nonce))) p.2.2
        pure (ReaderReply.ofBool (hybridCacheAccepts p.2.1 p.1.sessionNonce transcript),
          p.1, p.2.1, rs.2)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridSpareHandler` on a tag query whose slot budget is exhausted: returns `none`, state
unchanged. -/
lemma hybridSpareHandler_tag_run_of_not_lt (tag : TagId)
    (p : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache ×
      ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hslot : ¬ p.1.sessionsUsed tag < sessionsPerTag) :
    (hybridSpareHandler (Sum.inl tag)) p = pure (none, p) := by
  change dite _ _ _ = _; exact dif_neg hslot

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridSpareHandler` on a tag query with a free slot: sample a nonce, then branch on the spare
reservoir. The handler reduces to sampling a nonce followed by the reservoir-keyed continuation
`hybridSpareTagStep`, which consumes a reservoir spare when present and draws fresh otherwise. -/
lemma hybridSpareHandler_tag_run_of_lt (tag : TagId)
    (p : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache ×
      ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hslot : p.1.sessionsUsed tag < sessionsPerTag) :
    (hybridSpareHandler (Sum.inl tag)) p =
      ($ᵗ Nonce) >>= fun nonce =>
        (match p.2.2 (tag, nonce) with
          | some d =>
              pure (some (⟨nonce, d⟩ : TagTranscript Nonce Digest),
                ({ sessionsUsed :=
                    Function.update p.1.sessionsUsed tag (p.1.sessionsUsed tag + 1)
                   sessionNonce := Function.update p.1.sessionNonce
                    (tag, ⟨p.1.sessionsUsed tag, hslot⟩) (some nonce) } :
                  HybridState TagId Nonce sessionsPerTag),
                p.2.1.cacheQuery ((tag, ⟨p.1.sessionsUsed tag, hslot⟩), nonce) d,
                Function.update p.2.2 (tag, nonce) none)
          | none =>
              idealCacheStep p.2.1 ((tag, ⟨p.1.sessionsUsed tag, hslot⟩), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
                  ({ sessionsUsed :=
                      Function.update p.1.sessionsUsed tag (p.1.sessionsUsed tag + 1)
                     sessionNonce := Function.update p.1.sessionNonce
                      (tag, ⟨p.1.sessionsUsed tag, hslot⟩) (some nonce) } :
                    HybridState TagId Nonce sessionsPerTag),
                  r.2, p.2.2)) := by
  change (if h : p.1.sessionsUsed tag < sessionsPerTag then
      ($ᵗ Nonce) >>= fun nonce =>
        (match p.2.2 (tag, nonce) with
          | some d => pure (_, _, _, Function.update p.2.2 (tag, nonce) none)
          | none => idealCacheStep p.2.1 ((tag, ⟨p.1.sessionsUsed tag, h⟩), nonce) >>= fun r =>
              pure (_, _, r.2, p.2.2))
      else pure (none, p)) = _
  rw [dif_pos hslot]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridSpareHandler` on a reader query: fold `idealCacheStep` over the reservoir cells
`(tag, transcript.nonce)` for every tag (write-once spare population), and return the read-only
session-cache acceptance bit unchanged from `hybridLazyHandler`. -/
lemma hybridSpareHandler_reader_run (transcript : TagTranscript Nonce Digest)
    (p : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache ×
      ((TagId × Nonce) →ₒ Digest).QueryCache) :
    (hybridSpareHandler (Sum.inr transcript)) p =
      idealCacheMapM ((Finset.univ : Finset TagId).toList.map
          (fun tag => (tag, transcript.nonce))) p.2.2 >>= fun rs =>
        pure (ReaderReply.ofBool (hybridCacheAccepts p.2.1 p.1.sessionNonce transcript),
          p.1, p.2.1, rs.2) := by
  rfl

end UnlinkReduction

end PRFTagReader
