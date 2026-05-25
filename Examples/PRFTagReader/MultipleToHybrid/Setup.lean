/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.HybridToSingle

/-!
# PRF Tag/Reader Protocol — Multiple-to-hybrid coupling setup

Coupling infrastructure for the multiple-session → hybrid transition of the unlinkability
reduction. Includes:

* the multiple-vs-hybrid cache coupling invariants `MHBInv`, `MHBRel`, and the reader-aware
  refinement `MultipleHybridCoupling`;
* the instrumented multiple-session handler `multipleBadQueryImpl` with its bad-flag advance
  `multipleBadAdvance` and per-query reductions;
* the spare-draw distribution-neutrality lemmas (`evalDist_bind_const_eq`,
  `evalDist_idealCacheMapM_bind_const_eq`);
* the `MultipleHybridColFresh` predicate tracking collision-freshness across reader queries;
* initial-state lemmas (`MHBInv_init`, `MHBRel_init`, `MultipleHybridCoupling_init`,
  `multipleHybridColFresh_init`).

The eager-table coupling proof itself (`multipleBadEager_le_hybridEager_aux`) lives in the
sibling `MultipleToHybrid.Eager` module.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

section EagerComposed

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ### Multiple-to-hybrid: the multiple-vs-hybrid cache coupling

This couples the multiple-session ideal handler `multipleIdealQueryImpl` (a lazy random oracle
over `TagId × Nonce`, whose tag oracle reuses the cell `(tag, nonce)` whenever two sessions of one
tag draw the same nonce) against the per-session-fresh hybrid handler `hybridLazyHandler` (a lazy
random oracle over `(TagId × Fin sessionsPerTag) × Nonce`, whose tag oracle always consults a fresh
session slot `(tag, sid)`). Off the within-tag nonce collision the two worlds produce the same
fresh-uniform digest, so the gap is charged to two terms: the collision goes into the bad-world
probability `Pr[bad]` and the reader-cell asymmetry goes into the reader-slack
`qReader * |TagId| / |Digest|`.

The coupling is threaded by `MHBInv`, a state relation on the three handler states (the multiple
cache, the hybrid cache + session-nonce map, and the bad-world `responses` cache). -/

/-- **Multiple-to-hybrid coupling invariant.** Relates a multiple-session ideal state `sM`, a hybrid-world state
`sH`, and a bad-event state `sB`. It records that:

* the three worlds' session counters agree (reader-stable, untouched by reader queries);
* the bad flag has not yet fired;
* the multiple cache and the bad-world `responses` cache have the same support — a `(tag, nonce)`
  pair is cached in the multiple world exactly when it has a recorded random-function response in
  the bad world (off `bad`, the bad world has drawn each cached pair exactly once, so its response
  list is a singleton);
* the multiple cache cell at a *tag-drawn* nonce mirrors the corresponding per-session hybrid cell:
  whenever a hybrid session `(tag, sid)` recorded the draw `sn (tag, sid) = some nonce`, the
  multiple cell `(tag, nonce)` and the hybrid cell `((tag, sid), nonce)` carry the same digest;
* the hybrid session-nonce map is collision-free per tag: at most one session of each tag has
  drawn any given nonce (this is exactly the off-collision regime);
* the hybrid session-nonce map is write-once: a session at or beyond the session counter has no
  recorded nonce;
* the hybrid cache only records cells produced by a tag draw: a cached hybrid cell
  `((tag, sid), nonce)` has `sessionNonce (tag, sid) = some nonce`;
* conversely the hybrid cache and session-nonce map are consistent: a recorded draw
  `sessionNonce (tag, sid) = some nonce` has the cell `((tag, sid), nonce)` cached. -/
def MHBInv
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) : Prop :=
  sM.1.sessionsUsed = sH.1.sessionsUsed ∧
    sM.1.sessionsUsed = sB.sessionsUsed ∧
    sB.bad = false ∧
    (∀ tag n, (sM.2 (tag, n)).isSome ↔ (sB.responses (tag, n)).isSome) ∧
    (∀ tag sid n, sH.1.sessionNonce (tag, sid) = some n →
      sM.2 (tag, n) = sH.2 ((tag, sid), n)) ∧
    (∀ tag sid₁ sid₂ n, sH.1.sessionNonce (tag, sid₁) = some n →
      sH.1.sessionNonce (tag, sid₂) = some n → sid₁ = sid₂) ∧
    (∀ tag (sid : Fin sessionsPerTag), sH.1.sessionsUsed tag ≤ sid.val →
      sH.1.sessionNonce (tag, sid) = none) ∧
    (∀ tag sid n, (sH.2 ((tag, sid), n)).isSome →
      sH.1.sessionNonce (tag, sid) = some n) ∧
    (∀ tag sid n, sH.1.sessionNonce (tag, sid) = some n →
      (sH.2 ((tag, sid), n)).isSome)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The three initial states satisfy the hop-A coupling invariant: counters are all zero, the bad
flag is unset, all caches and the session-nonce map are empty. -/
lemma MHBInv_init :
    MHBInv (TagId := TagId) (Nonce := Nonce) (Digest := Digest) (sessionsPerTag := sessionsPerTag)
      (UnlinkState.init, ∅) (HybridState.init, ∅) UnlinkBadState.init := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tag n; simp [UnlinkBadState.init]
  · intro tag sid n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])
  · intro tag sid₁ sid₂ n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])
  · intro tag sid _; rfl
  · intro tag sid n h; exact absurd h (by simp)
  · intro tag sid n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])

/-- The list of multiple-world cells inspected by a reader query at `transcript.nonce`: one cell
`(tag, transcript.nonce)` per tag. -/
noncomputable def multipleReaderCells (transcript : TagTranscript Nonce Digest) :
    List (TagId × Nonce) :=
  (Finset.univ : Finset TagId).toList.map (fun tag => (tag, transcript.nonce))

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The multiple-world reader-cell list is duplicate-free. -/
lemma multipleReaderCells_nodup (transcript : TagTranscript Nonce Digest) :
    (multipleReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      transcript).Nodup := by
  unfold multipleReaderCells
  refine (Finset.univ : Finset TagId).nodup_toList.map ?_
  intro a b hab
  simpa using hab

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The multiple-world reader-cell list has exactly `|TagId|` cells. -/
lemma multipleReaderCells_length (transcript : TagTranscript Nonce Digest) :
    (multipleReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      transcript).length = Fintype.card TagId := by
  unfold multipleReaderCells
  rw [List.length_map, Finset.length_toList, Finset.card_univ]

omit [Nonempty TagId] [SampleableType Nonce] in
/-- **Per-reader-query multiple-vs-hybrid disagreement bound.** Fix a multiple cache `cM`, a hybrid
cache `cH` and a session-nonce map `sn`. Suppose every multiple cell `(tag, transcript.nonce)` that
is *already cached* was produced by a tag draw — recorded in `sn` (`hcol`) — and that every
tag-drawn cell of the multiple cache mirrors the hybrid cache (`hcorr`, the `MHBInv` cache
correspondence). Then, folding `idealCacheStep` over the `|TagId|` multiple reader cells, the
probability that the multiple reader accepts while the hybrid reader (`hybridCacheAccepts`) rejects
is at most `|TagId| / |Digest|`: the only way they disagree is a fresh draw at a never-drawn cell
hitting the authenticator, bounded by `probEvent_idealCacheMapM_mem_le`. -/
lemma probEvent_multipleReader_disagree_le [Fintype Digest]
    (cM : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (cH : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (transcript : TagTranscript Nonce Digest)
    (hcol : ∀ tag, (cM (tag, transcript.nonce)).isSome →
      ∃ sid, sn (tag, sid) = some transcript.nonce)
    (hcorr : ∀ tag sid n, sn (tag, sid) = some n → cM (tag, n) = cH ((tag, sid), n)) :
    Pr[fun rs : List Digest × ((TagId × Nonce) →ₒ Digest).QueryCache =>
        decide (∃ d ∈ rs.1, d = transcript.auth) = true ∧
          hybridCacheAccepts (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) cH sn transcript = false |
        idealCacheMapM (multipleReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          transcript) cM] ≤
      (Fintype.card TagId : ℕ) / (Fintype.card Digest : ℝ≥0∞) := by
  classical
  rw [← multipleReaderCells_length (TagId := TagId) (Digest := Digest) transcript]
  push_cast
  refine le_trans (probEvent_mono fun rs _ hrs => ?_)
    (probEvent_idealCacheMapM_mem_le _
      (multipleReaderCells_nodup (TagId := TagId) (Digest := Digest) transcript) cM
      transcript.auth)
  obtain ⟨haccept, hreject⟩ := hrs
  rw [decide_eq_true_eq] at haccept
  refine ⟨haccept.1, fun cell hcell hcc => ?_⟩
  obtain ⟨tag, rfl⟩ : ∃ tag, cell = (tag, transcript.nonce) := by
    unfold multipleReaderCells at hcell
    rw [List.mem_map] at hcell
    obtain ⟨tag, _, rfl⟩ := hcell
    exact ⟨tag, rfl⟩
  -- the cell `(tag, transcript.nonce)` is cached and equals `auth`; it must be tag-drawn
  obtain ⟨sid, hsid⟩ := hcol tag (by rw [hcc]; rfl)
  rw [hybridCacheAccepts, decide_eq_false_iff_not] at hreject
  refine hreject ⟨tag, sid, hsid, ?_⟩
  rw [← hcorr tag sid transcript.nonce hsid, hcc]

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Multiple-to-hybrid, off-collision tag-step invariant preservation.** Given `MHBInv sM sH sB`, a free slot
`hslot`, an off-collision nonce `n` (`sM.2 (tag, n) = none`) and a digest `u`, the three
post-states produced by the off-collision tag step — the multiple, hybrid and bad worlds all
caching the fresh digest `u` for tag `tag` at nonce `n` — again satisfy `MHBInv`. -/
lemma MHBInv_tag_step
    (tag : TagId) (n : Nonce) (u : Digest)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MHBInv (sessionsPerTag := sessionsPerTag) sM sH sB)
    (hslot : sM.1.sessionsUsed tag < sessionsPerTag)
    (hfresh : sM.2 (tag, n) = none) :
    MHBInv (sessionsPerTag := sessionsPerTag)
      ({ sM.1 with sessionsUsed :=
          Function.update sM.1.sessionsUsed tag (sM.1.sessionsUsed tag + 1) },
        sM.2.cacheQuery (tag, n) u)
      (({ sessionsUsed :=
            Function.update sH.1.sessionsUsed tag (sH.1.sessionsUsed tag + 1),
          sessionNonce := Function.update sH.1.sessionNonce
            (tag, ⟨sM.1.sessionsUsed tag, hslot⟩) (some n) } :
          HybridState TagId Nonce sessionsPerTag),
        sH.2.cacheQuery ((tag, ⟨sM.1.sessionsUsed tag, hslot⟩), n) u)
      ({ sessionsUsed :=
            Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1),
          responses := sB.responses.cacheQuery (tag, n)
            (u :: Option.getD (sB.responses (tag, n)) []),
          bad := sB.bad || (sB.responses (tag, n)).isSome } :
          UnlinkBadState TagId Nonce Digest) := by
  obtain ⟨hcMH, hcMB, hbad, hsupp, hcorr, hcollfree, hwo, hrec, hcons⟩ := hInv
  set sid : Fin sessionsPerTag := ⟨sM.1.sessionsUsed tag, hslot⟩ with hsid
  -- the bad-world `responses` cell `(tag, n)` is empty off-collision
  have hBfresh : sB.responses (tag, n) = none := by
    have hni := hsupp tag n
    rw [hfresh] at hni
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at hni
    exact Option.not_isSome_iff_eq_none.mp hni
  -- the hybrid cell `((tag, sid), n)` is empty: `sid` is the unused current slot
  have hHfresh : sH.2 ((tag, sid), n) = none := by
    by_contra hne
    have hsnsome := hrec tag sid n (Option.isSome_iff_ne_none.mpr hne)
    rw [hwo tag sid (by rw [← hcMH, hsid])] at hsnsome
    exact absurd hsnsome (by simp)
  -- no session of `tag` had drawn `n` before (else the multiple cell would be cached)
  have hnodrawn : ∀ sid', sH.1.sessionNonce (tag, sid') ≠ some n := by
    intro sid' hsn'
    have := hcorr tag sid' n hsn'
    rw [hfresh] at this
    exact absurd (hcons tag sid' n hsn') (by rw [← this]; simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [HybridState.sessionsUsed]; rw [hcMH]
  · dsimp only; rw [hcMB]
  · rw [hbad, hBfresh]; rfl
  · -- multiple/bad cache support
    intro tag' n'
    dsimp only
    by_cases hkey : (tag', n') = (tag, n)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]; simp
    · rw [QueryCache.cacheQuery_of_ne _ _ hkey, QueryCache.cacheQuery_of_ne _ _ hkey]
      exact hsupp tag' n'
  · -- multiple/hybrid cache correspondence
    intro tag' sid' n' hsn'
    dsimp only at hsn' ⊢
    by_cases hts : (tag', sid') = (tag, sid)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hts
      rw [Function.update_self] at hsn'
      obtain rfl : n' = n := (Option.some.inj hsn').symm
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    · rw [Function.update_of_ne hts] at hsn'
      by_cases hmkey : (tag', n') = (tag, n)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmkey
        exact absurd hsn' (hnodrawn sid')
      · rw [QueryCache.cacheQuery_of_ne _ _ hmkey]
        have hhkey : ((tag', sid'), n') ≠ ((tag, sid), n) := fun h => hts (congrArg Prod.fst h)
        rw [QueryCache.cacheQuery_of_ne _ _ hhkey]
        exact hcorr tag' sid' n' hsn'
  · -- collision-freeness
    intro tag' s₁ s₂ n' h₁ h₂
    dsimp only at h₁ h₂
    by_cases ht1 : (tag', s₁) = (tag, sid)
    · obtain ⟨htg, hs₁⟩ := Prod.mk.inj ht1
      subst hs₁; subst htg
      rw [Function.update_self] at h₁
      obtain rfl : n' = n := (Option.some.inj h₁).symm
      by_cases ht2 : (tag', s₂) = (tag', sid)
      · exact ((Prod.mk.inj ht2).2).symm
      · rw [Function.update_of_ne ht2] at h₂
        exact absurd h₂ (hnodrawn s₂)
    · rw [Function.update_of_ne ht1] at h₁
      by_cases ht2 : (tag', s₂) = (tag, sid)
      · obtain ⟨htg, hs₂⟩ := Prod.mk.inj ht2
        subst hs₂; subst htg
        rw [Function.update_self] at h₂
        obtain rfl : n' = n := (Option.some.inj h₂).symm
        exact absurd h₁ (hnodrawn s₁)
      · rw [Function.update_of_ne ht2] at h₂
        exact hcollfree tag' s₁ s₂ n' h₁ h₂
  · -- write-once
    intro tag' sid' hle
    dsimp only at hle ⊢
    by_cases htag : tag' = tag
    · subst htag
      rw [Function.update_self] at hle
      have hne : sid' ≠ sid := by
        intro h; rw [h, hsid] at hle; rw [← hcMH] at hle; simp only [Fin.val] at hle; omega
      rw [Function.update_of_ne (by simp [Prod.ext_iff, hne])]
      exact hwo tag' sid' (by omega)
    · rw [Function.update_of_ne htag] at hle
      rw [Function.update_of_ne (by simp [htag])]
      exact hwo tag' sid' hle
  · -- cache-recorded
    intro tag' sid' n' hsome
    dsimp only at hsome ⊢
    by_cases hhkey : ((tag', sid'), n') = ((tag, sid), n)
    · obtain ⟨hkk, rfl⟩ := Prod.mk.inj hhkey
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkk
      rw [Function.update_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hhkey] at hsome
      have hsn := hrec tag' sid' n' hsome
      have hts : (tag', sid') ≠ (tag, sid) := by
        intro h
        rw [h] at hsn
        rw [hwo tag sid (by rw [← hcMH, hsid])] at hsn
        exact absurd hsn (by simp)
      rw [Function.update_of_ne hts]
      exact hsn
  · -- cache-consistency
    intro tag' sid' n' hsn'
    dsimp only at hsn' ⊢
    by_cases hts : (tag', sid') = (tag, sid)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hts
      rw [Function.update_self] at hsn'
      obtain rfl : n' = n := (Option.some.inj hsn').symm
      rw [QueryCache.cacheQuery_self]; simp
    · rw [Function.update_of_ne hts] at hsn'
      have hhkey : ((tag', sid'), n') ≠ ((tag, sid), n) := fun h => hts (congrArg Prod.fst h)
      rw [QueryCache.cacheQuery_of_ne _ _ hhkey]
      exact hcons tag' sid' n' hsn'

/-! ### Multiple-to-hybrid: the instrumented multiple-session handler

`multipleIdealQueryImpl`'s state — a lazy random-oracle cache over `(TagId × Nonce)` — cannot
express "a within-tag tag–tag nonce collision has occurred": the cache key does not record whether
a cell was written by a tag draw or by a reader query, and a collision is history. The
instrumented handler `multipleBadQueryImpl` carries, beside the multiple-ideal state, a full
bad-world `UnlinkBadState` whose `bad` flag fires exactly on a tag-written cell collision. Its
*output bit* is identical to `multipleIdealQueryImpl`'s — the instrumentation only threads an extra
state component — so `Pr[= true]` is unchanged (`probOutput_multipleBad_run'_eq_multipleIdeal`),
while `Pr[bad]` is exactly the bad-world collision probability
(`probEvent_multipleBad_bad_eq_unlinkBad`). -/

/-- Joint handler state for the instrumented multiple-session world: the multiple-ideal state
(session counters + lazy random-oracle cache over `TagId × Nonce`) paired with a full bad-world
`UnlinkBadState` whose `responses` cache and `bad` flag detect within-tag nonce collisions. -/
abbrev MultipleBadState (TagId Nonce Digest : Type) (sessionsPerTag : ℕ) : Type :=
  (UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) ×
    UnlinkBadState TagId Nonce Digest

/-- Bad-world state advance on a tag query: given the previous bad state `sB` and the transcript
the multiple-ideal tag oracle produced, advance `sB` exactly as `unlinkBadTagQueryImpl` would —
recording the drawn digest and firing `bad` on a repeat `(tag, nonce)`. A `none` transcript (slot
exhausted) leaves `sB` untouched. -/
def multipleBadAdvance (tag : TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (r : Option (TagTranscript Nonce Digest)) : UnlinkBadState TagId Nonce Digest :=
  match r with
  | none => sB
  | some tr =>
      { sessionsUsed := Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1)
        responses := sB.responses.cacheQuery (tag, tr.nonce)
          (tr.auth :: Option.getD (sB.responses (tag, tr.nonce)) [])
        bad := sB.bad || (sB.responses (tag, tr.nonce)).isSome }

/-- `multipleIdealQueryImpl` re-targeted to the larger `MultipleBadState` monad: runs the
multiple-ideal handler on the inner state component and threads the extra `UnlinkBadState`
component through unchanged. This is the "base" handler that `multipleBadQueryImpl` instruments
via `QueryImpl.postInsert`.

Exists to bridge a framework gap: there is no standard `MonadLift` instance between
`StateT σ₁ m` and `StateT (σ₁ × σ₂) m`, so `postInsert` cannot lift a handler in the
smaller-state monad into the larger-state monad directly. The right fix is a general
`StateT.liftWith : MonadLift (StateT σ₁ m) (StateT (σ₁ × σ₂) m)` instance under
`VCVio/OracleComp/SimSemantics/StateT/`; until that lands, the manual lift here is the
template for future bad-flag-style instrumentation. -/
noncomputable def multipleIdealLiftedQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (MultipleBadState TagId Nonce Digest sessionsPerTag) ProbComp) :=
  fun q => fun p =>
    (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) q) p.1 >>= fun r =>
      pure (r.1, (r.2, p.2))

/-- Instrumented multiple-session handler: defined via `QueryImpl.postInsert` on top of
`multipleIdealLiftedQueryImpl`. The inserted side effect is a `modify` on the bad-world component
that fires `multipleBadAdvance` on a tag query and is a no-op on a reader query. The output bit and
inner-state evolution match `multipleIdealQueryImpl` exactly; only the extra `UnlinkBadState`
component carries the bad-flag instrumentation.

This shape validates the `postInsert` combinator for the "bad-flag" pattern: future reductions can
use the same idiom (lift the base ideal handler to the larger state, then `postInsert` a
`modify`-based bad-flag advance). -/
noncomputable def multipleBadQueryImpl :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (MultipleBadState TagId Nonce Digest sessionsPerTag) ProbComp) :=
  (multipleIdealLiftedQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)).postInsert
    (fun q (r : (UnlinkOracleSpec TagId Nonce Digest).Range q) =>
      (modify (fun s : MultipleBadState TagId Nonce Digest sessionsPerTag =>
        match q, r with
        | Sum.inl tag, r => (s.1, multipleBadAdvance tag s.2 r)
        | Sum.inr _, _ => s) :
          StateT (MultipleBadState TagId Nonce Digest sessionsPerTag) ProbComp Unit))

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `multipleIdealLiftedQueryImpl` on a query: explicit form as an inner-state bind with the extra
state component preserved. -/
lemma multipleIdealLiftedQueryImpl_run
    (q : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (multipleIdealLiftedQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) q) s =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) q) s.1 >>= fun r =>
        pure (r.1, (r.2, s.2)) := rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `multipleBadQueryImpl` on a tag query: the multiple-ideal tag step with the bad-world component
advanced by `multipleBadAdvance`. -/
lemma multipleBadQueryImpl_tag_run (tag : TagId)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s.1 >>= fun r =>
        pure (r.1, (r.2.1, r.2.2), multipleBadAdvance tag s.2 r.1) := by
  show (multipleIdealLiftedQueryImpl (Sum.inl tag) s) >>= _ = _
  rw [multipleIdealLiftedQueryImpl_run, bind_assoc]
  refine bind_congr fun r => ?_
  rw [pure_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `multipleBadQueryImpl` on a reader query: the multiple-ideal reader step, bad-world component
untouched. -/
lemma multipleBadQueryImpl_reader_run (transcript : TagTranscript Nonce Digest)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s =
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s.1 >>= fun r =>
        pure (r.1, (r.2.1, r.2.2), s.2) := by
  show (multipleIdealLiftedQueryImpl (Sum.inr transcript) s) >>= _ = _
  rw [multipleIdealLiftedQueryImpl_run, bind_assoc]
  refine bind_congr fun r => ?_
  rw [pure_bind]
  rfl

open OracleComp.ProgramLogic.Relational in
omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- **Multiple-to-hybrid, output equivalence.** The instrumented handler `multipleBadQueryImpl` produces the
same output distribution as `multipleIdealQueryImpl`: the bad-world component it threads beside the
multiple-ideal state never feeds back into the output bit. Hence `Pr[= true]` is unchanged. -/
lemma probOutput_multipleBad_run'_eq_multipleIdeal
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) :
    Pr[= true | (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' (s, sB)] =
      Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run' s] := by
  have hrt : RelTriple
      ((simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) adversary).run' (s, sB))
      ((simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) adversary).run' s)
      (EqRel Bool) := by
    refine relTriple_simulateQ_run'
      (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag))
      (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag))
      (fun s₁ s₂ => s₁.1 = s₂) adversary ?_ (s, sB) s rfl
    intro t s₁ s₂ hs
    -- the head: `multipleBadQueryImpl t s₁` is `multipleIdealQueryImpl t s₁.1 >>= pure (…)`
    subst hs
    cases t with
    | inl tag =>
      change RelTriple ((multipleBadQueryImpl (Sum.inl tag)) s₁) _ _
      rw [multipleBadQueryImpl_tag_run]
      refine relTriple_of_evalDist_eq_right
        (congrArg evalDist (bind_pure ((multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) s₁.1))) ?_
      refine relTriple_bind (relTriple_refl _) ?_
      rintro a b rfl
      exact relTriple_pure_pure ⟨rfl, rfl⟩
    | inr transcript =>
      change RelTriple ((multipleBadQueryImpl (Sum.inr transcript)) s₁) _ _
      rw [multipleBadQueryImpl_reader_run]
      refine relTriple_of_evalDist_eq_right
        (congrArg evalDist (bind_pure ((multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) s₁.1))) ?_
      refine relTriple_bind (relTriple_refl _) ?_
      rintro a b rfl
      exact relTriple_pure_pure ⟨rfl, rfl⟩
  exact probOutput_eq_of_relTriple_eqRel hrt true

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- The bad flag threaded by `multipleBadQueryImpl` is monotone under a single per-query step:
started from a `MultipleBadState` whose bad flag is set, every output state still has it set.
`multipleBadAdvance` only ever OR-s into the flag, and reader queries leave the bad-world component
untouched. -/
lemma multipleBadQueryImpl_step_preserves_bad
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) (hbad : s.2.bad = true) :
    ∀ z ∈ support ((multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t) s), z.2.2.bad = true := by
  cases t with
  | inl tag =>
    intro z hz
    rw [multipleBadQueryImpl_tag_run tag s] at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    cases hr : r.1 with
    | none => simp [multipleBadAdvance, hr, hbad]
    | some tr => simp [multipleBadAdvance, hr, hbad]
  | inr transcript =>
    intro z hz
    rw [multipleBadQueryImpl_reader_run transcript s] at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    exact hbad

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Bad monotonicity for a full `simulateQ multipleBadQueryImpl` run: started from a state whose
bad flag is set, every reachable output state keeps it set. This is the `hmono` hypothesis of the
heterogeneous bad+slack `simulateQ` rule. -/
lemma multipleBadQueryImpl_run_preserves_bad {α : Type}
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) (hbad : s.2.bad = true) :
    ∀ z ∈ support ((simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run s), z.2.2.bad = true := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure b =>
    intro z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz; exact hbad
  | query_bind t f ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact ih p.1 p.2 (multipleBadQueryImpl_step_preserves_bad t s hbad p hp) z hz

/-! ### Multiple-to-hybrid: spare uniform draws are distribution-neutral

The hop-A coupling pairs each multiple-cache cell written by a *reader* query with a reserved
hybrid "spare" digest. Operationally the hybrid side draws those spares and discards them. The
lemma below is the soundness core making that free: appending any failure-free probabilistic
prefix to a computation — in particular a fold of fresh uniform digest draws via
`idealCacheMapM` — leaves the output distribution unchanged. `ProbComp` never fails
(`probFailure_eq_zero`), so a discarded draw cannot shift any output probability. -/

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Appending a failure-free probabilistic prefix and discarding its result is
distribution-neutral: `𝒟[mx >>= fun _ => my] = 𝒟[my]`. Since every `ProbComp` has zero failure
probability, the discarded draw `mx` contributes only the constant factor `1`. -/
lemma evalDist_bind_const_eq {α β : Type} (mx : ProbComp α) (my : ProbComp β) :
    𝒟[mx >>= fun _ => my] = 𝒟[my] := by
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- **Spare draws are distribution-neutral.** Folding `idealCacheStep` over an arbitrary list of
domain points — drawing a fresh uniform digest at every uncached cell — and then discarding the
result leaves the output distribution unchanged. This is the soundness core of the hop-A
spare-draws coupling: the hybrid reader may draw `|TagId|` spare digests it never reads, matching
the cells the multiple reader writes, without shifting any output probability. -/
lemma evalDist_idealCacheMapM_bind_const_eq {D β : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache) (my : ProbComp β) :
    𝒟[idealCacheMapM l c >>= fun _ => my] = 𝒟[my] :=
  evalDist_bind_const_eq (idealCacheMapM l c) my

end EagerComposed

/-! ### Multiple-to-hybrid: the multiple-vs-hybrid coupling relation

The heterogeneous bad+slack `simulateQ` rule couples the instrumented multiple handler
`multipleBadQueryImpl` (state `MultipleBadState`, the multiple-ideal state paired with the
bad-world `UnlinkBadState`) against the lazy hybrid handler `hybridLazyHandler` (state
`HybridState × QueryCache`). `MHBRel` repackages the three-way coupling invariant `MHBInv` —
which relates a multiple-ideal state, a hybrid state and a bad-world state — as the binary
relation the rule expects, by pairing the multiple-ideal and bad-world components inside the
`MultipleBadState`. -/

/-- Hop-A coupling relation for the heterogeneous bad+slack `simulateQ` rule: relate a
`MultipleBadState` (a multiple-ideal state `s₁.1` together with a bad-world state `s₁.2`) and a
lazy-hybrid state `s₂` exactly when the underlying three components satisfy `MHBInv`. -/
def MHBRel
    (s₁ : MultipleBadState TagId Nonce Digest sessionsPerTag)
    (s₂ : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) : Prop :=
  MHBInv (sessionsPerTag := sessionsPerTag) s₁.1 s₂ s₁.2

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The initial `MultipleBadState` and lazy-hybrid state are `MHBRel`-related. -/
lemma MHBRel_init :
    MHBRel (TagId := TagId) (Nonce := Nonce) (Digest := Digest) (sessionsPerTag := sessionsPerTag)
      ((UnlinkState.init, ∅), UnlinkBadState.init) (HybridState.init, ∅) :=
  MHBInv_init

/-! ### Multiple-to-hybrid: the reader-aware coupling relation `MultipleHybridCoupling`

`MHBInv`/`MHBRel` is *insufficient* for hop A: its clause
`(sM.2 (tag, n)).isSome ↔ (sB.responses (tag, n)).isSome` couples the multiple-ideal cache
one-to-one with the bad-world `responses` cache. But the multiple-session *reader* oracle writes
the multiple cache — `multipleIdealQueryImpl_reader_run` folds `idealCacheMapM`, caching every
`(tag, n)` cell it inspects — while leaving the bad-world `responses` untouched
(`multipleBadQueryImpl_reader_run`). So after one reader query that biconditional is broken.

`MultipleHybridCoupling` is the reader-aware replacement. It distinguishes multiple-cache cells written by
*tag* queries from those written by *reader* queries: a cell `(tag, n)` is *tag-written* exactly
when some hybrid session recorded the draw, `∃ sid, sH.sessionNonce (tag, sid) = some n`. The
bad-world `responses` cache then mirrors precisely the *tag-written* cells (clause `hbadcol`),
not the whole multiple cache — so a reader query, which writes only reader cells, preserves it.
The cache correspondence `hcorr` already quantifies only over recorded sessions, hence is itself
reader-stable: reader-written cells (whose nonce is in no session) are simply not constrained. -/

/-- Reader-aware hop-A coupling invariant relating a multiple-ideal state `sM`
(`UnlinkState × multiple cache`), a lazy-hybrid state `sH` (`HybridState × hybrid cache`) and a
bad-world state `sB` (`UnlinkBadState`).

The clauses are those of `MHBInv` except that the multiple/bad cache biconditional is replaced by
`hbadcol`: the bad-world `responses` cache holds an entry at `(tag, n)` *exactly* for the
tag-written cells — those `n` recorded by some session of `tag`. This makes the invariant stable
under reader queries, which write the multiple cache but not the bad-world or session-nonce
components. -/
def MultipleHybridCoupling
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) : Prop :=
  sM.1.sessionsUsed = sH.1.sessionsUsed ∧
    sM.1.sessionsUsed = sB.sessionsUsed ∧
    sB.bad = false ∧
    (∀ tag n, (sB.responses (tag, n)).isSome ↔
      ∃ sid, sH.1.sessionNonce (tag, sid) = some n) ∧
    (∀ tag sid n, sH.1.sessionNonce (tag, sid) = some n →
      sM.2 (tag, n) = sH.2 ((tag, sid), n)) ∧
    (∀ tag sid₁ sid₂ n, sH.1.sessionNonce (tag, sid₁) = some n →
      sH.1.sessionNonce (tag, sid₂) = some n → sid₁ = sid₂) ∧
    (∀ tag (sid : Fin sessionsPerTag), sH.1.sessionsUsed tag ≤ sid.val →
      sH.1.sessionNonce (tag, sid) = none) ∧
    (∀ tag sid n, (sH.2 ((tag, sid), n)).isSome →
      sH.1.sessionNonce (tag, sid) = some n) ∧
    (∀ tag sid n, sH.1.sessionNonce (tag, sid) = some n →
      (sH.2 ((tag, sid), n)).isSome)

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The three initial states satisfy the reader-aware hop-A coupling: counters are all zero, the
bad flag is unset, and all caches and the session-nonce map are empty. -/
lemma MultipleHybridCoupling_init :
    MultipleHybridCoupling (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)
      (UnlinkState.init, ∅) (HybridState.init, ∅) UnlinkBadState.init := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tag n
    simp only [UnlinkBadState.init, QueryCache.empty_apply, Option.isSome_none,
      Bool.false_eq_true, false_iff, not_exists]
    intro sid h
    exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])
  · intro tag sid n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])
  · intro tag sid₁ sid₂ n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])
  · intro tag sid _; rfl
  · intro tag sid n h; exact absurd h (by simp)
  · intro tag sid n h; exact absurd h (by simp [HybridState.init, HybridSessionNonce.init])

/-- Reader-aware hop-A coupling relation for the heterogeneous bad+slack `simulateQ` rule: relate a
`MultipleBadState` (multiple-ideal state `s₁.1` together with a bad-world state `s₁.2`) and a
lazy-hybrid state `s₂` exactly when the three underlying components satisfy `MultipleHybridCoupling`. -/
def MultipleHybridRel
    (s₁ : MultipleBadState TagId Nonce Digest sessionsPerTag)
    (s₂ : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) : Prop :=
  MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) s₁.1 s₂ s₁.2

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce]
  [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The initial `MultipleBadState` and lazy-hybrid state are `MultipleHybridRel`-related. -/
lemma MultipleHybridRel_init :
    MultipleHybridRel (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag)
      ((UnlinkState.init, ∅), UnlinkBadState.init) (HybridState.init, ∅) :=
  MultipleHybridCoupling_init

/-- **Multiple-to-hybrid freshness invariant** (the `HybridColFresh`-analogue for the multiple cache). A cached
multiple-cache cell `(tag, n)` that was *not* produced by a tag draw — no session of `tag` recorded
the nonce `n` in the hybrid session-nonce map `sH.1.sessionNonce` — can only have been written by
an earlier *reader* query. Under `HasDistinctUnlinkReaderNonces` a second reader query at `n` is
then impossible, which is recorded here as the residual reader budget at `n` being exhausted.

The hybrid tag oracle records `sessionNonce (tag, sid) := some n` exactly when it draws nonce `n`
for session `(tag, sid)`, and the hop-A cache correspondence `MultipleHybridCoupling.hcorr` ties tag-drawn
multiple cells to recorded sessions; so a cached multiple cell with no recorded session is genuinely
reader-written. This predicate is the freshness witness that the reader-step coupling threads
through the induction, exactly mirroring `HybridColFresh` in hop B. -/
def MultipleHybridColFresh (oa : UnlinkAdversary TagId Nonce Digest)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (cM : ((TagId × Nonce) →ₒ Digest).QueryCache) : Prop :=
  ∀ (n : Nonce) (tag : TagId),
    (cM (tag, n)).isSome → (∀ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) ≠ some n) →
      OracleComp.IsQueryBoundP oa (pReaderNonce n) 0

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The empty multiple cache satisfies the hop-A freshness invariant vacuously: no cell is cached,
so the hypothesis `(cM (tag, n)).isSome` is never met. -/
lemma multipleHybridColFresh_init (oa : UnlinkAdversary TagId Nonce Digest)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    MultipleHybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa sH ∅ := by
  intro n tag hsome _
  simp at hsome

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [NeZero sessionsPerTag] in
/-- **Multiple-to-hybrid, reader-step coupling stability.** A multiple-session reader query folds
`idealCacheStep` over its cells, extending the multiple cache `sM.2` to some `r.2` while leaving
the session counters, the hybrid state and the bad-world state untouched. Because `idealCacheStep`
only fills `none` cells — never overwriting an already-cached cell — and every tag-written cell is
already cached (clause `hcorr` together with the hybrid cache/session-nonce consistency), the
reader-extended state still satisfies `MultipleHybridCoupling`. This is the precise sense in which the
reader-aware invariant is stable across reader queries. -/
lemma MultipleHybridCoupling_reader_step
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (cells : List (TagId × Nonce))
    (r : List Digest × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hr : r ∈ support (idealCacheMapM (Digest := Digest) cells sM.2)) :
    MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) (sM.1, r.2) sH sB := by
  obtain ⟨hcnt1, hcnt2, hbad, hbadcol, hcorr, hcolfree, hwo, hhyb1, hhyb2⟩ := hInv
  refine ⟨hcnt1, hcnt2, hbad, hbadcol, ?_, hcolfree, hwo, hhyb1, hhyb2⟩
  intro tag sid n hsn
  have hcell : (sM.2 (tag, n)).isSome := by
    rw [hcorr tag sid n hsn]
    exact hhyb2 tag sid n hsn
  rw [idealCacheMapM_cache_off cells sM.2 r hr (tag, n) hcell]
  exact hcorr tag sid n hsn

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Multiple-to-hybrid, off-collision tag-step coupling stability.** Given `MultipleHybridCoupling sM sH sB`, a free
slot `hslot`, an off-collision nonce `n` (`sM.2 (tag, n) = none`) and a digest `u`, the three
post-states produced by the off-collision tag step — the multiple, hybrid and bad worlds all
caching the fresh digest `u` for tag `tag` at nonce `n` — again satisfy `MultipleHybridCoupling`.

Off-collision means no session of `tag` had drawn `n` before, so the new draw both extends the
session-nonce map at the fresh slot `sid` and writes a fresh bad-world `responses` entry; the
reader-aware clause `hbadcol` is preserved because both the new session record and the new
bad-world entry sit at the same cell `(tag, n)`. -/
lemma MultipleHybridCoupling_tag_step
    (tag : TagId) (n : Nonce) (u : Digest)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (hslot : sM.1.sessionsUsed tag < sessionsPerTag)
    (hfresh : sM.2 (tag, n) = none) :
    MultipleHybridCoupling (sessionsPerTag := sessionsPerTag)
      ({ sM.1 with sessionsUsed :=
          Function.update sM.1.sessionsUsed tag (sM.1.sessionsUsed tag + 1) },
        sM.2.cacheQuery (tag, n) u)
      (({ sessionsUsed :=
            Function.update sH.1.sessionsUsed tag (sH.1.sessionsUsed tag + 1),
          sessionNonce := Function.update sH.1.sessionNonce
            (tag, ⟨sM.1.sessionsUsed tag, hslot⟩) (some n) } :
          HybridState TagId Nonce sessionsPerTag),
        sH.2.cacheQuery ((tag, ⟨sM.1.sessionsUsed tag, hslot⟩), n) u)
      ({ sessionsUsed :=
            Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1),
          responses := sB.responses.cacheQuery (tag, n)
            (u :: Option.getD (sB.responses (tag, n)) []),
          bad := sB.bad || (sB.responses (tag, n)).isSome } :
          UnlinkBadState TagId Nonce Digest) := by
  obtain ⟨hcMH, hcMB, hbad, hbadcol, hcorr, hcollfree, hwo, hrec, hcons⟩ := hInv
  set sid : Fin sessionsPerTag := ⟨sM.1.sessionsUsed tag, hslot⟩ with hsid
  -- no session of `tag` had drawn `n` before (else the multiple cell would be cached)
  have hnodrawn : ∀ sid', sH.1.sessionNonce (tag, sid') ≠ some n := by
    intro sid' hsn'
    have := hcorr tag sid' n hsn'
    rw [hfresh] at this
    exact absurd (hcons tag sid' n hsn') (by rw [← this]; simp)
  -- the bad-world `responses` cell `(tag, n)` is empty off-collision
  have hBfresh : sB.responses (tag, n) = none := by
    rw [← Option.not_isSome_iff_eq_none, hbadcol tag n, not_exists]
    intro sid' hsn'
    exact hnodrawn sid' hsn'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [HybridState.sessionsUsed]; rw [hcMH]
  · dsimp only; rw [hcMB]
  · rw [hbad, hBfresh]; rfl
  · -- bad-world / session-nonce correspondence
    intro tag' n'
    dsimp only
    by_cases hkey : (tag', n') = (tag, n)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
      rw [QueryCache.cacheQuery_self]
      exact ⟨fun _ => ⟨sid, Function.update_self _ _ _⟩, fun _ => rfl⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ hkey, hbadcol tag' n']
      constructor
      · rintro ⟨sid', hsn'⟩
        refine ⟨sid', ?_⟩
        have hts : (tag', sid') ≠ (tag, sid) := by
          rintro h
          obtain ⟨htg, hsd⟩ := Prod.mk.inj h
          rw [htg, hsd, hwo tag sid (by rw [← hcMH, hsid])] at hsn'
          exact absurd hsn' (by simp)
        rw [Function.update_of_ne hts]; exact hsn'
      · rintro ⟨sid', hsn'⟩
        by_cases hts : (tag', sid') = (tag, sid)
        · obtain ⟨htg, hsd⟩ := Prod.mk.inj hts
          rw [htg, hsd, Function.update_self] at hsn'
          exact absurd (Prod.ext htg (Option.some.inj hsn').symm) hkey
        · rw [Function.update_of_ne hts] at hsn'
          exact ⟨sid', hsn'⟩
  · -- multiple/hybrid cache correspondence
    intro tag' sid' n' hsn'
    dsimp only at hsn' ⊢
    by_cases hts : (tag', sid') = (tag, sid)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hts
      rw [Function.update_self] at hsn'
      obtain rfl : n' = n := (Option.some.inj hsn').symm
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    · rw [Function.update_of_ne hts] at hsn'
      by_cases hmkey : (tag', n') = (tag, n)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmkey
        exact absurd hsn' (hnodrawn sid')
      · rw [QueryCache.cacheQuery_of_ne _ _ hmkey]
        have hhkey : ((tag', sid'), n') ≠ ((tag, sid), n) := fun h => hts (congrArg Prod.fst h)
        rw [QueryCache.cacheQuery_of_ne _ _ hhkey]
        exact hcorr tag' sid' n' hsn'
  · -- collision-freeness
    intro tag' s₁ s₂ n' h₁ h₂
    dsimp only at h₁ h₂
    by_cases ht1 : (tag', s₁) = (tag, sid)
    · obtain ⟨htg, hs₁⟩ := Prod.mk.inj ht1
      subst hs₁; subst htg
      rw [Function.update_self] at h₁
      obtain rfl : n' = n := (Option.some.inj h₁).symm
      by_cases ht2 : (tag', s₂) = (tag', sid)
      · exact ((Prod.mk.inj ht2).2).symm
      · rw [Function.update_of_ne ht2] at h₂
        exact absurd h₂ (hnodrawn s₂)
    · rw [Function.update_of_ne ht1] at h₁
      by_cases ht2 : (tag', s₂) = (tag, sid)
      · obtain ⟨htg, hs₂⟩ := Prod.mk.inj ht2
        subst hs₂; subst htg
        rw [Function.update_self] at h₂
        obtain rfl : n' = n := (Option.some.inj h₂).symm
        exact absurd h₁ (hnodrawn s₁)
      · rw [Function.update_of_ne ht2] at h₂
        exact hcollfree tag' s₁ s₂ n' h₁ h₂
  · -- write-once
    intro tag' sid' hle
    dsimp only at hle ⊢
    by_cases htag : tag' = tag
    · subst htag
      rw [Function.update_self] at hle
      have hne : sid' ≠ sid := by
        intro h; rw [h, hsid] at hle; rw [← hcMH] at hle; simp only [Fin.val] at hle; omega
      rw [Function.update_of_ne (by simp [Prod.ext_iff, hne])]
      exact hwo tag' sid' (by omega)
    · rw [Function.update_of_ne htag] at hle
      rw [Function.update_of_ne (by simp [htag])]
      exact hwo tag' sid' hle
  · -- cache-recorded
    intro tag' sid' n' hsome
    dsimp only at hsome ⊢
    by_cases hhkey : ((tag', sid'), n') = ((tag, sid), n)
    · obtain ⟨hkk, rfl⟩ := Prod.mk.inj hhkey
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkk
      rw [Function.update_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hhkey] at hsome
      have hsn := hrec tag' sid' n' hsome
      have hts : (tag', sid') ≠ (tag, sid) := by
        intro h
        rw [h] at hsn
        rw [hwo tag sid (by rw [← hcMH, hsid])] at hsn
        exact absurd hsn (by simp)
      rw [Function.update_of_ne hts]
      exact hsn
  · -- cache-consistency
    intro tag' sid' n' hsn'
    dsimp only at hsn' ⊢
    by_cases hts : (tag', sid') = (tag, sid)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hts
      rw [Function.update_self] at hsn'
      obtain rfl : n' = n := (Option.some.inj hsn').symm
      rw [QueryCache.cacheQuery_self]; simp
    · rw [Function.update_of_ne hts] at hsn'
      have hhkey : ((tag', sid'), n') ≠ ((tag, sid), n) := fun h => hts (congrArg Prod.fst h)
      rw [QueryCache.cacheQuery_of_ne _ _ hhkey]
      exact hcons tag' sid' n' hsn'

/-! ### Multiple-to-hybrid: closing `multipleIdeal_le_hybrid_add_bad`

The reader and tag per-query coupling steps are discharged below and assembled through the
heterogeneous bad+slack `simulateQ` rule `probOutput_simulateQ_run'_le_add_bad_add_slack`. -/

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- If a multiple-reader cell `(tag, n)` is already cached with digest `v`, then folding
`idealCacheStep` over a cell list containing `(tag, n)` produces a drawn list containing `v`: a
cached cell is read back unchanged. -/
lemma mem_drawn_of_cached_cell {D : Type} [DecidableEq D]
    (l : List D) (c : (D →ₒ Digest).QueryCache)
    (rs : List Digest × (D →ₒ Digest).QueryCache)
    (hrs : rs ∈ support (idealCacheMapM (Digest := Digest) l c))
    (d : D) (hd : d ∈ l) (v : Digest) (hcd : c d = some v) :
    v ∈ rs.1 := by
  classical
  have hr2 : rs.2 d = c d :=
    idealCacheMapM_cache_off l c rs hrs d (by rw [hcd]; rfl)
  have hmap := idealCacheMapM_support l c rs hrs (fun _ => v)
  rw [hmap]
  refine List.mem_map.mpr ⟨d, hd, ?_⟩
  simp [OracleComp.tableExtending, hr2, hcd]

omit [Nonempty TagId] [SampleableType Nonce] [NeZero sessionsPerTag] in
/-- **Multiple-to-hybrid, reader-step output domination.** Under `MultipleHybridCoupling sM sH sB`, whenever the lazy
hybrid reader accepts a transcript (`hybridCacheAccepts` reads `true`), the multiple reader also
accepts: the accepting hybrid session cell mirrors a cached multiple cell holding the
authenticator, which the multiple reader fold reads back into its drawn list. Hence the two
readers disagree only in the direction `multiple accepts, hybrid rejects`. -/
lemma multipleReader_accepts_of_hybridCacheAccepts
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (transcript : TagTranscript Nonce Digest)
    (rs : List Digest × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (hrs : rs ∈ support (idealCacheMapM (multipleReaderCells (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) transcript) sM.2))
    (hhyb : hybridCacheAccepts (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) sH.2 sH.1.sessionNonce transcript = true) :
    decide (∃ d ∈ rs.1, d = transcript.auth) = true := by
  classical
  obtain ⟨_, _, _, _, hcorr, _, _, _, _⟩ := hInv
  rw [hybridCacheAccepts, decide_eq_true_eq] at hhyb
  obtain ⟨tag, sid, hsn, hcell⟩ := hhyb
  have hmcell : sM.2 (tag, transcript.nonce) = some transcript.auth := by
    rw [hcorr tag sid transcript.nonce hsn]; exact hcell
  have hmem : (tag, transcript.nonce) ∈ multipleReaderCells (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) transcript := by
    unfold multipleReaderCells
    exact List.mem_map.mpr ⟨tag, Finset.mem_toList.mpr (Finset.mem_univ tag), rfl⟩
  exact decide_eq_true (⟨transcript.auth,
    mem_drawn_of_cached_cell _ sM.2 rs hrs (tag, transcript.nonce) hmem transcript.auth hmcell,
    rfl⟩)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ multipleBadQueryImpl` of a `query_bind`, run from a state and projected to its
output bit: the per-query handler followed by the recursive simulation of the continuation. -/
lemma multipleBad_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' s =
      (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t s) >>= fun p =>
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ multipleBadQueryImpl` of a `query_bind`, run from a state and projected to its full
output: the per-query handler followed by the recursive simulation of the continuation. -/
lemma multipleBad_run_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : MultipleBadState TagId Nonce Digest sessionsPerTag) :
    (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run s =
      (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t s) >>= fun p =>
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl


end UnlinkReduction

end PRFTagReader
