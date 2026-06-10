/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.PRFReductions.IdealHandlers

/-!
# PRF Tag/Reader Protocol — Structural `query_bind` Reductions and Distinct Reader Nonces

Structural `query_bind`-decomposition lemmas for the composed ideal handlers (turning the
coupling induction into a sequence of `bind`-decomposition steps), per-query reductions and `bad`
monotonicity for `unlinkBadQueryImpl`, and the `HasDistinctUnlinkReaderNonces` predicate together
with its single-reader-query corollary `hasDistinctUnlinkReaderNonces_of_readerBound`.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ### Structural reductions of the composed ideal handlers on a `query_bind`

The next two lemmas expose `simulateQ … (query_bind t f)` run from a state as a single monadic
`bind`: the per-query handler applied to the head, then the recursive `simulateQ` of the
continuation threaded through the resulting state. They are pure rewriting facts (`simulateQ` is a
monad morphism), and they turn the coupling induction into a sequence of `bind`-decomposition
steps that `probEvent_bind_le_add` / `probEvent_bind_congr_le_add` can attack. -/

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
               bad := sB.bad || (sB.responses (tag, nonce)).isSome
               cacheBad := sB.cacheBad } :
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
with `bad = true` the run keeps `bad = true`. Derived from the per-step monotonicity via the
generic `OracleComp.simulateQ_run_preservesInv`. -/
lemma simulateQ_unlinkBad_preserves_bad
    (adv : UnlinkAdversary TagId Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) (hbad : sB.bad = true) :
    ∀ z ∈ support ((simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adv).run sB), z.2.bad = true :=
  OracleComp.simulateQ_run_preservesInv
    (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag))
    (fun s => s.bad = true) (fun t s h z hz => unlinkBadQueryImpl_step_preserves_bad t s h z hz)
    adv sB hbad

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

The reader-slack half of the coupling is sound only when the adversary's reader queries carry
pairwise-distinct nonces: a reader query at nonce `n` programs an entire column of the random
oracle, and the coupling between the multiple- and single-session worlds can charge that column
only once. `HasDistinctUnlinkReaderNonces` is the unlinkability analogue of
`PRFTagReader.HasDistinctReaderNonces` from the authentication collision proof: it bounds, for
every nonce `n`, the number of reader queries carrying `n` by `1`. -/

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

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] in
/-- `HasDistinctUnlinkReaderNonces` unfolds definitionally to a per-nonce reader-query bound: it
holds exactly when, for every nonce `n`, at most one reader query carries `n`. -/
lemma hasDistinctUnlinkReaderNonces_iff (adversary : UnlinkAdversary TagId Nonce Digest) :
    HasDistinctUnlinkReaderNonces adversary ↔
      ∀ n : Nonce, OracleComp.IsQueryBoundP adversary (pReaderNonce n) 1 :=
  Iff.rfl

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- Every `pReaderNonce n`-query is a reader query: `pReaderNonce n` is false on tag (`Sum.inl`)
queries and, on reader (`Sum.inr`) queries, refines `Sum.isRight`. -/
lemma pReaderNonce_imp_isRight (n : Nonce)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain) :
    pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n t → t.isRight := by
  cases t with
  | inl x => exact fun h => (h : (False : Prop)).elim
  | inr tr => exact fun _ => rfl

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- An adversary making at most one reader query has pairwise-distinct reader nonces: a single
reader query cannot collide with itself. Adversaries with no reader queries also qualify. -/
theorem hasDistinctUnlinkReaderNonces_of_readerBound
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (hq : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) 1) :
    HasDistinctUnlinkReaderNonces adversary := fun n =>
  OracleComp.IsQueryBoundP.of_imp (pReaderNonce_imp_isRight n) hq

end UnlinkReduction

end PRFTagReader
