/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.Collision

/-!
# PRF Tag/Reader Protocol — Bad-Event Bound

The bad-event world for the multiple-session unlinkability game, which records nonce collisions
across repeated sessions of a tag. Proves the per-step bad-event bounds and the overall session
collision bound `unlinkBadExp_le_sessionCollisionBound`.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section Theorems

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-- The number of still-available successful tag sessions in a bad-event state. -/
def unlinkBadRemaining (st : UnlinkBadState TagId Nonce Digest) : ℕ :=
  (Finset.univ : Finset TagId).sum fun tag => sessionsPerTag - st.sessionsUsed tag

/-- Reachable bad-event states only cache nonces that came from successful tag sessions. For each
tag, we retain a finite witness set of cached nonces whose size is bounded by that tag's session
counter. -/
def unlinkBadCacheBounded (st : UnlinkBadState TagId Nonce Digest) : Prop :=
  ∀ tag : TagId, ∃ nonces : Finset Nonce,
    nonces.card ≤ st.sessionsUsed tag ∧
      ∀ nonce : Nonce, (st.responses (tag, nonce)).isSome = true → nonce ∈ nonces

/-- State produced by a successful `RF_bad` tag query after sampling `nonce` and `auth`. -/
def unlinkBadTagNext
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest) : UnlinkBadState TagId Nonce Digest :=
  { sessionsUsed := Function.update st.sessionsUsed tag (st.sessionsUsed tag + 1)
    responses := st.responses.cacheQuery (tag, nonce)
      (auth :: Option.getD (st.responses (tag, nonce)) [])
    bad := st.bad || (st.responses (tag, nonce)).isSome
    cacheBad := st.cacheBad }

omit [Fintype TagId] [Nonempty TagId] [DecidableEq TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The initial state satisfies `unlinkBadCacheBounded`: the response cache is empty, so the empty
witness set trivially bounds each tag's nonce count. -/
lemma unlinkBadCacheBounded_init :
    unlinkBadCacheBounded
      (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) := by
  refine fun tag => ⟨∅, by simp [UnlinkBadState.init], ?_⟩
  intro nonce hcached
  simp [UnlinkBadState.init] at hcached

omit [Nonempty TagId] [DecidableEq TagId] [DecidableEq Nonce]
    [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The `unlinkBadReaderQueryImpl` does not modify the state. -/
private lemma unlinkBadReaderQueryImpl_state_eq
    (transcript : TagTranscript Nonce Digest)
    (st : UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support ((unlinkBadReaderQueryImpl transcript).run st), z.2 = st := by
  intro z hz
  unfold unlinkBadReaderQueryImpl at hz
  simpa using congrArg Prod.snd hz

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- When the tag still has a free slot (`sessionsUsed tag < sessionsPerTag`), the tag oracle samples
a fresh nonce and digest and advances the state via `unlinkBadTagNext`. -/
private lemma unlinkBadTagQueryImpl_run_of_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadTagQueryImpl (sessionsPerTag := sessionsPerTag) tag).run st =
      (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
        ($ᵗ Digest : ProbComp Digest) >>= fun auth =>
          pure (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
            unlinkBadTagNext tag st nonce auth)) := by
  simp [unlinkBadTagQueryImpl, unlinkBadTagNext, hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- When the tag has exhausted its slot budget, the tag oracle returns `none` and leaves the state
unchanged. -/
private lemma unlinkBadTagQueryImpl_run_of_not_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : ¬ st.sessionsUsed tag < sessionsPerTag) :
    (unlinkBadTagQueryImpl (sessionsPerTag := sessionsPerTag) tag).run st = pure (none, st) := by
  simp [unlinkBadTagQueryImpl, hslot]

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- Every outcome in the support of a successful tag query has the form
`(some ⟨nonce, auth⟩, unlinkBadTagNext tag st nonce auth)` for some sampled `nonce` and `auth`. -/
private lemma unlinkBadTagQueryImpl_support_of_lt
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    ∀ z ∈ support ((unlinkBadTagQueryImpl (sessionsPerTag := sessionsPerTag) tag).run st),
      ∃ nonce auth,
        z = (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
          unlinkBadTagNext tag st nonce auth) := by
  intro z hz
  rw [unlinkBadTagQueryImpl_run_of_lt (sessionsPerTag := sessionsPerTag) tag st hslot,
    mem_support_bind_iff] at hz
  rcases hz with ⟨nonce, _, hz⟩
  rw [mem_support_bind_iff] at hz
  rcases hz with ⟨auth, _, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  exact ⟨nonce, auth, hz⟩

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
    [DecidableEq Digest] [SampleableType Digest] in
/-- `unlinkBadCacheBounded` is preserved by a successful tag step: the new nonce is added to the
witness set, keeping its cardinality within the incremented session counter. -/
lemma unlinkBadTagNext_cacheBounded
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hbounded : unlinkBadCacheBounded st) :
    unlinkBadCacheBounded (unlinkBadTagNext tag st nonce auth) := by
  intro tag'
  obtain ⟨S, hScard, hS⟩ := hbounded tag'
  by_cases htag : tag' = tag
  · subst tag'
    refine ⟨insert nonce S, ?_, ?_⟩
    · simpa [unlinkBadTagNext] using
        (Finset.card_insert_le nonce S).trans (by omega : S.card + 1 ≤ st.sessionsUsed tag + 1)
    · intro nonce' hcached
      by_cases hkey : (tag, nonce') = (tag, nonce)
      · simp only [Prod.mk.injEq, true_and] at hkey
        subst nonce'
        exact Finset.mem_insert_self nonce S
      · exact Finset.mem_insert_of_mem (hS nonce' (by
          simpa [unlinkBadTagNext, QueryCache.cacheQuery_of_ne _ _ hkey] using hcached))
  · refine ⟨S, ?_, ?_⟩
    · simpa [unlinkBadTagNext, Function.update_of_ne htag] using hScard
    · intro nonce' hcached
      have hkey : (tag', nonce') ≠ (tag, nonce) := fun h => htag (Prod.ext_iff.mp h).1
      exact hS nonce' (by
        simpa [unlinkBadTagNext, QueryCache.cacheQuery_of_ne _ _ hkey] using hcached)

omit [Fintype TagId] [Nonempty TagId]
    [SampleableType Nonce] [DecidableEq Digest] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- A successful tag step does not push any tag's session counter above `sessionsPerTag`,
preserving the `sessionsUsed ≤ sessionsPerTag` invariant needed by the induction. -/
lemma unlinkBadTagNext_sessionsUsed_le
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag)
    (hused : ∀ tag, st.sessionsUsed tag ≤ sessionsPerTag) :
    ∀ tag', (unlinkBadTagNext tag st nonce auth).sessionsUsed tag' ≤ sessionsPerTag := by
  intro tag'
  by_cases htag : tag' = tag
  · subst htag
    simp [unlinkBadTagNext, Function.update_self]
    omega
  · simpa [unlinkBadTagNext, Function.update_of_ne htag] using hused tag'

omit [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
    [SampleableType Digest] [NeZero sessionsPerTag] in
/-- A successful tag step decrements `unlinkBadRemaining` by exactly 1, which is the key
step in the union-bound induction. -/
lemma unlinkBadRemaining_tagNext
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (nonce : Nonce) (auth : Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (unlinkBadTagNext tag st nonce auth) =
      unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 := by
  let remainingAt : TagId → ℕ := fun tag' => sessionsPerTag - st.sessionsUsed tag'
  have hpos : 0 < remainingAt tag := Nat.sub_pos_of_lt hslot
  have hpoint :
      (fun tag' : TagId =>
        sessionsPerTag -
          (unlinkBadTagNext tag st nonce auth).sessionsUsed tag') =
        Function.update remainingAt tag (remainingAt tag - 1) := by
    funext tag'
    by_cases htag : tag' = tag
    · subst htag
      simp [unlinkBadTagNext, remainingAt, Function.update_self]
      omega
    · simp [unlinkBadTagNext, remainingAt, Function.update_of_ne htag]
  calc
    unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (unlinkBadTagNext tag st nonce auth)
        = ∑ tag' : TagId, Function.update remainingAt tag (remainingAt tag - 1) tag' := by
          simp [unlinkBadRemaining, hpoint]
    _ = (∑ tag' : TagId, remainingAt tag') - 1 := sum_update_pred hpos
    _ = unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 := by
          simp [unlinkBadRemaining, remainingAt]

omit [DecidableEq TagId] [DecidableEq Nonce] [DecidableEq Digest]
    [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- If any tag still has a free slot, the total remaining budget is positive. Used to justify
the `- 1` arithmetic in `unlinkBadRemaining_tagNext`. -/
lemma unlinkBadRemaining_pos_of_slot
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (hslot : st.sessionsUsed tag < sessionsPerTag) :
    0 < unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st :=
  lt_of_lt_of_le (Nat.sub_pos_of_lt hslot) (by
    simpa [unlinkBadRemaining] using Finset.single_le_sum (s := (Finset.univ : Finset TagId))
      (f := fun tag' => sessionsPerTag - st.sessionsUsed tag')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ tag))

omit [Fintype TagId] [Nonempty TagId] [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- A single tag step raises `bad` with probability at most `sessionsUsed tag * maxNonceProb`:
the new nonce collides with one of the (at most `sessionsUsed tag`) previously cached nonces,
each matchable with probability at most `maxNonceProb`. -/
private lemma unlinkBadTagStep_bad_le
    (tag : TagId) (st : UnlinkBadState TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ maxNonceProb)
    (hbad : st.bad = false)
    (hbounded : unlinkBadCacheBounded st) :
    Pr[fun z : Option (TagTranscript Nonce Digest) × UnlinkBadState TagId Nonce Digest =>
        z.2.bad = true |
      (unlinkBadTagQueryImpl (sessionsPerTag := sessionsPerTag) tag).run st] ≤
      (st.sessionsUsed tag : ℝ≥0∞) * maxNonceProb := by
  by_cases hslot : st.sessionsUsed tag < sessionsPerTag
  · rw [unlinkBadTagQueryImpl_run_of_lt (sessionsPerTag := sessionsPerTag) tag st hslot,
      probEvent_bind_eq_tsum]
    have hinner : ∀ nonce : Nonce,
        Pr[fun z : Option (TagTranscript Nonce Digest) × UnlinkBadState TagId Nonce Digest =>
            z.2.bad = true |
          ($ᵗ Digest : ProbComp Digest) >>= fun auth =>
            pure (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest),
              unlinkBadTagNext tag st nonce auth)] =
          if (st.responses (tag, nonce)).isSome then 1 else 0 := by
      intro nonce
      by_cases hcached : (st.responses (tag, nonce)).isSome = true <;>
        simp [unlinkBadTagNext, hbad, hcached]
    simp_rw [hinner]
    obtain ⟨S, hScard, hS⟩ := hbounded tag
    calc
      ∑' nonce : Nonce,
          Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (st.responses (tag, nonce)).isSome then 1 else 0)
          = Pr[fun nonce : Nonce => (st.responses (tag, nonce)).isSome = true |
              ($ᵗ Nonce : ProbComp Nonce)] := by
            simp only [probEvent_eq_tsum_ite]
            refine tsum_congr fun nonce => ?_
            by_cases hcached : (st.responses (tag, nonce)).isSome = true <;>
              simp [hcached]
      _ ≤ Pr[fun nonce : Nonce => ∃ n ∈ S, nonce = n |
              ($ᵗ Nonce : ProbComp Nonce)] := by
            apply probEvent_mono
            intro nonce _ hcached
            exact ⟨nonce, hS nonce hcached, rfl⟩
      _ ≤ ∑ n ∈ S, Pr[fun nonce : Nonce => nonce = n |
              ($ᵗ Nonce : ProbComp Nonce)] :=
            probEvent_exists_finset_le_sum S ($ᵗ Nonce : ProbComp Nonce)
              (fun n nonce => nonce = n)
      _ ≤ ∑ _n ∈ S, maxNonceProb :=
            Finset.sum_le_sum fun n _ => by simpa [probEvent_eq_eq_probOutput] using hmax n
      _ = (S.card : ℝ≥0∞) * maxNonceProb := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (st.sessionsUsed tag : ℝ≥0∞) * maxNonceProb :=
            mul_le_mul' (Nat.cast_le.mpr hScard) le_rfl
  · rw [unlinkBadTagQueryImpl_run_of_not_lt (sessionsPerTag := sessionsPerTag) tag st hslot]
    simp [hbad]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- For any adversary and state `st` with `bad = false`,
the probability that bad fires is at most
`(∑ tag, sessionsPerTag − st.sessionsUsed tag) * sessionsPerTag * maxNonceProb`. -/
private lemma simulateQ_unlinkBad_prob_le
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ maxNonceProb)
    (st : UnlinkBadState TagId Nonce Digest)
    (hbounded : unlinkBadCacheBounded st)
    (hbad : st.bad = false)
    (hused : ∀ tag, st.sessionsUsed tag ≤ sessionsPerTag) :
    Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run st] ≤
      (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
        ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
  induction adversary using OracleComp.inductionOn generalizing st with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, hbad, Bool.false_eq_true,
      ite_false]
    exact zero_le
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind, monadLift_self]
    cases t with
    | inl tag =>
      simp only [unlinkBadQueryImpl, QueryImpl.add_apply_inl]
      by_cases hslot : st.sessionsUsed tag < sessionsPerTag
      · let step := (unlinkBadTagQueryImpl (sessionsPerTag := sessionsPerTag) tag).run st
        let cont := fun z : Option (TagTranscript Nonce Digest) ×
            UnlinkBadState TagId Nonce Digest =>
          (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) (oa z.1)).run z.2
        have hstep :
            Pr[fun z : Option (TagTranscript Nonce Digest) ×
                  UnlinkBadState TagId Nonce Digest => ¬ z.2.bad = false | step] ≤
              (sessionsPerTag : ℝ≥0∞) * maxNonceProb := by
          simpa [step] using (unlinkBadTagStep_bad_le (sessionsPerTag := sessionsPerTag)
            tag st maxNonceProb hmax hbad hbounded).trans
              (mul_le_mul' (Nat.cast_le.mpr (hused tag)) le_rfl)
        have hRpos := unlinkBadRemaining_pos_of_slot
          (sessionsPerTag := sessionsPerTag) tag st hslot
        have hcont :
            ∀ z ∈ support step, z.2.bad = false →
              Pr[fun y : Bool × UnlinkBadState TagId Nonce Digest => ¬ y.2.bad = false |
                  cont z] ≤
                ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) : ℝ≥0∞) *
                  ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
          intro z hz hzbad
          obtain ⟨nonce, auth, rfl⟩ :=
            unlinkBadTagQueryImpl_support_of_lt (sessionsPerTag := sessionsPerTag)
              tag st hslot z (by simpa [step] using hz)
          simpa [cont, unlinkBadRemaining_tagNext (sessionsPerTag := sessionsPerTag)
            tag st nonce auth hslot] using
            ih (some ({ nonce := nonce, auth := auth } : TagTranscript Nonce Digest))
              (unlinkBadTagNext tag st nonce auth)
              (unlinkBadTagNext_cacheBounded tag st nonce auth hbounded) hzbad
              (unlinkBadTagNext_sessionsUsed_le (sessionsPerTag := sessionsPerTag)
                tag st nonce auth hslot hused)
        calc
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
              step >>= cont]
              ≤ (sessionsPerTag : ℝ≥0∞) * maxNonceProb +
                  ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) :
                    ℝ≥0∞) * ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
                simpa [step, cont] using probEvent_bind_le_add (mx := step) (my := cont)
                  (p := fun z : Option (TagTranscript Nonce Digest) ×
                    UnlinkBadState TagId Nonce Digest => z.2.bad = false)
                  (q := fun y : Bool × UnlinkBadState TagId Nonce Digest => y.2.bad = false)
                  hstep hcont
          _ = (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
                have hRcast : (1 : ℝ≥0∞) +
                    ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st - 1 : ℕ) : ℝ≥0∞) =
                    (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) := by
                  exact_mod_cast Nat.add_sub_cancel' (Nat.succ_le_iff.mpr hRpos)
                nth_rw 1 [← one_mul ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)]
                rw [← add_mul, hRcast]
      · change Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
            ((unlinkBadTagQueryImpl tag).run st >>= fun p =>
              (simulateQ unlinkBadQueryImpl (oa p.1)).run p.2)] ≤ _
        rw [unlinkBadTagQueryImpl_run_of_not_lt (sessionsPerTag := sessionsPerTag) tag st hslot]
        simpa using ih none st hbounded hbad hused
    | inr transcript =>
      simp only [unlinkBadQueryImpl, QueryImpl.add_apply_inr]
      rw [probEvent_bind_eq_tsum]
      calc ∑' z, Pr[= z | (unlinkBadReaderQueryImpl transcript).run st] *
              Pr[fun w => w.2.bad | (simulateQ unlinkBadQueryImpl (oa z.1)).run z.2]
          ≤ ∑' z, Pr[= z | (unlinkBadReaderQueryImpl transcript).run st] *
              ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            apply ENNReal.tsum_le_tsum
            intro z
            by_cases hmem : z ∈ support ((unlinkBadReaderQueryImpl transcript).run st)
            · rw [unlinkBadReaderQueryImpl_state_eq transcript st z hmem]
              exact mul_le_mul' le_rfl (ih z.1 st hbounded hbad hused)
            · rw [probOutput_eq_zero_of_not_mem_support hmem]
              simp
        _ = (∑' z, Pr[= z | (unlinkBadReaderQueryImpl transcript).run st]) *
              ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            rw [ENNReal.tsum_mul_right]
        _ ≤ 1 * ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            gcongr
            exact tsum_probOutput_le_one
        _ = (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) st : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := one_mul _

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- A pointwise bound on the nonce sampler turns the bad-event probability into an explicit session
collision bound. -/
theorem unlinkBadExp_le_sessionCollisionBound
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce,
      (Pr[= nonce | ($ᵗ Nonce)]).toReal ≤ maxNonceProb) :
    (Pr[= true | unlinkBadExp (sessionsPerTag := sessionsPerTag) adversary]).toReal ≤
      ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb := by
  have hmax_ENNReal : ∀ n : Nonce,
      Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ ENNReal.ofReal maxNonceProb := by
    intro n
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top one_ne_top probOutput_le_one)]
    exact ENNReal.ofReal_le_ofReal (hmax n)
  have hlhs : Pr[= true | unlinkBadExp (sessionsPerTag := sessionsPerTag) adversary] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run
          UnlinkBadState.init] := by
    rw [← probEvent_eq_eq_probOutput, unlinkBadExp, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    simp
  rw [hlhs]
  have hcore := simulateQ_unlinkBad_prob_le (sessionsPerTag := sessionsPerTag)
    adversary (ENNReal.ofReal maxNonceProb)
    hmax_ENNReal UnlinkBadState.init unlinkBadCacheBounded_init (by simp [UnlinkBadState.init])
    (by simp [UnlinkBadState.init])
  have hconv := ENNReal.toReal_mono (a := Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest =>
      z.2.bad | (simulateQ (unlinkBadQueryImpl (sessionsPerTag := sessionsPerTag)) adversary).run
        UnlinkBadState.init]) (by simp [ENNReal.mul_eq_top]) hcore
  have hremaining :
      unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) =
          sessionsPerTag * Fintype.card TagId := by
    simp [unlinkBadRemaining, UnlinkBadState.init, Finset.sum_const, Finset.card_univ, mul_comm]
  have hsupp : (support ($ᵗ Nonce : ProbComp Nonce)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ne_eq, ← probFailure_eq_one_iff]; simp
  have hmax_nonneg : 0 ≤ maxNonceProb := ENNReal.toReal_nonneg.trans (hmax hsupp.choose)
  simp only [
    hremaining, Nat.cast_mul, toReal_mul, toReal_natCast, ENNReal.toReal_ofReal hmax_nonneg
  ] at hconv
  grind

end Theorems

end PRFTagReader
