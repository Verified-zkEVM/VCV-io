/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.HopAEager

/-!
# PRF Tag/Reader Protocol — Multiple-Bad Collision Bound

Composes the two hops into the multiple-vs-single ideal-world bound and discharges the
multiple-bad collision term in closed form:

* `multipleIdeal_le_hybrid_add_bad` (Hop A) and `hybrid_le_singleIdeal_add_readerSlack` (Hop B,
  from `Hybrid`/`HopB`) combine to give `multipleIdeal_le_singleIdeal_add_bad`;
* `multipleBadStep_*` lemmas track the per-step bad-flag bound and the session counter;
* `simulateQ_multipleBad_prob_le` unrolls those step lemmas to a union bound, yielding
  `multipleBad_bad_le_sessionCollisionBound`;
* the bad-event bridge `probOutput_unlinkBadExp_eq` connects `unlinkBadExp` to the bad flag of
  the instrumented multiple-bad handler, and `unlinkPRFIdeal_gap_le_unlinkBad` packages the
  middle hop of the headline reduction.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ### Multiple-vs-single bound via the hybrid

The multiple-vs-single bound `multipleIdeal_le_singleIdeal_add_bad` follows by chaining the two
hops:

* **Hop A** (`multipleIdeal_le_hybrid_add_bad`): the multiple-session ideal world is bounded by the
  hybrid world plus the within-tag nonce-collision probability (the `bad` flag of the instrumented
  `multipleBadQueryImpl`) plus the reader/tag slacks
  `qReader * |TagId| / |Digest|` and `qReader * qTag / |Nonce|`.
* **Hop B** (`hybrid_le_singleIdeal_add_readerSlack`): the hybrid world is bounded by the
  single-session ideal world plus the reader-slack term
  `qReader * |TagId| * sessionsPerTag / |Digest|`.

Combining the two yields the headline bound below, with the nonce-collision term expressed in the
`multipleBadQueryImpl` shape (this is the shape that Hop A actually produces; downstream consumers
either match this shape or take the bridge as a hypothesis). -/

/-- Core coupling bound for the unlinkability reduction, proved by chaining Hop A
(`multipleIdeal_le_hybrid_add_bad`) and Hop B (`hybrid_le_singleIdeal_add_readerSlack`).

The multiple-session ideal world is bounded by the single-session ideal world plus the
within-tag nonce-collision probability (carried by the instrumented `multipleBadQueryImpl`'s
`bad` flag) plus three additive slack terms:

* `qReader * Fintype.card TagId / Fintype.card Digest` (Hop A's reader-cell asymmetry between the
  multiple and hybrid worlds);
* `qReader * qTag / Fintype.card Nonce` (Hop A's Sub-B tag-cache aliasing slack);
* `qReader * Fintype.card TagId * sessionsPerTag / Fintype.card Digest` (Hop B's hybrid-vs-single
  reader-cell asymmetry).

The bound assumes `HasDistinctUnlinkReaderNonces` (each nonce is carried by at most one reader
query), which both hops require. -/
lemma multipleIdeal_le_singleIdeal_add_bad [Fintype Nonce] [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag)
    (hdist : HasDistinctUnlinkReaderNonces adversary) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] +
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] +
      ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  have hA := multipleIdeal_le_hybrid_add_bad (sessionsPerTag := sessionsPerTag)
    adversary qReader qTag hqReader hqTag hdist
  have hB := hybrid_le_singleIdeal_add_readerSlack (sessionsPerTag := sessionsPerTag)
    adversary qReader hdist hqReader
  -- Chain Hop A and Hop B: hybrid ≤ single + Hop-B slack, applied inside hA's RHS.
  calc Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
              (UnlinkState.init, ∅)]
      ≤ _ := hA
    _ ≤ _ := by
        -- Reorder/widen via Hop B on the hybrid term.
        have := add_le_add_right
          (add_le_add_right
            (add_le_add_right
              (add_le_add_right hB
                (Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                    z.2.2.bad |
                    (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
                      ((UnlinkState.init, ∅), UnlinkBadState.init)]))
              (((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) /
                (Fintype.card Digest : ℝ≥0∞)))
            (((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞))) 0
        -- The shape after `add_le_add_right` differs; we instead use a direct calc by
        -- rewriting the bound's RHS as a re-grouped sum.
        clear this
        -- Apply Hop B by widening the hybrid term.
        have hHybridLe :
            Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
                (HybridState.init, ∅)] +
            Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
              (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
                ((UnlinkState.init, ∅), UnlinkBadState.init)] +
            ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) /
              (Fintype.card Digest : ℝ≥0∞) +
            ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞)
              ≤
            Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
              (UnlinkState.init, ∅)] +
            ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
              (Fintype.card Digest : ℝ≥0∞) +
            Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
              (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
                ((UnlinkState.init, ∅), UnlinkBadState.init)] +
            ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) /
              (Fintype.card Digest : ℝ≥0∞) +
            ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
          gcongr
        refine hHybridLe.trans ?_
        -- Now re-associate the RHS terms to the canonical order in the goal.
        ring_nf
        rfl

/-! ### Multiple-vs-single bound: session-collision bound for `multipleBadQueryImpl`

The induction port `simulateQ_multipleBad_prob_le` mirrors the proven
`simulateQ_unlinkBad_prob_le`: at each tag step the bad flag fires with probability at most
`sessionsUsed tag * maxNonceProb`, and the per-tag session counter (synchronised with the
multiple-ideal state) drops by exactly one. The composed bound is
`unlinkBadRemaining sB * sessionsPerTag * maxNonceProb`, which collapses at the initial state to
the explicit `sessionsPerTag^2 * |TagId| * maxNonceProb` session collision bound. -/

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Per-step tag bound for `multipleBadQueryImpl`: a single tag query raises the bad flag with
probability at most `sB.sessionsUsed tag * maxNonceProb`. The proof factors through
`multipleIdealQueryImpl_tag_run_of_lt`'s `idealCacheStep`-based form; the inner `idealCacheStep`
draw is distribution-neutral for the bad bit because `multipleBadAdvance` only inspects the
*nonce* component of the transcript via `(sB.responses (tag, nonce)).isSome`. -/
lemma multipleBadStep_bad_le
    (tag : TagId) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ maxNonceProb)
    (hbad : sB.bad = false)
    (hbounded : unlinkBadCacheBounded sB) :
    Pr[fun z :
        Option (TagTranscript Nonce Digest) ×
          ((UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) ×
            UnlinkBadState TagId Nonce Digest) => z.2.2.bad |
      (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) ((s, c), sB)] ≤
      (sB.sessionsUsed tag : ℝ≥0∞) * maxNonceProb := by
  by_cases hslot : s.sessionsUsed tag < sessionsPerTag
  · rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)]
    -- The wrapper is `(multipleIdealQueryImpl tag (s,c)) >>= pure ∘ f` for
    -- `f r := (r.1, (r.2.1, r.2.2), multipleBadAdvance tag sB r.1)`. Push the bad bit through.
    change Pr[fun z :
        Option (TagTranscript Nonce Digest) ×
          ((UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache) ×
            UnlinkBadState TagId Nonce Digest) => z.2.2.bad |
        (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) (s, c) >>=
          pure ∘ fun r => (r.1, (r.2.1, r.2.2), multipleBadAdvance tag sB r.1)] ≤ _
    rw [probEvent_bind_pure_comp]
    -- Now the event is `(multipleBadAdvance tag sB r.1).bad = true`, evaluated on the multiple-
    -- ideal tag step. Unfold the tag step to its `idealCacheStep` form, factoring the structure
    -- update through a `set` to sidestep the 4.29 rewrite/elaboration quirk on `{ s with … }`.
    rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot]
    set advU := ({ sessionsUsed :=
        Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId)
      with hadvU
    change probEvent (($ᵗ Nonce : ProbComp Nonce) >>= fun nonce =>
        idealCacheStep c (tag, nonce) >>= fun r =>
          pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), advU, r.2)) _ ≤ _
    rw [probEvent_bind_eq_tsum]
    -- For each nonce, the inner bind `idealCacheStep c (tag, nonce) >>= fun r => pure (…)`'s bad
    -- bit only depends on `(sB.responses (tag, nonce)).isSome`.
    -- After `probEvent_bind_pure_comp`, the event is the composition; simplify per nonce.
    simp_rw [Function.comp_def]
    have hinner : ∀ x : Nonce,
        probEvent (idealCacheStep c (tag, x) >>= fun r =>
            pure (some (⟨x, r.1⟩ : TagTranscript Nonce Digest), advU, r.2))
          (fun x => (multipleBadAdvance tag sB x.1).bad = true) =
          if (sB.responses (tag, x)).isSome then 1 else 0 := by
      intro x
      rw [probEvent_bind_eq_tsum]
      by_cases hcached : (sB.responses (tag, x)).isSome = true
      · simp only [hcached, if_true]
        have hkey : ∀ r : Digest × ((TagId × Nonce) →ₒ Digest).QueryCache,
            probEvent
              (pure (some (⟨x, r.1⟩ : TagTranscript Nonce Digest), advU, r.2) : ProbComp _)
              (fun y => (multipleBadAdvance tag sB y.1).bad = true) = 1 := by
          intro r
          simp [multipleBadAdvance, hbad, hcached]
        simp_rw [hkey, mul_one]
        exact HasEvalPMF.tsum_probOutput_eq_one _
      · have hcached' : (sB.responses (tag, x)).isSome = false := by
          cases h : (sB.responses (tag, x)).isSome
          · rfl
          · exact absurd h hcached
        rw [if_neg (by simp [hcached'])]
        have hkey : ∀ r : Digest × ((TagId × Nonce) →ₒ Digest).QueryCache,
            probEvent
              (pure (some (⟨x, r.1⟩ : TagTranscript Nonce Digest), advU, r.2) : ProbComp _)
              (fun y => (multipleBadAdvance tag sB y.1).bad = true) = 0 := by
          intro r
          simp [multipleBadAdvance, hbad, hcached']
        simp_rw [hkey, mul_zero, tsum_zero]
    -- Replace the inner probEvent at each nonce with the explicit `if`.
    refine (tsum_congr (g := fun x => Pr[= x | ($ᵗ Nonce : ProbComp Nonce)] *
        (if (sB.responses (tag, x)).isSome then 1 else 0)) fun x => ?_).trans_le ?_
    · exact congrArg (Pr[= x | ($ᵗ Nonce : ProbComp Nonce)] * ·) (hinner x)
    -- The remaining inequality is the classic union bound, identical to `unlinkBadTagStep_bad_le`.
    -- Now mirror the proof of `unlinkBadTagStep_bad_le`.
    obtain ⟨S, hScard, hS⟩ := hbounded tag
    have hcard_le : S.card ≤ sB.sessionsUsed tag := hScard
    calc
      ∑' nonce : Nonce,
          Pr[= nonce | ($ᵗ Nonce : ProbComp Nonce)] *
            (if (sB.responses (tag, nonce)).isSome then 1 else 0)
          = Pr[fun nonce : Nonce => (sB.responses (tag, nonce)).isSome = true |
              ($ᵗ Nonce : ProbComp Nonce)] := by
            simp only [probEvent_eq_tsum_ite]
            refine tsum_congr fun nonce => ?_
            by_cases hcached : (sB.responses (tag, nonce)).isSome = true
            · simp [hcached]
            · simp [hcached]
      _ ≤ Pr[fun nonce : Nonce => ∃ n ∈ S, nonce = n |
              ($ᵗ Nonce : ProbComp Nonce)] := by
            apply probEvent_mono
            intro nonce _ hcached
            exact ⟨nonce, hS nonce hcached, rfl⟩
      _ ≤ ∑ n ∈ S, Pr[fun nonce : Nonce => nonce = n |
              ($ᵗ Nonce : ProbComp Nonce)] :=
            probEvent_exists_finset_le_sum S ($ᵗ Nonce : ProbComp Nonce)
              (fun n nonce => nonce = n)
      _ ≤ ∑ _n ∈ S, maxNonceProb := by
            apply Finset.sum_le_sum
            intro n _
            simpa [probEvent_eq_eq_probOutput] using hmax n
      _ = (S.card : ℝ≥0∞) * maxNonceProb := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (sB.sessionsUsed tag : ℝ≥0∞) * maxNonceProb :=
            mul_le_mul' (Nat.cast_le.mpr hcard_le) le_rfl
  · -- Slot exhausted: the tag oracle returns `none`, no state change, bad stays `false`.
    rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)]
    rw [multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot]
    -- Now `(pure (none, s, c)) >>= fun r => pure (..., multipleBadAdvance tag sB r.1)` evaluates
    -- to `pure (none, (s, c), sB)`; the bad bit is `sB.bad = false`.
    have h0 :
        (probEvent
          (do
            let r ← (pure ((none, s, c)) :
              ProbComp (Option (TagTranscript Nonce Digest) ×
                UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache))
            pure (r.1, (r.2.1, r.2.2), multipleBadAdvance tag sB r.1))
          (fun z : _ × _ × UnlinkBadState TagId Nonce Digest => z.2.2.bad = true)) = 0 := by
      simp [multipleBadAdvance, hbad]
    refine h0 ▸ zero_le _

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Bad-bit invariant: in any reachable state of `multipleBadQueryImpl`, the bad-world component's
session counters equal the multiple-ideal state's session counters. Used to swap the slot check
from `s.sessionsUsed` to `sB.sessionsUsed` in the per-step bound. -/
lemma multipleBadStep_sessionsUsed_eq
    (tag : TagId) (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hsync : sB.sessionsUsed = s.sessionsUsed) :
    ∀ z ∈ support ((multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) ((s, c), sB)),
      z.2.2.sessionsUsed = z.2.1.1.sessionsUsed := by
  intro z hz
  rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)] at hz
  obtain ⟨r, hr, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  have hz_eq : z = (r.1, (r.2.1, r.2.2), multipleBadAdvance tag sB r.1) := hz
  subst hz_eq
  -- The pair `r = (transcript?, s')` comes from `multipleIdealQueryImpl tag (s, c)`; we case-split
  -- on whether the slot was available, which determines whether `r.1 = some _` (sB advances) or
  -- `r.1 = none` (sB unchanged). In both cases the resulting bad-state's `sessionsUsed` equals
  -- the resulting ideal-state's `sessionsUsed`.
  by_cases hslot : s.sessionsUsed tag < sessionsPerTag
  · rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot] at hr
    set advU := ({ sessionsUsed :=
        Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId)
      with hadvU
    obtain ⟨nonce, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    obtain ⟨r', _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    have hr_eq : r = (some (⟨nonce, r'.1⟩ : TagTranscript Nonce Digest), advU, r'.2) := hr
    subst hr_eq
    simp only [multipleBadAdvance]
    funext t
    by_cases htag : t = tag
    · subst htag; simp [advU, Function.update_self, hsync]
    · simp [advU, Function.update_of_ne htag, hsync]
  · rw [multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot] at hr
    have hr_eq : r = (none, s, c) := hr
    subst hr_eq
    simp [multipleBadAdvance, hsync]

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Reader queries leave the bad-world component untouched: in any reachable state of
`multipleBadQueryImpl` on a reader query, the bad-state is unchanged. -/
lemma multipleBadStep_reader_state_eq
    (transcript : TagTranscript Nonce Digest)
    (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support ((multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) ((s, c), sB)),
      z.2.2 = sB := by
  intro z hz
  rw [multipleBadQueryImpl_reader_run transcript ((s, c), sB)] at hz
  obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  have hz_eq : z = (r.1, (r.2.1, r.2.2), sB) := hz
  subst hz_eq
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- Cache-bounded and sessions-used invariants of the bad-world state are preserved by reachable
states of `multipleBadQueryImpl`. The reader branch leaves `sB` untouched; the tag branch threads
through `unlinkBadTagNext_cacheBounded`/`unlinkBadTagNext_sessionsUsed_le` via the bridge between
`multipleBadAdvance` and `unlinkBadTagNext`. -/
lemma multipleBadStep_preserves
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hbounded : unlinkBadCacheBounded sB)
    (hused : ∀ tag : TagId, sB.sessionsUsed tag ≤ sessionsPerTag)
    (hsync : sB.sessionsUsed = s.sessionsUsed) :
    ∀ z ∈ support ((multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t) ((s, c), sB)),
      unlinkBadCacheBounded z.2.2 ∧
        (∀ tag : TagId, z.2.2.sessionsUsed tag ≤ sessionsPerTag) ∧
        z.2.2.sessionsUsed = z.2.1.1.sessionsUsed := by
  cases t with
  | inl tag =>
    intro z hz
    rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)] at hz
    obtain ⟨r, hr, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    have hz_eq : z = (r.1, (r.2.1, r.2.2), multipleBadAdvance tag sB r.1) := hz
    subst hz_eq
    by_cases hslot : s.sessionsUsed tag < sessionsPerTag
    · rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot] at hr
      set advU := ({ sessionsUsed :=
          Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId)
        with hadvU
      obtain ⟨nonce, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      obtain ⟨r', _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      have hr_eq : r = (some (⟨nonce, r'.1⟩ : TagTranscript Nonce Digest), advU, r'.2) := hr
      subst hr_eq
      -- `multipleBadAdvance tag sB (some ⟨nonce, r'.1⟩) = unlinkBadTagNext tag sB nonce r'.1`.
      have hbridge :
          multipleBadAdvance tag sB
              (some (⟨nonce, r'.1⟩ : TagTranscript Nonce Digest)) =
            unlinkBadTagNext tag sB nonce r'.1 := rfl
      have hsBslot : sB.sessionsUsed tag < sessionsPerTag := by rw [hsync]; exact hslot
      refine ⟨?_, ?_, ?_⟩
      · rw [hbridge]
        exact unlinkBadTagNext_cacheBounded tag sB nonce r'.1 hbounded
      · rw [hbridge]
        exact unlinkBadTagNext_sessionsUsed_le tag sB nonce r'.1 hsBslot hused
      · rw [hbridge]
        funext t
        by_cases htag : t = tag
        · subst htag
          simp [advU, unlinkBadTagNext, Function.update_self, hsync]
        · simp [advU, unlinkBadTagNext, Function.update_of_ne htag, hsync]
    · rw [multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot] at hr
      have hr_eq : r = (none, s, c) := hr
      subst hr_eq
      simp only [multipleBadAdvance]
      exact ⟨hbounded, hused, hsync⟩
  | inr transcript =>
    intro z hz
    rw [multipleBadQueryImpl_reader_run transcript ((s, c), sB)] at hz
    obtain ⟨r, hr, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    have hz_eq : z = (r.1, (r.2.1, r.2.2), sB) := hz
    subst hz_eq
    -- The reader handler `multipleIdealQueryImpl (Sum.inr transcript) (s, c)` produces
    -- `(reply, s, c')` for some `c'` — the multiple-ideal state component is unchanged.
    rw [multipleIdealQueryImpl_reader_run transcript s c] at hr
    obtain ⟨rs, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    have hr_eq : r = (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2) := hr
    subst hr_eq
    exact ⟨hbounded, hused, hsync⟩

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- **Bad-event union bound for `multipleBadQueryImpl`.** Starting from a multiple-bad state
satisfying the cache-boundedness, session-used-≤-`sessionsPerTag`, and sync invariants, with the
bad flag unset, the probability that bad fires under any adversary is at most
`unlinkBadRemaining sB * sessionsPerTag * maxNonceProb`. Direct port of
`simulateQ_unlinkBad_prob_le` to the multiple-bad handler. -/
lemma simulateQ_multipleBad_prob_le
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ≥0∞)
    (hmax : ∀ n : Nonce, Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ maxNonceProb)
    (s : UnlinkState TagId)
    (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hbounded : unlinkBadCacheBounded sB)
    (hbad : sB.bad = false)
    (hused : ∀ tag, sB.sessionsUsed tag ≤ sessionsPerTag)
    (hsync : sB.sessionsUsed = s.sessionsUsed) :
    Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) adversary).run ((s, c), sB)] ≤
      (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB : ℝ≥0∞) *
        ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
  induction adversary using OracleComp.inductionOn generalizing s c sB with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, hbad, Bool.false_eq_true,
      ite_false]
    exact zero_le _
  | query_bind t oa ih =>
    rw [multipleBad_run_query_bind' t (fun r => oa r) ((s, c), sB)]
    -- Per-query bound (depends on the query case)
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · -- Tag query, slot available: apply `multipleBadStep_bad_le`, then induct on the
        -- continuation with updated invariants.
        set step := (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) ((s, c), sB) with hstep
        set cont := fun p : Option (TagTranscript Nonce Digest) ×
            MultipleBadState TagId Nonce Digest sessionsPerTag =>
          (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag)) (oa p.1)).run p.2 with hcont
        have hstepBound :
            Pr[fun z : Option (TagTranscript Nonce Digest) ×
                  MultipleBadState TagId Nonce Digest sessionsPerTag => ¬ z.2.2.bad = false |
              step] ≤ (sessionsPerTag : ℝ≥0∞) * maxNonceProb := by
          have hbase :=
            multipleBadStep_bad_le (sessionsPerTag := sessionsPerTag) tag s c sB maxNonceProb
              hmax hbad hbounded
          have hbound :
              (sB.sessionsUsed tag : ℝ≥0∞) * maxNonceProb ≤
                (sessionsPerTag : ℝ≥0∞) * maxNonceProb :=
            mul_le_mul' (Nat.cast_le.mpr (hused tag)) le_rfl
          simpa [step] using hbase.trans hbound
        have hRpos : 0 < unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB := by
          apply unlinkBadRemaining_pos_of_slot (sessionsPerTag := sessionsPerTag) tag sB
          rw [hsync]; exact hslot
        have hcontBound :
            ∀ p ∈ support step, p.2.2.bad = false →
              Pr[fun y : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                  ¬ y.2.2.bad = false | cont p] ≤
                ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB - 1 : ℕ) : ℝ≥0∞) *
                  ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
          intro p hp hpbad
          have hp_real : p ∈ support
              (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (Sum.inl tag) ((s, c), sB)) := by
            simpa [step] using hp
          have hinvs := multipleBadStep_preserves (sessionsPerTag := sessionsPerTag)
            (Sum.inl tag) s c sB hbounded hused hsync p hp_real
          have hRdec :
              unlinkBadRemaining (sessionsPerTag := sessionsPerTag) p.2.2 =
                unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB - 1 := by
            -- The bad state advanced via `unlinkBadTagNext`; remaining drops by one.
            rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)] at hp_real
            obtain ⟨r, hr, hp⟩ := (mem_support_bind_iff _ _ _).mp hp_real
            have hp_eq : p = (r.1, (r.2.1, r.2.2), multipleBadAdvance tag sB r.1) := hp
            subst hp_eq
            rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot] at hr
            set advU := ({ sessionsUsed :=
                Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } : UnlinkState TagId)
              with hadvU
            obtain ⟨nonce, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
            obtain ⟨r', _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
            have hr_eq : r = (some (⟨nonce, r'.1⟩ : TagTranscript Nonce Digest), advU, r'.2) := hr
            subst hr_eq
            have hbridge :
                multipleBadAdvance tag sB
                    (some (⟨nonce, r'.1⟩ : TagTranscript Nonce Digest)) =
                  unlinkBadTagNext tag sB nonce r'.1 := rfl
            change unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
              (multipleBadAdvance tag sB
                (some (⟨nonce, r'.1⟩ : TagTranscript Nonce Digest))) = _
            rw [hbridge]
            exact unlinkBadRemaining_tagNext (sessionsPerTag := sessionsPerTag)
              tag sB nonce r'.1 (hsync ▸ hslot)
          have hih :=
            ih p.1 p.2.1.1 p.2.1.2 p.2.2 hinvs.1 hpbad hinvs.2.1 hinvs.2.2
          simpa [cont, hRdec, Prod.eq_iff_fst_eq_snd_eq, show (p.2.1.1, p.2.1.2) = p.2.1 from rfl]
            using hih
        have hcombine := probEvent_bind_le_add (mx := step) (my := cont)
          (p := fun z : Option (TagTranscript Nonce Digest) ×
            MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad = false)
          (q := fun y : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
            y.2.2.bad = false)
          (ε₁ := (sessionsPerTag : ℝ≥0∞) * maxNonceProb)
          (ε₂ := ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB - 1 : ℕ) :
              ℝ≥0∞) * ((sessionsPerTag : ℝ≥0∞) * maxNonceProb))
          hstepBound hcontBound
        calc
          Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
              step >>= cont]
              ≤ (sessionsPerTag : ℝ≥0∞) * maxNonceProb +
                  ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB - 1 : ℕ) :
                    ℝ≥0∞) * ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
                simpa [step, cont] using hcombine
          _ = (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := by
                let R := unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB
                let c' := (sessionsPerTag : ℝ≥0∞) * maxNonceProb
                have hR : 1 + (R - 1) = R := Nat.add_sub_cancel' (Nat.succ_le_iff.mpr hRpos)
                have hRcast : (1 : ℝ≥0∞) + ((R - 1 : ℕ) : ℝ≥0∞) = (R : ℝ≥0∞) := by
                  exact_mod_cast hR
                change c' + ((R - 1 : ℕ) : ℝ≥0∞) * c' = (R : ℝ≥0∞) * c'
                nth_rw 1 [← one_mul c']
                rw [← add_mul, hRcast]
      · -- Slot exhausted: the tag step is `pure (none, (s, c), sB)`; induct directly.
        change
          Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
            ((multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) ((s, c), sB)) >>= fun p =>
              (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (oa p.1)).run p.2] ≤
            (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)
        rw [multipleBadQueryImpl_tag_run tag ((s, c), sB),
          multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot]
        simp only [pure_bind, bind_assoc, multipleBadAdvance]
        exact ih none s c sB hbounded hbad hused hsync
    | inr transcript =>
      -- Reader branch: bad-world component untouched; induct on the continuation.
      rw [probEvent_bind_eq_tsum]
      calc ∑' z,
              Pr[= z | (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) ((s, c), sB)] *
              Pr[fun y : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => y.2.2.bad |
                (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (oa z.1)).run z.2]
          ≤ ∑' z,
              Pr[= z | (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) ((s, c), sB)] *
              ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            apply ENNReal.tsum_le_tsum
            intro z
            by_cases hmem :
                z ∈ support ((multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (Sum.inr transcript)) ((s, c), sB))
            · have hzeq := multipleBadStep_reader_state_eq (sessionsPerTag := sessionsPerTag)
                transcript s c sB z hmem
              have hinvs := multipleBadStep_preserves (sessionsPerTag := sessionsPerTag)
                (Sum.inr transcript) s c sB hbounded hused hsync z hmem
              have hih := ih z.1 z.2.1.1 z.2.1.2 z.2.2 hinvs.1
                (by rw [hzeq]; exact hbad) hinvs.2.1 hinvs.2.2
              refine mul_le_mul' le_rfl ?_
              have : ((z.2.1.1, z.2.1.2), z.2.2) = z.2 := by
                rcases z with ⟨z1, z21, z22⟩; rfl
              rw [this] at hih
              rw [hzeq] at hih
              exact hih
            · rw [probOutput_eq_zero_of_not_mem_support hmem]
              simp
        _ = (∑' z,
              Pr[= z | (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) ((s, c), sB)]) *
              ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB : ℝ≥0∞) *
                ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            rw [ENNReal.tsum_mul_right]
        _ ≤ 1 * ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb)) := by
            gcongr
            exact tsum_probOutput_le_one
        _ = (unlinkBadRemaining (sessionsPerTag := sessionsPerTag) sB : ℝ≥0∞) *
              ((sessionsPerTag : ℝ≥0∞) * maxNonceProb) := one_mul _

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- **Final session-collision bound** for the multiple-bad handler. Chains
`simulateQ_multipleBad_prob_le` at the initial state, where the `unlinkBadRemaining` collapses to
`sessionsPerTag * |TagId|`, giving the explicit `sessionsPerTag^2 * |TagId| * maxNonceProb`
session-collision bound. The headline analogue of `unlinkBadExp_le_sessionCollisionBound`. -/
theorem multipleBad_bad_le_sessionCollisionBound
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (maxNonceProb : ℝ)
    (hmax : ∀ nonce : Nonce, (Pr[= nonce | ($ᵗ Nonce)]).toReal ≤ maxNonceProb) :
    (Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)]).toReal ≤
      ((sessionsPerTag ^ 2 * Fintype.card TagId : ℕ) : ℝ) * maxNonceProb := by
  have hmax_ENNReal : ∀ n : Nonce,
      Pr[= n | ($ᵗ Nonce : ProbComp Nonce)] ≤ ENNReal.ofReal maxNonceProb := by
    intro n
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top one_ne_top probOutput_le_one)]
    exact ENNReal.ofReal_le_ofReal (hmax n)
  have hcore := simulateQ_multipleBad_prob_le (sessionsPerTag := sessionsPerTag)
    adversary (ENNReal.ofReal maxNonceProb) hmax_ENNReal UnlinkState.init ∅
    UnlinkBadState.init unlinkBadCacheBounded_init
    (by simp [UnlinkBadState.init]) (by simp [UnlinkBadState.init])
    (by simp [UnlinkState.init, UnlinkBadState.init])
  have hconv : (Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)]).toReal ≤
      ((unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
          (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) :
            ℝ≥0∞) *
        ((sessionsPerTag : ℝ≥0∞) * ENNReal.ofReal maxNonceProb)).toReal := by
    exact ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) hcore
  have hremaining :
      unlinkBadRemaining (sessionsPerTag := sessionsPerTag)
        (UnlinkBadState.init (TagId := TagId) (Nonce := Nonce) (Digest := Digest)) =
          sessionsPerTag * Fintype.card TagId := by
    simp [unlinkBadRemaining, UnlinkBadState.init, Finset.sum_const, Finset.card_univ,
      mul_comm]
  have hsupp : (support ($ᵗ Nonce : ProbComp Nonce)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ne_eq, ← probFailure_eq_one_iff]
    simp
  obtain ⟨nonce0, _⟩ := hsupp
  have hmax_nonneg : 0 ≤ maxNonceProb := ENNReal.toReal_nonneg.trans (hmax nonce0)
  simp only [
    hremaining, Nat.cast_mul, toReal_mul, toReal_natCast, ENNReal.toReal_ofReal hmax_nonneg
  ] at hconv
  grind

/-! ### Multiple-vs-single bound: bad-event bridge

The chain `multipleIdeal_le_singleIdeal_add_bad` produces a bad-event term in the shape
`Pr[bad | multipleBadQueryImpl]`. The lemma `multipleBad_bad_le_sessionCollisionBound` above gives
the explicit closed-form session-collision bound `(sessionsPerTag^2 * |TagId|) * maxNonceProb` over
this shape, the analogue of `unlinkBadExp_le_sessionCollisionBound` for the multiple-bad handler.
The per-step bound `multipleBadStep_bad_le` sidesteps a Lean 4.29 elaboration quirk on `do` blocks
containing structure updates by introducing a `set` binding for the advanced multiple-ideal
state. -/

/-- `unlinkBadExp` outputs `true` exactly with the probability that the bad flag fires. -/
lemma probOutput_unlinkBadExp_eq
    (adversary : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | unlinkBadExp (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) adversary] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad |
        (simulateQ (unlinkBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          UnlinkBadState.init] := by
  rw [← probEvent_eq_eq_probOutput, unlinkBadExp, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun z => ?_
  by_cases hz : z.2.bad <;> simp [hz]

/-- Coupling bound for the two random-function worlds (the ideal-PRF experiments of the multiple-
and single-session reductions): the gap is bounded by the within-tag nonce-collision probability
(carried by the instrumented `multipleBadQueryImpl`'s `bad` flag) plus three additive slack terms
from chaining Hops A and B. The two worlds are not identical-until-bad — their reader oracles
diverge unconditionally because the single-session reader checks `Fintype.card TagId *
sessionsPerTag` random-oracle cells against the multiple world's `Fintype.card TagId` — so the
bound also carries `qReader * Fintype.card TagId * sessionsPerTag / Fintype.card Digest`. -/
theorem unlinkPRFIdeal_gap_le_unlinkBad [Fintype Nonce] [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag)
    (hdist : HasDistinctUnlinkReaderNonces adversary) :
    (Pr[= true | PRFScheme.prfIdealExp (unlinkToMultiplePRFReduction
          (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) adversary)]).toReal -
        (Pr[= true | PRFScheme.prfIdealExp (unlinkToSinglePRFReduction
          (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) adversary)]).toReal ≤
      (Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)]).toReal +
      ((qReader * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) +
      ((qReader * qTag : ℕ) : ℝ) / (Fintype.card Nonce : ℝ) +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) /
        (Fintype.card Digest : ℝ) := by
  have hcore := multipleIdeal_le_singleIdeal_add_bad (sessionsPerTag := sessionsPerTag)
    adversary qReader qTag hqReader hqTag hdist
  rw [prfIdealExp_unlinkToMultiplePRFReduction_eq_run' adversary,
    prfIdealExp_unlinkToSinglePRFReduction_eq_run' adversary]
  set M := Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
    (UnlinkState.init, ∅)] with hM
  set S := Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
    (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
    (UnlinkState.init, ∅)] with hS
  set B := Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
    (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
      ((UnlinkState.init, ∅), UnlinkBadState.init)] with hB
  set slackR := ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) /
    (Fintype.card Digest : ℝ≥0∞) with hslackR
  set slackN := ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) with hslackN
  set slackS := ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
    (Fintype.card Digest : ℝ≥0∞) with hslackS
  have hSt : S ≠ ⊤ := ne_top_of_le_ne_top one_ne_top probOutput_le_one
  have hBt : B ≠ ⊤ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
  have hne : Nonempty Digest := ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  have hnen : Nonempty Nonce := ⟨(SampleableType.selectElem (β := Nonce)).defaultResult⟩
  have hcardposD : 0 < Fintype.card Digest := Fintype.card_pos
  have hcardposN : 0 < Fintype.card Nonce := Fintype.card_pos
  have hslackRt : slackR ≠ ⊤ := by
    rw [hslackR]
    refine ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hslackNt : slackN ≠ ⊤ := by
    rw [hslackN]
    refine ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hslackSt : slackS ≠ ⊤ := by
    rw [hslackS]
    refine ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hslackReq : slackR.toReal =
      ((qReader * Fintype.card TagId : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
    rw [hslackR, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hslackNeq : slackN.toReal =
      ((qReader * qTag : ℕ) : ℝ) / (Fintype.card Nonce : ℝ) := by
    rw [hslackN, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hslackSeq : slackS.toReal =
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ) / (Fintype.card Digest : ℝ) := by
    rw [hslackS, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hMt : M.toReal ≤ S.toReal + B.toReal + slackR.toReal + slackN.toReal + slackS.toReal := by
    have hSB : S + B ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hSt, hBt⟩
    have hSBR : S + B + slackR ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hSB, hslackRt⟩
    have hSBRN : S + B + slackR + slackN ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hSBR, hslackNt⟩
    rw [← ENNReal.toReal_add hSt hBt, ← ENNReal.toReal_add hSB hslackRt,
      ← ENNReal.toReal_add hSBR hslackNt, ← ENNReal.toReal_add hSBRN hslackSt]
    exact ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hSBRN, hslackSt⟩) hcore
  rw [hslackReq, hslackNeq, hslackSeq] at hMt
  linarith


end UnlinkReduction

end PRFTagReader
