/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.Hybrid
import VCVio.EvalDist.Monad.Disagreement

/-!
# PRF Tag/Reader Protocol — Hybrid-to-single coupling with reader-slack

Bounding the gap between the hybrid world and the single-session ideal world. Deliverables
2-4:

* **Deliverable 2**: the per-reader-query slack bound `probEvent_coupledReader_disagree_le`,
  which charges each reader-query column to `qReader * |TagId| * sessionsPerTag / |Digest|`
  via a union bound over `idealCacheStep`.
* **Deliverable 3**: the coupled reader step and the lazy-vs-coupled coupling theorem
  `evalDist_simulateQ_hybridCoupledHandler_run'_eq_lazy`.
* **Deliverable 4**: the coupled hybrid-vs-single coupling theorem
  `hybridCoupled_le_singleIdeal_add_readerSlack_aux` and the headline hybrid-to-single
  bound `hybrid_le_singleIdeal_add_readerSlack`.
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

/-! #### Hybrid-to-single, deliverable 2: the per-reader-query slack bound

A single reader query under the single-session ideal handler folds `idealCacheStep` over the
column of cells `l`. The hybrid reader inspects only the *already cached* cells; a cell that is
uncached in `c` is sampled fresh. The lemma below bounds the probability that the fresh draws
produce the target authenticator `v` at a cell whose cache slot does not already hold `v`, by
`l.length / |Digest|`. This is the per-step disagreement bound between the hybrid and single
readers. -/

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [SampleableType Nonce]
  [NeZero sessionsPerTag] in
/-- **Per-reader-query slack.** Folding `idealCacheStep` over a list `l` of distinct cells: the
probability that the produced digest list contains the target `v` while no cache slot of `l`
already holds `v` is at most `l.length / |Digest|`. Every such occurrence of `v` is a fresh
uniform draw, and a union bound over the list gives the stated cell-count-over-`|Digest|` bound. -/
lemma probEvent_idealCacheMapM_mem_le {D : Type} [DecidableEq D] [Fintype Digest]
    (l : List D) (hnd : l.Nodup) (c : (D →ₒ Digest).QueryCache) (v : Digest) :
    Pr[fun rs : List Digest × (D →ₒ Digest).QueryCache =>
        v ∈ rs.1 ∧ ∀ d ∈ l, c d ≠ some v | idealCacheMapM l c] ≤
      (l.length : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
  classical
  induction l generalizing c with
  | nil =>
    rw [idealCacheMapM, List.length_nil, Nat.cast_zero, ENNReal.zero_div]
    refine le_of_eq_of_le (probEvent_eq_zero (fun rs hrs => ?_)) (le_refl 0)
    rintro ⟨hmem, _⟩
    rw [support_pure, Set.mem_singleton_iff] at hrs
    subst hrs
    simp at hmem
  | cons d ds ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hdnd, hndtail⟩ := hnd
    rw [idealCacheMapM]
    by_cases hcd : c d = some v
    · refine le_of_eq_of_le (probEvent_eq_zero (fun rs _ => ?_)) (zero_le _)
      rintro ⟨_, hfresh⟩
      exact hfresh d (List.mem_cons_self ..) hcd
    · have hcons_len : ((d :: ds).length : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)
          = (1 : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)
            + (ds.length : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
        rw [List.length_cons, Nat.cast_add, Nat.cast_one, ENNReal.add_div, add_comm]
      rw [hcons_len]
      rw [show (fun rs : List Digest × (D →ₒ Digest).QueryCache =>
            v ∈ rs.1 ∧ ∀ d_1 ∈ d :: ds, c d_1 ≠ some v)
          = (fun rs => ¬¬(v ∈ rs.1 ∧ ∀ d_1 ∈ d :: ds, c d_1 ≠ some v)) from by
        funext rs; rw [not_not]]
      refine probEvent_bind_le_add (p := fun r => r.1 ≠ v) ?_ ?_
      · have hstep : Pr[fun r : Digest × (D →ₒ Digest).QueryCache => r.1 = v |
            idealCacheStep c d] ≤ (1 : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
          unfold idealCacheStep
          rcases hc : c d with _ | u
          · simp only [hc]
            rw [bind_pure_comp, probEvent_map]
            refine le_of_eq ?_
            rw [show ((fun r : Digest × (D →ₒ Digest).QueryCache => r.1 = v) ∘
                fun u => (u, c.cacheQuery d u)) = (fun u => u = v) from rfl]
            rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, one_div]
          · simp only [hc] at hcd
            simp only [hc, probEvent_pure]
            by_cases hu : u = v
            · exact absurd (hu ▸ rfl) hcd
            · simp [hu]
        simp only [not_not] at hstep ⊢
        exact hstep
      · intro r hr hrne
        simp only [not_not]
        rw [bind_pure_comp, probEvent_map]
        have hrcache : ∀ d' ∈ ds, r.2 d' = c d' := fun d' hd' =>
          idealCacheStep_cache_off c d r hr d' (fun h => hdnd (h ▸ hd'))
        refine le_trans (probEvent_mono (fun rs _ hrs => ?_)) (ih hndtail r.2)
        simp only [Function.comp, List.mem_cons] at hrs ⊢
        obtain ⟨hmem, hfresh⟩ := hrs
        refine ⟨?_, fun d' hd' => ?_⟩
        · rcases hmem with h | h
          · exact absurd h.symm hrne
          · exact h
        · rw [hrcache d' hd']; exact hfresh d' (Or.inr hd')

/-! #### Hybrid-to-single, deliverable 3: the coupled reader step and the coupling theorem

`hybridCoupledHandler` is the hybrid world run *in lockstep* with the single-session ideal handler:
its tag oracle is the lazy hybrid tag oracle and its reader oracle folds `idealCacheStep` over the
whole column of cells — exactly as the single reader does, so the two threads keep an identical
random-oracle cache — but its acceptance bit is the session-nonce bit `hybridCacheAccepts` read off
the *pre-extension* cache. The two handlers therefore differ only in the reader's output bit, and
the per-reader-query disagreement is bounded by `probEvent_idealCacheMapM_mem_le`. -/

/-- The column of single-session cells inspected by a reader query at `transcript.nonce`. -/
noncomputable def hybridReaderCells (transcript : TagTranscript Nonce Digest) :
    List ((TagId × Fin sessionsPerTag) × Nonce) :=
  (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
    (fun slot => (slot, transcript.nonce))

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The reader-cell column is duplicate-free: `Finset.univ.toList` is `Nodup` and pairing each slot
with the fixed nonce is injective. -/
lemma hybridReaderCells_nodup (transcript : TagTranscript Nonce Digest) :
    (hybridReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) transcript).Nodup := by
  unfold hybridReaderCells
  refine (Finset.univ : Finset (TagId × Fin sessionsPerTag)).nodup_toList.map ?_
  intro a b hab
  simpa using hab

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The reader-cell column has `|TagId| * sessionsPerTag` cells. -/
lemma hybridReaderCells_length (transcript : TagTranscript Nonce Digest) :
    (hybridReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) transcript).length
      = Fintype.card TagId * sessionsPerTag := by
  unfold hybridReaderCells
  rw [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]

omit [Nonempty TagId] [SampleableType Nonce] in
/-- **Per-reader-query coupled disagreement bound.** Fix a cache `c` in which every cached
column-`transcript.nonce` cell is recorded in the session-nonce map `sn` (the column-freshness
invariant guaranteed, at the current reader query, by `HasDistinctUnlinkReaderNonces`). Folding
`idealCacheStep` over the whole column, the probability that the single-session acceptance bit
exceeds the hybrid session-nonce bit `hybridCacheAccepts c sn transcript` is at most
`|TagId| * sessionsPerTag / |Digest|`: the only way they disagree is a fresh draw at an undrawn
cell hitting the authenticator, and `probEvent_idealCacheMapM_mem_le` bounds that. -/
lemma probEvent_coupledReader_disagree_le [Fintype Digest]
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sn : HybridSessionNonce TagId Nonce sessionsPerTag)
    (transcript : TagTranscript Nonce Digest)
    (hcol : ∀ (tag : TagId) (sid : Fin sessionsPerTag),
      (c ((tag, sid), transcript.nonce)).isSome →
        sn (tag, sid) = some transcript.nonce) :
    Pr[fun rs : List Digest × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache =>
        decide (∃ d ∈ rs.1, d = transcript.auth) = true ∧
          hybridCacheAccepts (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) c sn transcript = false |
        idealCacheMapM (hybridReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) transcript) c] ≤
      (Fintype.card TagId * sessionsPerTag : ℕ) / (Fintype.card Digest : ℝ≥0∞) := by
  classical
  rw [← hybridReaderCells_length (TagId := TagId) (Digest := Digest) transcript]
  push_cast
  refine le_trans (probEvent_mono fun rs _ hrs => ?_)
    (probEvent_idealCacheMapM_mem_le _
      (hybridReaderCells_nodup (TagId := TagId) (Digest := Digest) transcript) c transcript.auth)
  obtain ⟨haccept, hreject⟩ := hrs
  rw [decide_eq_true_eq] at haccept
  refine ⟨haccept.1, fun cell hcell hcc => ?_⟩
  obtain ⟨slot, rfl⟩ : ∃ slot, cell = (slot, transcript.nonce) := by
    unfold hybridReaderCells at hcell
    rw [List.mem_map] at hcell
    obtain ⟨slot, _, rfl⟩ := hcell
    exact ⟨slot, rfl⟩
  have hdrawn := hcol slot.1 slot.2 (by rw [hcc]; rfl)
  rw [hybridCacheAccepts, decide_eq_false_iff_not] at hreject
  exact hreject ⟨slot.1, slot.2, hdrawn, hcc⟩

/-- **Coupled hybrid handler.** The hybrid world run *in lockstep* with the single-session ideal
handler. Its tag oracle is the lazy hybrid tag oracle (`hybridLazyHandler` on `Sum.inl`); its
reader oracle folds `idealCacheStep` over the *whole* single-session column — exactly as
`singleIdealQueryImpl` does — so the random-oracle cache evolves identically in the two worlds.
The reader's output bit, however, is the session-nonce bit `hybridCacheAccepts` read off the
*pre-fold* cache, so the coupled handler returns the same answers as `hybridLazyHandler` while
maintaining a cache in lockstep with `singleIdealQueryImpl`. -/
noncomputable def hybridCoupledHandler :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (HybridState TagId Nonce sessionsPerTag ×
        (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag => hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag) p
    | Sum.inr transcript => do
        let rs ← idealCacheMapM (hybridReaderCells (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) transcript) p.2
        pure (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) p.2 p.1.sessionNonce transcript),
          p.1, rs.2)

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `simulateQ hybridCoupledHandler` of a `query_bind`, run from a state and projected to its
output: the per-query handler followed by the recursive simulation of the continuation. -/
lemma hybridCoupled_run'_query_bind' {α : Type}
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) (liftM (OracleSpec.query t) >>= f)).run' sH =
      (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) t sH) >>= fun p =>
        (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2 := by
  rw [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridCoupledHandler` on a tag query: identical to `hybridLazyHandler`. -/
lemma hybridCoupledHandler_tag_run (tag : TagId)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sH =
      (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inl tag)) sH := rfl

omit [Nonempty TagId] [NeZero sessionsPerTag] in
/-- `hybridCoupledHandler` on a reader query: fold `idealCacheStep` over the whole single-session
column, return the session-nonce bit read off the pre-fold cache, advance the cache. -/
lemma hybridCoupledHandler_reader_run (transcript : TagTranscript Nonce Digest)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :
    (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (Sum.inr transcript)) sH =
      idealCacheMapM (hybridReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) transcript) sH.2 >>= fun rs =>
        pure (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) sH.2 sH.1.sessionNonce transcript),
          sH.1, rs.2) := rfl

/-- **Coupled hybrid eager-table equivalence.** Running the coupled hybrid handler from a
session-nonce / cache consistent state `(s, c)` has the same output distribution as sampling a full
single-session random-oracle table `g`, overlaying the cache `c`, and running the deterministic
table hybrid handler `hybridTableHandler (tableExtending c g)` from `s`. The hybrid analogue of
`evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending`; the reader step folds the whole
column but the extra cells are absorbed by `evalDist_idealCacheMapM_bind_uniformTable_comp`. -/
lemma evalDist_simulateQ_hybridCoupledHandler_run'_eq_tableExtending
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hcons : HybridCacheConsistent (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) s c) :
    𝒟[(simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run' (s, c)] =
      𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)) oa).run' s] := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [hybridCoupled_run'_query_bind']
    have hrhs : 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
          (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
            (liftM (OracleSpec.query t) >>= f)).run' s]
        = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
            (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g) t s) >>= fun p =>
              (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g))
                (f p.1)).run' p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [hybridTable_run'_query_bind']
    rw [hrhs]
    cases t with
    | inl tag =>
      rw [hybridCoupledHandler_tag_run tag (s, c)]
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · rw [hybridLazyHandler_tag_run_of_lt tag (s, c) hslot]
        set sid := (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) with hsid
        set adv : Nonce → HybridState TagId Nonce sessionsPerTag :=
          fun nonce =>
            { sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1),
              sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } with hadv
        have hlhs_reassoc :
            ((($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), adv nonce, r.2))
              >>= fun p =>
              (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
            = (($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv nonce, r.2)) := by
          simp only [bind_assoc, pure_bind]
        refine (congrArg evalDist hlhs_reassoc).trans ?_
        have hlhs_inner : ∀ (n : Nonce),
            𝒟[idealCacheStep c ((tag, sid), n) >>= fun r =>
              (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))).run' (adv n, r.2)]
            = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                  (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c g))
                    (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                      TagTranscript Nonce Digest)))).run' (adv n)] := by
          intro n
          set Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun g' =>
            (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
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
                (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g)) (f p.1)).run' p.2)
            = (($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                ($ᵗ Nonce) >>= fun n =>
                (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g))
                  (f (some (⟨n, OracleComp.tableExtending c g ((tag, sid), n)⟩ :
                    TagTranscript Nonce Digest)))).run' (adv n)) := by
          simp only [bind_assoc, pure_bind]
        refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
        rw [evalDist_probComp_bind_comm ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))
          ($ᵗ Nonce)]
        refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        exact hlhs_inner n
      · rw [hybridLazyHandler_tag_run_of_not_lt tag (s, c) hslot]
        show 𝒟[(simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f none)).run' (s, c)] = _
        rw [ih none s c hcons]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hybridTableHandler_tag_run_of_not_lt _ tag s hslot]
        rfl
    | inr transcript =>
      rw [hybridCoupledHandler_reader_run transcript (s, c)]
      set cells := hybridReaderCells (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) transcript with hcells
      have hlhs_reassoc :
          ((idealCacheMapM cells c >>= fun rs =>
              pure (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce transcript),
                s, rs.2))
            >>= fun p => (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
          = (idealCacheMapM cells c >>= fun rs =>
              (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce
                  transcript)))).run' (s, rs.2)) := by
        simp only [bind_assoc, pure_bind]
      refine (congrArg evalDist hlhs_reassoc).trans ?_
      set Mψ : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → ProbComp Bool := fun g' =>
        (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
          (f (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce
            transcript)))).run' s
        with hMψ
      have hstep1 :
          𝒟[idealCacheMapM cells c >>= fun rs =>
              (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce
                  transcript)))).run' (s, rs.2)]
          = 𝒟[idealCacheMapM cells c >>= fun rs =>
              ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
                Mψ (OracleComp.tableExtending rs.2 g)] := by
        refine evalDist_bind_congr_of_support _ _ _ fun rs hrs => ?_
        have hcons' : HybridCacheConsistent (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) s rs.2 := by
          intro tag' sid' n' hsn
          exact idealCacheMapM_cache_off cells c rs hrs ((tag', sid'), n')
            (hcons tag' sid' n' hsn) ▸ hcons tag' sid' n' hsn
        rw [ih (ReaderReply.ofBool (hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce transcript))
          s rs.2 hcons']
      rw [hstep1, evalDist_idealCacheMapM_bind_uniformTable_comp cells c Mψ]
      refine (evalDist_bind_congr_of_support _ _ _ fun g _ => ?_).symm
      rw [hybridTableHandler_reader_run _ transcript s]
      rw [hMψ]
      rw [hybridCacheAccepts_eq_hybridReaderAccepts_tableExtending s c g hcons transcript]
      rfl

/-- **Coupled hybrid handler distributional equivalence.** Running the coupled hybrid handler from
the initial state has the same output distribution as running the lazy hybrid handler. Both equal
the eager-table form (`evalDist_simulateQ_hybridCoupledHandler_run'_eq_tableExtending` and
`evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending`); caching the extra column cells the
hybrid output ignores does not change the hybrid output distribution. -/
lemma evalDist_simulateQ_hybridCoupledHandler_run'_eq_lazy
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) :
    𝒟[(simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run' (HybridState.init, ∅)] =
      𝒟[(simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run' (HybridState.init, ∅)] := by
  rw [evalDist_simulateQ_hybridCoupledHandler_run'_eq_tableExtending oa HybridState.init ∅
      hybridCacheConsistent_init,
    evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending oa HybridState.init ∅
      hybridCacheConsistent_init]

/-- The coupled hybrid handler has the same success probability as the lazy hybrid handler. -/
lemma probOutput_hybridCoupled_run'_eq_lazy [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) :
    Pr[= true | (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run'
        (HybridState.init, ∅)] =
      Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run'
        (HybridState.init, ∅)] := by
  rw [probOutput_def, probOutput_def, evalDist_simulateQ_hybridCoupledHandler_run'_eq_lazy oa]

/-! #### Hybrid-to-single, deliverable 4: the coupled hybrid-vs-single coupling theorem

The coupled hybrid handler `hybridCoupledHandler` and the single-session ideal handler
`singleIdealQueryImpl` evolve their random-oracle cache and session counters in lockstep — they
differ only in the reader oracle's *output bit*. The hybrid reader accepts on a subset of the
single reader's cells, so the only disagreement is the single reader accepting on a non-tag-drawn
cell. Under `HasDistinctUnlinkReaderNonces` that cell is genuinely fresh, and
`probEvent_coupledReader_disagree_le` bounds the per-reader-query gap by
`|TagId| * sessionsPerTag / |Digest|`. -/

/-- Coupling invariant for hop B: a cached column-`n` cell that was *not* produced by the tag draw
of its own session forces the residual computation to make no further reader query at `n`. Tag
draws set the cache cell and the `sessionNonce` record together, so a non-tag-drawn cached cell can
only come from an earlier reader query; `HasDistinctUnlinkReaderNonces` then rules out a second
reader query at that nonce. -/
def HybridColFresh (oa : UnlinkAdversary TagId Nonce Digest)
    (s : HybridState TagId Nonce sessionsPerTag)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) : Prop :=
  ∀ (n : Nonce) (tag : TagId) (sid : Fin sessionsPerTag),
    (c ((tag, sid), n)).isSome → s.sessionNonce (tag, sid) ≠ some n →
      OracleComp.IsQueryBoundP oa (pReaderNonce n) 0

/-- Write-once invariant for the hybrid session-nonce map: a session that has not yet been used
(its index is at or beyond the session counter) carries no recorded nonce. -/
def HybridWriteOnce (s : HybridState TagId Nonce sessionsPerTag) : Prop :=
  ∀ (tag : TagId) (sid : Fin sessionsPerTag),
    s.sessionsUsed tag ≤ sid.val → s.sessionNonce (tag, sid) = none

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The initial hybrid state satisfies the write-once invariant: nothing is recorded. -/
lemma hybridWriteOnce_init :
    HybridWriteOnce (TagId := TagId) (Nonce := Nonce)
      (sessionsPerTag := sessionsPerTag) HybridState.init := by
  intro tag sid _
  rfl

omit [Nonempty TagId] [SampleableType Nonce] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- The empty cache satisfies the coupling invariant vacuously. -/
lemma hybridColFresh_init (oa : UnlinkAdversary TagId Nonce Digest)
    (s : HybridState TagId Nonce sessionsPerTag) :
    HybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa s ∅ := by
  intro n tag sid hsome _
  simp at hsome

/-- **Hybrid-to-single, core coupling bound.** For any hybrid state `s` and single state `sS`
with equal session counters, sharing a random-oracle cache `c`, the coupled hybrid handler's success
probability is bounded by the single-session ideal handler's plus the reader-slack term
`qR * |TagId| * sessionsPerTag / |Digest|`, provided the adversary has pairwise-distinct reader
nonces (`hdist`), at most `qR` reader queries (`hqR`), and the cache satisfies the coupling
invariants `HybridColFresh`/`HybridWriteOnce`. Proved by induction on the adversary. -/
lemma hybridCoupled_le_singleIdeal_add_readerSlack_aux [Fintype Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) (qR : ℕ)
    (s : HybridState TagId Nonce sessionsPerTag) (sS : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (hcounter : s.sessionsUsed = sS.sessionsUsed)
    (hqR : OracleComp.IsQueryBoundP oa (fun i => i.isRight) qR)
    (hdist : ∀ n : Nonce, OracleComp.IsQueryBoundP oa (pReaderNonce n) 1)
    (hwo : HybridWriteOnce (TagId := TagId) (Nonce := Nonce)
      (sessionsPerTag := sessionsPerTag) s)
    (hfresh : HybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa s c) :
    Pr[= true | (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' (s, c)] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' (sS, c)] +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  induction oa using OracleComp.inductionOn generalizing qR s sS c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact le_add_right (le_refl _)
  | query_bind t f ih =>
    rw [hybridCoupled_run'_query_bind', singleIdeal_run'_query_bind']
    cases t with
    | inl tag =>
      -- Tag query: the two handlers are pointwise identical; recurse with `ε₁ = 0`.
      have hqRf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) qR := fun u => by
        have := hqR; rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        simpa using this.2 u
      have hdistf : ∀ u, ∀ n, OracleComp.IsQueryBoundP (f u) (pReaderNonce n) 1 := fun u n => by
        have := hdist n; rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        simpa [pReaderNonce] using this.2 u
      have hfreshf : ∀ u, ∀ n, OracleComp.IsQueryBoundP
          (liftM (OracleSpec.query (Sum.inl tag : (UnlinkOracleSpec TagId Nonce Digest).Domain))
            >>= f) (pReaderNonce n) 0 →
          OracleComp.IsQueryBoundP (f u) (pReaderNonce n) 0 := fun u n hb => by
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
        simpa [pReaderNonce] using hb.2 u
      have hcounter_tag : sS.sessionsUsed tag = s.sessionsUsed tag := (congrFun hcounter tag).symm
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · rw [hybridCoupledHandler_tag_run tag (s, c),
          hybridLazyHandler_tag_run_of_lt tag (s, c) hslot,
          singleIdealQueryImpl_tag_run_of_lt tag sS c (hcounter_tag ▸ hslot)]
        dsimp only
        simp only [hcounter_tag]
        set sid := (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) with hsid
        set advH : Nonce → HybridState TagId Nonce sessionsPerTag := fun nonce =>
          { sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1),
            sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } with hadvH
        set advS : UnlinkState TagId :=
          { sS with sessionsUsed :=
            Function.update sS.sessionsUsed tag (s.sessionsUsed tag + 1) } with hadvS
        -- Reassociate both binds to a shared `mx`.
        set mx : ProbComp (Nonce × Digest ×
            (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :=
          ($ᵗ Nonce) >>= fun n => idealCacheStep c ((tag, sid), n) >>= fun r => pure (n, r)
          with hmx
        have hreassocH :
            (($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest),
                  ({ sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1),
                     sessionNonce := Function.update s.sessionNonce (tag, sid) (some nonce) } :
                    HybridState TagId Nonce sessionsPerTag), r.2))
              >>= (fun p => (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
            = mx >>= fun nr =>
                (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nr.1, nr.2.1⟩ : TagTranscript Nonce Digest)))).run'
                    (advH nr.1, nr.2.2) := by
          rw [hmx]
          simp only [bind_assoc, pure_bind, hadvH, hadvS]
        have hreassocS :
            (($ᵗ Nonce) >>= fun nonce => idealCacheStep c ((tag, sid), nonce) >>= fun r =>
                pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), advS, r.2))
              >>= (fun p => (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
            = mx >>= fun nr =>
                (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nr.1, nr.2.1⟩ : TagTranscript Nonce Digest)))).run'
                    (advS, nr.2.2) := by
          rw [hmx]
          simp only [bind_assoc, pure_bind, hadvH, hadvS]
        rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
        refine le_trans (le_of_eq (congrArg (fun m => probEvent m (· = true)) hreassocH)) ?_
        refine le_trans ?_ (le_of_eq (congrArg (fun z => z +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞))
          (congrArg (fun m => probEvent m (· = true)) hreassocS.symm)))
        refine le_trans (probEvent_bind_le_add_of_disagree (D := fun _ => False)
          (ε₁ := 0)
          (ε₂ := ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞))
          (oc := fun nr => (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag))
            (f (some (⟨nr.1, nr.2.1⟩ : TagTranscript Nonce Digest)))).run' (advS, nr.2.2))
          (by simp) ?_) (le_of_eq (by rw [add_zero]))
        · -- per-point inductive step
          rintro nr hnr -
          obtain ⟨n, hn, r, hr, hnreq⟩ : ∃ n, n ∈ support ($ᵗ Nonce) ∧
              ∃ r, r ∈ support (idealCacheStep c ((tag, sid), n)) ∧ nr = (n, r) := by
            rw [hmx, mem_support_bind_iff] at hnr
            obtain ⟨n, hn, hrest⟩ := hnr
            rw [mem_support_bind_iff] at hrest
            obtain ⟨r, hr, hpure⟩ := hrest
            rw [support_pure, Set.mem_singleton_iff] at hpure
            exact ⟨n, hn, r, hr, hpure⟩
          subst hnreq
          have hcellself : r.2 ((tag, sid), n) = some r.1 :=
            idealCacheStep_cache_self c ((tag, sid), n) r hr
          have hcounter' : (advH n).sessionsUsed = advS.sessionsUsed := by
            rw [hadvH, hadvS]
            dsimp only [HybridState.sessionsUsed]
            rw [hcounter]
          have hwo' : HybridWriteOnce (TagId := TagId) (Nonce := Nonce)
              (sessionsPerTag := sessionsPerTag) (advH n) := by
            intro tag' sid' hle
            simp only [hadvH] at hle ⊢
            by_cases htag : tag' = tag
            · subst htag
              rw [Function.update_self] at hle
              have hne : sid' ≠ sid := by
                intro h; rw [h, hsid] at hle; simp at hle
              rw [Function.update_of_ne (by simp [Prod.ext_iff, hne])]
              exact hwo tag' sid' (by omega)
            · rw [Function.update_of_ne htag] at hle
              rw [Function.update_of_ne (by simp [htag])]
              exact hwo tag' sid' hle
          have hfresh' : HybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag)
              (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest))) (advH n) r.2 := by
            intro n' tag' sid' hsome hne
            refine hfreshf _ n' ?_
            by_cases hkey : ((tag', sid'), n') = ((tag, sid), n)
            · obtain ⟨hkk, rfl⟩ := Prod.mk.injEq .. ▸ hkey
              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hkk
              exact absurd (by rw [hadvH]; exact Function.update_self ..) hne
            · have hcoff : r.2 ((tag', sid'), n') = c ((tag', sid'), n') :=
                idealCacheStep_cache_off c ((tag, sid), n) r hr _ hkey
              rw [hcoff] at hsome
              have hsnH : (advH n).sessionNonce (tag', sid') ≠ some n' := hne
              have hsn : s.sessionNonce (tag', sid') ≠ some n' := by
                simp only [hadvH] at hsnH
                by_cases hkey2 : (tag', sid') = (tag, sid)
                · rw [hkey2, hwo tag sid (by simp [hsid])]
                  simp
                · rwa [Function.update_of_ne hkey2] at hsnH
              exact hfresh n' tag' sid' hsome hsn
          have hih := ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) qR (advH n) advS r.2
            hcounter' (hqRf _) (fun n' => hdistf _ n') hwo' hfresh'
          rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput] at hih
          exact hih
      · rw [hybridCoupledHandler_tag_run tag (s, c),
          hybridLazyHandler_tag_run_of_not_lt tag (s, c) hslot,
          singleIdealQueryImpl_tag_run_of_not_lt tag sS c (hcounter_tag ▸ hslot)]
        have hfresh' : HybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (f none) s c := by
          intro n tag' sid' hsome hne
          exact hfreshf none n (hfresh n tag' sid' hsome hne)
        exact ih none qR s sS c hcounter (hqRf none) (fun n => hdistf none n) hwo hfresh'
    | inr transcript =>
      -- Reader query: handlers fold the same column; the output bits may disagree.
      set n₀ := transcript.nonce with hn₀
      rw [hybridCoupledHandler_reader_run transcript (s, c),
        singleIdealQueryImpl_reader_run transcript sS c]
      set cells := (Finset.univ : Finset (TagId × Fin sessionsPerTag)).toList.map
        (fun slot => (slot, transcript.nonce)) with hcells
      have hcellseq : cells = hybridReaderCells (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) transcript := rfl
      -- Budgets after the reader query.
      have hqRsplit := hqR
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hqRsplit
      obtain ⟨hvalid, hbudget⟩ := hqRsplit
      have hqRpos : 0 < qR := hvalid.resolve_left fun h => h rfl
      obtain ⟨qR', rfl⟩ : ∃ qR', qR = qR' + 1 := ⟨qR - 1, by omega⟩
      have hqRf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight) qR' := by
        intro u; simpa using hbudget u
      -- the residual budget at `n₀` is exhausted
      have hb0 : ∀ u, OracleComp.IsQueryBoundP (f u) (pReaderNonce n₀) 0 := fun u => by
        have := hdist n₀
        rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        have h2 := this.2 u
        simp only [pReaderNonce, hn₀] at h2
        simpa using h2
      -- off-`n₀` budget transfers to the continuation
      have hbn : ∀ u, ∀ n, n ≠ n₀ → OracleComp.IsQueryBoundP
          (liftM (OracleSpec.query (Sum.inr transcript :
            (UnlinkOracleSpec TagId Nonce Digest).Domain)) >>= f) (pReaderNonce n) 0 →
          OracleComp.IsQueryBoundP (f u) (pReaderNonce n) 0 := fun u n hne hb => by
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
        have h2 := hb.2 u
        have hpfalse : ¬ pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n
            (Sum.inr transcript) := fun h => hne (h.symm)
        simpa [hpfalse] using h2
      -- `hcol`: at the current reader nonce, no non-tag-drawn cached cell
      have hcol : ∀ (tag : TagId) (sid : Fin sessionsPerTag),
          (c ((tag, sid), n₀)).isSome → s.sessionNonce (tag, sid) = some n₀ :=
        fun tag sid hsome => by
          by_contra hne
          have hbad := hfresh n₀ tag sid hsome hne
          rw [OracleComp.isQueryBoundP_query_bind_iff] at hbad
          have hp : pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest) n₀
              (Sum.inr transcript) := rfl
          exact hbad.1.elim (fun h => h hp) (fun h => absurd h (lt_irrefl 0))
      -- reassociate both reader binds to a shared `mx`
      set mx : ProbComp (List Digest ×
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache) :=
        idealCacheMapM cells c with hmx
      set hybBit := hybridCacheAccepts (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce transcript
        with hhybBit
      have hreassocH :
          (mx >>= fun rs => pure (ReaderReply.ofBool hybBit, s, rs.2))
            >>= (fun p => (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
          = mx >>= fun rs =>
              (simulateQ (hybridCoupledHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool hybBit))).run' (s, rs.2) := by
        simp only [bind_assoc, pure_bind]
      have hreassocS :
          (mx >>= fun rs =>
              pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), sS, rs.2))
            >>= (fun p => (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run' p.2)
          = mx >>= fun rs =>
              (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run'
                (sS, rs.2) := by
        simp only [bind_assoc, pure_bind]
      rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
      refine le_trans (le_of_eq (congrArg (fun m => probEvent m (· = true)) hreassocH)) ?_
      refine le_trans ?_ (le_of_eq (congrArg (fun z => z +
        (((qR' + 1) * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞))
        (congrArg (fun m => probEvent m (· = true)) hreassocS.symm)))
      classical
      set D : List Digest × (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache → Prop :=
        fun rs => decide (∃ d ∈ rs.1, d = transcript.auth) = true ∧ hybBit = false with hD
      have hslackeq :
          (((qR' + 1) * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
              (Fintype.card Digest : ℝ≥0∞)
            = (Fintype.card TagId * sessionsPerTag : ℕ) / (Fintype.card Digest : ℝ≥0∞)
              + ((qR' * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
                (Fintype.card Digest : ℝ≥0∞) := by
        rw [← ENNReal.add_div]
        congr 1
        push_cast
        ring
      refine le_trans (probEvent_bind_le_add_of_disagree (D := D)
        (ε₁ := (Fintype.card TagId * sessionsPerTag : ℕ) / (Fintype.card Digest : ℝ≥0∞))
        (ε₂ := ((qR' * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
          (Fintype.card Digest : ℝ≥0∞))
        (oc := fun rs => (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag))
          (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run' (sS, rs.2))
        ?_ ?_) (le_of_eq (by rw [add_assoc, ← hslackeq]))
      · -- the disagreement probability is bounded by the per-query slack
        have hdis := probEvent_coupledReader_disagree_le (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) c s.sessionNonce transcript hcol
        rw [hmx, hcellseq]
        exact hdis
      · -- off the disagreement set, the bits agree; recurse with `ε₂ = 0`
        intro rs hrs hDrs
        have hrsmem : rs ∈ support (idealCacheMapM cells c) := by rw [hmx] at hrs; exact hrs
        -- `hybBit → single bit`
        have himp : hybBit = true →
            decide (∃ d ∈ rs.1, d = transcript.auth) = true := by
          intro hht
          rw [hhybBit, hybridCacheAccepts, decide_eq_true_eq] at hht
          obtain ⟨tag, sid, hsn, hcv⟩ := hht
          rw [decide_eq_true_eq]
          refine ⟨transcript.auth, ?_, rfl⟩
          have hcellmem : ((tag, sid), n₀) ∈ cells := by
            rw [hcells]
            exact List.mem_map.mpr ⟨(tag, sid), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
          have hcoff : rs.2 ((tag, sid), n₀) = c ((tag, sid), n₀) :=
            idealCacheMapM_cache_off cells c rs hrsmem ((tag, sid), n₀) (by rw [hcv]; rfl)
          have hrs1 : rs.1 = cells.map (OracleComp.tableExtending rs.2
              (fun _ => transcript.auth)) :=
            idealCacheMapM_support cells c rs hrsmem (fun _ => transcript.auth)
          rw [hrs1]
          refine List.mem_map.mpr ⟨((tag, sid), n₀), hcellmem, ?_⟩
          rw [OracleComp.tableExtending, hcoff, hcv, Option.getD_some]
        -- the bits are equal
        have hbiteq : decide (∃ d ∈ rs.1, d = transcript.auth) = hybBit := by
          have hDrs' : ¬ (decide (∃ d ∈ rs.1, d = transcript.auth) = true ∧ hybBit = false) :=
            hDrs
          rcases hb : hybBit with _ | _
          · -- hybBit false: `¬ D rs` forces single false
            rcases hd : decide (∃ d ∈ rs.1, d = transcript.auth) with _ | _
            · rfl
            · exact absurd ⟨hd, hb⟩ hDrs'
          · -- hybBit true: single true by `himp`
            exact himp hb
        beta_reduce
        rw [hbiteq]
        -- recurse on the shared continuation `f (ReaderReply.ofBool hybBit)`
        rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
        have hfresh' : HybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (f (ReaderReply.ofBool hybBit)) s rs.2 := by
          intro n tag sid hsome hne
          by_cases hnn : n = n₀
          · subst hnn; exact hb0 _
          · have hcellnotmem : ((tag, sid), n) ∉ cells := by
              rw [hcells]
              simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, not_exists]
              intro slot hslot
              exact hnn (congrArg Prod.snd hslot).symm
            have hcoff : rs.2 ((tag, sid), n) = c ((tag, sid), n) :=
              idealCacheMapM_cache_not_mem cells c rs hrsmem ((tag, sid), n) hcellnotmem
            rw [hcoff] at hsome
            exact hbn _ n hnn (hfresh n tag sid hsome hne)
        have hdistcont : ∀ n, OracleComp.IsQueryBoundP (f (ReaderReply.ofBool hybBit))
            (pReaderNonce n) 1 := by
          intro n
          by_cases hnn : n = n₀
          · subst hnn
            exact (hb0 (ReaderReply.ofBool hybBit)).mono (Nat.zero_le 1)
          · have := hdist n
            rw [OracleComp.isQueryBoundP_query_bind_iff] at this
            have h2 := this.2 (ReaderReply.ofBool hybBit)
            have hpf : ¬ pReaderNonce (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                n (Sum.inr transcript) := fun h => hnn h.symm
            simpa [hpf] using h2
        exact ih (ReaderReply.ofBool hybBit) qR' s sS rs.2 hcounter (hqRf _)
          hdistcont hwo hfresh'

/-- **Hybrid-to-single.** Under `HasDistinctUnlinkReaderNonces` and a reader-query bound
`qReader`, the hybrid world `H` (run as the lazy hybrid handler from the initial state) succeeds
with probability at most that of the single-session ideal world plus the reader-slack term
`qReader * |TagId| * sessionsPerTag / |Digest|`.

The lazy hybrid handler and the coupled hybrid handler agree in distribution
(`probOutput_hybridCoupled_run'_eq_lazy`), and the coupled handler is bounded against
`singleIdealQueryImpl` by `hybridCoupled_le_singleIdeal_add_readerSlack_aux`; the empty cache and
initial state satisfy the coupling invariants `hybridColFresh_init` / `hybridWriteOnce_init`. -/
theorem hybrid_le_singleIdeal_add_readerSlack [Fintype Nonce] [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader : ℕ)
    (hdist : HasDistinctUnlinkReaderNonces adversary)
    (hqReader : OracleComp.IsQueryBoundP adversary (fun i => i.isRight) qReader) :
    Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (HybridState.init, ∅)] ≤
      Pr[= true | (simulateQ (singleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] +
      ((qReader * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  rw [← probOutput_hybridCoupled_run'_eq_lazy adversary]
  refine hybridCoupled_le_singleIdeal_add_readerSlack_aux adversary qReader
    HybridState.init UnlinkState.init ∅ rfl hqReader
    ((hasDistinctUnlinkReaderNonces_iff adversary).mp hdist)
    (hybridWriteOnce_init) (hybridColFresh_init adversary HybridState.init)


end EagerComposed

end UnlinkReduction

end PRFTagReader
