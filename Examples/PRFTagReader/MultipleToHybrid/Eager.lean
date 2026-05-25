/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.MultipleToHybrid.EagerReader

/-!
# PRF Tag/Reader Protocol — Multiple-to-hybrid eager coupling theorem

The eager-table multiple-vs-hybrid coupling proof. The headline aux lemma
`multipleBadEager_le_hybridEager_aux` shows that running the deterministic-table instrumented
multiple handler `multipleBadTableHandler` against the eager-sampled
`(TagId × Nonce → Digest)` table is bounded by the hybrid lazy handler on the
single-session table plus the bad probability plus the reader/tag slacks.

Together with `multipleBad_le_hybrid_add_bad_add_slack_aux`, this delivers the
multiple-to-hybrid bound
`multipleIdeal_le_hybrid_add_bad`. The proof is large (around 1500 lines) — this module
therefore exceeds the project's 1500-line soft target by design; the surrounding modules
stay well under.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]


/-- **Multiple-to-hybrid, eager-coupled core.** The deterministic-table form of the multiple-to-hybrid coupling bound: with
both worlds eagerized (the multiple-side instrumented handler `multipleBadTableHandler` run against
`tableExtending sM2 gM`, the hybrid handler `hybridTableHandler` run against
`tableExtending sH2 gH`), the multiple success probability is bounded by the hybrid success
probability plus the bad-event probability plus the per-reader-query slack.

The two table samples are coupled cell-by-cell: an outer uniform draw of the hybrid table `gH`
determines, at every drawn hybrid cell `((tag,sid),n)`, the multiple value `gM(tag,n)` — the
multiple table being recovered from the hybrid table along the injective `couplingEmbed`
(see `evalDist_couplingProject_uniformSample`). The induction threads the reader budget `qR`
exactly as `hybridCoupled_le_singleIdeal_add_readerSlack_aux`.

### Open obligation (the two `query_bind` cases)

The `tag` slot-exhausted branch is closed (both handlers return `pure (none, …)` with state
untouched, so the step collapses to the continuation `f none` and the goal is exactly `ih`). The
two remaining `sorry`s are:

1. The **tag step, slot-available branch.** With `hslot : sM.1.sessionsUsed tag < sessionsPerTag`,
   both handlers unfold to `nonce ← $ᵗ Nonce` followed by a fresh per-cell read:
   `tableExtending sM.2 gM (tag, nonce)` on the multiple side, `tableExtending sH.2 gH ((tag,sid),
   nonce)` on the hybrid side, where `sid = ⟨sM.1.sessionsUsed tag, hslot⟩` is statically known.
   The cleanest split is on collision rather than on the global `couplingEmbed`: at each tag step
   the eager caches `sM.2`/`sH.2` carry only *tag-drawn* cells (the eager reader does not write
   them; only the `ih`-recording at past tag draws does), so a cell `sM.2 (tag, nonce)` being
   `some w` means a past session of `tag` already drew `nonce` — exactly the bad event. Hence:

   * **Bad branch** (`∃ sid', sH.1.sessionNonce (tag, sid') = some nonce`): `multipleBadAdvance`
     fires `bad`, the monotone lemma `multipleBadQueryImpl_step_preserves_bad` propagates it to
     the output, and the whole branch is absorbed into the `Pr[·.2.bad]` term via
     `probEvent_bind_le_add_bad_of_disagree'`.
   * **Fresh branch** (off-collision): `sM.2 (tag, nonce) = none` and
     `sH.2 ((tag,sid), nonce) = none` (by `MultipleHybridCoupling`'s `hcons`+`hwo`), so the two cell reads
     are independent uniform draws of `gM` and `gH`. Couple them via two applications of
     `evalDist_uniformSample_bind_update` (one per table) sharing a single fresh `u ← $ᵗ Digest`;
     record `(tag, nonce) ↦ u` into both caches, advance the multiple/hybrid/bad components by
     `MultipleHybridCoupling_tag_step`, and recurse with `ih` at the extended cache.

2. The **reader step.** Both readers fold over the column at `transcript.nonce`. Per-cell
   coupling from the tag-step patching maintains `tableExtending sM.2 gM (tag, n) =
   tableExtending sH.2 gH ((tag, chosen-sid), n)` for every tag-drawn `(tag, n)`. For non-recorded
   `(tag, n)`, the multiple reads a fresh `gM (tag, n)` which can spuriously match the
   authenticator with probability `1 / |Digest|`, but the hybrid skips that slot — so the
   disagreement set carries mass `|TagId| / |Digest|` per reader query, charged once via
   `probEvent_multipleReader_disagree_le` + `multipleReader_accepts_of_hybridCacheAccepts`, then
   `hdist` rules out a future reader query at the same nonce so the bookkeeping does not double-
   count; recurse with `qR' = qR - 1` and an updated `MultipleHybridColFresh`. -/
lemma multipleBadEager_le_hybridEager_aux [Fintype Nonce] [Fintype Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) (qR qT qRInit : ℕ)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (hqR : OracleComp.IsQueryBoundP oa (fun i => i.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP oa (fun i => i.isLeft) qT)
    (hdist : ∀ n : Nonce, OracleComp.IsQueryBoundP oa (pReaderNonce n) 1)
    (hfresh : MultipleHybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa sH sM.2)
    (hCacheBound : ∀ tag : TagId,
      (Finset.univ.filter (fun n : Nonce =>
        (sM.2 (tag, n)).isSome ∧
          ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)).card ≤
        qRInit - qR)
    (hqRle : qR ≤ qRInit) :
    Pr[= true | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] ≤
      Pr[= true | do
        let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sH.2 gH)) oa).run' sH.1] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
  classical
  induction oa using OracleComp.inductionOn generalizing qR qT qRInit sM sH sB with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, StateT.run'_eq, map_pure, bind_pure_comp]
    have h1 : Pr[= true | (fun _ => b) <$> ($ᵗ (TagId × Nonce → Digest))] =
        Pr[= true | (fun _ => b) <$> ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] := by
      rw [← bind_pure_comp, ← bind_pure_comp, probOutput_bind_const, probOutput_bind_const,
        probFailure_uniformSample, probFailure_uniformSample]
    exact le_add_right (le_add_right (le_add_right (le_of_eq h1)))
  | query_bind t f ih =>
    simp only [multipleBadTable_run_query_bind', hybridTable_run'_query_bind', map_bind]
    cases t with
    | inl tag =>
      -- Continuation query-bound facts: a tag query is neither charged by `isRight` nor by
      -- `pReaderNonce`, so the reader-side budgets pass straight through. The tag-step budget
      -- `qT` decrements by one (the head tag query consumes one unit).
      have hqRf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight = true) qR := by
        intro u
        have := hqR
        rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        simpa using this.2 u
      have hqTsplit := hqT
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hqTsplit
      have hqTpos : 0 < qT := by
        rcases hqTsplit.1 with h | h
        · exact absurd rfl h
        · exact h
      obtain ⟨qT', rfl⟩ : ∃ qT', qT = qT' + 1 := ⟨qT - 1, by omega⟩
      have hqTf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isLeft = true) qT' := by
        intro u; simpa using hqTsplit.2 u
      have hdistf : ∀ u, ∀ n, OracleComp.IsQueryBoundP (f u) (pReaderNonce n) 1 := by
        intro u n
        have := hdist n
        rw [OracleComp.isQueryBoundP_query_bind_iff] at this
        simpa [pReaderNonce] using this.2 u
      have hfreshf : ∀ u, MultipleHybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (f u) sH sM.2 := by
        intro u n tg hsome hns
        have hb := hfresh n tg hsome hns
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
        simpa [pReaderNonce] using hb.2 u
      by_cases hslot : sM.1.sessionsUsed tag < sessionsPerTag
      · -- **Slot-available tag step.** Unfold both table handlers to their nonce-sampling forms;
        -- the per-cell coupling at a fresh nonce is delegated to `evalDist_uniformSample_bind_update`
        -- on each side. The bad/fresh split charges collisions into `Pr[·.2.bad]` and discharges
        -- the fresh case by `MultipleHybridCoupling_tag_step` + `ih`.
        have hslotH : sH.1.sessionsUsed tag < sessionsPerTag := by
          rw [← congrFun hInv.1 tag]; exact hslot
        set sidH : Fin sessionsPerTag := ⟨sH.1.sessionsUsed tag, hslotH⟩ with hsidH
        set advM : UnlinkState TagId :=
          { sM.1 with sessionsUsed :=
              Function.update sM.1.sessionsUsed tag (sM.1.sessionsUsed tag + 1) } with hadvM
        set advH : Nonce → HybridState TagId Nonce sessionsPerTag := fun n =>
          ({ sessionsUsed :=
                Function.update sH.1.sessionsUsed tag (sH.1.sessionsUsed tag + 1),
             sessionNonce := Function.update sH.1.sessionNonce (tag, sidH) (some n) } :
            HybridState TagId Nonce sessionsPerTag) with hadvH
        -- Multiple-handler unfold at a free slot: sample a nonce, look up the table, advance
        -- multi/bad. The `← hadvM` rewrite is what lets `simp only [bind_assoc, pure_bind]`
        -- match (see the parallel proof at line 5189).
        have hMstep : ∀ g : TagId × Nonce → Digest,
            multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) (sM.1, sB)
            = ($ᵗ Nonce) >>= fun n =>
                pure (some (⟨n, g (tag, n)⟩ : TagTranscript Nonce Digest),
                  advM, multipleBadAdvance tag sB
                    (some (⟨n, g (tag, n)⟩ : TagTranscript Nonce Digest))) := by
          intro g
          change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) sM.1
              >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1)) = _
          rw [multipleTableHandler_tag_run_of_lt g tag sM.1 hslot, ← hadvM]
          exact bind_assoc ..
        -- Hybrid-handler unfold at a free slot.
        have hHstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) gS (Sum.inl tag) sH.1
            = ($ᵗ Nonce) >>= fun n =>
                pure (some (⟨n, gS ((tag, sidH), n)⟩ : TagTranscript Nonce Digest), advH n) := by
          intro gS
          rw [hybridTableHandler_tag_run_of_lt gS tag sH.1 hslotH, ← hsidH]
        -- **Step 1.** Lift `hMstep`/`hHstep` into the goal by `bind_congr`, flattening the inner
        -- `($ᵗ Nonce) >>= pure (…)` against the outer continuation via `bind_assoc` + `pure_bind`.
        -- This is a syntactic equality (no `evalDist` needed) because `hMstep`/`hHstep` are equalities
        -- of `ProbComp` values and `bind_congr` rewrites under the outer table draws.
        have hLHS_eq :
            (do let gM ← $ᵗ (TagId × Nonce → Digest)
                let a ← multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sM.2 gM)
                  (Sum.inl tag) (sM.1, sB)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sM.2 gM)) (f a.1)).run a.2)
            = (do let gM ← $ᵗ (TagId × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending sM.2 gM))
                      (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))).run
                      (advM, multipleBadAdvance tag sB
                        (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))) := by
          refine bind_congr fun gM => ?_
          rw [hMstep (OracleComp.tableExtending sM.2 gM)]
          exact bind_assoc ..
        have hRHS_eq :
            (do let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                let p ← hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sH.2 gH)
                  (Sum.inl tag) sH.1
                (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending sH.2 gH)) (f p.1)).run' p.2)
            = (do let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                    (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sH.2 gH))
                    (f (some (⟨n, OracleComp.tableExtending sH.2 gH ((tag, sidH), n)⟩ :
                        TagTranscript Nonce Digest)))).run' (advH n)) := by
          refine bind_congr fun gH => ?_
          rw [hHstep (OracleComp.tableExtending sH.2 gH)]
          exact bind_assoc ..
        have hBAD_eq :
            (do let gM ← $ᵗ (TagId × Nonce → Digest)
                let a ← multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sM.2 gM)
                  (Sum.inl tag) (sM.1, sB)
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sM.2 gM)) (f a.1)).run a.2)
            = (do let gM ← $ᵗ (TagId × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending sM.2 gM))
                      (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))).run
                      (advM, multipleBadAdvance tag sB
                        (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))) := by
          refine bind_congr fun gM => ?_
          rw [hMstep (OracleComp.tableExtending sM.2 gM)]
          exact bind_assoc ..
        rw [hLHS_eq, hRHS_eq, hBAD_eq]
        -- **Step 2.** Commute the outer table draw past the inner `n ← $ᵗ Nonce` at the `𝒟[·]`
        -- level (NOT syntactic) via `evalDist_probComp_bind_comm`, so the shared nonce draw is the
        -- outermost sample on every side. This is the canonical setup for
        -- `probEvent_bind_le_add_bad_of_disagree'` with `mx := $ᵗ Nonce`.
        have hLHS_comm :
            𝒟[(do let gM ← $ᵗ (TagId × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending sM.2 gM))
                      (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))).run
                      (advM, multipleBadAdvance tag sB
                        (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest))))]
            = 𝒟[(do let n ← $ᵗ Nonce
                    let gM ← $ᵗ (TagId × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending sM.2 gM))
                        (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                            TagTranscript Nonce Digest))))] :=
          evalDist_probComp_bind_comm ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce) _
        have hRHS_comm :
            𝒟[(do let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sH.2 gH))
                    (f (some (⟨n, OracleComp.tableExtending sH.2 gH ((tag, sidH), n)⟩ :
                        TagTranscript Nonce Digest)))).run' (advH n))]
            = 𝒟[(do let n ← $ᵗ Nonce
                    let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending sH.2 gH))
                      (f (some (⟨n, OracleComp.tableExtending sH.2 gH ((tag, sidH), n)⟩ :
                          TagTranscript Nonce Digest)))).run' (advH n))] :=
          evalDist_probComp_bind_comm
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) ($ᵗ Nonce) _
        have hBAD_comm :
            𝒟[(do let gM ← $ᵗ (TagId × Nonce → Digest)
                  let n ← $ᵗ Nonce
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending sM.2 gM))
                      (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest)))).run
                      (advM, multipleBadAdvance tag sB
                        (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                          TagTranscript Nonce Digest))))]
            = 𝒟[(do let n ← $ᵗ Nonce
                    let gM ← $ᵗ (TagId × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending sM.2 gM))
                        (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                            TagTranscript Nonce Digest))))] :=
          evalDist_probComp_bind_comm ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce) _
        rw [show Pr[= true | _] = _ from probOutput_congr rfl hLHS_comm,
            show Pr[= true | _] = _ from probOutput_congr rfl hRHS_comm,
            show probEvent _ _ = _ from probEvent_congr' (fun _ _ => Iff.rfl) hBAD_comm]
        -- **Step 3.** Apply `probEvent_bind_le_add_bad_disagree` (4-way) with the shared
        -- `$ᵗ Nonce` draw, splitting on the *Sub-B-off-collision* set
        -- `D n := (sM.2 (tag, n)).isSome ∧ ¬ ∃ sid, sH.1.sessionNonce (tag, sid) = some n`.
        --
        -- The 4-way bound concludes `Pr[q | mx >>= my] ≤ Pr[q | mx >>= oc] + Pr[r | mx >>= ob]
        -- + ε₁ + ε₂`. Set ε₁ := qRInit/|Nonce| (Sub-B mass) and ε₂ := IH slack. The bound's
        -- conclusion `... + qRInit/|Nonce| + IH_slack` is then ≤ the head goal's
        -- `... + slack_digest + qRInit*(qT'+1)/|Nonce|` by re-associating and using
        -- `qRInit*qT'/|Nonce| + qRInit/|Nonce| = qRInit*(qT'+1)/|Nonce|`.
        --
        -- Off `D` we split:
        --   * `∃ sid, sessionNonce (tag, sid) = some n`: collision, `multipleBadAdvance` flips
        --     `bad`, so `Pr[r | ob n] = 1` and the off-`D` inequality follows from
        --     `Pr[q | my n] ≤ 1 = Pr[r | ob n] ≤ Pr[q | oc n] + Pr[r | ob n] + ε₂`.
        --   * `¬ collision`: by `¬ D n`, the multi cache must be `none` at `(tag, n)` (Sub-A);
        --     the existing cell-patch coupling closes via `MultipleHybridCoupling_tag_step` + `hIh`.
        simp only [← probEvent_eq_eq_probOutput]
        classical
        -- Reshape the goal RHS to match the 4-way bound's `... + ε₁ + ε₂` shape, with
        -- ε₁ = qRInit/|Nonce| (Sub-B mass) and ε₂ = qR*|TagId|/|Digest| + qRInit*qT'/|Nonce|
        -- (IH slack). The split `qRInit*(qT'+1)/|Nonce| = qRInit/|Nonce| + qRInit*qT'/|Nonce|`
        -- separates the mass from the slack, and reassociation puts mass in the ε₁ slot.
        have hSplit : ((qRInit * (qT' + 1) : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞)
            = ((qRInit : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
              ((qRInit * qT' : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
          rw [show qRInit * (qT' + 1) = qRInit + qRInit * qT' from by ring,
            Nat.cast_add, ENNReal.add_div]
        rw [hSplit]
        -- Goal: `success + bad + slack_digest + (qRInit/|Nonce| + qRInit*qT'/|Nonce|)`. Reassociate
        -- to `success + bad + qRInit/|Nonce| + (slack_digest + qRInit*qT'/|Nonce|)`.
        rw [show ∀ a b c d e : ℝ≥0∞, a + b + c + (d + e) = a + b + d + (c + e) from
              fun a b c d e => by ring]
        refine probEvent_bind_le_add_bad_disagree
          (D := fun n : Nonce => (sM.2 (tag, n)).isSome ∧
            ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)
          ?_ ?_
        · -- **Sub-B mass charge.** `Pr[D | $ᵗ Nonce] = card(filter D) / |Nonce| ≤ qRInit/|Nonce|`.
          rw [probEvent_uniformSample]
          refine ENNReal.div_le_div_right ?_ _
          refine (Nat.cast_le.mpr (hCacheBound tag)).trans ?_
          exact_mod_cast Nat.sub_le qRInit qR
        intro n _ hnD
        -- **Off-D branch.** Either `sM.2 (tag, n) = none` (Sub-A) or
        -- `∃ sid, sessionNonce (tag, sid) = some n` (collision).
        by_cases hcoll : ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n
        · -- **Collision sub-case.** A past session of `tag` already drew `n`, so by
          -- `hInv.hbadcol` the bad-world `responses` cell `(tag, n)` is already filled. Hence
          -- `multipleBadAdvance` flips `bad := false || true = true`, then
          -- `multipleBadTableHandler_run_preserves_bad` propagates `bad = true` through the
          -- continuation, giving `Pr[r | ob n] = 1`. The off-`D` inequality then follows by
          -- bounding `Pr[q | my n] ≤ 1 = Pr[r | ob n] ≤ Pr[q | oc n] + Pr[r | ob n] + ε₂`.
            have hcell : (sB.responses (tag, n)).isSome = true := by
              rw [hInv.2.2.2.1]; exact hcoll
            have hadvBad : ∀ d : Digest,
                (multipleBadAdvance tag sB
                    (some (⟨n, d⟩ : TagTranscript Nonce Digest))).bad = true := by
              intro d; simp [multipleBadAdvance, hInv.2.2.1, hcell]
            -- The bad world fires `r := (·.2.bad = true)` with probability 1 on this `n`.
            have hPbadOne :
                Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) | do
                    let gM ← $ᵗ (TagId × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending sM.2 gM))
                        (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                            TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                            TagTranscript Nonce Digest)))] = 1 := by
              rw [probEvent_eq_one_iff]
              refine ⟨probFailure_eq_zero, ?_⟩
              intro z hz
              rw [mem_support_bind_iff] at hz
              obtain ⟨gM, _, hzM⟩ := hz
              rw [support_map, Set.mem_image] at hzM
              obtain ⟨w, hw, hzeq⟩ := hzM
              subst hzeq
              exact multipleBadTableHandler_run_preserves_bad
                (OracleComp.tableExtending sM.2 gM)
                (f (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                    TagTranscript Nonce Digest)))
                (advM, multipleBadAdvance tag sB
                  (some (⟨n, OracleComp.tableExtending sM.2 gM (tag, n)⟩ :
                    TagTranscript Nonce Digest)))
                (hadvBad _) w hw
            calc Pr[(· = true) | _]
                ≤ 1 := probEvent_le_one
              _ = Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true) | _] :=
                  hPbadOne.symm
              _ ≤ Pr[(· = true) | _] +
                    Pr[(fun z : Bool × UnlinkBadState TagId Nonce Digest =>
                        z.2.bad = true) | _] + _ :=
                  le_add_right (le_add_left le_rfl)
        · -- **Off-collision sub-case.** No session of `tag` drew `n`. Combined with `hnD`, the
          -- multi cache must be `none` at `(tag, n)` (since `D = isSome ∧ ¬ collision`, and we
          -- are off `D` and off collision, so we are off `isSome`). Couple `gM(tag, n)` and
          -- `gH((tag, sidH), n)` to a shared fresh `u ← $ᵗ Digest` via two
          -- `evalDist_uniformSample_bind_update` applications, then advance the coupling by
          -- `MultipleHybridCoupling_tag_step` and recurse with `ih`.
          have hncoll : ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n :=
            hcoll
          have hMustNone : sM.2 (tag, n) = none := by
            rw [← Option.not_isSome_iff_eq_none]
            intro hsome
            exact hnD ⟨hsome, hncoll⟩
          -- **Structural facts derivable from `hInv` at the off-collision nonce `n`:**
          -- the bad-world `responses` cell is unfilled, and the new hybrid cell `((tag, sidH), n)`
          -- is fresh (since `sidH` is the next-to-allocate slot and `hwo` / `hhyb1` rule out
          -- recorded sessions there).
          have hBfresh : sB.responses (tag, n) = none := by
            rw [← Option.not_isSome_iff_eq_none, hInv.2.2.2.1]
            exact hncoll
          have hSnNone : sH.1.sessionNonce (tag, sidH) = none := by
            -- `sidH.val = sH.1.sessionsUsed tag`, so by `hInv.hwo` (clause 7) the session-nonce is
            -- `none`.
            exact hInv.2.2.2.2.2.2.1 tag sidH (le_refl _)
          have hHcellNone : sH.2 ((tag, sidH), n) = none := by
            -- Contrapositive of `hhyb1` (clause 8): if the hybrid cache cell were some, the
            -- session-nonce would be `some n`, contradicting `hSnNone`.
            rw [← Option.not_isSome_iff_eq_none]
            intro hsome
            have hsn := hInv.2.2.2.2.2.2.2.1 tag sidH n hsome
            rw [hSnNone] at hsn
            cases hsn
          by_cases hMcellNone : sM.2 (tag, n) = none
          · -- **Sub-case A (principal): the multi cache is unfilled at `(tag, n)`.** Couple the
            -- two outer table draws `gM, gH` via two `evalDist_uniformSample_bind_update_map`
            -- applications sharing one fresh `u ← $ᵗ Digest`: after patching,
            -- `tableExtending sM.2 (gM_patched) (tag, n) = u` (by `tableExtending_update_of_none`
            -- and `hMcellNone`) and `tableExtending sH.2 (gH_patched) ((tag, sidH), n) = u`
            -- (by `hHcellNone`). The advanced multi state `mbAdv tag sB (some ⟨n, u⟩)` has
            -- `bad = false` (by `hBfresh`), so `MultipleHybridCoupling_tag_step` holds at every `u` and
            -- `ih (some ⟨n, u⟩) qR (advM, sM.2.cacheQuery (tag, n) u)
            --     (advH n_with_session, sH.2.cacheQuery ((tag, sidH), n) u)
            --     (mbAdv tag sB (some ⟨n, u⟩))` provides the inductive bound at the patched
            -- states.
            --
            -- **Per-`u` post-state bad flag.** With `sB.responses (tag, n) = none`,
            -- `multipleBadAdvance` does not flip `bad`, so the post-bad-state is `false`-flagged at
            -- every `u`.
            have hPostBad : ∀ u : Digest,
                (multipleBadAdvance tag sB
                  (some (⟨n, u⟩ : TagTranscript Nonce Digest))).bad = false := by
              intro u
              simp [multipleBadAdvance, hInv.2.2.1, hBfresh]
            -- **Per-`u` post-state coupling.** With both multi and hybrid caches unfilled at the
            -- target cell, `MultipleHybridCoupling_tag_step` packages the advance of all three states.
            -- We reshape `advH n` and `multipleBadAdvance tag sB (some ⟨n, u⟩)` into the
            -- canonical post-state form expected by the lemma.
            have hcMH' : sM.1.sessionsUsed tag = sH.1.sessionsUsed tag := congrFun hInv.1 tag
            have hsidEq : (⟨sM.1.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) = sidH := by
              apply Fin.eq_of_val_eq; exact hcMH'
            have hInvNew : ∀ u : Digest,
                MultipleHybridCoupling (sessionsPerTag := sessionsPerTag)
                  ({ sM.1 with sessionsUsed :=
                        Function.update sM.1.sessionsUsed tag (sM.1.sessionsUsed tag + 1) },
                    sM.2.cacheQuery (tag, n) u)
                  (advH n, sH.2.cacheQuery ((tag, sidH), n) u)
                  (multipleBadAdvance tag sB
                    (some (⟨n, u⟩ : TagTranscript Nonce Digest))) := by
              intro u
              have hstep := MultipleHybridCoupling_tag_step (sessionsPerTag := sessionsPerTag)
                tag n u sM sH sB hInv hslot hMcellNone
              -- `MultipleHybridCoupling_tag_step` produces post-hybrid state with `⟨sM.1.sessionsUsed tag, hslot⟩`
              -- as the new session index; rewrite to the user-defined `sidH`.
              rw [hsidEq] at hstep
              -- Reshape `multipleBadAdvance tag sB (some ⟨n, u⟩)` to the explicit record form.
              have hBadEq :
                  multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest))
                  = ({ sessionsUsed :=
                          Function.update sB.sessionsUsed tag (sB.sessionsUsed tag + 1),
                       responses := sB.responses.cacheQuery (tag, n)
                         (u :: Option.getD (sB.responses (tag, n)) []),
                       bad := sB.bad || (sB.responses (tag, n)).isSome } :
                      UnlinkBadState TagId Nonce Digest) := by
                simp [multipleBadAdvance]
              rw [hBadEq]
              -- Reshape `advH n` to the explicit `HybridState` record form used by the lemma.
              have hadvHEq : advH n
                  = ({ sessionsUsed :=
                          Function.update sH.1.sessionsUsed tag (sH.1.sessionsUsed tag + 1),
                       sessionNonce := Function.update sH.1.sessionNonce (tag, sidH) (some n) } :
                      HybridState TagId Nonce sessionsPerTag) := by
                rw [hadvH]
              rw [hadvHEq]
              exact hstep
            -- **Per-`u` `MultipleHybridColFresh` stability.** The advanced multi cache adds the cell
            -- `(tag, n)`; the advanced hybrid session-nonce map adds `(tag, sidH) ↦ some n`.
            -- A cached cell `(tag', n')` with no recorded session in the advanced map either
            -- coincides with the new entry (contradicting the no-session hypothesis at `n'`) or
            -- lifts the pre-advance freshness witness `hfreshf (some ⟨n, u⟩)` at `(tag', n')`.
            have hFreshNew : ∀ u : Digest,
                MultipleHybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                  (sessionsPerTag := sessionsPerTag) (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                  (advH n, sH.2.cacheQuery ((tag, sidH), n) u)
                  (sM.2.cacheQuery (tag, n) u) := by
              intro u n' tag' hcell hns
              -- Split on whether `(tag', n')` is the freshly cached cell.
              by_cases hkey : (tag', n') = (tag, n)
              · -- The advanced session-nonce map sends `(tag, sidH)` to `some n` = `some n'`,
                -- contradicting the universal `≠ some n'` hypothesis at `sidH`.
                obtain ⟨htag, hnn⟩ := Prod.mk.inj hkey
                refine absurd ?_ (hns sidH)
                show (advH n).sessionNonce (tag', sidH) = some n'
                rw [hadvH, htag, hnn]
                exact Function.update_self _ _ _
              · -- The freshly cached cell is elsewhere; reduce to the pre-advance witness.
                have hcell' : (sM.2 (tag', n')).isSome := by
                  rwa [QueryCache.cacheQuery_of_ne _ _ hkey] at hcell
                have hns' : ∀ sid, sH.1.sessionNonce (tag', sid) ≠ some n' := by
                  intro sid hsn
                  -- The pre-advance session-nonce at `(tag', sid)` equals the post-advance
                  -- value unless `(tag', sid) = (tag, sidH)`; rule out the latter and conclude.
                  by_cases hts : (tag', sid) = (tag, sidH)
                  · obtain ⟨htg, hsd⟩ := Prod.mk.inj hts
                    rw [htg, hsd, hInv.2.2.2.2.2.2.1 tag sidH (le_refl _)] at hsn
                    cases hsn
                  · refine hns sid ?_
                    show (advH n).sessionNonce (tag', sid) = some n'
                    rw [hadvH]
                    show Function.update sH.1.sessionNonce (tag, sidH) (some n) (tag', sid) = some n'
                    rw [Function.update_of_ne hts]
                    exact hsn
                exact hfreshf (some (⟨n, u⟩ : TagTranscript Nonce Digest)) n' tag' hcell' hns'
            -- **Per-`u` inductive hypothesis.** All preconditions of `ih` are now in scope at
            -- the cacheQuery-extended states. The remaining work is to relate the goal's outer
            -- `gM`/`gH` draws (where the patched cell is read from `tableExtending sM.2 gM` /
            -- `tableExtending sH.2 gH`) to this `ih` shape (where the cell read from
            -- `tableExtending (sM.2.cacheQuery (tag, n) u) gM` / `tableExtending (...) gH` is
            -- deterministically `u`), via `evalDist_uniformSample_bind_update_map` and
            -- `tableExtending_update_of_none` at each side.
            -- **Per-`u` Sub-B cache bound stability.** The advanced multi cache adds `(tag, n) ↦ u`
            -- and the advanced hybrid session-nonce map adds `(tag, sidH) ↦ some n`. The new
            -- entry is *not* Sub-B-off-collision (it has a recorded session at `sidH`), so it does
            -- not enter the filter; every other cell is unchanged. Hence the post-step filter is a
            -- subset of the pre-step filter for `tag`, and exactly equal for every other tag.
            have hCacheBoundNew : ∀ u : Digest, ∀ tag' : TagId,
                (Finset.univ.filter (fun n' : Nonce =>
                  ((sM.2.cacheQuery (tag, n) u) (tag', n')).isSome ∧
                    ¬ ∃ sid : Fin sessionsPerTag,
                      (advH n).sessionNonce (tag', sid) = some n')).card ≤ qRInit - qR := by
              intro u tag'
              refine (Finset.card_le_card ?_).trans (hCacheBound tag')
              intro n' hn'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn' ⊢
              obtain ⟨hsome, hnos⟩ := hn'
              by_cases hkey : (tag', n') = (tag, n)
              · -- The freshly added cell at `(tag, n)` has session `sidH` in `advH n`, contradicting
                -- the no-session hypothesis.
                obtain ⟨htg, hnn⟩ := Prod.mk.inj hkey
                exfalso
                refine hnos ⟨sidH, ?_⟩
                rw [hadvH, htg, hnn]
                show Function.update sH.1.sessionNonce (tag, sidH) (some n) (tag, sidH) = some n
                exact Function.update_self _ _ _
              · -- Off the freshly added cell, the multi cache is unchanged at `(tag', n')` and the
                -- hybrid session-nonce check reduces to the pre-step universal nonexistence.
                refine ⟨?_, ?_⟩
                · rwa [QueryCache.cacheQuery_of_ne _ _ hkey] at hsome
                · rintro ⟨sid, hsn⟩
                  -- Pre-step session-nonce equals post-step except at `(tag, sidH)`.
                  refine hnos ⟨sid, ?_⟩
                  rw [hadvH]
                  show Function.update sH.1.sessionNonce (tag, sidH) (some n) (tag', sid) =
                    some n'
                  by_cases hts : (tag', sid) = (tag, sidH)
                  · -- `(tag', sid) = (tag, sidH)` is impossible: `hsn` gives
                    -- `sH.1.sessionNonce (tag', sid) = some n'`, but `hSnNone` says
                    -- `sH.1.sessionNonce (tag, sidH) = none`.
                    exfalso
                    obtain ⟨htg, hsd⟩ := Prod.mk.inj hts
                    rw [htg, hsd] at hsn
                    rw [hSnNone] at hsn
                    cases hsn
                  · rw [Function.update_of_ne hts]
                    exact hsn
            have hIh : ∀ u : Digest,
                Pr[= true | do
                    let gM ← $ᵗ (TagId × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (sM.2.cacheQuery (tag, n) u) gM))
                        (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] ≤
                  Pr[= true | do
                    let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
                    (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending (sH.2.cacheQuery ((tag, sidH), n) u) gH))
                      (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' (advH n)] +
                  Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true | do
                    let gM ← $ᵗ (TagId × Nonce → Digest)
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (sM.2.cacheQuery (tag, n) u) gM))
                        (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] +
                  ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) /
                    (Fintype.card Digest : ℝ≥0∞) +
                  ((qRInit * qT' : ℕ) : ℝ≥0∞) /
                    (Fintype.card Nonce : ℝ≥0∞) := fun u =>
              ih (some (⟨n, u⟩ : TagTranscript Nonce Digest)) qR qT' qRInit
                (advM, sM.2.cacheQuery (tag, n) u)
                (advH n, sH.2.cacheQuery ((tag, sidH), n) u)
                (multipleBadAdvance tag sB (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
                (hInvNew u) (hqRf _) (hqTf _) (hdistf _) (hFreshNew u)
                (hCacheBoundNew u) hqRle
            -- **Cell-read simplification at the off-collision multi cell.** With `hMcellNone`,
            -- `tableExtending sM.2 gM (tag, n) = gM (tag, n)`: the multi-side cell read collapses
            -- to a direct lookup in the freshly drawn table `gM`.
            have hMcellRead : ∀ gM : TagId × Nonce → Digest,
                OracleComp.tableExtending sM.2 gM (tag, n) = gM (tag, n) := by
              intro gM
              simp [OracleComp.tableExtending, hMcellNone]
            -- **Cell-patch identity.** After patching `gM` at `(tag, n)` with `u`, the
            -- `tableExtending`-overlay equals the cache-extended overlay against the original `gM`.
            have hMpatchTable : ∀ (gM : TagId × Nonce → Digest) (u : Digest),
                OracleComp.tableExtending sM.2 (Function.update gM (tag, n) u)
                  = OracleComp.tableExtending (sM.2.cacheQuery (tag, n) u) gM := by
              intro gM u
              rw [← OracleComp.tableExtending_update_of_none sM.2 gM hMcellNone u,
                ← OracleComp.tableExtending_cacheQuery sM.2 gM (tag, n) u]
            -- **LHS distributional lift.** Define the multi-side continuation `contM gM u`
            -- abstracting the inner `simulateQ`-run-projection, parametric over both the drawn
            -- table `gM` and the cell value `u`. Then the goal LHS is `gM ← $ᵗ; contM gM (gM (tag, n))`
            -- (using `hMcellRead`), which the cell-extract helper lifts to
            -- `u ← $ᵗ Digest; gM ← $ᵗ; contM (Function.update gM (tag, n) u) u`, and the
            -- `hMpatchTable` rewrite absorbs the patched `gM` into a `cacheQuery` against the
            -- original `gM`, matching the `hIh u` LHS shape.
            set contM : (TagId × Nonce → Digest) → Digest →
                ProbComp (Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest)) :=
              fun gM u =>
                (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending sM.2 gM))
                  (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                  (advM, multipleBadAdvance tag sB
                    (some (⟨n, u⟩ : TagTranscript Nonce Digest)))
              with hcontM
            have hLHS_lift :
                𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$> contM gM (OracleComp.tableExtending sM.2 gM (tag, n))]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$> contM (Function.update gM (tag, n) u) u] := by
              -- Step 1: collapse `tableExtending sM.2 gM (tag, n)` to `gM (tag, n)`.
              have hStep1 :
                  𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$> contM gM (OracleComp.tableExtending sM.2 gM (tag, n))]
                  = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          z.1) <$> contM gM (gM (tag, n))] := by
                refine evalDist_bind_congr_of_support _ _ _ fun gM _ => ?_
                rw [hMcellRead gM]
              rw [hStep1]
              -- Step 2: apply the cell-extract helper.
              haveI : Nonempty Digest :=
                ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
              exact evalDist_uniformSample_bind_cell_extract (R := Digest)
                (D := TagId × Nonce) (tag, n)
                (fun gM u =>
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      z.1) <$> contM gM u)
            -- The patched-`gM` form on the RHS of `hLHS_lift` is distributionally equal to the
            -- `cacheQuery`-extended form via `hMpatchTable`.
            have hLHS_align :
                𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$> contM (Function.update gM (tag, n) u) u]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        z.1) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (sM.2.cacheQuery (tag, n) u) gM))
                        (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] := by
              refine evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
              refine evalDist_bind_congr_of_support _ _ _ fun gM _ => ?_
              show 𝒟[(fun z => z.1) <$> contM (Function.update gM (tag, n) u) u] = _
              rw [hcontM]
              show 𝒟[(fun z => z.1) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sM.2 (Function.update gM (tag, n) u)))
                    (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                    (advM, multipleBadAdvance tag sB
                      (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] = _
              rw [hMpatchTable gM u]
            -- **Hybrid-side cell-patch transformation.** Same shape as the multi side, with the
            -- hybrid cell `((tag, sidH), n)`, the hybrid handler `hybridTableHandler`, and the
            -- hybrid post-state `advH n`. The cell-is-none hypothesis is `hHcellNone`.
            have hHcellRead : ∀ gH : (TagId × Fin sessionsPerTag) × Nonce → Digest,
                OracleComp.tableExtending sH.2 gH ((tag, sidH), n) = gH ((tag, sidH), n) := by
              intro gH
              simp [OracleComp.tableExtending, hHcellNone]
            have hHpatchTable :
                ∀ (gH : (TagId × Fin sessionsPerTag) × Nonce → Digest) (u : Digest),
                  OracleComp.tableExtending sH.2 (Function.update gH ((tag, sidH), n) u)
                    = OracleComp.tableExtending (sH.2.cacheQuery ((tag, sidH), n) u) gH := by
              intro gH u
              rw [← OracleComp.tableExtending_update_of_none sH.2 gH hHcellNone u,
                ← OracleComp.tableExtending_cacheQuery sH.2 gH ((tag, sidH), n) u]
            set contH : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → Digest →
                ProbComp Bool :=
              fun gH u =>
                (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending sH.2 gH))
                  (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' (advH n)
              with hcontH
            have hRHS_lift :
                𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                    contH gH (OracleComp.tableExtending sH.2 gH ((tag, sidH), n))]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                    contH (Function.update gH ((tag, sidH), n) u) u] := by
              have hStep1 :
                  𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                      contH gH (OracleComp.tableExtending sH.2 gH ((tag, sidH), n))]
                  = 𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                      contH gH (gH ((tag, sidH), n))] := by
                refine evalDist_bind_congr_of_support _ _ _ fun gH _ => ?_
                rw [hHcellRead gH]
              rw [hStep1]
              haveI : Nonempty Digest :=
                ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
              exact evalDist_uniformSample_bind_cell_extract (R := Digest)
                (D := (TagId × Fin sessionsPerTag) × Nonce) ((tag, sidH), n)
                (fun gH u => contH gH u)
            have hRHS_align :
                𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                    contH (Function.update gH ((tag, sidH), n) u) u]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
                      (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (sH.2.cacheQuery ((tag, sidH), n) u) gH))
                        (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' (advH n)] := by
              refine evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
              refine evalDist_bind_congr_of_support _ _ _ fun gH _ => ?_
              show 𝒟[contH (Function.update gH ((tag, sidH), n) u) u] = _
              rw [hcontH]
              show 𝒟[(simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending sH.2 (Function.update gH ((tag, sidH), n) u)))
                  (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run' (advH n)] = _
              rw [hHpatchTable gH u]
            -- **Multi-side BAD cell-patch transformation.** Same `contM`/`hMcellRead`/`hMpatchTable`
            -- machinery as the LHS lift, just with the `(z.1, z.2.2)` projection.
            have hBAD_lift :
                𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      contM gM (OracleComp.tableExtending sM.2 gM (tag, n))]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$> contM (Function.update gM (tag, n) u) u] := by
              have hStep1 :
                  𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$>
                        contM gM (OracleComp.tableExtending sM.2 gM (tag, n))]
                  = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                      (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                          (z.1, z.2.2)) <$> contM gM (gM (tag, n))] := by
                refine evalDist_bind_congr_of_support _ _ _ fun gM _ => ?_
                rw [hMcellRead gM]
              rw [hStep1]
              haveI : Nonempty Digest :=
                ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
              exact evalDist_uniformSample_bind_cell_extract (R := Digest)
                (D := TagId × Nonce) (tag, n)
                (fun gM u =>
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$> contM gM u)
            have hBAD_align :
                𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$> contM (Function.update gM (tag, n) u) u]
                = 𝒟[($ᵗ Digest) >>= fun u =>
                    ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
                    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                        (z.1, z.2.2)) <$>
                      (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                        (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                        (OracleComp.tableExtending (sM.2.cacheQuery (tag, n) u) gM))
                        (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                        (advM, multipleBadAdvance tag sB
                          (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] := by
              refine evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
              refine evalDist_bind_congr_of_support _ _ _ fun gM _ => ?_
              show 𝒟[(fun z => (z.1, z.2.2)) <$>
                  contM (Function.update gM (tag, n) u) u] = _
              rw [hcontM]
              show 𝒟[(fun z => (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending sM.2 (Function.update gM (tag, n) u)))
                    (f (some (⟨n, u⟩ : TagTranscript Nonce Digest)))).run
                    (advM, multipleBadAdvance tag sB
                      (some (⟨n, u⟩ : TagTranscript Nonce Digest)))] = _
              rw [hMpatchTable gM u]
            -- **Final integration step.** Rewrite the goal using the three cell-patch lifts to
            -- expose a shared outer `u ← $ᵗ Digest`; apply the disagreement-free pointwise bind
            -- bound (`D := fun _ => False`) with `hIh u` as the pointwise per-`u` inequality.
            -- Unfold `contM`/`contH` in the lift hypotheses to match the goal's syntactic form
            -- (the `set`-introduced abbreviations are propositional, not definitional, so the
            -- goal does not see them after subsequent tactics).
            simp only [hcontM, hcontH]
              at hLHS_lift hLHS_align hRHS_lift hRHS_align hBAD_lift hBAD_align
            rw [show probEvent _ _ = _ from
                probEvent_congr' (fun _ _ => Iff.rfl) (hLHS_lift.trans hLHS_align),
              show probEvent _ _ = _ from
                probEvent_congr' (fun _ _ => Iff.rfl) (hRHS_lift.trans hRHS_align),
              show probEvent _ _ = _ from
                probEvent_congr' (fun _ _ => Iff.rfl) (hBAD_lift.trans hBAD_align)]
            refine probEvent_bind_le_add_bad_of_disagree'
              (D := fun _ : Digest => False)
              (fun u _ hF => absurd hF id)
              (fun u _ _ => ?_)
            -- The pointwise inequality is exactly `hIh u`, with `Pr[= true | ·]` normalized to
            -- `probEvent (· = true) ·` by `← probEvent_eq_eq_probOutput`. After the head goal's
            -- RHS reshape pulls the Sub-B mass `qRInit/|Nonce|` into the ε₁ slot of the outer
            -- 4-way bound, ε₂ matches `qR*|TagId|/|Digest| + qRInit*qT'/|Nonce|` — exactly the
            -- IH slack — so the inner inequality closes by `add_assoc` + `gcongr`.
            have hu := hIh u
            simp only [← probEvent_eq_eq_probOutput] at hu
            rw [add_assoc] at hu
            refine hu.trans ?_
            gcongr
          · -- **Sub-case B: unreachable.** This branch presupposes `sM.2 (tag, n) ≠ none`, but
            -- we already derived `hMustNone : sM.2 (tag, n) = none` from `hnD` (the off-`D`
            -- hypothesis) and `hncoll`. The Sub-B mass has been folded into the Sub-B-off-collision
            -- disagreement set `D` and charged by `hCacheBound` at the outer `probEvent_bind_le_add_
            -- bad_disagree` application above.
            exact absurd hMustNone hMcellNone
      · -- Slot exhausted: both table handlers return `none` with state untouched, so the step
        -- collapses to the continuation `f none` and the goal is exactly the induction hypothesis.
        have hnotH : ¬ sH.1.sessionsUsed tag < sessionsPerTag := by
          rw [← congrFun hInv.1 tag]; exact hslot
        have hM : ∀ g : TagId × Nonce → Digest,
            multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag) (sM.1, sB)
            = pure (none, sM.1, sB) := by
          intro g
          change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) sM.1
              >>= (fun r => pure (r.1, r.2, multipleBadAdvance tag sB r.1)) = pure (none, sM.1, sB)
          rw [multipleTableHandler_tag_run_of_not_lt g tag sM.1 hslot]
          rfl
        have hH : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
            hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) gS (Sum.inl tag) sH.1
            = pure (none, sH.1) :=
          fun gS => hybridTableHandler_tag_run_of_not_lt gS tag sH.1 hnotH
        simp only [hM, hH, pure_bind]
        -- Weaken the IH's `qRInit * qT' / |Nonce|` slack to the head's
        -- `qRInit * (qT' + 1) / |Nonce|`. `pure_bind` simp aligns the do-block shape; `gcongr`
        -- decomposes the +-chain, leaving only the slack weakening.
        refine (ih none qR qT' qRInit sM sH sB hInv (hqRf none) (hqTf none) (hdistf none)
            (hfreshf none) hCacheBound hqRle).trans ?_
        gcongr <;> first | rfl | omega
    | inr transcript =>
      -- Reader-query branch: see  in .
      exact multipleBadEager_reader_step transcript f
        (liftM (OracleSpec.query (spec := UnlinkOracleSpec TagId Nonce Digest)
          (Sum.inr transcript)) >>= f) rfl qR qT qRInit sM sH sB hInv hqR hqT hdist hfresh
        hCacheBound hqRle ih

/-- **Multiple-to-hybrid, core coupling bound.** Threaded by the reader-aware coupling invariant `MultipleHybridCoupling`
and the freshness witness `MultipleHybridColFresh`, the instrumented multiple handler's success probability
is bounded by the lazy hybrid handler's plus the bad-event probability plus the reader-slack term
`qR * |TagId| / |Digest|`.

**Eager route.** Both worlds are eagerized to deterministic-table handlers
(`evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending`,
`evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending`); the resulting deterministic runs are
coupled cell-by-cell by `multipleBadEager_le_hybridEager_aux`. -/
lemma multipleBad_le_hybrid_add_bad_add_slack_aux [Fintype Nonce] [Fintype Digest]
    (oa : UnlinkAdversary TagId Nonce Digest) (qR qT qRInit : ℕ)
    (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sH : HybridState TagId Nonce sessionsPerTag ×
      (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (hInv : MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) sM sH sB)
    (hqR : OracleComp.IsQueryBoundP oa (fun i => i.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP oa (fun i => i.isLeft) qT)
    (hdist : ∀ n : Nonce, OracleComp.IsQueryBoundP oa (pReaderNonce n) 1)
    (hfresh : MultipleHybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) oa sH sM.2)
    (hCacheBound : ∀ tag : TagId,
      (Finset.univ.filter (fun n : Nonce =>
        (sM.2 (tag, n)).isSome ∧
          ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)).card ≤
        qRInit - qR)
    (hqRle : qR ≤ qRInit) :
    Pr[= true | (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' (sM, sB)] ≤
      Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' sH] +
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run (sM, sB)] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
  classical
  -- **Eager route, step A.** Eagerize all three `Pr` terms with the landed equivalences, then
  -- discharge the resulting eager-coupled bound by `multipleBadEager_le_hybridEager_aux`.
  have hM := evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending
    (sessionsPerTag := sessionsPerTag) oa sM.1 sM.2 sB
  have hH := evalDist_simulateQ_hybridLazyHandler_run'_eq_tableExtending oa sH.1 sH.2
    hInv.2.2.2.2.2.2.2.2
  -- Multiple-side success term: `run' = (·.1) <$> run`, factored through `(z.1,z.2.2) <$> run`.
  have hMsucc :
      Pr[= true | (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' (sM, sB)] =
      Pr[= true | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] := by
    rw [probOutput_def, probOutput_def]
    have hlhs : (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' (sM, sB) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.1) <$>
          ((fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => (z.1, z.2.2)) <$>
            (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run (sM, sB)) := by
      rw [Functor.map_map]; rfl
    have hrhs : (do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.1) <$>
          (do
            let gM ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)) := by
      rw [map_bind]
      refine bind_congr fun gM => ?_
      rw [Functor.map_map]
    have hM' : (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
          (z.1, z.2.2)) <$>
        𝒟[(simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag)) oa).run (sM, sB)]
        = 𝒟[do
            let g ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending sM.2 g)) oa).run (sM.1, sB)] := by
      rw [← evalDist_map]; exact hM
    rw [hlhs, hrhs, evalDist_map, evalDist_map, evalDist_map, hM']
  -- Multiple-side bad term: factored through `(z.1,z.2.2) <$> run`.
  have hMbad :
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run (sM, sB)] =
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] := by
    have hbadev :
        (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad = true) =
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad = true) ∘
          (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => (z.1, z.2.2)) := rfl
    rw [hbadev, ← probEvent_map]
    exact probEvent_congr' (fun _ _ => Iff.rfl) hM
  -- Hybrid-side success term.
  have hHsucc :
      Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) oa).run' sH] =
      Pr[= true | do
        let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sH.2 gH)) oa).run'
          sH.1] := by
    rw [probOutput_def, probOutput_def]
    have := hH
    rw [show ((sH.1, sH.2) : HybridState TagId Nonce sessionsPerTag × _) = sH from rfl] at this
    rw [this]
  rw [hMsucc, hHsucc, hMbad]
  exact multipleBadEager_le_hybridEager_aux oa qR qT qRInit sM sH sB hInv hqR hqT hdist hfresh
    hCacheBound hqRle

/-- **Multiple-to-hybrid.** Under `HasDistinctUnlinkReaderNonces` and a reader-query bound `qReader`, the
multiple-session ideal world succeeds with probability at most that of the hybrid world plus the
within-tag nonce-collision probability plus the reader-slack term `qReader * |TagId| / |Digest|`. -/
theorem multipleIdeal_le_hybrid_add_bad [Fintype Nonce] [Fintype Digest]
    (adversary : UnlinkAdversary TagId Nonce Digest) (qReader qTag : ℕ)
    (hqReader : OracleComp.IsQueryBoundP adversary (·.isRight) qReader)
    (hqTag : OracleComp.IsQueryBoundP adversary (·.isLeft) qTag)
    (hdist : HasDistinctUnlinkReaderNonces adversary) :
    Pr[= true | (simulateQ (multipleIdealQueryImpl (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (UnlinkState.init, ∅)] ≤
      Pr[= true | (simulateQ (hybridLazyHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run'
        (HybridState.init, ∅)] +
      Pr[fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)) adversary).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] +
      ((qReader * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qReader * qTag : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) := by
  rw [← probOutput_multipleBad_run'_eq_multipleIdeal adversary (UnlinkState.init, ∅)
    UnlinkBadState.init]
  refine multipleBad_le_hybrid_add_bad_add_slack_aux adversary qReader qTag qReader
    (UnlinkState.init, ∅) (HybridState.init, ∅) UnlinkBadState.init
    MultipleHybridCoupling_init hqReader hqTag
    ((hasDistinctUnlinkReaderNonces_iff adversary).mp hdist)
    (multipleHybridColFresh_init adversary (HybridState.init, ∅)) ?_ le_rfl
  intro tag
  -- Initial multiple cache is empty, so the SubB-off-collision filter is empty.
  simp [QueryCache.empty_apply]


end UnlinkReduction

end PRFTagReader
