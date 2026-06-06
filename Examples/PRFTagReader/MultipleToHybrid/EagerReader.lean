/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.MultipleToHybrid.EagerSetup

/-!
# PRF Tag/Reader Protocol: multiple-to-hybrid eager coupling, reader step

Reader-query branch of `multipleBadEager_le_hybridEager_aux`. Both table handlers reduce on a
reader query to a deterministic `pure (bit, state)`. The two reader bits agree off the
disagreement set where the multi reader accepts but the hybrid reader rejects; that disagreement
mass is bounded by `|TagId| / |Digest|` per query via `probEvent_multipleReader_disagree_le`,
the `MultipleHybridColFresh` witness `hfresh` rules out rogue cached cells at `transcript.nonce`,
and `hdist` (the per-nonce reader-uniqueness budget) together with `hCacheBound` provides the
bookkeeping that prevents double-counting in the inductive step.

The lemma `multipleBadEager_reader_step` discharges the `| inr transcript =>` branch of the
`query_bind` case in the headline aux lemma.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]
  [SampleableType (TagId × Nonce → Digest)]
  [SampleableType ((TagId × Fin sessionsPerTag) × Nonce → Digest)]

omit [Nonempty TagId] in
/-- Reader step of the eager-coupled core. Closes the `| inr transcript =>` branch of the
`query_bind` case inside `multipleBadEager_le_hybridEager_aux`. Both table handlers collapse the
head reader query to a deterministic `pure`; lazifying the multi-side table draw to
`idealCacheMapM cells sM.2` exposes a disagreement set bounded by `|TagId| / |Digest|`
(`probEvent_multipleReader_disagree_le`), and off the disagreement set the inductive hypothesis
`ih` closes the per-list-rs pointwise bound via `MultipleHybridCoupling_reader_step`. -/
lemma multipleBadEager_reader_step [Fintype Nonce] [Fintype Digest]
    (transcript : TagTranscript Nonce Digest)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (hoa : oa = liftM (OracleSpec.query
      (spec := UnlinkOracleSpec TagId Nonce Digest) (Sum.inr transcript)) >>= f)
    (qR qT qRInit : ℕ)
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
    (hqRle : qR ≤ qRInit)
    (ih : ∀ (u : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript))
        (qR qT qRInit : ℕ)
        (sM : UnlinkState TagId × ((TagId × Nonce) →ₒ Digest).QueryCache)
        (sH : HybridState TagId Nonce sessionsPerTag ×
          (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
        (sB : UnlinkBadState TagId Nonce Digest),
        MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) sM sH sB →
        OracleComp.IsQueryBoundP (f u) (fun i => i.isRight = true) qR →
        OracleComp.IsQueryBoundP (f u) (fun i => i.isLeft = true) qT →
        (∀ n : Nonce, OracleComp.IsQueryBoundP (f u) (pReaderNonce n) 1) →
        MultipleHybridColFresh (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (f u) sH sM.2 →
        (∀ tag : TagId,
          (Finset.univ.filter (fun n : Nonce =>
            (sM.2 (tag, n)).isSome ∧
              ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)).card ≤
            qRInit - qR) →
        qR ≤ qRInit →
        Pr[= true | do
            let gM ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending sM.2 gM)) (f u)).run (sM.1, sB)] ≤
          Pr[= true | do
            let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sH.2 gH)) (f u)).run'
              sH.1] +
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
            let gM ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending sM.2 gM)) (f u)).run (sM.1, sB)] +
          ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
          ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞)) :
    Pr[= true | do
        let gM ← $ᵗ (TagId × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM)) oa).run (sM.1, sB)] ≤
      Pr[= true | do
        let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (hybridTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending sH.2 gH)) oa).run'
          sH.1] +
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
  subst hoa
  simp only [multipleBadTable_run_query_bind', hybridTable_run'_query_bind', map_bind]
  set n₀ := transcript.nonce with hn₀
  -- Reader-side budgets: `qR` decrements by one; `qT` is unchanged (the head reader query is
  -- right-not-left); `hdist` gives 0 residual reader queries at `n₀` in the continuation.
  have hqRsplit := hqR
  rw [OracleComp.isQueryBoundP_query_bind_iff] at hqRsplit
  obtain ⟨qR', rfl⟩ : ∃ qR', qR = qR' + 1 :=
    ⟨qR - 1, by have := hqRsplit.1.resolve_left (fun h => absurd rfl h); omega⟩
  have hqRf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isRight = true) qR' :=
    fun u => by simpa using hqRsplit.2 u
  have hqTf : ∀ u, OracleComp.IsQueryBoundP (f u) (fun i => i.isLeft = true) qT := by
    intro u
    have h := hqT
    rw [OracleComp.isQueryBoundP_query_bind_iff] at h
    simpa using h.2 u
  have hdistf : ∀ u, ∀ n, OracleComp.IsQueryBoundP (f u) (pReaderNonce n) 1 := by
    intro u n
    have h := hdist n
    rw [OracleComp.isQueryBoundP_query_bind_iff] at h
    have h2 := h.2 u
    by_cases hnn : n = n₀
    · subst hnn; simp only [pReaderNonce, hn₀] at h2; exact h2.mono (Nat.zero_le 1)
    · have hpf : ¬ pReaderNonce (TagId := TagId) (Digest := Digest) n
          (Sum.inr transcript) := fun h => hnn h.symm
      simpa [hpf] using h2
  have hb0 : ∀ u, OracleComp.IsQueryBoundP (f u) (pReaderNonce n₀) 0 := by
    intro u
    have h := hdist n₀
    rw [OracleComp.isQueryBoundP_query_bind_iff] at h
    have h2 := h.2 u
    simp only [pReaderNonce, hn₀] at h2; exact h2
  -- `hfresh` at the head query rules out rogue cached cells at `n₀`: a multi cell at
  -- `(tag, n₀)` with no recorded session would force the head query to be at residual
  -- budget 0, contradicting the actual head reader query at `n₀`.
  have hcol : ∀ tag : TagId, (sM.2 (tag, n₀)).isSome →
      ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n₀ := by
    intro tag hsome
    by_contra hne
    have hbad := hfresh n₀ tag hsome (fun sid hs => hne ⟨sid, hs⟩)
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hbad
    have hp : pReaderNonce (TagId := TagId) (Digest := Digest) n₀
        (Sum.inr transcript) := rfl
    rcases hbad.1 with h | h
    · exact h hp
    · exact absurd h (lt_irrefl 0)
  -- Reduce both handler calls to `pure`.
  have hMstep : ∀ g : TagId × Nonce → Digest,
      multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
          g (Sum.inr transcript) (sM.1, sB)
      = pure (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
          (fun tag nonce => g (tag, nonce))
          (multiplePattern (TagId := TagId) sessionsPerTag) transcript), sM.1, sB) := by
    intro g
    change (multipleTableHandler (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) sM.1
        >>= (fun r => pure (r.1, r.2, sB)) = _
    rw [multipleTableHandler_reader_run g transcript sM.1]; rfl
  have hHstep : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      hybridTableHandler gS (Sum.inr transcript) sH.1
      = pure (ReaderReply.ofBool (hybridReaderAccepts gS sH.1.sessionNonce transcript), sH.1) :=
    fun gS => hybridTableHandler_reader_run gS transcript sH.1
  -- The hybrid reader bit is independent of the table draw `gH`: every recorded session is
  -- already cached in `sH.2` by `hInv.hhyb2`, so `tableExtending sH.2 gH` reads the cache.
  set bHconst : Bool := hybridCacheAccepts sH.2 sH.1.sessionNonce transcript with hbHconst
  have hHbit_const : ∀ gH : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      hybridReaderAccepts (OracleComp.tableExtending sH.2 gH)
        sH.1.sessionNonce transcript = bHconst := by
    intro gH
    rw [hbHconst]
    unfold hybridReaderAccepts hybridCacheAccepts
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨tag, sid, hsn, hcell⟩
      have hHsome : (sH.2 ((tag, sid), transcript.nonce)).isSome :=
        hInv.2.2.2.2.2.2.2.2 tag sid transcript.nonce hsn
      rcases hHv : sH.2 ((tag, sid), transcript.nonce) with _ | v
      · exact absurd hHv (Option.isSome_iff_ne_none.mp hHsome)
      · rw [show OracleComp.tableExtending sH.2 gH ((tag, sid), transcript.nonce) = v by
              simp [OracleComp.tableExtending, hHv]] at hcell
        exact ⟨tag, sid, hsn, by rw [hHv, hcell]⟩
    · rintro ⟨tag, sid, hsn, hcell⟩
      exact ⟨tag, sid, hsn, by simp [OracleComp.tableExtending, hcell]⟩
  -- Multi reader cells.
  set cells := multipleReaderCells (TagId := TagId) (Digest := Digest) transcript with hcells
  -- Step 1: reduce the three goal terms (LHS / RHS₁ / RHS₂ via `hMstep`/`hHstep`). After the
  -- reductions, the handler call collapses to a `pure` whose payload determines the reader bit
  -- deterministically from the (drawn) table.
  have hLHS_eq :
      (do let gM ← $ᵗ (TagId × Nonce → Digest)
          let a ← multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM) (Sum.inr transcript) (sM.1, sB)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending sM.2 gM)) (f a.1)).run a.2)
      = (do let gM ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending sM.2 gM))
                (f (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
                  (fun tag nonce => OracleComp.tableExtending sM.2 gM (tag, nonce))
                  (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
                (sM.1, sB)) := by
    refine bind_congr fun gM => ?_
    rw [hMstep (OracleComp.tableExtending sM.2 gM)]; rfl
  have hRHS_eq :
      (do let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let p ← hybridTableHandler (OracleComp.tableExtending sH.2 gH)
            (Sum.inr transcript) sH.1
          (simulateQ (hybridTableHandler (OracleComp.tableExtending sH.2 gH))
            (f p.1)).run' p.2)
      = (do let gH ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (hybridTableHandler
              (OracleComp.tableExtending sH.2 gH)) (f (ReaderReply.ofBool bHconst))).run'
              sH.1) := by
    refine bind_congr fun gH => ?_
    rw [hHstep (OracleComp.tableExtending sH.2 gH), hHbit_const gH]; rfl
  have hBAD_eq :
      (do let gM ← $ᵗ (TagId × Nonce → Digest)
          let a ← multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending sM.2 gM) (Sum.inr transcript) (sM.1, sB)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending sM.2 gM)) (f a.1)).run a.2)
      = (do let gM ← $ᵗ (TagId × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending sM.2 gM))
                (f (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
                  (fun tag nonce => OracleComp.tableExtending sM.2 gM (tag, nonce))
                  (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
                (sM.1, sB)) := by
    refine bind_congr fun gM => ?_
    rw [hMstep (OracleComp.tableExtending sM.2 gM)]; rfl
  rw [hLHS_eq, hRHS_eq, hBAD_eq]
  classical
  -- Step 2: lazify the multi-side eager table draw to `idealCacheMapM cells sM.2` followed by an
  -- inner remaining draw. After lazification the multi reader bit becomes a function of the
  -- drawn list `rs.1`. Wrap both LHS and BAD terms as `Mψ (tableExtending sM.2 gM)` for some
  -- `Mψ`, so that `evalDist_idealCacheMapM_bind_uniformTable_comp` applies.
  set MψLHS : (TagId × Nonce → Digest) → ProbComp Bool := fun g =>
    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
      (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag) g)
        (f (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
          (fun tag nonce => g (tag, nonce))
          (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
        (sM.1, sB) with hMψLHS_def
  set MψBAD : (TagId × Nonce → Digest) →
      ProbComp (Bool × UnlinkBadState TagId Nonce Digest) := fun g =>
    (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
        (z.1, z.2.2)) <$>
      (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag) g)
        (f (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
          (fun tag nonce => g (tag, nonce))
          (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
        (sM.1, sB) with hMψBAD_def
  have hLHS_fold :
      (do let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending sM.2 gM))
              (f (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
                (fun tag nonce => OracleComp.tableExtending sM.2 gM (tag, nonce))
                (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
              (sM.1, sB))
      = (do let gM ← $ᵗ (TagId × Nonce → Digest)
            MψLHS (OracleComp.tableExtending sM.2 gM)) := rfl
  have hBAD_fold :
      (do let gM ← $ᵗ (TagId × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending sM.2 gM))
              (f (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
                (fun tag nonce => OracleComp.tableExtending sM.2 gM (tag, nonce))
                (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
              (sM.1, sB))
      = (do let gM ← $ᵗ (TagId × Nonce → Digest)
            MψBAD (OracleComp.tableExtending sM.2 gM)) := rfl
  -- Lazify: `($ᵗ-table) >>= λ gM => Mψ (tableExtending sM.2 gM) = idealCacheMapM cells sM.2
  -- >>= λ rs => ($ᵗ-table) >>= λ gM => Mψ (tableExtending rs.2 gM)`.
  have hLHS_lazify :
      𝒟[(do let gM ← $ᵗ (TagId × Nonce → Digest)
            MψLHS (OracleComp.tableExtending sM.2 gM))]
      = 𝒟[(do let rs ← idealCacheMapM (Digest := Digest) cells sM.2
              let gM ← $ᵗ (TagId × Nonce → Digest)
              MψLHS (OracleComp.tableExtending rs.2 gM))] :=
    (evalDist_idealCacheMapM_bind_uniformTable_comp cells sM.2 MψLHS).symm
  have hBAD_lazify :
      𝒟[(do let gM ← $ᵗ (TagId × Nonce → Digest)
            MψBAD (OracleComp.tableExtending sM.2 gM))]
      = 𝒟[(do let rs ← idealCacheMapM (Digest := Digest) cells sM.2
              let gM ← $ᵗ (TagId × Nonce → Digest)
              MψBAD (OracleComp.tableExtending rs.2 gM))] :=
    (evalDist_idealCacheMapM_bind_uniformTable_comp cells sM.2 MψBAD).symm
  rw [show Pr[= true | _] = _ from probOutput_congr rfl (hLHS_fold ▸ hLHS_lazify),
      show probEvent _ _ = _ from probEvent_congr' (fun _ _ => Iff.rfl)
        (hBAD_fold ▸ hBAD_lazify)]
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  -- Step 3: apply `probEvent_bind_le_add_bad_disagree` with the lazy
  -- `mx := idealCacheMapM cells sM.2` and disagreement set
  -- `D rs := decide (∃ d ∈ rs.1, d = transcript.auth) = true ∧ bHconst = false`.
  -- Off `D`: the multi reader bit equals `bHconst`, so the IH closes the bound.
  -- On `D`: charged to `ε₁ := |TagId|/|Digest|` via `probEvent_multipleReader_disagree_le`.
  set D : List Digest × ((TagId × Nonce) →ₒ Digest).QueryCache → Prop :=
    fun rs => decide (∃ d ∈ rs.1, d = transcript.auth) = true ∧ bHconst = false with hD
  have hslackeq :
      (((qR' + 1) * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)
        = (Fintype.card TagId : ℕ) / (Fintype.card Digest : ℝ≥0∞)
          + ((qR' * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
    rw [← ENNReal.add_div]; congr 1; push_cast; ring
  refine le_trans (probEvent_bind_le_add_bad_disagree
    (mx := idealCacheMapM (Digest := Digest) cells sM.2)
    (my := fun rs => ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
      MψLHS (OracleComp.tableExtending rs.2 gM))
    (oc := fun _ => ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun gH =>
      (simulateQ (hybridTableHandler (OracleComp.tableExtending sH.2 gH))
        (f (ReaderReply.ofBool bHconst))).run' sH.1)
    (ob := fun rs => ($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
      MψBAD (OracleComp.tableExtending rs.2 gM))
    (q := fun b => b = true)
    (r := fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true)
    (D := D)
    (ε₁ := (Fintype.card TagId : ℕ) / (Fintype.card Digest : ℝ≥0∞))
    (ε₂ := ((qR' * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞))
    ?hDcl ?hcl) ?fin
  case hDcl =>
    -- Bound the disagreement mass by `|TagId|/|Digest|` via
    -- `probEvent_multipleReader_disagree_le`.
    have hcol' : ∀ tag, (sM.2 (tag, transcript.nonce)).isSome →
        ∃ sid, sH.1.sessionNonce (tag, sid) = some transcript.nonce :=
      fun tag hsome => hn₀ ▸ hcol tag (hn₀ ▸ hsome)
    have hdisagree := probEvent_multipleReader_disagree_le (TagId := TagId) (Nonce := Nonce)
      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
      sM.2 sH.2 sH.1.sessionNonce transcript hcol' hInv.2.2.2.2.1
    refine le_trans (probEvent_mono ?_) hdisagree
    intro rs _ hDrs
    exact ⟨hDrs.1, by rw [← hbHconst]; exact hDrs.2⟩
  case hcl =>
    -- Off-`D` pointwise bound: recurse via IH on the post-reader state.
    intro rs hrs hDrs
    beta_reduce
    have hr2_not_mem : ∀ d : TagId × Nonce, d ∉ cells → rs.2 d = sM.2 d :=
      fun d hd => idealCacheMapM_cache_not_mem cells sM.2 rs hrs d hd
    have hMbit_eq : ∀ gM : TagId × Nonce → Digest,
        unlinkReaderAccepts
          (fun tag nonce => OracleComp.tableExtending rs.2 gM (tag, nonce))
          (multiplePattern (TagId := TagId) sessionsPerTag) transcript
        = decide (∃ d ∈ rs.1, d = transcript.auth) := by
      intro gM
      have hrs1' := idealCacheMapM_support cells sM.2 rs hrs gM
      unfold unlinkReaderAccepts tagAccepts multiplePattern
      simp only [decide_eq_decide]
      rw [hrs1']
      simp only [hcells, multipleReaderCells, List.map_map, List.mem_map,
        Finset.mem_toList, Finset.mem_univ, true_and, Function.comp, decide_eq_true_eq]
      constructor
      · rintro ⟨tag, _, hd⟩
        exact ⟨_, ⟨tag, rfl⟩, hd⟩
      · rintro ⟨d, ⟨tag, rfl⟩, hd⟩
        exact ⟨tag, ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne sessionsPerTag)⟩, hd⟩⟩
    have hhyb_to_multi : bHconst = true →
        decide (∃ d ∈ rs.1, d = transcript.auth) = true := by
      intro hbH
      rw [hbHconst, hybridCacheAccepts, decide_eq_true_eq] at hbH
      obtain ⟨tag, sid, hsn, hcell⟩ := hbH
      have hmcell : sM.2 (tag, transcript.nonce) = some transcript.auth := by
        rw [hInv.2.2.2.2.1 tag sid transcript.nonce hsn, hcell]
      have hcellmem : (tag, transcript.nonce) ∈ cells := by
        rw [hcells, multipleReaderCells, List.mem_map]
        exact ⟨tag, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
      exact decide_eq_true ⟨transcript.auth,
        mem_drawn_of_cached_cell _ sM.2 rs hrs (tag, transcript.nonce) hcellmem
          transcript.auth hmcell, rfl⟩
    have hbit_const : decide (∃ d ∈ rs.1, d = transcript.auth) = bHconst := by
      rcases hbHv : bHconst with _ | _
      · rcases hmv : decide (∃ d ∈ rs.1, d = transcript.auth) with _ | _
        · rfl
        · exact absurd (hDrs ⟨hmv, hbHv⟩) id
      · exact hhyb_to_multi hbHv
    have hMbit_const : ∀ gM : TagId × Nonce → Digest,
        unlinkReaderAccepts
          (fun tag nonce => OracleComp.tableExtending rs.2 gM (tag, nonce))
          (multiplePattern (TagId := TagId) sessionsPerTag) transcript = bHconst :=
      fun gM => by rw [hMbit_eq gM, hbit_const]
    have hMψLHS_rewrite : ∀ gM : TagId × Nonce → Digest,
        MψLHS (OracleComp.tableExtending rs.2 gM)
        = (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending rs.2 gM))
            (f (ReaderReply.ofBool bHconst))).run (sM.1, sB) := fun gM => by
      rw [hMψLHS_def]; dsimp only; rw [hMbit_const gM]
    have hMψBAD_rewrite : ∀ gM : TagId × Nonce → Digest,
        MψBAD (OracleComp.tableExtending rs.2 gM)
        = (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending rs.2 gM))
            (f (ReaderReply.ofBool bHconst))).run (sM.1, sB) := fun gM => by
      rw [hMψBAD_def]; dsimp only; rw [hMbit_const gM]
    have hInvNew : MultipleHybridCoupling (sessionsPerTag := sessionsPerTag) (sM.1, rs.2) sH sB :=
      MultipleHybridCoupling_reader_step sM sH sB hInv cells rs hrs
    have hfreshNew : MultipleHybridColFresh (sessionsPerTag := sessionsPerTag)
        (f (ReaderReply.ofBool bHconst)) sH rs.2 := by
      intro n tag hsome hns
      by_cases hnn : n = n₀
      · subst hnn; exact hb0 _
      · have hcellnotmem : (tag, n) ∉ cells := by
          rw [hcells, multipleReaderCells, List.mem_map]
          rintro ⟨_, _, h⟩
          exact hnn (congrArg Prod.snd h).symm
        rw [hr2_not_mem (tag, n) hcellnotmem] at hsome
        have hb := hfresh n tag hsome hns
        rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
        have hpf : ¬ pReaderNonce (TagId := TagId) (Digest := Digest) n
            (Sum.inr transcript) := fun h => hnn h.symm
        simpa [hpf] using hb.2 (ReaderReply.ofBool bHconst)
    have hCacheBoundNew : ∀ tag : TagId,
        (Finset.univ.filter (fun n : Nonce =>
          (rs.2 (tag, n)).isSome ∧
            ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)).card ≤
          qRInit - qR' := by
      intro tag
      have hsub :
          (Finset.univ.filter (fun n : Nonce =>
            (rs.2 (tag, n)).isSome ∧
              ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n))
          ⊆ insert n₀ (Finset.univ.filter (fun n : Nonce =>
            (sM.2 (tag, n)).isSome ∧
              ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)) := by
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
        obtain ⟨hsome, hns⟩ := hn
        by_cases hnn : n = n₀
        · subst hnn; exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hcellnotmem : (tag, n) ∉ cells := by
            rw [hcells, multipleReaderCells, List.mem_map]
            rintro ⟨_, _, h⟩
            exact hnn (congrArg Prod.snd h).symm
          exact ⟨by rwa [hr2_not_mem (tag, n) hcellnotmem] at hsome, hns⟩
      calc (Finset.univ.filter (fun n : Nonce =>
            (rs.2 (tag, n)).isSome ∧
              ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)).card
          ≤ (insert n₀ (Finset.univ.filter (fun n : Nonce =>
              (sM.2 (tag, n)).isSome ∧
                ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n))).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun n : Nonce =>
              (sM.2 (tag, n)).isSome ∧
                ¬ ∃ sid : Fin sessionsPerTag, sH.1.sessionNonce (tag, sid) = some n)).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ qRInit - qR' := by
            have hold := hCacheBound tag
            omega
    have hih := ih (ReaderReply.ofBool bHconst) qR' qT qRInit (sM.1, rs.2) sH sB
      hInvNew (hqRf _) (hqTf _) (hdistf _) hfreshNew hCacheBoundNew
      (Nat.le_of_succ_le hqRle)
    have hLHS_inner :
        (($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
            MψLHS (OracleComp.tableExtending rs.2 gM))
        = (($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                z.1) <$>
              (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending rs.2 gM))
                (f (ReaderReply.ofBool bHconst))).run (sM.1, sB)) :=
      bind_congr hMψLHS_rewrite
    have hBAD_inner :
        (($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
            MψBAD (OracleComp.tableExtending rs.2 gM))
        = (($ᵗ (TagId × Nonce → Digest)) >>= fun gM =>
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending rs.2 gM))
                (f (ReaderReply.ofBool bHconst))).run (sM.1, sB)) :=
      bind_congr hMψBAD_rewrite
    have hLHS_pe := probEvent_congr' (q := fun b : Bool => b = true)
      (fun _ _ => Iff.rfl) (congrArg evalDist hLHS_inner)
    have hBAD_pe := probEvent_congr'
      (q := fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad = true)
      (fun _ _ => Iff.rfl) (congrArg evalDist hBAD_inner)
    rw [hLHS_pe, hBAD_pe]
    have hih' := hih
    rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput] at hih'
    simp only at hih'
    -- The IH's bound matches the pointwise goal after reassociating `+ qR'_term + qRInit_term`
    -- to `+ (qR'_term + qRInit_term)`.
    refine hih'.trans ?_
    rw [add_assoc, add_assoc]
  case fin =>
    -- The disagree-lemma's `oc := fun _ => P_hyb` produces `mx >>= (fun _ => P_hyb)` on
    -- the RHS; `mx = idealCacheMapM cells sM.2` never fails so this equals `Pr[q | P_hyb]`.
    have hPF : Pr[⊥ | idealCacheMapM (Digest := Digest) cells sM.2] = 0 := by
      have hrec : ∀ {D : Type} [DecidableEq D] (l : List D)
          (c : (D →ₒ Digest).QueryCache),
          Pr[⊥ | idealCacheMapM (Digest := Digest) l c] = 0 := by
        intro D _ l
        induction l with
        | nil => intro c; simp [idealCacheMapM]
        | cons d ds ih =>
          intro c
          change Pr[⊥ | idealCacheStep c d >>= fun r =>
            idealCacheMapM ds r.2 >>= fun rs => pure (r.1 :: rs.1, rs.2)] = 0
          rw [probFailure_bind_eq_zero_iff]
          refine ⟨by unfold idealCacheStep; rcases c d with _ | _ <;> simp, fun r _ => ?_⟩
          rw [probFailure_bind_eq_zero_iff]
          exact ⟨ih r.2, fun _ _ => by simp⟩
      exact hrec cells sM.2
    rw [probEvent_bind_const, hPF, tsub_zero, one_mul, hslackeq]
    refine le_of_eq ?_
    push_cast; ring

end UnlinkReduction

end PRFTagReader
