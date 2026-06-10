/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.DirectCoupling
import Examples.PRFTagReader.DirectCoupling.StepLemmas
import Examples.PRFTagReader.MultipleToHybrid.EagerSetup

/-!
# PRF Tag/Reader Protocol — Direct Coupling, Reader Step

The reader (`Sum.inr transcript`) induction step of the direct M_ideal/S_ideal coupling aux
`multipleBadEager_le_singleEager_DC_aux`. Only the slot-0 column at the queried nonce is lazified
on both sides (via `idealCacheMapM` over the cells `{((T, 0), nonce) : T}`), so the M reader bit
collapses to a deterministic bit `m` of the extended cache while slot-positive cells stay uncached.

When `m = true` the S reader also accepts (the slot-0 witness lifts via
`mReader_accepts_imp_sReader_accepts`), both sides continue with the same reply, and the induction
hypothesis closes the step. When `m = false`, M rejects; the asymmetry `mAcc ⟹ sAcc` is one-sided,
so over `ℝ≥0∞` the S-side's slot-positive collision branch is *discarded*: the actual S reader bit
equals `cacheBadReader gS`, and replacing it by the constant `false` reply costs exactly the
collision event's uniform mass `≤ |TagId| · sessionsPerTag / |Digest|`, charged to a single slack
unit.

## Main results

* `dcAux_reader_step` — the reader induction step of the direct-coupling aux, taking the induction
  hypothesis as an explicit premise.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section DirectCouplingCompose

variable {TagId Nonce Digest : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

namespace UnlinkReduction

omit [Nonempty TagId] in
/-- The reader (`Sum.inr transcript`) induction step of the direct M_ideal/S_ideal coupling aux.
The induction hypothesis is supplied as the explicit premise `ih`; the conclusion is the aux bound
specialized to the adversary `query (Sum.inr transcript) >>= k`. -/
lemma dcAux_reader_step [Fintype Nonce] [Fintype Digest]
    (qRInit qR qT : ℕ)
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (R : Finset Nonce)
    (hqRle : qR + R.card ≤ qRInit)
    (hcInv : ∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
        ∀ n : Nonce, c ((tag, sid), n) = none)
    (hRespInv : ∀ tag : TagId, ∀ n : Nonce, n ∉ R →
        c ((tag, (0 : Fin sessionsPerTag)), n) ≠ none →
        sB.responses (tag, n) ≠ none)
    (transcript : TagTranscript Nonce Digest)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (ih : ∀ (u : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript))
        (qR qT : ℕ) (s : UnlinkState TagId)
        (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
        (sB : UnlinkBadState TagId Nonce Digest) (R : Finset Nonce),
        OracleComp.IsQueryBoundP (k u) (·.isRight) qR →
        OracleComp.IsQueryBoundP (k u) (·.isLeft) qT →
        qR + R.card ≤ qRInit →
        (∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
          ∀ n : Nonce, c ((tag, sid), n) = none) →
        (∀ tag : TagId, ∀ n : Nonce, n ∉ R →
          c ((tag, (0 : Fin sessionsPerTag)), n) ≠ none →
          sB.responses (tag, n) ≠ none) →
        Pr[= true | do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine) (k u)).run (s, sB)] ≤
          Pr[= true | do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)) (k u)).run' s] +
          Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine) (k u)).run (s, sB)] +
          ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
          ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞))
    (hqR : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)
      (·.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)
      (·.isLeft) qT) :
    Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine)
            (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)).run (s, sB)] ≤
      Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
          (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)).run' s] +
      Pr[fun z : Bool × UnlinkBadState TagId Nonce Digest => z.2.bad | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine)
            (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)).run (s, sB)] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  -- Reader case: the asymmetric-discard argument. Slot-0 column lazification
  -- on both sides makes M's reader bit a constant `m` of the extended cache `c₀′`; on `m = true`
  -- the IH closes directly, on `m = false` the slot-positive acceptance event `E gS` is the
  -- whole gap and is charged to one slack₃ unit via `cacheBadReader`.
  -- **Budget splits.** The head reader query is right-not-left, so `qR = qR' + 1` and `qT`
  -- is unchanged. `R` grows to `insert transcript.nonce R`.
  have hqTk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isLeft) qT := by
    intro u
    have h := hqT
    rw [OracleComp.isQueryBoundP_query_bind_iff] at h
    simpa using h.2 u
  have hqRsplit := hqR
  rw [OracleComp.isQueryBoundP_query_bind_iff] at hqRsplit
  have hqRpos : 0 < qR := hqRsplit.1.resolve_left (fun h => absurd rfl h)
  obtain ⟨qR', rfl⟩ : ∃ qR', qR = qR' + 1 := ⟨qR - 1, by omega⟩
  have hqRk : ∀ u, OracleComp.IsQueryBoundP (k u) (·.isRight) qR' := fun u => by
    simpa using hqRsplit.2 u
  -- Abbreviation for the M-side reader acceptance bit at a sub-table.
  set mAcc : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → Bool := fun gS =>
    unlinkReaderAccepts (Slot := TagId)
      (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
        (OracleComp.tableExtending c gS) (tag, nonce))
      (multiplePattern (TagId := TagId) sessionsPerTag) transcript with hmAcc
  set sAcc : ((TagId × Fin sessionsPerTag) × Nonce → Digest) → Bool := fun gS =>
    unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
      (fun slot nonce => OracleComp.tableExtending c gS (slot, nonce))
      (singlePattern (TagId := TagId) sessionsPerTag) transcript with hsAcc
  -- M-Fine reader head step: pure reply, state untouched, `cacheBad` advances by `gFine`.
  have hMstep : ∀ gS gFine,
      multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c gS)) gFine (Sum.inr transcript) (s, sB)
      = pure (ReaderReply.ofBool (mAcc gS), s,
          multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) := by
    intro gS gFine
    change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c gS)) (Sum.inr transcript)) s
        >>= (fun r => pure (r.1, r.2,
          multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB))
        = _
    rw [multipleTableHandler_reader_run_slotZeroSubTable]
    rfl
  -- S reader head step: pure reply, state untouched.
  have hSstep : ∀ gS,
      singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
        (Sum.inr transcript) s
      = pure (ReaderReply.ofBool (sAcc gS), s) := fun gS =>
    singleTableHandler_reader_run (OracleComp.tableExtending c gS) transcript s
  -- Collapse the head reader query on all three positions.
  simp only [multipleBadTableFine_run_query_bind', singleTable_run'_query_bind', map_bind]
  have hLHS_eq :
      (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let p ← multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine (Sum.inr transcript) (s, sB)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c gS)) gFine) (k p.1)).run p.2)
      = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine)
                (k (ReaderReply.ofBool (mAcc gS)))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB)) := by
    refine bind_congr fun gS => ?_
    refine bind_congr fun gFine => ?_
    rw [hMstep gS gFine]; rfl
  have hRHS_eq :
      (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let p ← singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS)
            (Sum.inr transcript) s
          (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
            (k p.1)).run' p.2)
      = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
              (k (ReaderReply.ofBool (sAcc gS)))).run' s) := by
    refine bind_congr fun gS => ?_
    rw [hSstep gS]; rfl
  have hBAD_eq :
      (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let p ← multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine (Sum.inr transcript) (s, sB)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c gS)) gFine) (k p.1)).run p.2)
      = (do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine)
                (k (ReaderReply.ofBool (mAcc gS)))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB)) := by
    refine bind_congr fun gS => ?_
    refine bind_congr fun gFine => ?_
    rw [hMstep gS gFine]; rfl
  rw [probOutput_congr rfl (congrArg evalDist hLHS_eq),
      probOutput_congr rfl (congrArg evalDist hRHS_eq),
      probEvent_congr' (fun _ _ => Iff.rfl) (congrArg evalDist hBAD_eq)]
  classical
  haveI : Nonempty Digest :=
    ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  -- **C1: slot-0 column lazification.** Cache every slot-0 cell of the queried column.
  set cells : List ((TagId × Fin sessionsPerTag) × Nonce) :=
    (Finset.univ.toList).map
      (fun T : TagId => ((T, (0 : Fin sessionsPerTag)), transcript.nonce)) with hcells
  -- The three terms (LHS-success, RHS-success, BAD) all have the shape
  -- `$ᵗ gS >>= fun gS => Mψ (tableExtending c gS)` for the continuations below; the
  -- lazification lemma rewrites `tableExtending c gS` to `idealCacheMapM cells c >>= …`.
  -- LHS continuation: absorbs the inner `$ᵗ gFine` binder.
  have hLHS_lazify :
      𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine)
                (k (ReaderReply.ofBool (mAcc gS)))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB))]
      = 𝒟[(do let rs ← idealCacheMapM (Digest := Digest) cells c
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  z.1) <$>
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending rs.2 gS)) gFine)
                  (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
                    (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending rs.2 gS) (tag, nonce))
                    (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
                  (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                    gFine transcript sB))] := by
    rw [hmAcc]
    exact (evalDist_idealCacheMapM_bind_uniformTable_comp cells c
      (fun T => do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) T) gFine)
            (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
              (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                T (tag, nonce))
              (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
            (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
              gFine transcript sB))).symm
  -- RHS continuation (no `gFine`).
  have hRHS_lazify :
      𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c gS))
              (k (ReaderReply.ofBool (sAcc gS)))).run' s)]
      = 𝒟[(do let rs ← idealCacheMapM (Digest := Digest) cells c
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending rs.2 gS))
                (k (ReaderReply.ofBool (unlinkReaderAccepts
                  (Slot := TagId × Fin sessionsPerTag)
                  (fun slot nonce => OracleComp.tableExtending rs.2 gS (slot, nonce))
                  (singlePattern (TagId := TagId) sessionsPerTag) transcript)))).run' s)] := by
    rw [hsAcc]
    exact (evalDist_idealCacheMapM_bind_uniformTable_comp cells c
      (fun T => (simulateQ (singleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) T)
        (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun slot nonce => T (slot, nonce))
          (singlePattern (TagId := TagId) sessionsPerTag) transcript)))).run' s)).symm
  -- BAD continuation: same as LHS but with the `(z.1, z.2.2)` projection.
  have hBAD_lazify :
      𝒟[(do let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine)
                (k (ReaderReply.ofBool (mAcc gS)))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB))]
      = 𝒟[(do let rs ← idealCacheMapM (Digest := Digest) cells c
              let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending rs.2 gS)) gFine)
                  (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
                    (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending rs.2 gS) (tag, nonce))
                    (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
                  (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                    gFine transcript sB))] := by
    rw [hmAcc]
    exact (evalDist_idealCacheMapM_bind_uniformTable_comp cells c
      (fun T => do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) T) gFine)
            (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
              (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                T (tag, nonce))
              (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
            (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
              gFine transcript sB))).symm
  -- Rewrite all three terms to their lazified forms.
  rw [probOutput_congr rfl hLHS_lazify, probOutput_congr rfl hRHS_lazify,
      probEvent_congr' (fun _ _ => Iff.rfl) hBAD_lazify]
  -- **Per-rs coupling.** All three terms now share the `idealCacheMapM cells c` head; couple
  -- them via the empty-`D` disagreement bound (mirroring the tag cases' `$ᵗ Nonce` coupling).
  -- The slacks are charged entirely in the per-rs obligation (closed in C2/C3); here `ε₁ = 0`,
  -- `ε₂ = slack₁ + slack₂ + slack₃`.
  simp only [← probEvent_eq_eq_probOutput]
  -- Regroup the RHS so the three slacks become a single trailing `ε₂` and insert `ε₁ = 0`.
  rw [show ∀ a b c d e : ℝ≥0∞, a + b + c + d + e = a + b + 0 + (c + d + e) from
        fun a b c d e => by ring]
  refine probEvent_bind_le_add_bad_disagree
    (mx := idealCacheMapM (Digest := Digest) cells c)
    (D := fun _ => False) (by simp) ?_
  intro rs hrs _
  -- **C2: per-rs facts.** Set `c₀′ := rs.2`, the cache with the slot-0 column cached.
  set c₀ := rs.2 with hc₀
  -- (a) hcInv for `c₀`: slot-positive cells are never in `cells`, so unchanged from `c`.
  have hc₀Inv : ∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
      ∀ n : Nonce, c₀ ((tag, sid), n) = none := by
    intro tag sid hsid n
    have hnotmem : ((tag, sid), n) ∉ cells := by
      rw [hcells]
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
      rintro ⟨T, hT⟩
      exact hsid (congrArg (fun p => p.1.2) hT).symm
    rw [hc₀, idealCacheMapM_cache_not_mem cells c rs hrs ((tag, sid), n) hnotmem]
    exact hcInv tag sid hsid n
  -- (b) Every slot-0 cell at column `transcript.nonce` is cached in `c₀`.
  have hc₀cached : ∀ tag : TagId,
      (c₀ ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)).isSome := by
    intro tag
    have hmem : ((tag, (0 : Fin sessionsPerTag)), transcript.nonce) ∈ cells := by
      rw [hcells]
      exact List.mem_map.mpr ⟨tag, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
    rw [hc₀]
    exact idealCacheMapM_cache_isSome_of_mem cells c rs hrs _ hmem
  -- (c) The slot-0 cell read is independent of `gS` (it is the cached value).
  have hcellConst : ∀ tag : TagId, ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      OracleComp.tableExtending c₀ gS ((tag, (0 : Fin sessionsPerTag)), transcript.nonce) =
        (c₀ ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)).getD
          (transcript.auth) := fun tag gS => by
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hc₀cached tag)
    change (c₀ ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)).getD
        (gS ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)) = _
    rw [hu]; rfl
  -- (d) The M reader bit is therefore a constant `m` independent of `gS`.
  set m : Bool := unlinkReaderAccepts (Slot := TagId)
    (fun tag _nonce => (c₀ ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)).getD
      (transcript.auth))
    (multiplePattern (TagId := TagId) sessionsPerTag) transcript with hm
  have hmConst : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      unlinkReaderAccepts (Slot := TagId)
        (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c₀ gS) (tag, nonce))
        (multiplePattern (TagId := TagId) sessionsPerTag) transcript = m := by
    intro gS
    rw [hm]
    unfold unlinkReaderAccepts tagAccepts multiplePattern
    simp only [decide_eq_decide]
    refine exists_congr fun tag => ?_
    simp only [slotZeroSubTable_apply, hcellConst tag gS]
  -- (e) Per-rs bookkeeping: `R′ := insert transcript.nonce R`.
  set R' : Finset Nonce := insert transcript.nonce R with hR'
  have hqRle' : qR' + R'.card ≤ qRInit := by
    calc qR' + R'.card ≤ qR' + (R.card + 1) :=
          Nat.add_le_add_left (Finset.card_insert_le _ _) _
      _ = qR' + 1 + R.card := by ring
      _ ≤ qRInit := hqRle
  -- (f) hRespInv-v2 for `c₀` at `R'`: off `R'` we have `n' ≠ transcript.nonce`, so the cell is
  -- not in `cells`, hence `c₀` agrees with `c` there and `sB` is unchanged by the reader step.
  have hRespInv' : ∀ tag' : TagId, ∀ n' : Nonce, n' ∉ R' →
      c₀ ((tag', (0 : Fin sessionsPerTag)), n') ≠ none →
      sB.responses (tag', n') ≠ none := by
    intro tag' n' hn'R' hne
    rw [hR', Finset.mem_insert, not_or] at hn'R'
    obtain ⟨hn'ne, hn'R⟩ := hn'R'
    have hnotmem : ((tag', (0 : Fin sessionsPerTag)), n') ∉ cells := by
      rw [hcells]
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
      rintro ⟨T, hT⟩
      exact hn'ne (congrArg (fun p => p.2) hT).symm
    rw [hc₀, idealCacheMapM_cache_not_mem cells c rs hrs _ hnotmem] at hne
    exact hRespInv tag' n' hn'R hne
  -- Rewrite the M reader bit (in LHS and BAD) to the constant `m`.
  simp only [hmConst]
  -- **m-split.**
  by_cases hmb : m = true
  · -- **Case m = true.** The S reader also accepts (slot-0 witness lifts), so for every `gS` the
    -- S bit is `true`; both sides run `k (ReaderReply.ofBool true)` at the same state, and the
    -- IH at `(c₀, qR', R')` closes it.
    have hsTrue : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
        unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun slot nonce => OracleComp.tableExtending c₀ gS (slot, nonce))
          (singlePattern (TagId := TagId) sessionsPerTag) transcript = true := by
      intro gS
      refine mReader_accepts_imp_sReader_accepts
        (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c₀ gS) transcript ?_
      rw [hmConst gS]; exact hmb
    -- Rewrite the M bit (LHS/BAD) and the S bit (RHS) to `true`.
    rw [hmb]
    simp only [hsTrue]
    -- Discard the `multipleBadReaderAdvance` perturbation of the initial state: the success
    -- bool and the bad flag both ignore `cacheBad`, so per-`gS,gFine` the run distribution is
    -- unchanged when starting from `(s, sB)` instead of `(s, advBad gFine)`.
    have hLHS_irr :
        probEvent (do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
              (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                gFine transcript sB)) (fun x => x = true)
        = probEvent (do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
              (s, sB)) (fun x => x = true) := by
      refine probEvent_bind_congr' _ _ fun gS => ?_
      refine probEvent_bind_congr' _ _ fun gFine => ?_
      refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
      -- `(z.1) <$> run = (z.1) <$> (proj <$> run)`; apply irrelevance under the outer map.
      have hirr := evalDist_simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c₀ gS)) gFine (k (ReaderReply.ofBool true)) s
        (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) sB
        sB.cacheBad rfl rfl rfl
      calc 𝒟[(fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c₀ gS)) gFine)
                (k (ReaderReply.ofBool true))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB)]
          = 𝒟[(fun z => z.1) <$> ((fun z => (z.1, z.2.1, {z.2.2 with
                cacheBad := (sB.cacheBad : Bool)})) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c₀ gS)) gFine)
                (k (ReaderReply.ofBool true))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB))] := by rw [Functor.map_map]
        _ = 𝒟[(fun z => z.1) <$> ((fun z => (z.1, z.2.1, {z.2.2 with
                cacheBad := (sB.cacheBad : Bool)})) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c₀ gS)) gFine)
                (k (ReaderReply.ofBool true))).run (s, sB))] := by
              rw [evalDist_map, hirr, ← evalDist_map]
        _ = 𝒟[(fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c₀ gS)) gFine)
                (k (ReaderReply.ofBool true))).run (s, sB)] := by
              rw [Functor.map_map]
    have hBAD_irr :
        probEvent (do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
              (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                gFine transcript sB)) (fun z => z.2.bad = true)
        = probEvent (do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
              (s, sB)) (fun z => z.2.bad = true) := by
      refine probEvent_bind_congr' _ _ fun gS => ?_
      refine probEvent_bind_congr' _ _ fun gFine => ?_
      have hirr := evalDist_simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c₀ gS)) gFine (k (ReaderReply.ofBool true)) s
        (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) sB
        sB.cacheBad rfl rfl rfl
      -- `Pr[bad | (z.1,z.2.2) <$> run]` equals `Pr[bad | proj <$> run]` since `proj` preserves
      -- the `bad` field; then apply `hirr`.
      set proj : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) →
          Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :=
        fun z => (z.1, z.2.1, {z.2.2 with cacheBad := (sB.cacheBad : Bool)}) with hproj
      set Eb : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) → Prop :=
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad = true) ∘
          (fun w => (w.1, w.2.2)) with hEb
      have hElaz : ∀ X : ProbComp (Bool × (UnlinkState TagId ×
            UnlinkBadState TagId Nonce Digest)),
          Pr[Eb | X] = Pr[Eb | proj <$> X] := fun X => by
        rw [probEvent_map]
        exact probEvent_congr' (fun _ _ => Iff.rfl) rfl
      rw [probEvent_map, probEvent_map,
          hElaz ((simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
            (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
              gFine transcript sB)),
          hElaz ((simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool true))).run
            (s, sB))]
      exact probEvent_congr' (fun _ _ => Iff.rfl) hirr
    -- Rewrite LHS-success and BAD to the unperturbed `(s, sB)` state, then apply the IH.
    rw [hLHS_irr, hBAD_irr, probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
    refine (ih (ReaderReply.ofBool true) qR' qT s c₀ sB R'
      (hqRk _) (hqTk _) hqRle' hc₀Inv hRespInv').trans ?_
    rw [show ∀ a b c d : ℝ≥0∞, a + (b + c + d) = a + b + c + d from
          fun a b c d => by ring]
    gcongr <;> exact Nat.le_succ _
  · -- **Case m = false.** M rejects (slot-0 miss). The S reader bit `sAcc gS` is exactly the
    -- slot-positive collision indicator `cacheBadReader gS transcript` (the slot-0 disjunct is
    -- ruled out by `m = false`, and slot-positive cells are uncached in `c₀` so they read raw
    -- `gS`). Its uniform-sample mass is bounded by `|TagId|·sp/|Digest|` via
    -- `probEvent_cacheBadReader_uniformSample_le`, charged to the slack₃ unit.
    replace hmb : m = false := by
      cases hm' : m with
      | false => rfl
      | true => exact absurd hm' hmb
    -- Reading an uncached slot-positive cell of `tableExtending c₀ gS` returns the raw `gS`.
    have htE : ∀ (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
        (tag : TagId) (sid : Fin sessionsPerTag), sid ≠ 0 →
        OracleComp.tableExtending c₀ gS ((tag, sid), transcript.nonce) =
          gS ((tag, sid), transcript.nonce) := fun gS tag sid hsid => by
      change (c₀ ((tag, sid), transcript.nonce)).getD _ = _
      rw [hc₀Inv tag sid hsid transcript.nonce]; rfl
    -- The S reader bit unfolds to a slot-existential over the raw table.
    have hsAccIff : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
        (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun slot nonce => OracleComp.tableExtending c₀ gS (slot, nonce))
          (singlePattern (TagId := TagId) sessionsPerTag) transcript = true)
        ↔ ∃ tag sid,
          OracleComp.tableExtending c₀ gS ((tag, sid), transcript.nonce) = transcript.auth :=
      fun gS => by
        unfold unlinkReaderAccepts tagAccepts singlePattern
        simp only [decide_eq_true_eq]
    -- (g) Under `m = false`, the S reader bit equals the slot-positive collision flag.
    have hsAccE : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
        unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun slot nonce => OracleComp.tableExtending c₀ gS (slot, nonce))
          (singlePattern (TagId := TagId) sessionsPerTag) transcript
        = cacheBadReader (sessionsPerTag := sessionsPerTag) gS transcript := by
      intro gS
      rw [Bool.eq_iff_iff, hsAccIff gS, cacheBadReader_eq_true_iff]
      constructor
      · rintro ⟨tag, sid, hcell⟩
        by_cases hsid0 : sid = 0
        · -- slot-0 ⟹ would make `m = true`, contradiction with `m = false`.
          subst hsid0
          have hmtrue : m = true := by
            rw [hm]
            unfold unlinkReaderAccepts tagAccepts multiplePattern
            simp only [decide_eq_true_eq]
            exact ⟨tag, 0, by rw [← hcellConst tag gS]; exact hcell⟩
          rw [hmb] at hmtrue; exact absurd hmtrue (by simp)
        · exact ⟨tag, sid, hsid0, by rw [← htE gS tag sid hsid0]; exact hcell⟩
      · rintro ⟨tag, sid, hsid, hcell⟩
        exact ⟨tag, sid, by rw [htE gS tag sid hsid]; exact hcell⟩
    -- Rewrite the M bit to `false` (LHS/BAD) and the actual S bit to `cacheBadReader` (RHS).
    rw [hmb]
    simp only [hsAccE]
    -- Strip the `multipleBadReaderAdvance` perturbation from the LHS-success and BAD terms: the
    -- success bool and the bad flag both ignore `cacheBad`, so per-`gS,gFine` the run
    -- distribution is unchanged when starting from `(s, sB)` instead of the advanced state.
    have hLHS_irr :
        probEvent (do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool false))).run
              (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                gFine transcript sB)) (fun x => x = true)
        = probEvent (do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool false))).run
              (s, sB)) (fun x => x = true) := by
      refine probEvent_bind_congr' _ _ fun gS => ?_
      refine probEvent_bind_congr' _ _ fun gFine => ?_
      refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
      have hirr := evalDist_simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c₀ gS)) gFine (k (ReaderReply.ofBool false)) s
        (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) sB
        sB.cacheBad rfl rfl rfl
      calc 𝒟[(fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c₀ gS)) gFine)
                (k (ReaderReply.ofBool false))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB)]
          = 𝒟[(fun z => z.1) <$> ((fun z => (z.1, z.2.1, {z.2.2 with
                cacheBad := (sB.cacheBad : Bool)})) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c₀ gS)) gFine)
                (k (ReaderReply.ofBool false))).run
                (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript sB))] := by rw [Functor.map_map]
        _ = 𝒟[(fun z => z.1) <$> ((fun z => (z.1, z.2.1, {z.2.2 with
                cacheBad := (sB.cacheBad : Bool)})) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c₀ gS)) gFine)
                (k (ReaderReply.ofBool false))).run (s, sB))] := by
              rw [evalDist_map, hirr, ← evalDist_map]
        _ = 𝒟[(fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                z.1) <$>
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c₀ gS)) gFine)
                (k (ReaderReply.ofBool false))).run (s, sB)] := by
              rw [Functor.map_map]
    have hBAD_irr :
        probEvent (do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool false))).run
              (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                gFine transcript sB)) (fun z => z.2.bad = true)
        = probEvent (do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool false))).run
              (s, sB)) (fun z => z.2.bad = true) := by
      refine probEvent_bind_congr' _ _ fun gS => ?_
      refine probEvent_bind_congr' _ _ fun gFine => ?_
      have hirr := evalDist_simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant
        (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c₀ gS)) gFine (k (ReaderReply.ofBool false)) s
        (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) sB
        sB.cacheBad rfl rfl rfl
      set proj : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) →
          Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :=
        fun z => (z.1, z.2.1, {z.2.2 with cacheBad := (sB.cacheBad : Bool)}) with hproj
      set Eb : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) → Prop :=
        (fun w : Bool × UnlinkBadState TagId Nonce Digest => w.2.bad = true) ∘
          (fun w => (w.1, w.2.2)) with hEb
      have hElaz : ∀ X : ProbComp (Bool × (UnlinkState TagId ×
            UnlinkBadState TagId Nonce Digest)),
          Pr[Eb | X] = Pr[Eb | proj <$> X] := fun X => by
        rw [probEvent_map]
        exact probEvent_congr' (fun _ _ => Iff.rfl) rfl
      rw [probEvent_map, probEvent_map,
          hElaz ((simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool false))).run
            (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
              gFine transcript sB)),
          hElaz ((simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag)
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c₀ gS)) gFine) (k (ReaderReply.ofBool false))).run
            (s, sB))]
      exact probEvent_congr' (fun _ _ => Iff.rfl) hirr
    rw [hLHS_irr, hBAD_irr, probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
    refine (ih (ReaderReply.ofBool false) qR' qT s c₀ sB R'
      (hqRk _) (hqTk _) hqRle' hc₀Inv hRespInv').trans ?_
    -- **Asymmetric discard.** Replace the S reader bit `false` by its actual value
    -- `cacheBadReader gS`. For every `gS` with `cacheBadReader gS = false` the bit is `false`
    -- and the two S-runs coincide; for the rest, drop the `false`-run summand (≤ 1) and charge
    -- its uniform mass to the `E`-event. The `E`-mass is `≤ |TagId| * sessionsPerTag / |Digest|`.
    have hEmass :
        Pr[fun b : Bool => b = true | do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gS transcript)] ≤
          ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞) :=
      probEvent_cacheBadReader_uniformSample_le (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) transcript
    have hDiscard :
        Pr[= true | do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (singleTableHandler (OracleComp.tableExtending c₀ gS))
              (k (ReaderReply.ofBool false))).run' s] ≤
          Pr[= true | do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (singleTableHandler (OracleComp.tableExtending c₀ gS))
              (k (ReaderReply.ofBool
                (cacheBadReader (sessionsPerTag := sessionsPerTag) gS transcript)))).run' s] +
          ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞) := by
      refine le_trans ?_ (add_le_add_right hEmass _)
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, probEvent_bind_eq_tsum,
        ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun gS => ?_
      rw [← mul_add]
      gcongr _ * ?_
      by_cases hcb : cacheBadReader (sessionsPerTag := sessionsPerTag) gS transcript = true
      · -- `E gS`: drop the `false`-run summand (`Pr ≤ 1`); charge it to the `E` term, which is
        -- `1` here.
        rw [hcb, probEvent_pure_eq_indicator]
        simp only [Set.indicator, Set.mem_setOf_eq, if_true]
        exact probOutput_le_one.trans le_add_self
      · -- `¬E gS`: `cacheBadReader gS = false`, so the actual S-run uses the bit `false`, the two
        -- summands coincide, and the `E` term is `0`.
        rw [Bool.not_eq_true] at hcb
        rw [hcb, probEvent_pure_eq_indicator]
        simp only [Set.indicator, Set.mem_setOf_eq, reduceCtorEq, if_false, add_zero, le_refl]
    -- Flatten the right-hand slack and split the `(qR'+1)` units so the discard's `T·sp/|D|`
    -- and the `≤`-monotone `qR' ≤ qR'+1` headroom land in their own summands.
    have hsplitR : ((qR' + 1) * Fintype.card TagId : ℕ) =
        (qR' * Fintype.card TagId : ℕ) + Fintype.card TagId := by ring
    have hsplitC : ((qR' + 1) * Fintype.card TagId * sessionsPerTag : ℕ) =
        (qR' * Fintype.card TagId * sessionsPerTag : ℕ) +
          Fintype.card TagId * sessionsPerTag := by ring
    rw [hsplitC, hsplitR, Nat.cast_add, Nat.cast_add, ENNReal.add_div, ENNReal.add_div]
    -- The discard's `T·sp/|D|` charge pairs with the `qR'+1 = qR'+1` headroom unit on the
    -- `C`-slack; the extra `T/|D|` unit on the `A`-slack is pure (≥ 0) headroom.
    set S0 : ℝ≥0∞ := Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (OracleComp.tableExtending c₀ gS))
          (k (ReaderReply.ofBool false))).run' s] with hS0
    set Scb : ℝ≥0∞ := Pr[= true | do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (OracleComp.tableExtending c₀ gS))
          (k (ReaderReply.ofBool
            (cacheBadReader (sessionsPerTag := sessionsPerTag) gS transcript)))).run' s] with hScb
    set BADt : ℝ≥0∞ := probEvent (do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine (slotZeroSubTable (sessionsPerTag :=
            sessionsPerTag) (OracleComp.tableExtending c₀ gS)) gFine)
            (k (ReaderReply.ofBool false))).run (s, sB)) (fun z => z.2.bad = true) with hBADt
    set Tsp : ℝ≥0∞ := ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
      (Fintype.card Digest : ℝ≥0∞) with hTsp
    set A : ℝ≥0∞ := ((qR' * Fintype.card TagId : ℕ) : ℝ≥0∞) /
      (Fintype.card Digest : ℝ≥0∞) with hA
    set Td : ℝ≥0∞ := (Fintype.card TagId : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) with hTd
    set B : ℝ≥0∞ := ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) with hB
    set C : ℝ≥0∞ := ((qR' * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
      (Fintype.card Digest : ℝ≥0∞) with hC
    -- Goal: `S0 + BADt + A + B + C ≤ Scb + BADt + (A + Td) + B + (C + Tsp)`.
    calc S0 + BADt + A + B + C
        ≤ (Scb + Tsp) + BADt + A + B + C := by gcongr
      _ ≤ Scb + BADt + (A + Td) + B + (C + Tsp) := by
          rw [show (Scb + Tsp) + BADt + A + B + C
                = Scb + BADt + A + B + (C + Tsp) from by ring,
              show Scb + BADt + (A + Td) + B + (C + Tsp)
                = (Scb + BADt + A + B + (C + Tsp)) + Td from by ring]
          exact le_self_add
      _ = Scb + BADt + (A + Td + B + (C + Tsp)) := by ring

end UnlinkReduction

end DirectCouplingCompose

end PRFTagReader
