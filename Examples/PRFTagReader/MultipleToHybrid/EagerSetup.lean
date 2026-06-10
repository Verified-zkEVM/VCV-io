/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.MultipleToHybrid.Setup

/-!
# PRF Tag/Reader Protocol — Multiple-to-hybrid eager coupling, shared setup

Shared definitions and helpers for the eager-table multiple-vs-hybrid coupling proof. This
module hosts:

* the reader-side cell-collision predicate `cacheBadReader` with its Boolean characterizations,
  and the reader-side bad-state advance `multipleBadReaderAdvance` that ORs it into the
  `cacheBad` flag;
* the deterministic-table instrumented multiple-session handler `multipleBadTableHandler` and
  its fine-grained companion `multipleBadTableHandlerFine`, with their per-step / per-run
  bad-flag monotonicity lemmas;
* the per-step uniform-table bound `probEvent_cacheBadReader_uniformSample_le` on
  `cacheBadReader` at a freshly sampled fine table;
* the eager equivalence
  `evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending` lifting the lazy-vs-eager
  equivalence to the instrumented handler;
* the Fine→original bridges
  `evalDist_simulateQ_multipleBadTableHandler_cacheBad_irrelevant` and
  `evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_eq`, showing the `cacheBad`
  field is invisible to the original handler and marginalizes away from the Fine handler.

These shared definitions and bridges supply the eager-table instrumentation consumed by the
direct-coupling headline in `DirectCoupling.Compose`.
-/

open OracleComp OracleSpec ENNReal

namespace PRFTagReader

section UnlinkReduction

variable {TagId Nonce Digest K : Type}
  [DecidableEq TagId] [Fintype TagId] [Nonempty TagId]
  [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [SampleableType Digest]
  {sessionsPerTag : ℕ} [NeZero sessionsPerTag]

/-! ### Reader-side cell-collision predicate

`cacheBadReader T transcript` is the deterministic Boolean predicate that holds at the queried
reader transcript `⟨nonce, auth⟩` against an eager fine-grained table `T` exactly when *some*
slot-positive cell at the queried nonce already carries the queried auth. Under the slot-zero
embedding, only slot-zero cells are M-reachable, so a slot-positive collision is an
M-rejects / S-accepts witness in the coupled-table comparison of `DirectCoupling/Compose.lean`.

This is the deterministic per-reader-step indicator that is OR-accumulated into the `cacheBad`
flag of the bad state via `multipleBadReaderAdvance`. With the bad-state field in place,
`Pr[cacheBad]` absorbs the reader-cell asymmetry slack as a separate bad-mass term, mirroring
how `Pr[bad]` absorbs the tag-side nonce-collision mass.

Lives in this module (rather than `DirectCoupling.Compose`) so that the instrumented fine handler
`multipleBadTableHandlerFine` defined below can reach it without inducing an import cycle. -/
def cacheBadReader [Fintype TagId]
    (T : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (t : TagTranscript Nonce Digest) : Bool :=
  decide (∃ tag : TagId, ∃ sid : Fin sessionsPerTag, sid ≠ 0 ∧ T ((tag, sid), t.nonce) = t.auth)

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- **`cacheBadReader = true` characterization.** Unfolds the `decide` wrapper to its
existential form, exposing the slot-positive witness used by the structural bridges in
`DirectCoupling/Compose.lean`. -/
lemma cacheBadReader_eq_true_iff
    (T : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (t : TagTranscript Nonce Digest) :
    cacheBadReader (sessionsPerTag := sessionsPerTag) T t = true ↔
      ∃ tag : TagId, ∃ sid : Fin sessionsPerTag, sid ≠ 0 ∧ T ((tag, sid), t.nonce) = t.auth := by
  unfold cacheBadReader; exact decide_eq_true_iff

/-- Reader-step bad-state advance: OR `cacheBadReader gFine transcript` into the `cacheBad`
flag, leaving every other field of the bad state untouched. This is the reader-side analogue of
`multipleBadAdvance`, but mutating `cacheBad` instead of `bad`. The two flags are independent:
reader steps never touch `bad`, tag steps never touch `cacheBad`. -/
def multipleBadReaderAdvance [Fintype TagId]
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) : UnlinkBadState TagId Nonce Digest :=
  { sB with cacheBad := sB.cacheBad ||
      cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript }

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- `multipleBadReaderAdvance` preserves the tag-side `bad` flag (it only ORs into `cacheBad`). -/
@[simp] lemma multipleBadReaderAdvance_bad
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB).bad =
      sB.bad := rfl

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- `multipleBadReaderAdvance` preserves `sessionsUsed`. -/
@[simp] lemma multipleBadReaderAdvance_sessionsUsed
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB).sessionsUsed =
      sB.sessionsUsed := rfl

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- `multipleBadReaderAdvance` preserves `responses`. -/
@[simp] lemma multipleBadReaderAdvance_responses
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB).responses =
      sB.responses := rfl

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- **`cacheBad` projection through `multipleBadReaderAdvance`.** The post-advance `cacheBad`
flag equals the pre-advance flag OR the `cacheBadReader` predicate. Definitional rewrite
extracted as a `@[simp]` lemma so inductive `cacheBad`-probability arguments can split on
whether the reader step flipped the bit. -/
@[simp] lemma multipleBadReaderAdvance_cacheBad
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB).cacheBad =
      (sB.cacheBad || cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript) := rfl

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- **`cacheBad`-false characterization of `multipleBadReaderAdvance`.** The post-advance
`cacheBad = false` iff both the pre-advance flag and the `cacheBadReader` predicate are `false`.
Direct corollary of `multipleBadReaderAdvance_cacheBad`, for case-splitting on whether the
current reader step flipped the bit. -/
lemma multipleBadReaderAdvance_cacheBad_eq_false_iff
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) :
    (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB).cacheBad =
        false ↔
      sB.cacheBad = false ∧
        cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript = false := by
  rw [multipleBadReaderAdvance_cacheBad]
  exact Bool.or_eq_false_iff

/-! ### Multiple-to-hybrid: the eager-table instrumented multiple handler

A lazy `Prop`-valued state-coupling induction cannot encode the run-determined session index that
a later tag query reads back, so the coupling bound is established on the eager route instead, by
sampling the random-oracle table up front.

`multipleBadTableHandler g` is the deterministic-table instrumented multiple handler: it runs the
deterministic real handler `multipleTableHandler g` on the multiple-ideal component and threads the
bad-world `UnlinkBadState` via `multipleBadAdvance` exactly as `multipleBadQueryImpl` does. The
eager equivalence `evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending` lifts the
lazy-vs-eager equivalence to the instrumented handler, threading the bad state. -/

/-- Deterministic-table instrumented multiple-session handler: runs `multipleTableHandler g` on the
multiple-ideal component (now just `UnlinkState`) and, on a tag query, advances the bad-world
component via `multipleBadAdvance`. The eager-table analogue of `multipleBadQueryImpl`. -/
noncomputable def multipleBadTableHandler (g : TagId × Nonce → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag =>
        (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1 >>= fun r =>
          pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)
    | Sum.inr transcript =>
        (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r =>
          pure (r.1, r.2, p.2)

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- `simulateQ multipleBadTableHandler` of a `query_bind`, run from a state and projected to its
full output. -/
lemma multipleBadTable_run_query_bind' {α : Type} (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g) (liftM (OracleSpec.query t) >>= f)).run s =
      (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g t s) >>= fun p =>
        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Eager-table single-step bad monotonicity.** If the bad flag is already set in the
multiple-bad state `p.2`, then every reachable output of `multipleBadTableHandler g t p` keeps
`bad = true`. The eager-table analogue of `multipleBadQueryImpl_step_preserves_bad`; the proof
case-splits on tag vs. reader and unfolds `multipleBadAdvance`. -/
lemma multipleBadTableHandler_step_preserves_bad (g : TagId × Nonce → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g t p), z.2.2.bad = true := by
  cases t with
  | inl tag =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1
        >>= fun r => pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    cases hr : r.1 <;> simp [multipleBadAdvance, hbad]
  | inr transcript =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1
        >>= fun r => pure (r.1, r.2, p.2)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    exact hbad

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Eager-table full-run bad monotonicity.** Starting `simulateQ multipleBadTableHandler` from a
state whose bad flag is set, every reachable output keeps `bad = true`. The eager-table analogue of
`multipleBadQueryImpl_run_preserves_bad`. -/
lemma multipleBadTableHandler_run_preserves_bad {α : Type} (g : TagId × Nonce → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support ((simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) oa).run p), z.2.2.bad = true :=
  OracleComp.simulateQ_run_preservesInv
    (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) g)
    (fun s : UnlinkState TagId × UnlinkBadState TagId Nonce Digest => s.2.bad = true)
    (fun t s h z hz => multipleBadTableHandler_step_preserves_bad g t s h z hz) oa p hbad

/-! ### Fine-grained eager handler

`multipleBadTableHandlerFine g gFine` is a *parallel* eager handler that runs identical M-side
dynamics to `multipleBadTableHandler g` (same coarse table `g : TagId × Nonce → Digest` for the
multiple-ideal output computation, so output-distribution-equivalent) but additionally threads a
fine-grained eager table `gFine : (TagId × Fin sessionsPerTag) × Nonce → Digest` through the
reader branch to advance the `cacheBad` flag via `multipleBadReaderAdvance`.

The instrumented variant is invariant on the `bad` flag, on the multiple-ideal output, and on
`sessionsUsed` / `responses`; it only differs from `multipleBadTableHandler` in the `cacheBad`
field of the bad state on the reader branch.

The per-step uniform-table bound `probEvent_cacheBadReader_uniformSample_le` below controls
the probability that a single reader step of this handler flips `cacheBad` at a freshly
sampled fine table. -/
noncomputable def multipleBadTableHandlerFine
    (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest) :
    QueryImpl (UnlinkOracleSpec TagId Nonce Digest)
      (StateT (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) ProbComp) :=
  fun q => fun p => match q with
    | Sum.inl tag =>
        (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1 >>= fun r =>
          pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)
    | Sum.inr transcript =>
        (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r =>
          pure (r.1, r.2,
            multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript p.2)

omit [Nonempty TagId] [SampleableType Digest] in
/-- `simulateQ multipleBadTableHandlerFine` of a `query_bind`, run from a state. Analogue of
`multipleBadTable_run_query_bind'`. -/
lemma multipleBadTableFine_run_query_bind' {α : Type} (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (f : (UnlinkOracleSpec TagId Nonce Digest).Range t →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g gFine) (liftM (OracleSpec.query t) >>= f)).run s =
      (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g gFine t s) >>= fun p =>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g gFine) (f p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Fine eager-table single-step bad monotonicity.** If `bad` is set in the multiple-bad state
`p.2`, every reachable output of `multipleBadTableHandlerFine g gFine t p` keeps `bad = true`. The
reader branch ORs into `cacheBad` but never touches `bad`. -/
lemma multipleBadTableHandlerFine_step_preserves_bad (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (t : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) g gFine t p), z.2.2.bad = true := by
  cases t with
  | inl tag =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1
        >>= fun r => pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    change (multipleBadAdvance tag p.2 r.1).bad = true
    rcases r.1 with _ | tr
    · exact hbad
    · change (p.2.bad || _ : Bool) = true
      rw [hbad, Bool.true_or]
  | inr transcript =>
    intro z hz
    change z ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1
        >>= fun r => pure (r.1, r.2,
          multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript p.2)) at hz
    obtain ⟨r, _, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    rw [mem_support_pure_iff] at hz
    subst hz
    change (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
      gFine transcript p.2).bad = true
    rw [multipleBadReaderAdvance_bad]; exact hbad

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Fine eager-table full-run bad monotonicity.** Starting `simulateQ multipleBadTableHandlerFine`
from a state whose `bad` flag is set, every reachable output keeps `bad = true`. -/
lemma multipleBadTableHandlerFine_run_preserves_bad {α : Type} (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (hbad : p.2.bad = true) :
    ∀ z ∈ support ((simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run p),
        z.2.2.bad = true :=
  OracleComp.simulateQ_run_preservesInv
    (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
      (sessionsPerTag := sessionsPerTag) g gFine)
    (fun s : UnlinkState TagId × UnlinkBadState TagId Nonce Digest => s.2.bad = true)
    (fun t s h z hz => multipleBadTableHandlerFine_step_preserves_bad g gFine t s h z hz) oa p hbad

/-! ### Per-step uniform-table `cacheBadReader` bound -/

omit [DecidableEq TagId] [Fintype TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [DecidableEq Digest] [NeZero sessionsPerTag] in
/-- **Single-cell marginal at a uniform function.** Drawing a uniform function `gFine` and
reading off its value at a fixed cell `x` produces a uniform digest, so any specific value `v`
appears with probability `1 / |Digest|`.

This is a consequence of the marginalization lemma
`OracleComp.evalDist_uniformSample_bind_update_map`: rewriting a uniform function as the
post-composition of a fresh uniform value at `x` with a uniform function at the remaining cells. -/
lemma probOutput_uniformSample_fun_eval [Finite TagId] [Finite Nonce] [Fintype Digest]
    [Nonempty Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (x : (TagId × Fin sessionsPerTag) × Nonce) (v : Digest) :
    Pr[= v | do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
                pure (gFine x)] =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  -- Bridge via `evalDist_uniformSample_bind_update_map` at the cell `x`, with `ψ = fun g => g x`.
  have hbridge :=
    OracleComp.evalDist_uniformSample_bind_update_map
      (D := (TagId × Fin sessionsPerTag) × Nonce) (R := Digest) x (fun g => g x)
  have hLHS :
      (do let u ← ($ᵗ Digest); let g ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
          pure ((Function.update g x u) x))
        = (do let u ← ($ᵗ Digest); let _g ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
              pure u) := by
    refine bind_congr fun u => bind_congr fun g => ?_
    rw [Function.update_self]
  rw [hLHS] at hbridge
  -- Use the equivalence on `Pr[= v |...]` to convert the target to `Pr[= v | $ᵗ Digest]`.
  have htarget : Pr[= v | do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
                              pure (gFine x)] =
                 Pr[= v | do let u ← ($ᵗ Digest);
                              let _g ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
                              pure u] := probOutput_congr rfl hbridge.symm
  rw [htarget]
  -- Eliminate the unused `_g` bind: probability factors as `Pr[= v | $ᵗ Digest] * 1`.
  rw [probOutput_bind_eq_tsum]
  have hinner : ∀ u : Digest,
      Pr[= v | (do let _g ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)); pure u)]
        = Pr[= v | (pure u : ProbComp Digest)] := fun u => by
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  simp_rw [hinner]
  -- ∑' u, Pr[= u | $ᵗ Digest] * Pr[= v | pure u] = Pr[= v | $ᵗ Digest]
  rw [show (∑' u : Digest, Pr[= u | ($ᵗ Digest)] * Pr[= v | (pure u : ProbComp Digest)]) =
        Pr[= v | (do let u ← ($ᵗ Digest); pure u : ProbComp Digest)]
      from (probOutput_bind_eq_tsum _ _ _).symm]
  rw [bind_pure, probOutput_uniformSample]

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce] in
/-- **Per-step uniform-table bound on `cacheBadReader`.** Sampling a uniform fine-grained
table `gFine` and checking `cacheBadReader gFine transcript`, the probability of a hit is
bounded by `|TagId| * sessionsPerTag / |Digest|`.

The proof is a union bound over the cell set `TagId × Fin sessionsPerTag` (existence in a
finset), where each summand is the single-cell marginal `1 / |Digest|` from
`probOutput_uniformSample_fun_eval`. The `sid ≠ 0` filter is dropped by monotonicity, giving
the slightly loose `|TagId| * sessionsPerTag` bound (rather than the tight
`|TagId| * (sessionsPerTag - 1)`). -/
lemma probEvent_cacheBadReader_uniformSample_le [Finite Nonce] [Fintype Digest]
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (transcript : TagTranscript Nonce Digest) :
    Pr[fun b : Bool => b = true |
        do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
           pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript)] ≤
      ((Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  haveI : Nonempty Digest := ⟨(SampleableType.selectElem (β := Digest)).defaultResult⟩
  -- Step 1: expand the predicate. `cacheBadReader g t = true` is `∃ tag sid, sid ≠ 0 ∧
  -- g((tag,sid), t.nonce) = t.auth`; drop the `sid ≠ 0` filter by monotonicity.
  set P : (((TagId × Fin sessionsPerTag) × Nonce) → Digest) → Prop :=
    fun gFine => ∃ slot : TagId × Fin sessionsPerTag, slot ∈
      (Finset.univ : Finset (TagId × Fin sessionsPerTag)) ∧
      gFine (slot, transcript.nonce) = transcript.auth with hP
  have hmono :
      Pr[fun b : Bool => b = true |
          do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
             pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript)] ≤
        Pr[fun gFine => P gFine |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] := by
    -- Direct via `probEvent_mono` once we rewrite the LHS into a `Pr[.. | $ᵗ]` form.
    rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite (p := fun gFine => P gFine)]
    refine ENNReal.tsum_le_tsum fun gFine => ?_
    -- Inner factor:
    -- `Pr[(b=true) | pure (cacheBadReader gFine t)] = if cacheBadReader gFine t then 1 else 0`
    have hinner :
        Pr[fun b : Bool => b = true |
            (pure (cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript)
              : ProbComp Bool)] =
          (if cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript = true
            then (1 : ℝ≥0∞) else 0) := by
      simp
    rw [hinner]
    by_cases hcb : cacheBadReader (sessionsPerTag := sessionsPerTag) gFine transcript = true
    · rw [if_pos hcb, mul_one, if_pos]
      unfold cacheBadReader at hcb
      rw [decide_eq_true_eq] at hcb
      obtain ⟨tag, sid, _, hg⟩ := hcb
      exact ⟨(tag, sid), Finset.mem_univ _, hg⟩
    · rw [if_neg hcb, mul_zero]; exact zero_le
  refine hmono.trans ?_
  -- Step 2: union bound over the slot set.
  have hsum :
      Pr[fun gFine => P gFine |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] ≤
        ∑ slot ∈ (Finset.univ : Finset (TagId × Fin sessionsPerTag)),
          Pr[fun gFine => gFine (slot, transcript.nonce) = transcript.auth |
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))] := by
    simpa [P] using probEvent_exists_finset_le_sum
      (s := (Finset.univ : Finset (TagId × Fin sessionsPerTag)))
      (mx := ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)))
      (E := fun slot gFine => gFine (slot, transcript.nonce) = transcript.auth)
  refine hsum.trans ?_
  -- Step 3: each summand equals `1 / |Digest|` via the single-cell marginal.
  have hcell : ∀ slot : TagId × Fin sessionsPerTag,
      Pr[fun gFine => gFine (slot, transcript.nonce) = transcript.auth |
          ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))]
        = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
    intro slot
    -- Rewrite the probEvent as `Pr[= transcript.auth | g ←$ᵗ; pure (g (slot, nonce))]`
    -- via the bind/map bridge, then apply the single-cell marginal.
    have hkey :
        Pr[fun gFine => gFine (slot, transcript.nonce) = transcript.auth |
            ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest))]
          = Pr[= transcript.auth |
              do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
                 pure (gFine (slot, transcript.nonce))] := by
      rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite]
      refine tsum_congr fun gFine => ?_
      by_cases h : gFine (slot, transcript.nonce) = transcript.auth
      · simp [h, probOutput_pure]
      · simp only [h, ite_false, probOutput_pure]
        rw [if_neg (fun heq => h heq.symm), mul_zero]
    rw [hkey]
    exact probOutput_uniformSample_fun_eval (slot, transcript.nonce) transcript.auth
  rw [Finset.sum_congr rfl (fun slot _ => hcell slot)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [nsmul_eq_mul]
  rw [ENNReal.div_eq_inv_mul, Nat.cast_mul]
  rw [show (((Fintype.card Digest : ℝ≥0∞)⁻¹ *
    ((Fintype.card TagId : ℝ≥0∞) * (sessionsPerTag : ℝ≥0∞))))
      = ((Fintype.card TagId : ℝ≥0∞) * (sessionsPerTag : ℝ≥0∞) *
          (Fintype.card Digest : ℝ≥0∞)⁻¹) by ring]

omit [Nonempty TagId] in
/-- **Eager-table equivalence for the instrumented multiple handler.** Running the instrumented
multiple handler `multipleBadQueryImpl` from `((s, c), sB)` has the same *full-output* distribution
(output bit, multiple-ideal state and bad-world state) as sampling a full random-oracle table `g`,
overlaying the cache `c`, and running the deterministic instrumented table handler
`multipleBadTableHandler (tableExtending c g)` from `(s, sB)`.

Proved by induction on the adversary, generalized over the state. It mirrors
`evalDist_simulateQ_multipleIdealQueryImpl_run'_eq_tableExtending`, threading the bad-world
component (which `multipleBadAdvance` advances deterministically from the realized transcript). -/
lemma evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending
    [Fintype Nonce] [Finite Digest]
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) :
    𝒟[(fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => (z.1, z.2.2)) <$>
        (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag)) oa).run ((s, c), sB)] =
      𝒟[do let g ← $ᵗ (TagId × Nonce → Digest);
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                (OracleComp.tableExtending c g)) oa).run (s, sB)] := by
  classical
  induction oa using OracleComp.inductionOn generalizing s c sB with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    refine (evalDist_ext fun x => ?_).symm
    rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  | query_bind t f ih =>
    rw [multipleBad_run_query_bind', map_bind]
    have hrhs : 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
          (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
              (z.1, z.2.2)) <$>
            (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c g))
              (liftM (OracleSpec.query t) >>= f)).run (s, sB)]
        = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
            (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g) t (s, sB))
              >>= fun p =>
              (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c g)) (f p.1)).run p.2] := by
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      rw [multipleBadTable_run_query_bind', map_bind]
    rw [hrhs]
    cases t with
    | inl tag =>
      by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · -- tag query, slot available
        rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)]
        dsimp only
        rw [multipleIdealQueryImpl_tag_run_of_lt tag s c hslot]
        set advU :=
          ({ s with sessionsUsed := Function.update s.sessionsUsed tag (s.sessionsUsed tag + 1) } :
            UnlinkState TagId) with hadvU
        -- Normalise the LHS: pull the nonce/cell binds to the top.
        have hlhs_norm :
            ((((($ᵗ Nonce) >>= fun nonce => idealCacheStep c (tag, nonce) >>= fun r =>
              pure (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest), advU, r.2))) >>=
              fun r => pure (r.1, (r.2.1, r.2.2), multipleBadAdvance tag sB r.1)) >>=
              fun p => (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                (z.1, z.2.2)) <$>
                (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2)
            = (($ᵗ Nonce) >>= fun nonce => idealCacheStep c (tag, nonce) >>= fun r =>
                (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))).run
                    ((advU, r.2), multipleBadAdvance tag sB
                      (some (⟨nonce, r.1⟩ : TagTranscript Nonce Digest)))) := by
          simp only [bind_assoc, pure_bind]
        refine (congrArg evalDist hlhs_norm).trans ?_
        -- per-nonce eager equivalence under the inner idealCacheStep
        have hlhs_inner : ∀ (n : Nonce),
            𝒟[idealCacheStep c (tag, n) >>= fun r =>
                (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))).run
                    ((advU, r.2), multipleBadAdvance tag sB
                      (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))]
            = 𝒟[($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                  (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                      (z.1, z.2.2)) <$>
                    (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                      (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                      (OracleComp.tableExtending c g))
                      (f (some (⟨n, OracleComp.tableExtending c g (tag, n)⟩ :
                        TagTranscript Nonce Digest)))).run
                      (advU, multipleBadAdvance tag sB (some (⟨n,
                        OracleComp.tableExtending c g (tag, n)⟩ :
                        TagTranscript Nonce Digest)))] := by
          intro n
          set Mψ : (TagId × Nonce → Digest) → ProbComp (Bool × UnlinkBadState TagId Nonce Digest) :=
            fun g' =>
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
                (f (some (⟨n, g' (tag, n)⟩ : TagTranscript Nonce Digest)))).run
                (advU, multipleBadAdvance tag sB
                  (some (⟨n, g' (tag, n)⟩ : TagTranscript Nonce Digest)))
            with hMψ
          refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp c (tag, n) Mψ)
          refine evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
          rw [ih (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)) advU r.2
            (multipleBadAdvance tag sB (some (⟨n, r.1⟩ : TagTranscript Nonce Digest)))]
          refine congrArg _ (congrArg _ (funext fun g => ?_))
          have hcell : OracleComp.tableExtending r.2 g (tag, n) = r.1 := by
            simp only [OracleComp.tableExtending,
              idealCacheStep_cache_self c (tag, n) r hr, Option.getD_some]
          rw [hMψ]
          simp only [hcell]
        -- RHS: collapse the table-handler tag query and swap the two samples.
        have hrhs_swap :
            (($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
              (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
                (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)
                (Sum.inl tag) (s, sB)) >>= fun p =>
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c g)) (f p.1)).run p.2)
            = (($ᵗ (TagId × Nonce → Digest)) >>= fun g => ($ᵗ Nonce) >>= fun n =>
                (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                    (z.1, z.2.2)) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag)
                    (OracleComp.tableExtending c g))
                    (f (some (⟨n, OracleComp.tableExtending c g (tag, n)⟩ :
                      TagTranscript Nonce Digest)))).run
                    (advU, multipleBadAdvance tag sB (some (⟨n,
                      OracleComp.tableExtending c g (tag, n)⟩ :
                      TagTranscript Nonce Digest)))) := by
          refine bind_congr fun g => ?_
          change ((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)
              (Sum.inl tag)) s >>= (fun r => pure (r.1, r.2,
                multipleBadAdvance tag sB r.1))) >>= _ = _
          rw [multipleTableHandler_tag_run_of_lt _ tag s hslot, ← hadvU]
          simp only [bind_assoc, pure_bind]
          exact bind_assoc ..
        refine Eq.trans ?_ (congrArg evalDist hrhs_swap).symm
        rw [evalDist_probComp_bind_comm ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce)]
        refine evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        exact hlhs_inner n
      · -- tag query, slot exhausted
        rw [multipleBadQueryImpl_tag_run tag ((s, c), sB)]
        dsimp only
        rw [multipleIdealQueryImpl_tag_run_of_not_lt tag s c hslot]
        change 𝒟[(fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
            (z.1, z.2.2)) <$>
            (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f none)).run
              ((s, c), multipleBadAdvance tag sB none)] = _
        rw [ih none s c (multipleBadAdvance tag sB none)]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        change _ = ((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)
            (Sum.inl tag)) s >>= (fun r => pure (r.1, r.2,
              multipleBadAdvance tag sB r.1))) >>= _
        rw [multipleTableHandler_tag_run_of_not_lt _ tag s hslot]
        rfl
    | inr transcript =>
      rw [multipleBadQueryImpl_reader_run transcript ((s, c), sB)]
      dsimp only
      rw [multipleIdealQueryImpl_reader_run transcript s c]
      set cells := (Finset.univ : Finset TagId).toList.map
        (fun tag => (tag, transcript.nonce)) with hcells
      -- Normalise the LHS: pull all binds outward, projection at the leaf.
      have hlhs_norm :
          (((idealCacheMapM cells c >>= fun rs =>
                pure (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth)), s, rs.2))
              >>= fun r => pure (r.1, (r.2.1, r.2.2), sB)) >>= fun p =>
              (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag)) (f p.1)).run p.2)
          = (idealCacheMapM cells c >>= fun rs =>
              (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                  (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                  (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run
                  ((s, rs.2), sB)) := by
        simp only [bind_assoc]; rfl
      refine (congrArg evalDist hlhs_norm).trans ?_
      -- eager equivalence under idealCacheMapM
      set Mψ : (TagId × Nonce → Digest) → ProbComp (Bool × UnlinkBadState TagId Nonce Digest) :=
        fun g' =>
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) g')
            (f (ReaderReply.ofBool (decide (∃ d ∈ cells.map g', d = transcript.auth))))).run
            (s, sB)
        with hMψ
      have hstep1 :
          𝒟[idealCacheMapM cells c >>= fun rs =>
              (fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag =>
                  (z.1, z.2.2)) <$>
                (simulateQ (multipleBadQueryImpl (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag))
                (f (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))))).run
                ((s, rs.2), sB)]
          = 𝒟[idealCacheMapM cells c >>= fun rs =>
              ($ᵗ (TagId × Nonce → Digest)) >>= fun g =>
                Mψ (OracleComp.tableExtending rs.2 g)] := by
        refine evalDist_bind_congr_of_support _ _ _ fun rs hrs => ?_
        rw [ih (ReaderReply.ofBool (decide (∃ d ∈ rs.1, d = transcript.auth))) s rs.2 sB]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        rw [hMψ]
        simp only [idealCacheMapM_support cells c rs hrs g]
      rw [hstep1, evalDist_idealCacheMapM_bind_uniformTable_comp cells c Mψ]
      -- RHS: collapse the table-handler reader query
      refine (evalDist_bind_congr_of_support _ _ _ fun g _ => ?_).symm
      have hrhs_reader : (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c g) (Sum.inr transcript) (s, sB))
          = pure (ReaderReply.ofBool (unlinkReaderAccepts (TagId := TagId) (Slot := TagId)
              (Nonce := Nonce) (Digest := Digest)
              (fun tag nonce => OracleComp.tableExtending c g (tag, nonce))
              (multiplePattern (TagId := TagId) sessionsPerTag) transcript), s, sB) := by
        change (multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c g)
            (Sum.inr transcript)) s >>= _ = _
        rw [multipleTableHandler_reader_run _ transcript s]; rfl
      rw [hrhs_reader, hMψ]
      have hAccept : decide (∃ d ∈ cells.map (OracleComp.tableExtending c g),
            d = transcript.auth)
          = unlinkReaderAccepts (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
            (fun tag nonce => OracleComp.tableExtending c g (tag, nonce))
            (multiplePattern (TagId := TagId) sessionsPerTag) transcript := by
        unfold unlinkReaderAccepts tagAccepts
        rw [hcells]
        simp only [List.map_map, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
          multiplePattern, decide_eq_decide, decide_eq_true_eq, Function.comp]
        constructor
        · rintro ⟨d, ⟨a, rfl⟩, hd⟩
          exact ⟨a, ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne sessionsPerTag)⟩, hd⟩⟩
        · rintro ⟨tag, _, hd⟩
          exact ⟨_, ⟨tag, rfl⟩, hd⟩
      rw [← hAccept]
      rfl

/-! ### Fine→original eager-table bridge

The Fine handler `multipleBadTableHandlerFine g gFine` agrees with the original
`multipleBadTableHandler g` on every field of the bad state EXCEPT `cacheBad`. Projecting that
field away — i.e. overwriting the output bad-state's `cacheBad` with an arbitrary constant `cb` —
the two handlers produce identical distributions, even pointwise in the outer `gFine` sample.

Together with the constancy of `cacheBad` along original-handler runs, this yields the headline
bridge: marginalizing the Fine-run distribution over `cacheBad` recovers the original-run
distribution exactly. -/

omit [Fintype TagId] [Nonempty TagId] [SampleableType Nonce] [DecidableEq Digest]
  [SampleableType Digest] in
/-- **`multipleBadAdvance` preserves `cacheBad`.** The bad-side tag advance literally copies
`cacheBad := sB.cacheBad` in both Option branches; this is `rfl` after pattern-matching. Used at
the tag-step of the Fine→original bridge induction. -/
@[simp] lemma multipleBadAdvance_cacheBad (tag : TagId)
    (sB : UnlinkBadState TagId Nonce Digest)
    (r : Option (TagTranscript Nonce Digest)) :
    (multipleBadAdvance tag sB r).cacheBad = sB.cacheBad := by
  cases r <;> rfl

omit [DecidableEq TagId] [Nonempty TagId] [DecidableEq Nonce] [SampleableType Nonce]
  [SampleableType Digest] in
/-- **`with cacheBad := cb` flattens `multipleBadReaderAdvance`.** Overwriting the
post-advance bad state's `cacheBad` field with an arbitrary `cb` discards the only field the
reader-advance touched — so the result is structurally equal to the pre-advance state with the
same overwrite. Used at the reader-step of the Fine→original bridge induction to align the
Fine post-state with the Original post-state under the projection. -/
lemma multipleBadReaderAdvance_with_cacheBad_eq
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    (transcript : TagTranscript Nonce Digest)
    (sB : UnlinkBadState TagId Nonce Digest) (cb : Bool) :
    ({multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB with
        cacheBad := cb} : UnlinkBadState TagId Nonce Digest) = {sB with cacheBad := cb} := by
  cases sB; rfl

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **`cacheBad`-constancy of original handler runs.** The original `multipleBadTableHandler g`
never updates `cacheBad`: the tag branch copies it via `multipleBadAdvance` and the reader branch
threads the whole bad state through. So every reachable output's `cacheBad` equals the initial
value. Used to discharge the trailing projection in the Fine→original bridge headline. -/
lemma multipleBadTableHandler_run_cacheBad_const {α : Type} (g : TagId × Nonce → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    ∀ z ∈ support ((simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
        (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) oa).run p),
        z.2.2.cacheBad = p.2.cacheBad := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure b =>
    intro z hz
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz; rfl
  | query_bind t f ih =>
    intro z hz
    rw [multipleBadTable_run_query_bind', mem_support_bind_iff] at hz
    obtain ⟨q, hq, hz⟩ := hz
    have hstep : q.2.2.cacheBad = p.2.cacheBad := by
      cases t with
      | inl tag =>
        change q ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) p.1
            >>= fun r => pure (r.1, r.2, multipleBadAdvance tag p.2 r.1)) at hq
        obtain ⟨r, _, hq⟩ := (mem_support_bind_iff _ _ _).mp hq
        rw [mem_support_pure_iff] at hq
        subst hq
        exact multipleBadAdvance_cacheBad tag p.2 r.1
      | inr transcript =>
        change q ∈ support ((multipleTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1
            >>= fun r => pure (r.1, r.2, p.2)) at hq
        obtain ⟨r, _, hq⟩ := (mem_support_bind_iff _ _ _).mp hq
        rw [mem_support_pure_iff] at hq
        subst hq
        rfl
    exact (ih q.1 q.2 z hz).trans hstep

omit [Nonempty TagId] [SampleableType Digest] [NeZero sessionsPerTag] in
/-- **Original handler is `cacheBad`-irrelevant.** Two initial states `(s, sB)` and `(s, sB')`
that differ only in `cacheBad` produce identical original-handler-run distributions after the
projection `with cacheBad := cb`. The original handler never reads or writes `cacheBad`, so the
field is invisible to the run. -/
lemma evalDist_simulateQ_multipleBadTableHandler_cacheBad_irrelevant
    {α : Type} (g : TagId × Nonce → Digest)
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (s : UnlinkState TagId) (sB sB' : UnlinkBadState TagId Nonce Digest) (cb : Bool)
    (hSU : sB.sessionsUsed = sB'.sessionsUsed)
    (hR : sB.responses = sB'.responses) (hB : sB.bad = sB'.bad) :
    𝒟[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g) oa).run (s, sB)]
      = 𝒟[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
          (sessionsPerTag := sessionsPerTag) g) oa).run (s, sB')] := by
  induction oa using OracleComp.inductionOn generalizing s sB sB' with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    congr 2
    cases sB; cases sB'
    simp_all
  | query_bind t f ih =>
    rw [multipleBadTable_run_query_bind', multipleBadTable_run_query_bind', map_bind, map_bind]
    cases t with
    | inl tag =>
      change 𝒟[((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) s >>= fun r =>
                pure (r.1, r.2, multipleBadAdvance tag sB r.1)) >>= fun a =>
            (fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) (f a.1)).run a.2]
          = 𝒟[((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inl tag)) s >>= fun r =>
                pure (r.1, r.2, multipleBadAdvance tag sB' r.1)) >>= fun a =>
            (fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) (f a.1)).run a.2]
      rw [bind_assoc, bind_assoc]
      refine evalDist_bind_congr_of_support _ _ _ fun r _ => ?_
      rw [pure_bind, pure_bind]
      have hAdv_SU : (multipleBadAdvance tag sB r.1).sessionsUsed
          = (multipleBadAdvance tag sB' r.1).sessionsUsed := by
        cases r.1 with
        | none => exact hSU
        | some tr =>
          change Function.update sB.sessionsUsed tag _ = Function.update sB'.sessionsUsed tag _
          rw [hSU]
      have hAdv_R : (multipleBadAdvance tag sB r.1).responses
          = (multipleBadAdvance tag sB' r.1).responses := by
        cases r.1 with
        | none => exact hR
        | some tr =>
          change (sB.responses.cacheQuery (tag, tr.nonce) _) = (sB'.responses.cacheQuery _ _)
          rw [hR]
      have hAdv_B : (multipleBadAdvance tag sB r.1).bad
          = (multipleBadAdvance tag sB' r.1).bad := by
        cases r.1 with
        | none => exact hB
        | some tr =>
          change (sB.bad || _) = (sB'.bad || _)
          rw [hB, hR]
      exact ih r.1 r.2 (multipleBadAdvance tag sB r.1) (multipleBadAdvance tag sB' r.1)
        hAdv_SU hAdv_R hAdv_B
    | inr transcript =>
      change 𝒟[((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) s >>= fun r =>
                pure (r.1, r.2, sB)) >>= fun a =>
            (fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) (f a.1)).run a.2]
          = 𝒟[((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
              (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) s >>= fun r =>
                pure (r.1, r.2, sB')) >>= fun a =>
            (fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
              (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) (f a.1)).run a.2]
      rw [bind_assoc, bind_assoc]
      refine evalDist_bind_congr_of_support _ _ _ fun r _ => ?_
      rw [pure_bind, pure_bind]
      exact ih r.1 r.2 sB sB' hSU hR hB

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Pointwise-in-`gFine` Fine→original projection equality.** For every fixed `gFine` and
every overwrite value `cb`, projecting `cacheBad := cb` on the Fine-run distribution yields the
same distribution as projecting `cacheBad := cb` on the original-run distribution. The workhorse
of the headline bridge: parametrized over `cb` (rather than `p.2.cacheBad`) so the induction can
pass through query-bind steps where the post-state's `cacheBad` differs from the pre-state's. -/
lemma evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_pointwise_eq
    (g : TagId × Nonce → Digest)
    (gFine : ((TagId × Fin sessionsPerTag) × Nonce) → Digest)
    {α : Type} (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) (cb : Bool) :
    𝒟[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
          (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run p]
      = 𝒟[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
          (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
            (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) oa).run p] := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure b =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t f ih =>
    rw [multipleBadTableFine_run_query_bind', multipleBadTable_run_query_bind', map_bind, map_bind]
    cases t with
    | inl tag =>
      -- Tag branch: handlers are byte-identical; bind_congr + ih.
      refine evalDist_bind_congr_of_support _ _ _ fun q _ => ?_
      exact ih q.1 q.2
    | inr transcript =>
      -- Reader branch: handlers differ only in cacheBad of post-state.
      -- Unfold both handler-step calls to expose the shared inner `multipleTableHandler` bind.
      change 𝒟[((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r =>
              pure (r.1, r.2,
                multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
                  gFine transcript p.2)) >>= fun a =>
                (fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
                  (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine)
                    (f a.1)).run a.2]
            = 𝒟[((multipleTableHandler (TagId := TagId) (Nonce := Nonce) (Digest := Digest)
            (sessionsPerTag := sessionsPerTag) g (Sum.inr transcript)) p.1 >>= fun r =>
              pure (r.1, r.2, p.2)) >>= fun a =>
                (fun z => (z.1, z.2.1, {z.2.2 with cacheBad := cb})) <$>
                  (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                    (Digest := Digest) (sessionsPerTag := sessionsPerTag) g)
                    (f a.1)).run a.2]
      rw [bind_assoc, bind_assoc]
      refine evalDist_bind_congr_of_support _ _ _ fun r _ => ?_
      rw [pure_bind, pure_bind]
      -- Apply IH on the LHS to convert Fine to Original on a perturbed bad state,
      -- then apply cacheBad-irrelevance to align that to the RHS bad state.
      rw [ih r.1 (r.2, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
        gFine transcript p.2)]
      exact evalDist_simulateQ_multipleBadTableHandler_cacheBad_irrelevant g (f r.1) r.2
        (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript p.2)
        p.2 cb rfl rfl rfl

omit [Nonempty TagId] [SampleableType Digest] in
/-- **Fine→original eager-table bridge.** Marginalizing the Fine-run output distribution over a
fresh `gFine ← $ᵗ` and overwriting `cacheBad := p.2.cacheBad` on the final bad state recovers
the original-run output distribution exactly.

The proof composes the pointwise-in-`gFine` projection equality
(`…_forget_cacheBad_pointwise_eq`) with the constancy of `cacheBad` along original-handler runs
(`multipleBadTableHandler_run_cacheBad_const`), then collapses the outer `gFine` binder via
`probOutput_bind_const` (uniform sample doesn't fail). -/
lemma evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_eq
    [SampleableType (((TagId × Fin sessionsPerTag) × Nonce) → Digest)]
    (g : TagId × Nonce → Digest) {α : Type}
    (oa : OracleComp (UnlinkOracleSpec TagId Nonce Digest) α)
    (p : UnlinkState TagId × UnlinkBadState TagId Nonce Digest) :
    𝒟[(fun z => (z.1, z.2.1, {z.2.2 with cacheBad := p.2.cacheBad})) <$>
          (do let gFine ← ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest));
              (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run p)]
      = 𝒟[(simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
                (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) oa).run p] := by
  classical
  -- Push the projection map under the outer bind.
  rw [map_bind]
  -- Per-point distribution equality by extensional probOutput, on every output `x`.
  refine evalDist_ext fun x => ?_
  -- Step 1: the per-gFine projected Fine-run distribution equals the projected Original-run
  -- distribution pointwise in gFine (via the pointwise lemma); collapse the constant gFine
  -- bind with `probOutput_bind_of_const` and `probFailure_uniformSample = 0`.
  have hpointwise : ∀ gFine ∈ support
      ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)),
      Pr[= x | (fun z => (z.1, z.2.1, {z.2.2 with cacheBad := p.2.cacheBad})) <$>
        (simulateQ (multipleBadTableHandlerFine (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g gFine) oa).run p] =
      Pr[= x | (fun z => (z.1, z.2.1, {z.2.2 with cacheBad := p.2.cacheBad})) <$>
        (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) oa).run p] := by
    intro gFine _
    rw [probOutput_def, probOutput_def,
      evalDist_simulateQ_multipleBadTableHandlerFine_forget_cacheBad_pointwise_eq
        g gFine oa p p.2.cacheBad]
  rw [probOutput_bind_of_const _ hpointwise, probFailure_uniformSample, tsub_zero, one_mul]
  -- Step 2: π acts as identity on the support of the original run (since cacheBad is constant).
  rw [probOutput_map_eq_tsum_subtype_ite]
  rw [show Pr[= x | (simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
          (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) oa).run p]
        = Pr[= x |
            (id <$> ((simulateQ (multipleBadTableHandler (TagId := TagId) (Nonce := Nonce)
              (Digest := Digest) (sessionsPerTag := sessionsPerTag) g) oa).run p))]
      from by rw [id_map]]
  rw [probOutput_map_eq_tsum_subtype_ite]
  -- The two subtype-sums agree pointwise since π acts as identity on the support.
  have hcb := multipleBadTableHandler_run_cacheBad_const (sessionsPerTag := sessionsPerTag) g oa p
  refine tsum_congr fun z => ?_
  have hz := hcb z.val z.property
  have hrec : ((z.val.1, z.val.2.1,
        ({z.val.2.2 with cacheBad := p.2.cacheBad} : UnlinkBadState TagId Nonce Digest))
        : α × UnlinkState TagId × UnlinkBadState TagId Nonce Digest) = z.val := by
    have heq : ({z.val.2.2 with cacheBad := p.2.cacheBad} : UnlinkBadState TagId Nonce Digest)
        = z.val.2.2 := by
      conv_lhs => rw [← hz]
    rw [heq]
  rw [hrec, id_eq]

end UnlinkReduction

end PRFTagReader
