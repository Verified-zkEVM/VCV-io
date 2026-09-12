/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.CouplingEngine

/-!
# EUF-CMA for Fiat-Shamir with aborts: ReadRecording

The read-recording handler `deferredDrawReadImpl`: the deferred-draw run's
read-time bad flag is dominated by the final-state predicate "some recorded
read-commit is in the final drawn list".

Part of the CMA-to-NMA security development for the Fiat-Shamir-with-aborts
transform; `VCVio.CryptoFoundations.FiatShamir.WithAbort.Security` assembles
the headline `euf_cma_to_nma` and holds the overview docstring.
-/

public section

universe u v

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section EUF_CMA

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

section scaffold

variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
variable (adv : SignatureAlg.unforgeableAdv
  (FiatShamirWithAbort
    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))

/-! ### Read-recording handler: bad as a final-state predicate

The deferred-draw run's bad flag is set at *read time*: a read fires when its target commitment is
in the drawn list **as it stands at that read**. Because the drawn list only grows
(`deferredDraw_run_drawn_prefix`), a read that hits the drawn-so-far list certainly hits the *final*
drawn list, so the bad event is dominated by the final-state predicate "some recorded read-commit
is in the final drawn list". The handler `deferredDrawReadImpl` records, in an extra `List Commit`
component, the commitment `mc.2` of every adversarial read; its read step is otherwise identical to
`deferredDrawImpl` (same answer via `roStep`, same drawn list, same bad flag). The reduction
`deferredDraw_bad_le_readRecord` is the pointwise coupling that reads the bad ordering off the run;
it converts the *read-time* bad flag into the *final-state* membership predicate
`∃ rc ∈ readlist, rc ∈ drawnlist`, which removes the read-time/final-state mismatch that obstructs a
direct expectation bound. The recorded read commits are **value-free** (answers come from the real
layer via `roStep`; the drawn *values* never feed the read points), which is what
`Security/TapeFactorization.lean` charges against the recorded draws.

Why a bespoke handler rather than generic query instrumentation. The framework's generic
`QueryImpl` decorations (`withLogging`, `withTrace`/`withTraceBefore`, and cursor/path-style
wrappers) instrument *occurrences of queries in the computation being simulated*: they observe the
query's input, and optionally its answer, at each node of the original tree. That is enough for the
read half of the state here — the adversary's random-oracle reads *are* nodes of `adv.main pk`, so
their commitment components could be logged generically. It is not enough for the draw half. The
commitment draws being recorded are not occurrences in the adversary's tree at all: they are
introduced *inside the signing handler*, by `ghostSignDrawBody`, when the handler answers a signing
query, and their number is itself random (one per rejected attempt). No input-only instrumentation
of the adversary's queries can name them, so the drawn list has to be a component of the handler's
own state, written by the signing branch. Recording both lists in one handler state is also what
makes the pair `(readlist, drawnlist)` available at a single final state, which is the form the
first-moment charge consumes. -/

/-- State of the read-recording deferred-draw handler: the underlying `DeferredState` together with
the accumulated list of commitment components `mc.2` of every adversarial random-oracle read. The
extra list makes the read-hit event a *final-state* predicate (membership in the drawn list) rather
than a read-time flag. -/
abbrev DeferredReadState (M Commit Chal : Type) : Type :=
  DeferredState M Commit Chal × List Commit

/-- The read-recording deferred-draw handler. Identical to `deferredDrawImpl` on the underlying
`DeferredState`, additionally appending the read's commitment component `mc.2` to the recorded
read-commit list on every adversarial random-oracle read. Uniform and signing steps leave the
read-commit list untouched. -/
@[expose] noncomputable def deferredDrawReadImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (DeferredReadState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun cu => (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
          mc.2 :: s.2))) <$>
        roStep M s.1.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
        (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1

omit [SampleableType Stmt] in
/-- **Coupling invariant for the read-recording reduction.** The underlying deferred state matches,
and whenever the deferred bad flag is set there is a recorded read-commit already in the deferred
drawn list. The drawn list grows monotonically, so a read-time hit (recorded in the bad flag) is
witnessed by a recorded read-commit lying in the *current* (hence final) drawn list. -/
@[expose] def deferredReadInv
    (s₁ : DeferredState M Commit Chal) (s₂ : DeferredReadState M Commit Chal) : Prop :=
  s₁.1 = s₂.1.1 ∧ (s₁.2 = true → ∃ rc ∈ s₂.2, rc ∈ s₂.1.1.2)

omit [SampleableType Stmt] in
/-- **Per-query coupling step for the read-recording reduction.** From any pair of
`deferredReadInv`-related states one step of `deferredDrawImpl` couples with one step of
`deferredDrawReadImpl` with equal output and the invariant preserved.

* **Uniform** forwards the same draw; states untouched.
* **Read** answers from the shared real layer via `roStep` (same answer, same cache, same drawn
  list); the recorded read-commit `mc.2` witnesses any newly-set bad flag (it is appended to the
  read-commit list and, when the flag fires, lies in the drawn list).
* **Sign** runs the shared `ghostSignDrawBody`; the drawn list grows in lockstep, so an existing
  read-commit witness is preserved (the drawn list only appends). -/
theorem deferredDrawRead_step (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (u₁ : DeferredState M Commit Chal) (u₂ : DeferredReadState M Commit Chal)
    (hu : deferredReadInv M u₁ u₂) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((deferredDrawImpl ids M maxAttempts pk sk t).run u₁)
      ((deferredDrawReadImpl ids M maxAttempts pk sk t).run u₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ deferredReadInv M p₁.2 p₂.2) := by
  obtain ⟨hst, hbad⟩ := hu
  rcases t with (n | mc) | msg
  · -- UNIFORM: both forward the same draw; state untouched.
    have hrun₁ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₁ =
        (fun u => (u, u₁)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    have hrun₂ : (deferredDrawReadImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₂ =
        (fun u => (u, u₂)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    rw [hrun₁, hrun₂]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
    rintro a b (rfl : a = b)
    exact ⟨rfl, hst, hbad⟩
  · -- READ: shared `roStep`; the recorded read-commit witnesses any newly-set bad flag.
    have hrun₁ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₁ =
        (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, u₁.1.1.2), u₁.1.2), u₁.2 || decide (mc.2 ∈ u₁.1.2)))) <$>
          roStep M u₁.1.1.1 mc := rfl
    have hrun₂ : (deferredDrawReadImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₂ =
        (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, ((((cu.2, u₂.1.1.1.2), u₂.1.1.2), u₂.1.2 || decide (mc.2 ∈ u₂.1.1.2)),
              mc.2 :: u₂.2))) <$>
          roStep M u₂.1.1.1.1 mc := rfl
    rw [hrun₁, hrun₂, show u₁.1.1.1 = u₂.1.1.1.1 from by rw [hst],
      show u₁.1.1.2 = u₂.1.1.1.2 from by rw [hst], show u₁.1.2 = u₂.1.1.2 from by rw [hst]]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
    rintro a b (rfl : a = b)
    refine ⟨rfl, rfl, ?_⟩
    intro hb
    rcases Bool.or_eq_true _ _ |>.mp hb with hb' | hb'
    · obtain ⟨rc, hrcmem, hrcdraw⟩ := hbad hb'
      exact ⟨rc, List.mem_cons_of_mem _ hrcmem, hrcdraw⟩
    · exact ⟨mc.2, List.mem_cons_self, by simpa using hb'⟩
  · -- SIGN: shared signing body; drawn list grows, witness preserved.
    have hrun₁ : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run u₁ =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: u₁.1.1.2), u₁.1.2 ++ alc.1.2), u₁.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run u₁.1.1.1 := rfl
    have hrun₂ : (deferredDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run u₂ =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, ((((alc.2, msg :: u₂.1.1.1.2), u₂.1.1.2 ++ alc.1.2), u₂.1.2), u₂.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run u₂.1.1.1.1 := rfl
    rw [hrun₁, hrun₂, show u₁.1.1.1 = u₂.1.1.1.1 from by rw [hst],
      show u₁.1.1.2 = u₂.1.1.1.2 from by rw [hst], show u₁.1.2 = u₂.1.1.2 from by rw [hst]]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
    rintro a b (rfl : a = b)
    refine ⟨rfl, rfl, ?_⟩
    intro hb
    obtain ⟨rc, hrcmem, hrcdraw⟩ := hbad hb
    exact ⟨rc, hrcmem, List.mem_append_left _ hrcdraw⟩

omit [SampleableType Stmt] in
/-- **The read-recording run coupling.** By induction on the adversary computation `oa`, the
deferred-draw run and the read-recording run are coupled with `deferredReadInv` preserved at every
leaf, using `deferredDrawRead_step` per query and the inductive hypothesis for the continuation.
Mirrors `deferredCouple_run`. -/
theorem deferredDrawRead_run {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s₁ : DeferredState M Commit Chal) (s₂ : DeferredReadState M Commit Chal),
      deferredReadInv M s₁ s₂ →
      OracleComp.ProgramLogic.Relational.RelTriple
        ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₁)
        ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s₂)
        (fun q₁ q₂ => deferredReadInv M q₁.2 q₂.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s₁ s₂ hinv
      simp only [simulateQ_pure, StateT.run_pure]
      exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure hinv
  | query_bind t ob ih =>
      intro s₁ s₂ hinv
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (deferredDrawRead_step ids M maxAttempts pk sk t s₁ s₂ hinv) ?_
      rintro p₁ p₂ ⟨hout, hinv'⟩
      rw [show p₁.1 = p₂.1 from hout]
      exact ih p₂.1 p₁.2 p₂.2 hinv'

omit [SampleableType Stmt] in
/-- **The read-recording reduction.** The deferred-draw run's bad marginal is at most the
read-recording run's final-state predicate "some recorded read-commit lies in the final drawn
list", from any pair of `deferredReadInv`-related start states.

Reads off the bad-ordering component of `deferredReadInv` from the run coupling
`deferredDrawRead_run` via `probEvent_le_of_relTriple_imp`. This converts the read-time bad flag of
`deferredDrawImpl` into the membership predicate over the read-recording run's final state, where
both the recorded read-commit list and the drawn list are available together. -/
theorem deferredDraw_bad_le_readRecord {γ : Type}
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s₁ : DeferredState M Commit Chal) (s₂ : DeferredReadState M Commit Chal)
    (hinv : deferredReadInv M s₁ s₂) :
    Pr[fun z : γ × DeferredState M Commit Chal => z.2.2 = true |
        (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₁]
      ≤ Pr[fun z : γ × DeferredReadState M Commit Chal => ∃ rc ∈ z.2.2, rc ∈ z.2.1.1.2 |
          (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s₂] :=
  OracleComp.ProgramLogic.Relational.probEvent_le_of_relTriple_imp
    (deferredDrawRead_run ids M maxAttempts pk sk oa s₁ s₂ hinv)
    (fun _ _ hp hbad => hp.2 hbad)

omit [SampleableType Stmt] in
/-- **Markov reduction for the read-recording firing event.** The read-recording run's final-state
read-hit predicate `∃ rc ∈ readlist, rc ∈ drawnlist` has probability at most the *expected
coincidence count* `E[#{ rc ∈ readlist : rc ∈ drawnlist }]`, the first moment of the number of
recorded read-commits that lie in the drawn list.

This is the elementary first-moment (Markov) step of the per-position route: a firing run has at
least one coincidence, so the indicator of the firing event is dominated by the (nonnegative,
integer-valued) coincidence count, and `Pr[fire] ≤ E[count]` by the Markov core
`probEvent_le_tsum_probOutput_mul_cost`. The probabilistic content — bounding `E[count]` by
`(qH+1)·ε·E[#attempts]` — is the per-position independence of each fresh draw from the
value-free recorded read-commit list, supplied by `readRecord_expected_coincidences_le`. This
lemma is exactly the step that isolates that independence from the firing event. -/
theorem readRecord_pred_le_expected_coincidences {γ : Type}
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s : DeferredReadState M Commit Chal) :
    Pr[fun z : γ × DeferredReadState M Commit Chal => ∃ rc ∈ z.2.2, rc ∈ z.2.1.1.2 |
        (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s]
      ≤ ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            (z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) : ℝ≥0∞) := by
  classical
  refine probEvent_le_tsum_probOutput_mul_cost _ _ _ (fun z hz => ?_)
  obtain ⟨rc, hrc, hrd⟩ := hz
  have hpos : 0 < z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) := by
    rw [List.countP_pos_iff]
    exact ⟨rc, hrc, by simpa using hrd⟩
  have h1 : (1 : ℕ) ≤ z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) := hpos
  exact_mod_cast h1

end scaffold

end EUF_CMA

end FiatShamirWithAbort
