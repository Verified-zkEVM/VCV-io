/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps

/-!
# Deferred sampling: tape factorization of answer-irrelevant draws

This module collects the reusable, scheme-independent kernels behind the
*deferred-sampling* technique: rewriting a probabilistic computation whose per-step
draws do not influence the control flow into one where those draws are *front-loaded*
into a single independent "tape", drawn ahead of time and then consumed.

The technique underlies several proofs in this library (Fiat–Shamir with abort, GPV
preimage sampling, collision/birthday bounds). Those proofs each instantiate a bespoke
state machine; what is genuinely generic — and lives here — is:

* **i.i.d. bind-commutation** (`evalSPMF_bind_comm`, `evalSPMF_bind_const_neverFails`,
  `evalSPMF_bind_congr_left`): the *answer-irrelevant draw commutes past its
  continuation* step at the distribution level. `OracleComp`'s syntactic `bind` is not
  commutative, but its `evalSPMF` image into `SPMF` is; this is what lets a per-step draw
  be moved to the front tape.
* **The list-multiplicity ε-kernel** (`tsum_count_eq_length`,
  `tsum_probOutput_fresh_mul_count_le`): one fresh draw `w ← oa`, *independent of* a
  value-free list `rl`, contributes expected multiplicity
  `E[rl.count (key w)] ≤ ε · rl.length` whenever each slot is hit with probability `≤ ε`.
  This is the single source of the `ε` in deferred-sampling read bounds.
* **The general factorization statement** (`DeferredTape.Factorizes`): an abstract
  predicate packaging "the read-recording run distributes as a single front draw block
  followed by a tape-consuming run". Scheme-specific factorizations (e.g.
  `FiatShamirWithAbort.evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`) are instances
  of this shape; the predicate names the target so downstream consumers share vocabulary.

The genuinely hard, scheme-specific glue — proving a particular state machine's run *is*
a tape factorization — is not generic and stays with each scheme. What this module
provides is the toolbox that those proofs are built out of.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp.DeferredSampling

/-! ## i.i.d. bind-commutation at the distribution level

These lemmas implement the *answer-irrelevant draw commutes past its continuation* step.
`OracleComp`'s `bind` is syntactic and *not* commutative as a free monad, but its
`evalSPMF` image into `SPMF` is — the two iterated sums over independent draws exchange by
`ENNReal.tsum_comm`. This is the local resampling step that front-loads a draw whose value
the rest of the computation may use but whose *position* is irrelevant. -/

/-- **i.i.d. bind-commutation.** Two independent draws `oa`, `ob` feeding a common
continuation `k` may be drawn in either order without changing the output distribution. -/
theorem evalSPMF_bind_comm {α β γ : Type} (oa : ProbComp α) (ob : ProbComp β)
    (k : α → β → ProbComp γ) :
    𝒮[oa >>= fun a => ob >>= fun b => k a b] = 𝒮[ob >>= fun b => oa >>= fun a => k a b] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒮[oa >>= fun a => ob >>= fun b => k a b] x
        = Pr[= x | oa >>= fun a => ob >>= fun b => k a b] from (probOutput_def _ _).symm,
    show 𝒮[ob >>= fun b => oa >>= fun a => k a b] x
        = Pr[= x | ob >>= fun b => oa >>= fun a => k a b] from (probOutput_def _ _).symm]
  rw [probOutput_bind_eq_tsum]
  rw [show (∑' a : α, Pr[= a | oa] * Pr[= x | ob >>= fun b => k a b])
      = ∑' (a : α) (b : β), Pr[= a | oa] * (Pr[= b | ob] * Pr[= x | k a b]) from
    tsum_congr fun a => by rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]]
  rw [probOutput_bind_eq_tsum]
  rw [show (∑' b : β, Pr[= b | ob] * Pr[= x | oa >>= fun a => k a b])
      = ∑' (b : β) (a : α), Pr[= b | ob] * (Pr[= a | oa] * Pr[= x | k a b]) from
    tsum_congr fun b => by rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun a => tsum_congr fun b => by ring

/-- **Dropping a never-failing value-irrelevant prefix.** A leading draw `od` whose
continuation ignores its value contributes only its total mass; when `od` never fails
(mass `1`, e.g. a `drawList` front block) it can be discarded from the output
distribution. -/
theorem evalSPMF_bind_const_neverFails {α γ : Type} (od : ProbComp α) (hmass : Pr[⊥ | od] = 0)
    (k : ProbComp γ) : 𝒮[od >>= fun _ => k] = 𝒮[k] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒮[od >>= fun _ => k] x = Pr[= x | od >>= fun _ => k] from (probOutput_def _ _).symm,
    show 𝒮[k] x = Pr[= x | k] from (probOutput_def _ _).symm]
  rw [probOutput_bind_const, hmass]; simp

/-- **Distribution-level congruence under a leading bind.** If two continuations agree as
distributions pointwise then the bound computations agree as distributions. -/
theorem evalSPMF_bind_congr_left {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β)
    (h : ∀ a, 𝒮[f a] = 𝒮[g a]) : 𝒮[oa >>= f] = 𝒮[oa >>= g] := by
  rw [evalSPMF_bind, evalSPMF_bind]; exact congrArg _ (funext h)

/-! ## The list-multiplicity ε-kernel

The single source of the `ε` in a deferred-sampling read bound: one fresh draw,
independent of a value-free list, hits each list slot with probability `≤ ε`. -/

/-- Summing the multiplicity `rl.count rc` of every element `rc` over the whole index type
recovers the list length (the multiplicities partition the list). -/
lemma tsum_count_eq_length {C : Type} [DecidableEq C] (rl : List C) :
    (∑' rc : C, (rl.count rc : ℝ≥0∞)) = (rl.length : ℝ≥0∞) := by
  induction rl with
  | nil => simp
  | cons a rl ih =>
      have hsplit : ∀ rc : C,
          ((a :: rl).count rc : ℝ≥0∞) = (if rc = a then 1 else 0) + (rl.count rc : ℝ≥0∞) := by
        intro rc; rw [List.count_cons]; by_cases h : rc = a
        · subst h; simp [add_comm]
        · simp [h, Ne.symm h]
      simp_rw [hsplit]
      rw [ENNReal.tsum_add, ih, List.length_cons, tsum_ite_eq]
      push_cast; ring

/-- **The atomic value-free charge.** One fresh draw `w ← oa : ProbComp (C × P)`,
*independent of* a value-free list `rl : List C`, contributes expected multiplicity
`E[rl.count (key w)] ≤ ε · rl.length`: each of the `rl.length` slots of `rl` is hit by the
fresh draw's key with probability `Pr[= slot | key <$> oa] ≤ ε`.

Stated for `key = Prod.fst` (a draw of a `(C × P)`-pair, of which only the `C`-component is
matched against the list), as it arises when a commitment draw carries an auxiliary private
state. This is the irreducible probabilistic kernel of a deferred-sampling read bound. -/
lemma tsum_probOutput_fresh_mul_count_le {C P : Type} [DecidableEq C]
    (oa : ProbComp (C × P)) (rl : List C) (ε : ℝ)
    (hGuess : ∀ cm : C, Pr[= cm | Prod.fst <$> oa] ≤ ENNReal.ofReal ε) :
    (∑' w : C × P, Pr[= w | oa] * (rl.count w.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * (rl.length : ℝ≥0∞) := by
  have hcount : ∀ w : C × P,
      ((rl.count w.1 : ℕ) : ℝ≥0∞)
        = ∑' rc : C, (rl.count rc : ℝ≥0∞) * (if w.1 = rc then 1 else 0) := by
    intro w; rw [tsum_eq_single w.1 (fun rc hrc => by simp [Ne.symm hrc])]; simp
  simp_rw [hcount]
  rw [show (∑' w : C × P, Pr[= w | oa] *
        ∑' rc : C, (rl.count rc : ℝ≥0∞) * (if w.1 = rc then 1 else 0))
      = ∑' rc : C, ∑' w : C × P,
          Pr[= w | oa] * ((rl.count rc : ℝ≥0∞) * (if w.1 = rc then 1 else 0)) from by
    rw [ENNReal.tsum_comm]; exact tsum_congr fun w => by rw [ENNReal.tsum_mul_left]]
  have hmarg : ∀ rc : C,
      (∑' w : C × P, Pr[= w | oa] * ((rl.count rc : ℝ≥0∞) * (if w.1 = rc then 1 else 0)))
        = (rl.count rc : ℝ≥0∞) * Pr[= rc | Prod.fst <$> oa] := by
    intro rc
    rw [show Pr[= rc | Prod.fst <$> oa]
          = ∑' w : C × P, Pr[= w | oa] * (if w.1 = rc then 1 else 0) from by
      rw [probOutput_map_eq_tsum]; refine tsum_congr fun w => ?_
      simp only [eq_comm]; split <;> rename_i h <;> simp [h]]
    rw [show (∑' w : C × P,
            Pr[= w | oa] * ((rl.count rc : ℝ≥0∞) * (if w.1 = rc then 1 else 0)))
          = ∑' w : C × P,
              (rl.count rc : ℝ≥0∞) * (Pr[= w | oa] * (if w.1 = rc then 1 else 0)) from
      tsum_congr fun w => by ring]
    rw [ENNReal.tsum_mul_left]
  simp_rw [hmarg]
  calc (∑' rc : C, (rl.count rc : ℝ≥0∞) * Pr[= rc | Prod.fst <$> oa])
      ≤ ∑' rc : C, (rl.count rc : ℝ≥0∞) * ENNReal.ofReal ε :=
        ENNReal.tsum_le_tsum fun rc => by gcongr; exact hGuess rc
    _ = ENNReal.ofReal ε * (rl.length : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, mul_comm, tsum_count_eq_length]

/-! ## The general factorization shape

The hard, scheme-specific content of deferred sampling is proving that a particular
read-recording run *equals* a front-tape factorization. The shape of that target is
generic and named here, so that scheme instances and downstream consumers share a single
vocabulary. -/

/-- **The deferred-tape factorization predicate.** `Factorizes run tape tapeRun` asserts
that running the deferred-draw computation `run : ProbComp γ` is distributionally identical
to first drawing an independent front tape `tape : ProbComp τ` and then running the
tape-consuming variant `tapeRun : τ → ProbComp γ` that reads its per-step draws off the
tape head-first:

`𝒮[run] = 𝒮[tape >>= tapeRun]`.

A scheme establishes this by induction on its adversary computation: at an
*answer-irrelevant* step the front tape commutes past the query (`evalSPMF_bind_comm`), and
at a *drawing* step the inline draw block is split off the front tape. The
over-provisioned suffix of the tape is discarded by the never-failing prefix lemma
(`evalSPMF_bind_const_neverFails`). See
`FiatShamirWithAbort.evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead` for a worked
instance. -/
def Factorizes {γ τ : Type} (run : ProbComp γ) (tape : ProbComp τ)
    (tapeRun : τ → ProbComp γ) : Prop :=
  𝒮[run] = 𝒮[tape >>= tapeRun]

/-- A factorization may be rewritten through any distribution-level continuation: if
`run` factorizes through `tape`/`tapeRun`, then binding a continuation `k` after `run`
factorizes through `tape` and `tapeRun >=> k` (definitional unfolding plus `evalSPMF_bind`
associativity). This is the recombination step used when a factorized head feeds a fold. -/
theorem Factorizes.bind {γ τ δ : Type} {run : ProbComp γ} {tape : ProbComp τ}
    {tapeRun : τ → ProbComp γ} (h : Factorizes run tape tapeRun) (k : γ → ProbComp δ) :
    Factorizes (run >>= k) tape (fun t => tapeRun t >>= k) := by
  simp only [Factorizes, evalSPMF_bind] at h ⊢
  rw [h, bind_assoc]

/-! ## The answer-irrelevant step commute (the framework induction step)

The inductive heart of a tape factorization is: at a query whose per-step draw does *not* consult
the tape, the front tape commutes past the step. This is the abstract, state-shape-independent form
of that step — it takes the per-continuation factorization as a hypothesis (the inductive
hypothesis) and concludes the factorization for one more leading answer-irrelevant step. Drawing and
read steps are handled by their own (scheme-specific) splice/commute; this is the
*answer-irrelevant* case, which is fully generic. -/

/-- **Answer-irrelevant step commutes past the front tape.** An answer-irrelevant step
`step : ProbComp (Ans × S)` (a query whose answer-draw does not consult the front tape) composed
with a deferred continuation `defCont` factors as the front tape `tape : ProbComp τ` drawn first,
followed by a tape-threaded continuation:

* `defCont a s' : ProbComp (γ × S)` is the deferred continuation after the step;
* `tapeCont a (s', t) : ProbComp (γ × ρ)` is its tape-consuming variant, threading the tape `t`;
* `proj : γ × ρ → γ × S` discards the spent-tape suffix on output.

Given the per-continuation factorization `hcont` (supplied by the inductive hypothesis), the leading
answer-irrelevant step commutes past the front draw block: the continuation is rewritten by `hcont`
under the step bind (`evalSPMF_bind_congr_left`), the front tape commutes past the answer-irrelevant
step (`evalSPMF_bind_comm`), and the inner step bind is re-associated into the mapped tape-step form
(`bind_map_left`/`map_bind`). This is the genuine framework content of a tape factorization's
non-drawing case; see
`FiatShamirWithAbort.evalSPMF_tapePreserving_step_commute` for the worked Fiat–Shamir instance
(`tape := drawList (ids.commit pk sk) L`, `S := DeferredReadState …`). -/
theorem evalSPMF_step_commute_tape {γ S Ans τ ρ : Type}
    (step : ProbComp (Ans × S)) (tape : ProbComp τ)
    (proj : γ × ρ → γ × S)
    (defCont : Ans → S → ProbComp (γ × S))
    (tapeCont : Ans → S × τ → ProbComp (γ × ρ))
    (hcont : ∀ (a : Ans) (s' : S),
      𝒮[defCont a s'] = 𝒮[tape >>= fun t => proj <$> tapeCont a (s', t)]) :
    𝒮[step >>= fun p => defCont p.1 p.2] =
      𝒮[tape >>= fun t =>
          proj <$>
            (((fun p : Ans × S => (p.1, (p.2, t))) <$> step) >>= fun p => tapeCont p.1 p.2)] := by
  classical
  rw [evalSPMF_bind_congr_left step (fun p => defCont p.1 p.2)
    (fun p => tape >>= fun t => proj <$> tapeCont p.1 (p.2, t)) (fun p => hcont p.1 p.2)]
  rw [evalSPMF_bind_comm step tape (fun p t => proj <$> tapeCont p.1 (p.2, t))]
  refine evalSPMF_bind_congr_left tape _ _ (fun t => ?_)
  rw [bind_map_left, map_bind]

/-! ## State-relation transfer for expected output functionals

The value-substitution lemmas of deferred sampling (e.g. "the recorded read list of the run is
independent of the rejected-draw content of the start state") are instances of a single generic
fact: an expected output functional through `simulateQ impl` of a `StateT σ ProbComp` handler is
equal at two start states related by `Rel`, provided every query step transfers `Rel` to its
continuation and the functional is `Rel`-invariant. -/

/-- **State-relation transfer for an expected output functional.** Let
`impl : QueryImpl spec (StateT σ ProbComp)` and let `Rel : σ → σ → Prop` be a relation on the
handler state. Suppose:

* every query step transfers `Rel`: for `Rel`-related start states and any `Rel`-invariant
  continuation functional `K`, the per-query expected `K` agrees at the two states (`hstep`);
* the output functional `F : γ → σ → ℝ≥0∞` is `Rel`-invariant (`hF`).

Then the run-level expected output `∑' z, Pr[= z | (simulateQ impl oa).run s] * F z.1 z.2` agrees at
`Rel`-related start states `s₁`, `s₂`. The proof inducts on `oa`: at `pure` the output is the start
state (`hF` applies); at a query bind the step's expected continuation functional is itself
`Rel`-invariant by the inductive hypothesis, so `hstep` closes the step.

This is the generic value-substitution engine; a scheme discharges `hstep` by its per-query run
shapes. See `FiatShamirWithAbort.deferredDrawRead_run_count_dl_invariant` for the worked instance
(the recorded read-list multiplicity is invariant under the start drawn-list and bad-flag). -/
theorem tsum_probOutput_simulateQ_run_mul_of_rel
    {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    {γ : Type} (oa : OracleComp spec γ)
    (Rel : σ → σ → Prop)
    (hstep : ∀ (t : spec.Domain) (s₁ s₂ : σ), Rel s₁ s₂ →
      ∀ (K : spec.Range t → σ → ℝ≥0∞),
        (∀ (b : spec.Range t) (t₁ t₂ : σ), Rel t₁ t₂ → K b t₁ = K b t₂) →
        (∑' p : spec.Range t × σ, Pr[= p | (impl t).run s₁] * K p.1 p.2)
          = ∑' p : spec.Range t × σ, Pr[= p | (impl t).run s₂] * K p.1 p.2) :
    ∀ (F : γ → σ → ℝ≥0∞), (∀ (g : γ) (s₁ s₂ : σ), Rel s₁ s₂ → F g s₁ = F g s₂) →
      ∀ (s₁ s₂ : σ), Rel s₁ s₂ →
        (∑' z : γ × σ, Pr[= z | (simulateQ impl oa).run s₁] * F z.1 z.2)
          = ∑' z : γ × σ, Pr[= z | (simulateQ impl oa).run s₂] * F z.1 z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro F hF s₁ s₂ hs
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact hF a s₁ s₂ hs
  | query_bind t ob ih =>
      intro F hF s₁ s₂ hs
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      set K : spec.Range t → σ → ℝ≥0∞ := fun b u =>
        ∑' z : γ × σ, Pr[= z | (simulateQ impl (ob b)).run u] * F z.1 z.2 with hK
      have hKinv : ∀ (b : spec.Range t) (t₁ t₂ : σ), Rel t₁ t₂ → K b t₁ = K b t₂ :=
        fun b t₁ t₂ ht => ih b F hF t₁ t₂ ht
      exact hstep t s₁ s₂ hs K hKinv

end OracleComp.DeferredSampling
