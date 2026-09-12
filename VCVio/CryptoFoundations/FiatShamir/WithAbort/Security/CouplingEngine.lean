/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.HiddenReadFold

/-!
# EUF-CMA for Fiat-Shamir with aborts: CouplingEngine

`avgBadM_eager_le_lazy_joint`, a reusable free-monad telescoping engine for
dominating averaged bad masses under a two-measure coupling invariant, together
with its deferral primitives and the attempt-count law. Not on the live path of
the ghost-read bound; retained as general infrastructure.

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

/-! ## Measure-level eager↔lazy coupling engine

`avgBadM_eager_le_lazy_joint` is a reusable free-monad telescoping engine for dominating
averaged bad masses under a two-measure coupling invariant. It is not on the live path of
the ghost-read bound, which goes through the ghost-blind first-moment route
(`probEvent_ghostHybridImpl_bad_le_ghostBlind` into `probEvent_ghostBlindImpl_bad_le`). It
is retained here as general infrastructure for a joint-law approach to the eager↔lazy
comparison.

The engine carries a **two-measure coupling invariant** `Inv νe νl` through the free-monad
induction on `oa`: the uniform and signing steps preserve `Inv` on the per-output post-step
measures (the handlers are definitionally identical on those steps, so `postStepOutM` agrees
and `Inv` is threaded unchanged), the pure leaf compares the carried bad mass under `Inv`, and
the read step supplies the genuine deferred-sampling inequality — the eager read's averaged
ghost-hit marginal over `νe` dominated by the lazy read's deferred-fire marginal over `νl`.

A per-state (single-measure, `νe = νl`) version of the read inequality is **false** — at a
committed ghost-hit state the eager read flips the bad flag with mass `1` while the lazy read
fires with sub-unit mass — so the two-measure coupling is essential for any future application. -/

omit [SampleableType Stmt] in
/-- **Two-measure eager↔lazy averaged-bad coupling engine.** Threads a coupling invariant
`Inv : (state-measure) → (state-measure) → Prop` through the free-monad induction on `oa`:

* `h_step_eq`: a non-read step (uniform forward or signing query) preserves `Inv` on the
  per-output post-step measures. The eager and lazy handlers are definitionally identical on
  these steps, so the two `postStepOutM` measures are produced by the same map and `Inv` is
  threaded across them.
* `h_pure`: at a pure leaf the carried bad mass of `νe` is dominated by that of `νl` (under
  `Inv`).
* `h_read`: at a random-oracle read step, the eager read's averaged ghost-hit bad marginal
  over `νe` is dominated by the lazy read's deferred-fire marginal over `νl` (under `Inv`),
  with the invariant-conditional inductive hypothesis on the continuations available.

Given these, `avgBadM eager νe oa ≤ avgBadM lazy νl oa` for every `Inv`-related pair. This is
the measure-level coupling vehicle: the read-step averaging (signing-time draw into `νe`
versus read-time redraw of `νl`) is exactly what the per-output post-step *measures* (not
per-state Diracs) carry, which is why a per-state comparison cannot replace it. -/
lemma avgBadM_eager_le_lazy_joint (pk : Stmt) (sk : Wit)
    (Inv : (GhostState M Commit Chal → ℝ≥0∞) → (GhostState M Commit Chal → ℝ≥0∞) → Prop)
    (h_step_eq : ∀ (νe νl : GhostState M Commit Chal → ℝ≥0∞), Inv νe νl →
      ∀ (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain),
        (¬ t matches Sum.inl (Sum.inr _)) →
        ∀ u, Inv (OracleComp.ProgramLogic.Relational.postStepOutM
                (ghostHybridImpl ids M maxAttempts true pk sk) νe t u)
              (OracleComp.ProgramLogic.Relational.postStepOutM
                (lazyGhostHybridImpl ids M maxAttempts pk sk) νl t u))
    (h_read : ∀ (νe νl : GhostState M Commit Chal → ℝ≥0∞), Inv νe νl →
      ∀ (mc : M × Commit)
        (cont : Chal → OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))) (M × Option (Commit × Resp))),
        (∀ u νe' νl', Inv νe' νl' →
          OracleComp.ProgramLogic.Relational.avgBadM
              (ghostHybridImpl ids M maxAttempts true pk sk) νe' (cont u)
            ≤ OracleComp.ProgramLogic.Relational.avgBadM
              (lazyGhostHybridImpl ids M maxAttempts pk sk) νl' (cont u)) →
        (∑' p : GhostState M Commit Chal, νe p *
            ∑' z : Chal × GhostState M Commit Chal,
              Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk
                  (Sum.inl (Sum.inr mc))).run p] *
                Pr[ fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal =>
                    w.2.2 = true |
                  (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont z.1)).run z.2])
          ≤ ∑' p : GhostState M Commit Chal, νl p *
            ∑' z : Chal × GhostState M Commit Chal,
              Pr[= z | (lazyGhostHybridImpl ids M maxAttempts pk sk
                  (Sum.inl (Sum.inr mc))).run p] *
                Pr[ fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal =>
                    w.2.2 = true |
                  (simulateQ (lazyGhostHybridImpl ids M maxAttempts pk sk) (cont z.1)).run z.2])
    (h_pure : ∀ (νe νl : GhostState M Commit Chal → ℝ≥0∞), Inv νe νl →
      ∀ _x : M × Option (Commit × Resp),
        (∑' p : GhostState M Commit Chal, νe p * (if p.2 = true then 1 else 0))
            ≤ ∑' p : GhostState M Commit Chal, νl p * (if p.2 = true then 1 else 0))
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (M × Option (Commit × Resp))) :
    ∀ νe νl : GhostState M Commit Chal → ℝ≥0∞, Inv νe νl →
      OracleComp.ProgramLogic.Relational.avgBadM
          (ghostHybridImpl ids M maxAttempts true pk sk) νe oa
        ≤ OracleComp.ProgramLogic.Relational.avgBadM
          (lazyGhostHybridImpl ids M maxAttempts pk sk) νl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro νe νl hInv
      rw [OracleComp.ProgramLogic.Relational.avgBadM_pure,
        OracleComp.ProgramLogic.Relational.avgBadM_pure]
      exact h_pure νe νl hInv x
  | @query_bind t cont ih =>
      intro νe νl hInv
      rcases t with (n | mc) | msg
      · rw [OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output,
          OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output]
        refine ENNReal.tsum_le_tsum fun u => ?_
        exact ih u _ _ (h_step_eq νe νl hInv (Sum.inl (Sum.inl n)) (by simp) u)
      · rw [OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq,
          OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq]
        exact h_read νe νl hInv mc cont (fun u νe' νl' h => ih u νe' νl' h)
      · rw [OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output,
          OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output]
        refine ENNReal.tsum_le_tsum fun u => ?_
        exact ih u _ _ (h_step_eq νe νl hInv (Sum.inr msg) (by simp) u)

omit [SampleableType Stmt] in
/-- **M1: the identical-until-bad / ghost-blind reduction** (foundational step of the
ghost-read bound). The eager hybrid handler `ghostHybridImpl … true` and the ghost-blind
handler `ghostBlindImpl` flip the adversarial-read bad flag with *exactly the same*
probability at the empty-cache Dirac start:

`Pr[bad | (simulateQ (ghostHybridImpl … true) (adv.main pk)).run δ_∅]`
`  = Pr[bad | (simulateQ ghostBlindImpl (adv.main pk)).run δ_∅]`.

The two handlers are *identical until bad*: they coincide on uniform queries, on signing
queries, and on ghost-*miss* reads (all run the same `roStep` / `ghostSignBody`), and on a
ghost-*hit* read both flip the bad flag (`ghostBlindImpl_agree_good`), while neither ever
unsets it (`ghostHybridImpl_bad_mono` / `ghostBlindImpl_bad_mono`). The blind handler answers
a hit from the real layer instead of returning the ghost value, so the ghost-key values never
influence the run — they are consulted only to record the would-hit. Because the runs differ
only on the already-bad trajectory (where both flags read `true`), the bad marginals coincide,
by the exact identical-until-bad bad-event equality
`probEvent_output_bad_eq'`. -/
lemma probEvent_ghostHybridImpl_bad_eq_ghostBlind (pk : Stmt) (sk : Wit) :
    Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      = Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)] :=
  OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq'
    (ghostHybridImpl ids M maxAttempts true pk sk)
    (ghostBlindImpl ids M maxAttempts pk sk)
    (ghostBlindImpl_agree_good ids M maxAttempts pk sk)
    (ghostHybridImpl_bad_mono ids M maxAttempts true pk sk)
    (ghostBlindImpl_bad_mono ids M maxAttempts pk sk)
    (adv.main pk) (((∅, ∅), []) : _)

omit [SampleableType Stmt] in
/-- **M1 (≤ form).** The eager ghost-read bad mass is bounded by the ghost-blind handler's
bad mass at the empty-cache Dirac start; immediate from the equality
`probEvent_ghostHybridImpl_bad_eq_ghostBlind`. This is the reduction the read-bound spine
chains with M2 (reads ⊥ ghost-key values) and M3 (geometric first-fire charge). -/
lemma probEvent_ghostHybridImpl_bad_le_ghostBlind (pk : Stmt) (sk : Wit) :
    Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)] :=
  (probEvent_ghostHybridImpl_bad_eq_ghostBlind ids hr M maxAttempts adv pk sk).le

/-! ### M3: the geometric first-fire charge (assembly)

`probEvent_ghostBlind_bad_le_of_fac` is the **M3** charge: given the **M2** deferred-sampling
factorization `hfac` — the ghost-blind run's bad marginal exhibited as the value-free
multi-key hidden-target game `kn >>= hiddenReadList (Prod.fst <$> ids.commit pk sk) (qH+1) σ`
(rejected commitment values deferred to a front block, read off by the adversary's adaptive
all-miss strategy `σ`) — the target bound `qS·(qH+1)·ε/(1-p)` follows by the
union-bound + geometric-fold pipeline:

* per-target guessing bound `hGuess` (raw `Pr[= w | commit] ≤ ε`) feeds the multi-key
  first-fire union bound `OracleComp.probEvent_bind_hiddenReadList_le`, giving
  `E[n]·((qH+1)·ε)` where `E[n] = ∑' n, Pr[= n | kn]·n` is the expected ghost-key count;
* the expected-count mean bound `hmean` (`E[n] ≤ qS/(1-p)`, the aggregate of
  `tsum_probOutput_commit_mul_abort_le` over the `qS` signing queries) folds into the target
  via `hiddenReadList_fold_le_target`.

The `Pr[reject|mc] ≤ 1` skew-drop is already baked into the raw-`commit` per-target bound
`hGuess` (the hidden targets are drawn from the *raw* commit law, not the rejection-conditioned
law), so no skew survives into this charge. The accepting attempt contributes `0` because it
is not a rejected draw and so is absent from `kn`'s key count. -/
omit [SampleableType Stmt] in
theorem probEvent_ghostBlind_bad_le_of_fac
    (qS qH : ℕ) (ε p_abort : ℝ) (hp : p_abort < 1)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (σ : List Bool → Commit) (kn : ProbComp ℕ)
    (hmean : ∑' n : ℕ, Pr[= n | kn] * (n : ℝ≥0∞)
      ≤ ENNReal.ofReal ((qS : ℝ) / (1 - p_abort)))
    (hfac : Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ Pr[(fun b : Bool => b = true) |
        kn >>= fun n => OracleComp.hiddenReadList (Prod.fst <$> ids.commit pk sk) (qH + 1) σ n]) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  refine (OracleComp.probEvent_le_of_eq_bind_hiddenReadList (oa := Prod.fst <$> ids.commit pk sk)
    (ε := ENNReal.ofReal ε) hGuess (qH + 1) σ kn hfac).trans ?_
  -- The averaged union bound `E[n]·((qH+1)·ε)` folds into the target via the geometric fold.
  refine le_trans (le_of_eq ?_)
    (hiddenReadList_fold_le_target qS qH ε p_abort hp (fun n => Pr[= n | kn]) hmean)
  -- Reconcile the `((qH+1)·ofReal ε)` factor shapes: `((qH:ℝ≥0∞)+1)` vs `↑(qH+1)`.
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [mul_assoc]
  congr 2
  push_cast
  ring

omit [SampleableType Stmt] in
/-- **Ghost-blind read-step bad indicator** (an M2 structural building block). Starting from a
state with the bad flag unset, the ghost-blind handler's adversarial random-oracle read at `mc`
sets the bad flag with mass exactly `1` if `mc` lies in the ghost-cache domain and `0`
otherwise. Identical indicator to the eager handler's `probOutput_ghostHybridImpl_read_bad`, but
here the *answer* is `roStep` on the real layer in **both** branches (hit and miss): the ghost
value never reaches the output, only the bad flag records the structural hit. This is the
manifest output-irrelevance of `ghostBlindImpl` at the read step — the per-read membership test
the M2 factorization reads off as a `hiddenReadList` probe. -/
lemma probEvent_ghostBlindImpl_read_bad (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) :
    Pr[fun z : Chal × GhostState M Commit Chal => z.2.2 = true |
        (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run (s, false)] =
      if s.1.2 mc = none then 0 else 1 := by
  rw [ghostBlindImpl_eq_ghostHybridImpl_false]
  cases hgh : s.1.2 mc with
  | some v =>
      rw [ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk hgh]
      simp
  | none =>
      rw [ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk hgh, if_pos rfl]
      simp [probEvent_eq_zero]

/-! ### Stage 2: single-query deferral primitives

The value-free foundation (`blindStepProj_map_ghostBlindImpl_indep`, Stage 1) shows the stored
ghost commitment values never feed back into the ghost-blind run. The two lemmas here are the
*single-query* deferral atoms that Stage 3 instantiates once per rejected signing attempt:

* `ghostBlindImpl_read_singletonGhost_bad` connects the ghost-blind read handler to the
  membership predicate. With the ghost cache holding a single rejected-attempt key `(msg, w) ↦ c`,
  an adversarial read at `mc` fires the bad flag *exactly* when `mc = (msg, w)` — the structural
  read-hit test that `OracleComp.readMany` models for one hidden target.
* `ghostBlind_singleDraw_fire_le` is the commit-sampler instance of the deferral primitive
  `OracleComp.probEvent_bind_fire_le_of_gen`: a run that draws one ghost commitment up front and
  feeds it *only* through the fixed `q`-read game of a value-free generator fires with probability
  at most `q · ε`. This is the "front-loaded one draw" charge; Stage 3 supplies the value-free
  generator `gen` from `blindStepProj_map_ghostBlindImpl_indep` and folds the `qS` per-query
  charges into the aggregate `kn >>= drawList` block. -/

omit [SampleableType Stmt] in
/-- **Stage 2 read-membership atom.** With the ghost cache holding exactly the single
rejected-attempt key `(msg, w) ↦ c`, an adversarial random-oracle read at `mc` in the ghost-blind
run fires the bad flag with mass `1` when `mc = (msg, w)` and `0` otherwise. This is the structural
single-target read-hit indicator (`OracleComp.readMany`'s per-read test) realised by the
ghost-blind handler: the value `w` enters the run *only* through this membership test, never through
the read's answer (which is `roStep` on the real layer — `probEvent_ghostBlindImpl_read_bad`). -/
lemma ghostBlindImpl_read_singletonGhost_bad (pk : Stmt) (sk : Wit) (mc : M × Commit) (msg : M)
    (w : Commit) (c : Chal) (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    Pr[fun z : Chal × GhostState M Commit Chal => z.2.2 = true |
        (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run
          (((re, (∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery (msg, w) c), l), false)] =
      if mc = (msg, w) then 1 else 0 := by
  rw [probEvent_ghostBlindImpl_read_bad ids M maxAttempts pk sk mc
    ((re, (∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery (msg, w) c), l)]
  by_cases h : mc = (msg, w)
  · subst h
    rw [if_neg (by simp), if_pos rfl]
  · rw [if_pos (by simp [QueryCache.cacheQuery_of_ne _ _ h]), if_neg h]

omit [SampleableType Stmt] [SampleableType Chal] in
/-- **Stage 2 single-query deferral.** A run that draws one ghost commitment
`w ← Prod.fst <$> ids.commit pk sk` (each outcome of mass at most `ε`) and feeds it to a
*value-free* continuation `k w = gen >>= fun p => pure (p.1, readMany w q p.2)` — a `w`-free
generator `gen` producing the visible output `p.1` and the `q`-read strategy `p.2`, with the drawn
commitment entering *only* through the fixed read game `readMany w q p.2` — fires with probability
at most `q · ε`.

This is the commit-sampler instance of `OracleComp.probEvent_bind_fire_le_of_gen`. The hypothesis
`hk` is exactly the value-freeness supplied by `blindStepProj_map_ghostBlindImpl_indep` (Stage 1):
because the ghost value never influences the run, the continuation's fire-marginal factors through
a `w`-free generator with the draw confined to the read-membership test
(`ghostBlindImpl_read_singletonGhost_bad`). Stage 3 instantiates this once per rejected attempt. -/
lemma ghostBlind_singleDraw_fire_le {α : Type} (pk : Stmt) (sk : Wit) {ε : ℝ≥0∞}
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ε)
    (q : ℕ) (gen : ProbComp (α × (List Bool → Commit))) (k : Commit → ProbComp (α × Bool))
    (hk : ∀ w : Commit, k w = gen >>= fun p => pure (p.1, OracleComp.readMany w q p.2)) :
    Pr[(fun z : α × Bool => z.2 = true) | (Prod.fst <$> ids.commit pk sk) >>= k]
      ≤ (q : ℝ≥0∞) * ε :=
  OracleComp.probEvent_bind_fire_le_of_gen hGuess q gen k hk

/-! ### M2: the deferred-sampling factorization

The **M2** content is the ghost-blind run's bad marginal *factoring* as a value-free deferred-draw
game. In this module it appears as the hypothesis `hfac` of `probEvent_ghostBlind_bad_le_of_fac`,
which is the σ-indexed (front-loaded hidden-target) form of the factorization. The headline takes
the σ-free route instead, charging the ghost-read bound through the first-moment residual
`readRecord_expected_coincidences_le` (the expected coincidence count of the value-free recorded
read-commit list with the recorded rejected draws).

Why it factors (the sound argument). In `ghostBlindImpl` an adversarial random-oracle read at a
ghost-cache hit answers from the *real* layer via `roStep` — identically to a miss — and only
*records* the would-hit by flipping the bad flag (`ghostBlindImpl_eq_ghostHybridImpl_false`,
`ghostBlindImpl_agree_good`). So the ghost-cache *values* are write-only side-data: they never
influence the run's outputs or continuation. Consequently the run's joint law of (adversary read
points, reject pattern / loop lengths, real cache) is produced by a value-free run that is
*independent of the stored commitment values*; those values are drawn `~ Prod.fst <$> ids.commit`
per *rejected* attempt and gated into the ghost cache by the reject decision.

Formalize as a deferred-sampling factorization: pull every rejected attempt's commitment draw
into the recorded drawn-list of the deferred handler `deferredDrawReadImpl`, independent of the
value-free recorded read-commit list. The expected coincidence count is then bounded by
`(#reads) · (#draws) · (max draw mass) ≤ (qH+1) · ε · E[#attempts]`, with `E[#attempts] ≤
qS/(1-p)` the aggregate of `tsum_probOutput_commit_mul_abort_le` over the `qS` signing queries
(each rejected attempt is reached with geometric probability, summed by `geomAttemptSum_le`).

Supporting tools for the σ-indexed form: the read-marginal equalities
`probEvent_ghostHybridImpl_read_bad_single_eq_lazyFire` /
`probOutput_eagerMultiReadBad_eq_lazyFire_or` (the signing-time→read-time draw commutation, here
applied to the value-free `ghostBlindImpl` continuation rather than the eager one whose
continuation depends on the read value), `probOutput_lazyGhostFire_one`, and the value-free
read-answer agreement (`ghostBlindImpl`'s hit branch is `roStep`, the same `map`-of-`roStep` as a
miss and as the lazy handler). Lifting the output-irrelevance through the `simulateQ` fold, so that
the per-rejected-attempt draws commute to the front independently of the intervening adversary
computation, is carried out on the σ-free route by
`evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead` in `Security/TapeFactorization.lean`.

This factorization route is sound precisely because `ghostBlindImpl` reads never feed the ghost
value into the run, so the draws are genuinely deferrable. -/

/-! ### Stage 3a: deferred-handler ingredients

The sound first-moment route couples the eager ghost-blind run to a *deferred* handler `impl₂` (a
genuine `QueryImpl`) via a per-step coupling relation `Rrun` on the two run distributions and the
two bad predicates `bad₁ / bad₂`. This block constructs those ingredients.

The deferred handler `deferredDrawImpl` carries, instead of eager-committed ghost keys, the
*accumulated list of drawn rejected-attempt commitments* (the front block, grown lazily as sign
steps draw) together with the real cache, the signed list, and the "some recorded read hit a drawn
commitment" flag. Its state is

  `DeferredState M Commit Chal :=
    (((M × Commit →ₒ Chal).QueryCache × List M) × List Commit) × Bool`.

Branch behaviour, designed so that the *observable* component (output, real cache, signed list)
coincides with the ghost-blind handler value-free (Stage 1):
* a **uniform** query forwards exactly as `ghostBlindImpl` does, touching neither the drawn list nor
  the bad flag;
* a **random-oracle read** answers from the real layer via `roStep` (identical read point and answer
  to `ghostBlindImpl`'s value-free hit/miss branches) and sets the bad flag iff the read point's
  commitment `mc.2` is among the accumulated drawn list — the deferred counterpart of the eager
  membership test against the ghost domain;
* a **signing** query runs the value-free signing body (`run_ghostSignBody_fst` recovers
  `transSignBody`, the accepted-only loop) for the output and real cache, and appends to the drawn
  list one i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw per rejected attempt, mirroring the eager
  ghost writes. -/

/-- State of the deferred-draw handler: real cache, signed-message list, the accumulated list of
drawn rejected-attempt commitments (the deferral front block), and the monotone "some recorded read
hit a drawn commitment" flag. The drawn list replaces the eager ghost cache: where `ghostBlindImpl`
commits sampled keys into its ghost layer, `deferredDrawImpl` only records the *list* of drawn
commitments, which is later read off as the front `drawList` block. -/
abbrev DeferredState (M Commit Chal : Type) : Type :=
  (((M × Commit →ₒ Chal).QueryCache × List M) × List Commit) × Bool

/-- Draw-collecting signing body: mirrors `ghostSignBody` but threads only the *real* cache and
accumulates the list of drawn *rejected*-attempt commitments instead of writing them to a ghost
layer. Returns `(output, drawn commits this query)`. Only the rejected-attempt commitments are
recorded, in attempt order; the accepted attempt (whose commitment is returned to the caller and
cached in the real layer) records nothing, exactly mirroring `ghostSignBody`, whose ghost layer
holds the rejected commitments and `uncacheQuery`-s the accepted one. Forgetting the drawn list
recovers `transSignBody` (the value-free output and real cache), and the drawn list is exactly the
list of i.i.d. raw `Prod.fst <$> ids.commit pk sk` samples taken on the *rejected* attempts — the
value-free side-data that never feeds back into the run's outputs. -/
@[expose] noncomputable def ghostSignDrawBody (pk : Stmt) (sk : Wit) (msg : M) :
    ℕ → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp) × List Commit)
  | 0 => pure (none, [])
  | n + 1 => do
    let (w, st) ← liftM (ids.commit pk sk)
    let c ← (liftM (uniformSample Chal) :
      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp Chal)
    let oz ← liftM (ids.respond pk sk st c)
    match oz with
    | some z =>
        modify fun cache => cache.cacheQuery (msg, w) c
        pure (some (w, z), [])
    | none =>
        let (res, ws) ← ghostSignDrawBody pk sk msg n
        pure (res, w :: ws)

omit [SampleableType Stmt] in
/-- One-step unfolding of the draw-collecting signing body, mirroring `run_ghostSignBody_succ`.
The body draws a commitment `w`, samples a challenge `ch`, responds, and on accept records *no*
drawn commitment (the accepted commit is returned, not deferred) while on reject prepends `w` to
the recursively collected list of rejected commitments. -/
lemma run_ghostSignDrawBody_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (re : (M × Commit →ₒ Chal).QueryCache) :
    (ghostSignDrawBody ids M pk sk msg (n + 1)).run re =
      ids.commit pk sk >>= fun ws =>
        uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re := by
  simp only [ghostSignDrawBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
    pure_bind]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => simp [StateT.run_modify]
  | none => simp [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp]

/-! ### Body-level tape resampling (the per-body half of the tape factorization)

The draw-collecting signing body `ghostSignDrawBody` draws each attempt's commitment *inline*. The
genuine fold-lift content of the ghost-read bound is to front-load every interleaved per-attempt
draw into one independent block, so the drawn *values* factor away from the value-free adversarial
read points. The body-level half of that program — recasting one signing body's inline draws as
consumption from a *pre-drawn* tape — is proved here as a distributional equality
`evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody`:

`𝒮[(ghostSignDrawBody … n).run re] = 𝒮[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`.

Pre-drawing the `n`-block of full `(Commit × PrvState)` commitment draws and consuming them
head-first (`tapeSignBody`) is distributionally identical to drawing them inline: the control flow
(accept/reject, via the inline `uniformSample`/`respond`) reads the *same* tape values, and the
unused suffix on an early accept is discarded. The proof is a structural induction on `n` that, at
each attempt, commutes the recursive front block `drawList n` past the inline
`uniformSample`/`respond` draws (`evalSPMF_bind_comm_probComp`, the i.i.d. resampling step) and
matches the reject-branch recursion to the inductive hypothesis.

This is the local, per-body `bind`-commutation. Its lift across the *opaque adversary*
`simulateQ (oa)` fold — the interleaved per-query draw blocks all commuting to the front, past the
adaptive read points — is `evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead` in
`Security/TapeFactorization.lean`. -/

/-- **i.i.d. bind-commutation at the distribution level for `ProbComp`.** Two independent draws
`oa`, `ob` feeding a common continuation `k` may be drawn in either order without changing the
output distribution. The `OracleComp` monad is *not* commutative as a free monad (its `bind` is
syntactic), but its `evalSPMF` image into `SPMF` is: the two iterated sums over the independent
draws exchange by `ENNReal.tsum_comm`. This is the local resampling step that front-loads an
output-irrelevant draw past its continuation. -/
theorem evalSPMF_bind_comm_probComp {α β γ : Type} (oa : ProbComp α) (ob : ProbComp β)
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

/-- **Dropping a never-failing prefix at the distribution level.** A leading draw `od` whose
continuation ignores its value contributes only its total mass; when `od` never fails (mass `1`,
e.g. a `drawList` front block) it can be discarded from the output distribution. -/
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

/-- **Tape-consuming signing body.** Identical to `ghostSignDrawBody` except that each attempt's
commitment draw `(Commit × PrvState)` is *consumed* from a pre-drawn tape (head-first) instead of
drawn inline. The challenge sampling and response stay inline. On accept the remaining tape suffix
is discarded; an empty tape ends the loop (mirroring budget exhaustion). The recorded
rejected-commit list is built exactly as in `ghostSignDrawBody`. -/
@[expose] noncomputable def tapeSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    List (Commit × PrvState) → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp) × List Commit)
  | [] => pure (none, [])
  | (w, st) :: rest => do
    let c ← (liftM (uniformSample Chal) :
      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp Chal)
    let oz ← liftM (ids.respond pk sk st c)
    match oz with
    | some z =>
        modify fun cache => cache.cacheQuery (msg, w) c
        pure (some (w, z), [])
    | none =>
        let (res, ws) ← tapeSignBody pk sk msg rest
        pure (res, w :: ws)

omit [SampleableType Stmt] in
/-- One-step unfolding of the tape-consuming signing body on a non-empty tape, mirroring
`run_ghostSignDrawBody_succ`: the head `(w, st)` is consumed, a challenge sampled and a response
computed; on accept the body records no commitment, on reject it prepends `w` to the recursively
collected list and continues on the tape tail. -/
lemma run_tapeSignBody_cons (pk : Stmt) (sk : Wit) (msg : M) (w : Commit) (st : PrvState)
    (rest : List (Commit × PrvState)) (re : (M × Commit →ₒ Chal).QueryCache) :
    (tapeSignBody ids M pk sk msg ((w, st) :: rest)).run re =
      uniformSample Chal >>= fun ch =>
        ids.respond pk sk st ch >>= fun oz =>
          match oz with
          | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
          | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
              (tapeSignBody ids M pk sk msg rest).run re := by
  simp only [tapeSignBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT, pure_bind]
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => simp [StateT.run_modify]
  | none => simp [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp]

omit [SampleableType Stmt] in
/-- **The body-level tape resampling equality.** Drawing one signing body's `n` attempt
commitments inline (`ghostSignDrawBody`) is distributionally identical to pre-drawing the `n`-block
of full commitment draws into a tape and consuming it head-first (`tapeSignBody`):

`𝒮[(ghostSignDrawBody … n).run re] = 𝒮[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`.

The proof inducts on `n`: at each attempt, the recursive front block `drawList n` is commuted past
the inline `uniformSample`/`respond` draws (the i.i.d. resampling step
`evalSPMF_bind_comm_probComp`), the accepting branch discards the unused suffix
(`evalSPMF_bind_const_neverFails`, `drawList` never
fails), and the rejecting branch matches the inductive hypothesis. This is the per-body half of the
tape factorization; its lift across the opaque adversary fold is
`evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`. -/
theorem evalSPMF_ghostSignDrawBody_eq_drawList_tapeSignBody (pk : Stmt) (sk : Wit) (msg : M)
    (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache) :
    𝒮[(ghostSignDrawBody ids M pk sk msg n).run re] =
      𝒮[OracleComp.drawList (ids.commit pk sk) n >>= fun tape =>
          (tapeSignBody ids M pk sk msg tape).run re] := by
  induction n generalizing re with
  | zero => simp [ghostSignDrawBody, tapeSignBody, OracleComp.drawList]
  | succ n ih =>
      rw [run_ghostSignDrawBody_succ, OracleComp.drawList]
      simp only [bind_assoc, pure_bind]
      rw [evalSPMF_bind, evalSPMF_bind]
      refine congrArg (𝒮[ids.commit pk sk] >>= ·) (funext fun ws => ?_)
      obtain ⟨w, st⟩ := ws
      simp only [run_tapeSignBody_cons]
      set dl := OracleComp.drawList (ids.commit pk sk) n with hdl
      have hdlmass : Pr[⊥ | dl] = 0 := by rw [hdl]; exact OracleComp.probFailure_drawList _ _
      rw [show (𝒮[dl >>= fun rest => uniformSample Chal >>= fun ch =>
            ids.respond pk sk st ch >>= fun oz =>
              (match oz with
              | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
              | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                  (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)])
          = 𝒮[uniformSample Chal >>= fun ch => dl >>= fun rest =>
              ids.respond pk sk st ch >>= fun oz =>
                (match oz with
                | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
                | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                    (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)] from
        evalSPMF_bind_comm_probComp dl (uniformSample Chal) _]
      refine evalSPMF_bind_congr_left (uniformSample Chal) _ _ (fun ch => ?_)
      rw [show (𝒮[dl >>= fun rest => ids.respond pk sk st ch >>= fun oz =>
            (match oz with
            | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
            | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)])
          = 𝒮[ids.respond pk sk st ch >>= fun oz => dl >>= fun rest =>
              (match oz with
              | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
              | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                  (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)] from
        evalSPMF_bind_comm_probComp dl (ids.respond pk sk st ch) _]
      refine evalSPMF_bind_congr_left (ids.respond pk sk st ch) _ _ (fun oz => ?_)
      cases oz with
      | some z => rw [evalSPMF_bind_const_neverFails dl hdlmass]
      | none =>
          change 𝒮[(fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
            (ghostSignDrawBody ids M pk sk msg n).run re] = _
          rw [evalSPMF_map_eq_of_evalSPMF_eq (ih re)]
          rw [map_eq_bind_pure_comp, bind_assoc]
          refine evalSPMF_bind_congr_left dl _ _ (fun rest => ?_)
          rw [map_eq_bind_pure_comp]

omit [SampleableType Stmt] in
/-- **Expected drawn-list length of the draw-collecting signing body.** Each attempt of
`ghostSignDrawBody` records exactly one i.i.d. raw `Prod.fst <$> ids.commit pk sk` commitment;
the loop continues only on a fresh-challenge rejection (probability `≤ p` per attempt), so the
expected length of the collected list is at most `∑_{a<n} p ^ a`, the geometric attempt-count
fold (`geomAttemptSum_le`) that bounds the per-signing-query draw count. This is the deferred-draw
counterpart of `tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le`: the drawn list replaces
the eager ghost layer, so its length plays the role of the ghost-cache size. -/
lemma tsum_probOutput_run_ghostSignDrawBody_mul_length_le (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞)
        ≤ ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a := by
  intro n
  induction n with
  | zero =>
      intro re
      simp only [ghostSignDrawBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro re
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a with hS
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ a =
          1 + ENNReal.ofReal p_abort * S := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => pow_succ' _ _
      rw [run_ghostSignDrawBody_succ, tsum_probOutput_bind_mul]
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
          ≤ 1 + Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] * S := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
            ≤ 1 + Pr[= none | ids.respond pk sk ws.2 ch] * S := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          have h_oz : ∀ oz : Option Resp,
              (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= z | (match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re :
                  ProbComp ((Option (Commit × Resp) × List Commit) ×
                    (M × Commit →ₒ Chal).QueryCache))] * (z.1.2.length : ℝ≥0∞))
              ≤ 1 + (if oz = none then S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), add_zero, tsum_probOutput_pure_mul]
                simp
            | none =>
                rw [if_pos rfl]
                -- length of `ws.1 :: rws.1.2` is `1 + rws.1.2.length`; rewrite map as bind+pure.
                rw [map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
                calc (∑' z : (Option (Commit × Resp) × List Commit) ×
                      (M × Commit →ₒ Chal).QueryCache,
                    Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                      (∑' y : (Option (Commit × Resp) × List Commit) ×
                          (M × Commit →ₒ Chal).QueryCache,
                        Pr[= y | (pure ((fun rws : (Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache =>
                          ((rws.1.1, ws.1 :: rws.1.2), rws.2)) z) :
                          ProbComp ((Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache))] * (y.1.2.length : ℝ≥0∞)))
                    = ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (1 + (z.1.2.length : ℝ≥0∞)) := by
                      refine tsum_congr fun z => ?_
                      rw [tsum_probOutput_pure_mul]
                      simp only [List.length_cons]
                      push_cast
                      ring_nf
                  _ = (∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re]) +
                      ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (z.1.2.length : ℝ≥0∞) := by
                      rw [← ENNReal.tsum_add]
                      exact tsum_congr fun z => by rw [mul_add, mul_one]
                  _ ≤ 1 + S := add_le_add tsum_probOutput_le_one (ih re)
          refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_oz) ?_
          refine add_le_add_right (le_of_eq ?_) _
          rw [tsum_eq_single (none : Option Resp) fun oz hoz => by simp [hoz]]
          simp [mul_comm]
        refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ch) ?_
        refine add_le_add_right (le_of_eq ?_) _
        rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ws) ?_
      rw [hSucc]
      gcongr
      calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            (Pr[= none | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch] * S)
          = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch]) * S := by
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun ws => (mul_assoc _ _ _).symm
        _ ≤ ENNReal.ofReal p_abort * S :=
            mul_le_mul_left (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _

omit [SampleableType Stmt] in
/-- **Tight expected drawn-list length of the draw-collecting signing body.** Sharper companion to
`tsum_probOutput_run_ghostSignDrawBody_mul_length_le`: the expected number of *recorded* (rejected)
commitments of one `ghostSignDrawBody` run is at most the *reject-gated* geometric sum
`∑_{a<n} ofReal p^(a+1)` (each summand starts at `p^1`, not `p^0`). The first attempt's commitment
is recorded only on a *rejection* (probability `≤ p`); the accepting attempt records nothing. This
is the tight reject-count bound — `∑_{a<n} p^(a+1) ≤ p/(1-p)` — that the attempt-count law of the
redrafted residual needs: combined with the unconditional `+1` per signing query (the signed-message
list always grows by one), it gives the clean per-query charge `∑_{a≤n} p^a ≤ 1/(1-p)`, whereas the
loose bound `∑_{a<n} p^a` already saturates `1/(1-p)` for the rejects alone and cannot absorb the
extra `+1`. -/
lemma tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞)
        ≤ ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ (a + 1) := by
  intro n
  induction n with
  | zero =>
      intro re
      simp only [ghostSignDrawBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro re
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ (a + 1) with hS
      -- Target: the `(n+1)`-attempt reject-count expectation is `≤ ofReal p * (1 + S)`, which
      -- equals `∑_{a<n+1} ofReal p^(a+1)`.
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ (a + 1)
          = ENNReal.ofReal p_abort * (1 + S) := by
        rw [mul_add, mul_one, hS, Finset.mul_sum, Finset.sum_range_succ', pow_succ, pow_zero,
          one_mul, add_comm]
        congr 1
        exact Finset.sum_congr rfl fun a _ => by rw [← pow_succ']
      rw [hSucc, run_ghostSignDrawBody_succ, tsum_probOutput_bind_mul]
      -- Per-commit-draw `ws`: the recorded list is empty on accept and `ws.1 :: recursive` on
      -- reject; reject happens with probability `Pr[= none | uniformSample >>= respond]`.
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
          ≤ Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] * (1 + S) := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
            ≤ Pr[= none | ids.respond pk sk ws.2 ch] * (1 + S) := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          -- Per response `oz`: accept contributes `0`, reject contributes `1 + S`.
          have h_oz : ∀ oz : Option Resp,
              (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= z | (match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re :
                  ProbComp ((Option (Commit × Resp) × List Commit) ×
                    (M × Commit →ₒ Chal).QueryCache))] * (z.1.2.length : ℝ≥0∞))
              ≤ (if oz = none then (1 : ℝ≥0∞) + S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), tsum_probOutput_pure_mul]
                simp [List.length]
            | none =>
                rw [if_pos rfl, map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
                calc (∑' z : (Option (Commit × Resp) × List Commit) ×
                      (M × Commit →ₒ Chal).QueryCache,
                    Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                      (∑' y : (Option (Commit × Resp) × List Commit) ×
                          (M × Commit →ₒ Chal).QueryCache,
                        Pr[= y | (pure ((fun rws : (Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache =>
                          ((rws.1.1, ws.1 :: rws.1.2), rws.2)) z) :
                          ProbComp ((Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache))] * (y.1.2.length : ℝ≥0∞)))
                    = ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (1 + (z.1.2.length : ℝ≥0∞)) := by
                      refine tsum_congr fun z => ?_
                      rw [tsum_probOutput_pure_mul]
                      simp only [List.length_cons]
                      push_cast
                      ring_nf
                  _ = (∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re]) +
                      ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (z.1.2.length : ℝ≥0∞) := by
                      rw [← ENNReal.tsum_add]
                      exact tsum_congr fun z => by rw [mul_add, mul_one]
                  _ ≤ 1 + S := add_le_add tsum_probOutput_le_one (ih re)
          refine le_trans (ENNReal.tsum_le_tsum fun oz =>
            mul_le_mul_right (h_oz oz) _) ?_
          rw [tsum_eq_single (none : Option Resp) fun oz hoz => by
            rw [if_neg hoz, mul_zero]]
          rw [if_pos rfl, mul_comm]
        refine le_trans (ENNReal.tsum_le_tsum fun ch =>
          mul_le_mul_right (h_ch ch) _) ?_
        rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
        exact le_of_eq (tsum_congr fun ch => (mul_assoc _ _ _).symm)
      refine le_trans (ENNReal.tsum_le_tsum fun ws => mul_le_mul_right (h_ws ws) _) ?_
      calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            (Pr[= none | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch] * (1 + S))
          = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch]) * (1 + S) := by
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun ws => (mul_assoc _ _ _).symm
        _ ≤ ENNReal.ofReal p_abort * (1 + S) :=
            mul_le_mul_left (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _

omit [SampleableType Stmt] in
/-- **Single-signing-body resampling over-count.** Testing the *drawn list* produced by one
`ghostSignDrawBody` run (the rejected-attempt commitments, write-only side-data) against any *fixed*
read strategy `σ` with `q` reads fires with probability at most testing `n` *fresh* i.i.d. raw
`Prod.fst <$> ids.commit pk sk` draws against the same strategy (`drawList … n`, where `n` is the
attempt budget `maxAttempts`).

This is the genuine per-query resampling content, isolated to one signing body. The drawn list of
the body is *not* equal in law to `n` fresh raw draws (the rejected draws are skewed by the
rejection-conditioning `commit | reject`), but the firing event over-counts to the fresh game: on
the accept branch the body records *no* commitment (so its read-game fires with probability `0`,
dominated by the fresh side, which still draws and tests one value); on the reject branch the body's
recorded commitment is a raw `Prod.fst <$> ids.commit pk sk` draw — distributed exactly as the fresh
head — and its `readMany` test matches the fresh head's, while the recursive rejected list is
dominated by the recursive fresh list (induction). The read strategy `σ` is *fixed* (the read points
are determined by the all-miss reply history; the drawn values never feed them — value-freeness),
which is what lets a single `σ` dominate both sides. The corresponding fold-level statement —
front-loading every signing query's interleaved draws into one aggregate `drawList` block — is
`evalSPMF_deferredDrawRead_eq_drawList_tapeDrawRead`, which the headline uses on the σ-free
first-moment route. This lemma is the single-body over-count in σ-indexed form; it is not on the
live headline path (which charges the expected coincidence count directly). -/
lemma ghostSignDrawBody_readManyList_le_drawList (pk : Stmt) (sk : Wit) (msg : M)
    (q : ℕ) (σ : List Bool → Commit) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      Pr[(fun b : Bool => b = true) |
          (ghostSignDrawBody ids M pk sk msg n).run re >>= fun rws =>
            pure (OracleComp.readManyList rws.1.2 q σ)]
        ≤ Pr[(fun b : Bool => b = true) |
            OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun ws =>
              pure (OracleComp.readManyList ws q σ)] := by
  intro n
  induction n with
  | zero =>
      intro re
      simp [ghostSignDrawBody, OracleComp.drawList, OracleComp.readManyList]
  | succ n ih =>
      intro re
      -- Unfold one attempt on the left and one fresh draw on the right; both bind over the same
      -- raw `ids.commit pk sk` draw, so compare the per-draw fire-marginals termwise.
      rw [run_ghostSignDrawBody_succ]
      rw [OracleComp.drawList, bind_assoc, bind_map_left]
      simp only [bind_assoc, pure_bind]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun ws => ?_
      gcongr
      -- Per commit draw `ws`: name the recursive fresh `n`-draw game and the recursive body-`n`
      -- game; the latter is `≤` the former by the inductive hypothesis (`ih`).
      set RHSinner : ℝ≥0∞ := Pr[(fun b : Bool => b = true) |
        OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun rest =>
          pure (OracleComp.readManyList rest q σ)] with hRHSinner
      by_cases hhead : OracleComp.readMany ws.1 q σ = true
      · -- The head already fires: the RHS `readManyList (ws.1 :: rest)` is always `true`, so the
        -- RHS per-draw marginal is the full mass of `drawList n` = 1 ≥ the LHS.
        refine le_trans probEvent_le_one (le_of_eq ?_)
        symm
        have hcongr : (OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun rest =>
              pure (OracleComp.readManyList (ws.1 :: rest) q σ))
            = (OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun _ =>
              (pure true : ProbComp Bool)) := by
          refine bind_congr fun rest => ?_
          rw [OracleComp.readManyList, List.any_cons, hhead, Bool.true_or]
        rw [hcongr, probEvent_bind_eq_tsum]
        simp only [probEvent_pure, if_pos]
        rw [ENNReal.tsum_mul_right, OracleComp.tsum_probOutput_drawList_eq_one, one_mul]
      · -- The head misses: the RHS reduces to the recursive fresh game `RHSinner`, and the LHS is
        -- dominated by the recursive body-`n` game, which is `≤ RHSinner` by `ih`.
        rw [Bool.not_eq_true] at hhead
        have hRHS : Pr[(fun b : Bool => b = true) |
              OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun rest =>
                pure (OracleComp.readManyList (ws.1 :: rest) q σ)] = RHSinner := by
          rw [hRHSinner]
          refine probEvent_bind_congr fun rest _ => ?_
          rw [OracleComp.readManyList, List.any_cons, hhead, Bool.false_or, OracleComp.readManyList]
        rw [hRHS]
        -- The LHS per-draw game is dominated by the recursive body-`n` game: drop the
        -- `uniformSample`/`respond` draws (mass `≤ 1`); the accept branch records `[]`
        -- (`readManyList [] = false`, fires with probability `0`) and the reject branch's head
        -- test `readMany ws.1 q σ` misses (`hhead`), so its `readManyList (ws.1 :: inner)` reduces
        -- to the body-`n` game's `readManyList inner`.
        refine le_trans ?_ (ih re)
        refine probEvent_bind_le_of_forall_le fun ch _ => ?_
        refine probEvent_bind_le_of_forall_le fun oz _ => ?_
        cases oz with
        | some z => simp [OracleComp.readManyList]
        | none =>
            rw [bind_map_left]
            refine le_of_eq ?_
            refine probEvent_bind_congr fun rws _ => ?_
            rw [OracleComp.readManyList, List.any_cons, hhead, Bool.false_or,
              OracleComp.readManyList]

/-- The deferred-draw handler for the adversary's oracles, driving the distribution-level mono
skeleton against `ghostBlindImpl`. Carries the accumulated drawn-commitment list and a monotone
read-hit flag in place of the eager ghost cache (see `DeferredState`). -/
@[expose] noncomputable def deferredDrawImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (DeferredState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun cu => (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
        roStep M s.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
        (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1

omit [SampleableType Stmt] in
/-- **Per-step expected drawn-list length growth of the deferred-draw handler.** One step of
`deferredDrawImpl` grows the expected drawn-list length by at most `1/(1-p)` on a signing query and
by `0` on a uniform or random-oracle-read query (which leave the drawn list untouched). The
signing-step bound is the per-query draw count `tsum_probOutput_run_ghostSignDrawBody_mul_length_le`
folded with `geomAttemptSum_le`. This is the per-step charge that the run-level mean fold
`deferredDraw_run_expected_length_le` telescopes against `signHashQueryBound`. -/
lemma deferredDrawImpl_step_expected_length_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredState M Commit Chal,
      Pr[= z | (deferredDrawImpl ids M maxAttempts pk sk t).run s] * (z.2.1.2.length : ℝ≥0∞))
      ≤ (s.1.2.length : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · -- UNIFORM: state untouched, drawn list `s.1.2` preserved.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · -- READ: writes only the base cache / bad flag; drawn list `s.1.2` preserved.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
            roStep M s.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawImpl, StateT.run_mk]
      rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · -- SIGN: drawn list becomes `s.1.2 ++ alc.1.2`; expected new length ≤ 1/(1-p).
    rw [if_pos (by simp)]
    have hrun : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2)))
      (fun z => (z.2.1.2.length : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              ((s.1.2.length : ℝ≥0∞) + (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append]
          push_cast
          ring
      _ = (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (s.1.2.length : ℝ≥0∞)) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (alc.1.2.length : ℝ≥0∞) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ (s.1.2.length : ℝ≥0∞) + ENNReal.ofReal (1 / (1 - p_abort)) := by
          refine add_le_add ?_ ?_
          · rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          · exact le_trans (tsum_probOutput_run_ghostSignDrawBody_mul_length_le ids M pk sk msg
              hAbort maxAttempts s.1.1.1) (geomAttemptSum_le maxAttempts hp₀ hp)

omit [SampleableType Stmt] in
/-- **Sign-step coupling.** The eager ghost signing body `ghostSignBody` and the deferred draw-
collecting body `ghostSignDrawBody` are coupled, with their `ids.commit`/`uniformSample`/`respond`
draws matched, so that the outputs and real caches agree and the eager ghost layer's key domain is
covered by the front drawn list `drawn` extended with the body's collected commitments. Proved by
induction on the attempt budget: the accept branch writes the accepted commitment to both real
caches and leaves the ghost layer covered by `drawn`; the reject branch records the commitment in
the ghost layer and prepends it to the deferred collected list, recursing with a wider cover. -/
theorem signBody_couple (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache) (drawn : List Commit),
      (∀ mc : M × Commit, gh mc ≠ none → mc.2 ∈ drawn) →
      OracleComp.ProgramLogic.Relational.RelTriple
        ((ghostSignBody ids M pk sk msg n).run (re, gh))
        ((ghostSignDrawBody ids M pk sk msg n).run re)
        (fun p₁ p₂ => p₁.1 = p₂.1.1 ∧ p₁.2.1 = p₂.2 ∧
          (∀ mc : M × Commit, p₁.2.2 mc ≠ none → mc.2 ∈ drawn ++ p₂.1.2))
  | 0, re, gh, drawn, hcov => by
      simp only [ghostSignBody, ghostSignDrawBody, StateT.run_pure]
      exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        ⟨rfl, rfl, fun mc hmc => List.mem_append.2 (Or.inl (hcov mc hmc))⟩
  | (n+1), re, gh, drawn, hcov => by
      have hrun₁ : (ghostSignBody ids M pk sk msg (n+1)).run (re, gh) =
          (ids.commit pk sk >>= fun wst => uniformSample Chal >>= fun c =>
            ids.respond pk sk wst.2 c >>= fun oz =>
              match oz with
              | some z => pure (some (wst.1, z),
                  (re.cacheQuery (msg, wst.1) c, uncacheQuery M gh (msg, wst.1)))
              | none => (ghostSignBody ids M pk sk msg n).run
                  (re, gh.cacheQuery (msg, wst.1) c)) := by
        simp only [ghostSignBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
          pure_bind]
        refine congrArg (ids.commit pk sk >>= ·) (funext fun wst => ?_)
        refine congrArg (uniformSample Chal >>= ·) (funext fun c => ?_)
        refine congrArg (ids.respond pk sk wst.2 c >>= ·) (funext fun oz => ?_)
        cases oz with
        | some z => simp [StateT.run_modify]
        | none => simp [StateT.run_bind, StateT.run_modify]
      have hrun₂ : (ghostSignDrawBody ids M pk sk msg (n+1)).run re =
          (ids.commit pk sk >>= fun wst => uniformSample Chal >>= fun c =>
            ids.respond pk sk wst.2 c >>= fun oz =>
              match oz with
              | some z => pure ((some (wst.1, z), []), re.cacheQuery (msg, wst.1) c)
              | none => (fun rws => ((rws.1.1, wst.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re) := by
        simp only [ghostSignDrawBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
          pure_bind]
        refine congrArg (ids.commit pk sk >>= ·) (funext fun wst => ?_)
        refine congrArg (uniformSample Chal >>= ·) (funext fun c => ?_)
        refine congrArg (ids.respond pk sk wst.2 c >>= ·) (funext fun oz => ?_)
        cases oz with
        | some z => simp [StateT.run_modify]
        | none => simp [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp]
      rw [hrun₁, hrun₂]
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_
      rintro wst _ (rfl : wst = _)
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_
      rintro c _ (rfl : c = _)
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_
      rintro oz _ (rfl : oz = _)
      cases oz with
      | some z =>
          refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, rfl, ?_⟩
          intro mc hmc
          -- accept branch: ghost layer is `uncacheQuery M gh (msg, wst.1)`, whose domain ⊆ dom gh
          refine List.mem_append.2 (Or.inl (hcov mc ?_))
          by_cases hmceq : mc = (msg, wst.1)
          · exact absurd (by simp [uncacheQuery, hmceq]) hmc
          · simpa [uncacheQuery, hmceq] using hmc
      | none =>
          have hcov' : ∀ mc : M × Commit, (gh.cacheQuery (msg, wst.1) c) mc ≠ none →
              mc.2 ∈ drawn ++ [wst.1] := by
            intro mc hmc
            by_cases hmceq : mc = (msg, wst.1)
            · subst hmceq; exact List.mem_append.2 (Or.inr (by simp))
            · rw [QueryCache.cacheQuery_of_ne _ _ hmceq] at hmc
              exact List.mem_append.2 (Or.inl (hcov mc hmc))
          have hih := signBody_couple pk sk msg n re (gh.cacheQuery (msg, wst.1) c)
            (drawn ++ [wst.1]) hcov'
          rw [show ((fun rws : (Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache => ((rws.1.1, wst.1 :: rws.1.2), rws.2)) <$>
              (ghostSignDrawBody ids M pk sk msg n).run re)
              = ((ghostSignDrawBody ids M pk sk msg n).run re >>= fun rws =>
                pure ((rws.1.1, wst.1 :: rws.1.2), rws.2)) from by rw [map_eq_bind_pure_comp]; rfl]
          rw [show ((ghostSignBody ids M pk sk msg n).run (re, gh.cacheQuery (msg, wst.1) c))
              = ((ghostSignBody ids M pk sk msg n).run (re, gh.cacheQuery (msg, wst.1) c) >>= pure)
              from by rw [bind_pure]]
          refine OracleComp.ProgramLogic.Relational.relTriple_bind hih ?_
          rintro p₁ p₂ ⟨hout, hcache, hghcov⟩
          refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ⟨hout, hcache, ?_⟩
          intro mc hmc
          have hmem := hghcov mc hmc
          rw [List.append_assoc] at hmem
          simpa using hmem

/-! ### Stage 3a: the deferred-coupling reduction (Piece A)

The eager ghost-blind bad marginal reduces, through the deferred-draw handler `deferredDrawImpl`,
to the deferred run's bad marginal:

* **Piece A** (`ghostBlind_bad_le_deferredDraw`): a *pointwise coupling* of the eager ghost-blind
  run with the deferred-draw run, established on the pointwise mono skeleton
  `relTriple_simulateQ_run_mono` carrying the state invariant `deferredCoupleInv` (real cache and
  signed list equal; ghost domain covered by the drawn-commitment list; bad-flag ordered). The
  read step is an output-equal coupling (both answer from the real layer via `roStep`, and the
  membership flag fires more readily on the deferred side because it ignores the message component);
  the sign step couples the two bodies' `ids.commit` draws so the eager ghost writes and the
  deferred draws stay in lockstep. `probEvent_le_of_relTriple_imp` then reads off the ordered bad
  marginals.

The deferred run's bad marginal is then carried — through the read-recording reduction
(`deferredDraw_bad_le_readRecord`) and the first-moment Markov step
(`readRecord_pred_le_expected_coincidences`) — to the expected coincidence count bounded by
`readRecord_expected_coincidences_le`.

This reduction uses the pointwise coupling because the bad flags *are* pointwise linkable (eager
ghost-membership ⟹ deferred commitment-membership, since the drawn list grows in lockstep with the
ghost cache), so the pointwise `relTriple_simulateQ_run_mono` route applies. The value-free charge
that this reduction feeds into is `readRecord_expected_coincidences_le`.

The state invariant linking the eager `GhostState` and the deferred `DeferredState`: real cache and
signed-message list agree, every key in the ghost cache has its commitment recorded in the drawn
list, and the bad flag is ordered (eager-bad ⟹ deferred-bad). The read points coincide because both
sides answer from the (shared) real layer. -/
omit [SampleableType Stmt] in
/-- The coupling invariant between the eager ghost-blind state and the deferred-draw state: real
cache and signed list agree, every ghost-cache key's commitment is in the drawn list, and the bad
flag is ordered. -/
@[expose] def deferredCoupleInv
    (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal) : Prop :=
  s₁.1.1.1 = s₂.1.1.1 ∧ s₁.1.2 = s₂.1.1.2 ∧
    (∀ mc : M × Commit, s₁.1.1.2 mc ≠ none → mc.2 ∈ s₂.1.2) ∧
    (s₁.2 = true → s₂.2 = true)

omit [SampleableType Stmt] in
/-- **Per-query coupling step for the ghost-blind → deferred coupling.** From any pair of
`deferredCoupleInv`-related states, one step of the eager ghost-blind handler couples with one step
of the deferred-draw handler with equal output and the invariant preserved.

* **Uniform** steps forward the same draw; the state is untouched, so the invariant is inherited.
* **Read** steps answer from the shared real layer via `roStep` (same answer, same cache update);
  the eager bad flag fires on ghost-domain membership and the deferred one on drawn-list membership;
  the domain-coverage invariant makes the eager fire imply the deferred fire (it ignores the message
  component), preserving the bad ordering.
* **Sign** steps invoke `signBody_couple`: the matched `ids.commit` draws keep the outputs and real
  caches equal and extend the drawn list to cover the new ghost writes; the bad flag is intact. -/
theorem deferredCouple_step (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (u₁ : GhostState M Commit Chal) (u₂ : DeferredState M Commit Chal)
    (hu : deferredCoupleInv M u₁ u₂) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((ghostBlindImpl ids M maxAttempts pk sk t).run u₁)
      ((deferredDrawImpl ids M maxAttempts pk sk t).run u₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ deferredCoupleInv M p₁.2 p₂.2) := by
  obtain ⟨hre, hl, hdom, hbad⟩ := hu
  rcases t with (n | mc) | msg
  · -- UNIFORM: both forward the same draw; state untouched.
    have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₁ =
        (fun u => (u, u₁)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₂ =
        (fun u => (u, u₂)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    rw [hrun₁, hrun₂]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
    rintro a b (rfl : a = b)
    exact ⟨rfl, hre, hl, hdom, hbad⟩
  · -- READ: answer from the shared real layer; bad flag dominated under domain coverage.
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₂ =
        (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, u₂.1.1.2), u₂.1.2), u₂.2 || decide (mc.2 ∈ u₂.1.2)))) <$>
          roStep M u₂.1.1.1 mc := rfl
    cases hgh : u₁.1.1.2 mc with
    | none =>
        have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₁ =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, (((cu.2, u₁.1.1.2), u₁.1.2), u₁.2))) <$> roStep M u₁.1.1.1 mc := by
          rw [ghostBlindImpl_eq_ghostHybridImpl_false]
          exact ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk hgh
        rw [hrun₁, hrun₂, hre]
        refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
          (OracleComp.ProgramLogic.Relational.relTriple_post_mono
            (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
        rintro a b (rfl : a = b)
        exact ⟨rfl, rfl, hl, hdom, fun hb => by rw [hbad hb]; rfl⟩
    | some v =>
        have hgh2 : u₁.1.1.2 mc ≠ none := by rw [hgh]; exact Option.some_ne_none v
        have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₁ =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, (((cu.2, u₁.1.1.2), u₁.1.2), true))) <$> roStep M u₁.1.1.1 mc := by
          rw [ghostBlindImpl_eq_ghostHybridImpl_false,
            ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk hgh,
            if_neg Bool.false_ne_true]
        rw [hrun₁, hrun₂, hre]
        refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
          (OracleComp.ProgramLogic.Relational.relTriple_post_mono
            (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
        rintro a b (rfl : a = b)
        have hdef : (u₂.2 || decide (mc.2 ∈ u₂.1.2)) = true := by simp [hdom mc hgh2]
        exact ⟨rfl, rfl, hl, hdom, fun _ => hdef⟩
  · -- SIGN: couple the two signing bodies via `signBody_couple`; bad flag untouched.
    have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inr msg)).run u₁ =
        (fun alc : Option (Commit × Resp) ×
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
          (alc.1, ((alc.2, msg :: u₁.1.2), u₁.2))) <$>
          (ghostSignBody ids M pk sk msg maxAttempts).run u₁.1.1 := by
      rw [ghostBlindImpl_eq_ghostHybridImpl_false]
      exact ghostHybridImpl_run_sign ids M maxAttempts false pk sk msg u₁
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run u₂ =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: u₂.1.1.2), u₂.1.2 ++ alc.1.2), u₂.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run u₂.1.1.1 := rfl
    rw [hrun₁, hrun₂]
    have hu11 : u₁.1.1 = (u₂.1.1.1, u₁.1.1.2) := by rw [← hre]
    rw [hu11]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (signBody_couple ids M pk sk msg maxAttempts u₂.1.1.1 u₁.1.1.2 u₂.1.2 hdom) ?_)
    rintro p₁ p₂ ⟨hout, hcache, hghcov⟩
    exact ⟨hout, hcache, by rw [hl], hghcov, hbad⟩

omit [SampleableType Stmt] in
/-- **The ghost-blind → deferred run coupling.** By induction on the adversary computation `oa`,
the eager ghost-blind run and the deferred-draw run are coupled with the invariant
`deferredCoupleInv` preserved at every leaf, using `deferredCouple_step` at each query and the
inductive hypothesis for the continuation. -/
theorem deferredCouple_run {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal),
      deferredCoupleInv M s₁ s₂ →
      OracleComp.ProgramLogic.Relational.RelTriple
        ((simulateQ (ghostBlindImpl ids M maxAttempts pk sk) oa).run s₁)
        ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₂)
        (fun q₁ q₂ => deferredCoupleInv M q₁.2 q₂.2) := by
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
        (deferredCouple_step ids M maxAttempts pk sk t s₁ s₂ hinv) ?_
      rintro p₁ p₂ ⟨hout, hinv'⟩
      rw [show p₁.1 = p₂.1 from hout]
      exact ih p₂.1 p₁.2 p₂.2 hinv'

omit [SampleableType Stmt] in
/-- **Piece A: the ghost-blind → deferred coupling.** The ghost-blind run's bad marginal is at most
the deferred-draw run's bad marginal, from any pair of `deferredCoupleInv`-related start states.

Reads off the bad-flag ordering component of the invariant from the run coupling
`deferredCouple_run` via `probEvent_le_of_relTriple_imp`. -/
theorem ghostBlind_bad_le_deferredDraw {γ : Type}
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal)
    (hinv : deferredCoupleInv M s₁ s₂) :
    Pr[fun z : γ × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) oa).run s₁]
      ≤ Pr[fun z : γ × DeferredState M Commit Chal => z.2.2 = true |
          (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₂] :=
  OracleComp.ProgramLogic.Relational.probEvent_le_of_relTriple_imp
    (deferredCouple_run ids M maxAttempts pk sk oa s₁ s₂ hinv)
    (fun _ _ hp => hp.2.2.2)

omit [SampleableType Stmt] in
/-- **The drawn list only grows.** Every reachable final state of the deferred-draw run from a
start state `s` has the start's drawn list `s.1.2` as a prefix: uniform and read steps leave the
drawn list untouched, and a signing step appends (`s.1.2 ++ alc.1.2`). Hence the number of *new*
draws is `final.length - s.1.2.length` and is well-behaved (`s.1.2.length ≤ final.length`). -/
theorem deferredDraw_run_drawn_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredState M Commit Chal)
      (z : γ × DeferredState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.2 <+: z.2.1.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact List.prefix_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine List.IsPrefix.trans ?_ (ih x.1 x.2 z hzx)
      -- The step's output drawn list extends `s.1.2`.
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact List.prefix_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
              roStep M s.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact List.prefix_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; exact List.prefix_append s.1.2 alc.1.2

omit [SampleableType Stmt] in
/-- **The signed-message list only grows in length.** Every reachable final state of the
deferred-draw run from a start state `s` has signed-message list at least as long as the start's
`s.1.1.2`: uniform and read steps leave it untouched, and a signing step prepends one message
(`msg :: s.1.1.2`). Hence the number of *new* signing queries is `final.length - s.1.1.2.length`. -/
theorem deferredDraw_run_signed_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredState M Commit Chal)
      (z : γ × DeferredState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.1.2.length ≤ z.2.1.1.2.length := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact le_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine le_trans ?_ (ih x.1 x.2 z hzx)
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
              roStep M s.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; simp

omit [SampleableType Stmt] in
/-- **Run-level expected drawn-list length of the deferred-draw run.** By induction on the
adversary computation `oa`, the expected final drawn-list length of the deferred-draw run from a
start state `s` is at most `s.1.2.length + qSrem · (1/(1-p))`, where `qSrem` bounds the number of
signing queries `oa` makes (the `(· matches .inr _)` component of `signHashQueryBound`). Each
signing query grows the expected drawn length by at most `1/(1-p)` (the per-step charge
`deferredDrawImpl_step_expected_length_le`), and uniform/read queries leave it unchanged; the
signing-query budget `qSrem` telescopes across the fold exactly as in
`IsQueryBoundP.simulateQ_run_StateT_of_step`. This is the mean bound that the constructed count law
`kn` of Piece B inherits. -/
theorem deferredDraw_run_expected_length_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredState M Commit Chal),
        (∑' z : γ × DeferredState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s] *
            (z.2.1.2.length : ℝ≥0∞))
          ≤ (s.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      -- Total mass of one deferred step is `1` (no failure).
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
          Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawImpl]
          · simp only [deferredDrawImpl, StateT.run_mk]
            rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawImpl])
      -- Abstract the continuation's carried budget `b` and the per-step abort charge.
      -- Generic combiner: with continuation bound `≤ x.length + b·c`, step charge `extra`,
      -- and `extra + b·c ≤ qSrem·c`, the fold gives the run bound.
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
            (∑' z : γ × DeferredState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                (z.2.1.2.length : ℝ≥0∞))
              ≤ (x.2.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
            (x.2.1.2.length : ℝ≥0∞)) ≤ (s.1.2.length : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                  (z.2.1.2.length : ℝ≥0∞))
            ≤ (s.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * (z.2.1.2.length : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                ((x.2.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                  (x.2.1.2.length : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                    ((x.2.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      (x.2.1.2.length : ℝ≥0∞) +
                    Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ ((s.1.2.length : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by gcongr
          _ ≤ (s.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by rw [add_assoc]; gcongr
      -- Case on the query head so the `if p t` budget/charge reduce concretely.
      rcases t with (n | mc) | msg
      · -- UNIFORM: budget unchanged, no charge.
        refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · -- READ: budget unchanged, no charge.
        refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · -- SIGN: budget decrements; `0 < qSrem`, charge `c`, recombine `c + (qSrem-1)·c = qSrem·c`.
        have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawImpl_step_expected_length_le ids M maxAttempts pk sk
            hp₀ hp hAbort (.inr msg) s
          rwa [if_pos (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **The deferred-draw run never fails.** Every step of `deferredDrawImpl` is a pushforward of a
non-failing `ProbComp` (uniform sampling, `roStep`, or the draw-collecting signing body), so the
whole `simulateQ` fold has zero failure mass. -/
theorem deferredDraw_run_neverFail {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredState M Commit Chal),
      Pr[⊥ | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s] = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; simp [simulateQ_pure]
  | query_bind t ob ih =>
      intro s
      rw [simulateQ_query_bind, StateT.run_bind, probFailure_bind_eq_zero_iff]
      refine ⟨?_, fun x _ => ih x.1 x.2⟩
      rcases t with (n | mc) | msg
      · simp [deferredDrawImpl]
      · simp only [deferredDrawImpl]
        rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
      · simp [deferredDrawImpl]

omit [SampleableType Stmt] in
/-- **The constructed count law of Piece B and its mean bound.** Mapping the deferred-draw run to
its number of *new* draws beyond the start prefix `ws₀` (i.e. `final.length - ws₀.length`) gives a
count law `kn` whose mean is at most `qSrem/(1-p)`. The mean equals the expected total drawn length
minus `ws₀.length` (valid because `ws₀` is always a prefix, `deferredDraw_run_drawn_prefix`), and
the expected total length is bounded by `ws₀.length + qSrem·(1/(1-p))`
(`deferredDraw_run_expected_length_le`), so the `ws₀.length` cancels. This is the mean obligation of
Piece B, discharged for the constructed `kn`. -/
theorem deferredDraw_kn_mean_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ) (hQ : oa.IsQueryBoundP (· matches Sum.inr _) qSrem)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) (ws₀ : List Commit) :
    (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal => z.2.1.2.length - ws₀.length) <$>
          (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false)] *
        (n : ℝ≥0∞))
      ≤ ENNReal.ofReal ((qSrem : ℝ) / (1 - p_abort)) := by
  classical
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  set run : ProbComp (γ × DeferredState M Commit Chal) :=
    (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false) with hrun
  -- The mean of `kn` equals the run-expectation of the new-draw count.
  have hmean : (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal => z.2.1.2.length - ws₀.length) <$> run] *
        (n : ℝ≥0∞))
      = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
          ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞) :=
    tsum_probOutput_map_mul run
      (fun z => z.2.1.2.length - ws₀.length) (fun n => (n : ℝ≥0∞))
  rw [hmean]
  -- Add back `ws₀.length` to recover the total-length expectation, bounded by the fold lemma.
  have hsplit : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞)) + (ws₀.length : ℝ≥0∞)
      ≤ (ws₀.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    have hmass : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run]) = 1 := by
      rw [hrun]
      exact tsum_probOutput_eq_one'
        (deferredDraw_run_neverFail ids M maxAttempts pk sk oa (((re, l), ws₀), false))
    calc (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞)) + (ws₀.length : ℝ≥0∞)
        = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            (((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞) + (ws₀.length : ℝ≥0∞)) := by
          rw [show (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                (((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞) + (ws₀.length : ℝ≥0∞)))
              = (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                  ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞)) +
                ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] * (ws₀.length : ℝ≥0∞) from by
              rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
          rw [ENNReal.tsum_mul_right, hmass, one_mul]
      _ = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            (z.2.1.2.length : ℝ≥0∞) := by
          refine tsum_congr fun z => ?_
          by_cases hz : z ∈ support run
          · have hpre : ws₀.length ≤ z.2.1.2.length :=
              (deferredDraw_run_drawn_prefix ids M maxAttempts pk sk oa _ z hz).length_le
            congr 1
            rw [← Nat.cast_add, Nat.sub_add_cancel hpre]
          · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
      _ ≤ (ws₀.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
          have := deferredDraw_run_expected_length_le ids M maxAttempts pk sk hp₀ hp hAbort oa
            qSrem hQ (((re, l), ws₀), false)
          rwa [← hrun] at this
  -- Cancel `ws₀.length` (finite) and rewrite `qSrem·ofReal(1/(1-p)) = ofReal(qSrem/(1-p))`.
  have hcancel : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞))
      ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [add_comm] at hsplit
    exact (ENNReal.add_le_add_iff_left (by simp : (ws₀.length : ℝ≥0∞) ≠ ∞)).mp hsplit
  refine hcancel.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_natCast qSrem, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ### Attempt-count law: the tight redraft of the deferral count

The firing event tests reads against the *actual* (rejected) drawn list, whose draws are skewed by
the rejection conditioning `commit | reject`. The `drawList`-game RHS, by contrast, draws *raw*
`Prod.fst <$> ids.commit pk sk`. A reject-count `kn = drawnlist.length` is therefore *too small* to
dominate the firing (the residual was false-as-stated with that `kn`). The sound count is the total
*attempt* count, which over-counts each query's rejected draws by the accepting attempt's one fresh
raw draw and whose mean is exactly `qSrem/(1-p)`.

The attempt count is recovered *without a new state field* as `(drawn-list growth) + (signed-list
growth)`: every signing query increments the signed-message list by exactly one (in
`deferredDrawImpl`'s sign branch) and the drawn list by its rejected-attempt count. Their sum
dominates the per-query attempt count and has the clean charge `∑_{a≤maxAttempts} p^a ≤ 1/(1-p)`,
combining the tight reject bound (`tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight`, the
`∑_{a<n} p^(a+1)` rejects) with the unconditional `+1` (signed list). -/

omit [SampleableType Stmt] in
/-- **Per-step expected attempt-count growth of the deferred-draw handler.** One step of
`deferredDrawImpl` grows the expected combined size `drawnlist.length + signedlist.length` by at
most `1/(1-p)` on a signing query and by `0` on uniform/read queries. On a signing query the drawn
list grows by the rejected-attempt count (expected `≤ ∑_{a<maxAttempts} p^(a+1)`, the tight bound)
and the signed list grows by exactly `1`; their sum is `∑_{a≤maxAttempts} p^a ≤ 1/(1-p)`. This is
the per-step charge for the attempt-count law `kn`. -/
lemma deferredDrawImpl_step_expected_attemptCount_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredState M Commit Chal,
      Pr[= z | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
        ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
      ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · -- UNIFORM: state untouched.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · -- READ: writes only the base cache / bad flag; both lists preserved.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
            roStep M s.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawImpl, StateT.run_mk]
      rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · -- SIGN: drawn list `s.1.2 ++ alc.1.2`, signed list `msg :: s.1.1.2` (one longer).
    rw [if_pos (by simp)]
    have hrun : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2)))
      (fun z => ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞) +
                (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append, List.length_cons]
          push_cast
          ring
      _ = ((∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞))) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (alc.1.2.length : ℝ≥0∞)) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + ENNReal.ofReal (1 / (1 - p_abort)) := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          rw [add_assoc]
          gcongr
          refine le_trans (add_le_add_right
            (tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight ids M pk sk msg
              hAbort maxAttempts s.1.1.1) _) ?_
          rw [add_comm]
          refine le_trans (le_of_eq ?_) (geomSum_le hp₀ hp (maxAttempts + 1))
          rw [Finset.sum_range_succ']
          simp only [pow_zero]

omit [SampleableType Stmt] in
/-- **Run-level expected attempt count of the deferred-draw run.** By induction on `oa`, the
expected combined size `drawnlist.length + signedlist.length` of the deferred-draw run from a start
state `s` is at most `(s.1.2.length + s.1.1.2.length) + qSrem · (1/(1-p))`, where `qSrem` bounds the
number of signing queries. Each signing query grows the expected combined size by at most `1/(1-p)`
(the per-step charge `deferredDrawImpl_step_expected_attemptCount_le`), and uniform/read queries
leave it unchanged; the signing-query budget telescopes across the fold exactly as in
`deferredDraw_run_expected_length_le`. The attempt-count law `kn` of the redrafted residual inherits
this mean. -/
theorem deferredDraw_run_expected_attemptCount_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredState M Commit Chal),
        (∑' z : γ × DeferredState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s] *
            ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
          ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) +
              (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
          Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawImpl]
          · simp only [deferredDrawImpl, StateT.run_mk]
            rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawImpl])
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
            (∑' z : γ × DeferredState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
            ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                  ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                (((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                  ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                    (((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) +
                    Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ (((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by gcongr
          _ ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
              rw [add_assoc]; gcongr
      rcases t with (n | mc) | msg
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
            hp₀ hp hAbort (.inr msg) s
          rwa [if_pos (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **The attempt-count law of the redrafted residual and its mean bound.** Mapping the
deferred-draw run to its attempt count — the combined new growth of the drawn and signed lists,
`(drawnlist.length - ws₀.length) + (signedlist.length - l.length)` — gives a count law whose mean is
at most `qSrem/(1-p)`. The attempt count dominates the reject count (it adds the signed-list growth,
one per signing query, covering each accepting attempt's fresh raw draw) yet keeps the same clean
mean, because the per-query charge `(reject expectation) + 1 = ∑_{a≤maxAttempts} p^a ≤ 1/(1-p)` is
identical to the loose reject charge — the `+1` is absorbed by tightening the reject bound from
`∑_{a<n} p^a` to `∑_{a<n} p^(a+1)`. -/
theorem deferredDraw_attemptKn_mean_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ) (hQ : oa.IsQueryBoundP (· matches Sum.inr _) qSrem)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) (ws₀ : List Commit) :
    (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal =>
            (z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length)) <$>
          (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false)] *
        (n : ℝ≥0∞))
      ≤ ENNReal.ofReal ((qSrem : ℝ) / (1 - p_abort)) := by
  classical
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  set run : ProbComp (γ × DeferredState M Commit Chal) :=
    (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false) with hrun
  have hmean : (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal =>
            (z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length)) <$> run] *
        (n : ℝ≥0∞))
      = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
          (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) :=
    tsum_probOutput_map_mul run
      (fun z => (z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length))
      (fun n => (n : ℝ≥0∞))
  rw [hmean]
  -- Add back `ws₀.length + l.length` to recover the total combined size, bounded by the fold.
  have hmass : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run]) = 1 := by
    rw [hrun]
    exact tsum_probOutput_eq_one'
      (deferredDraw_run_neverFail ids M maxAttempts pk sk oa (((re, l), ws₀), false))
  have hsplit : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
        ((ws₀.length + l.length : ℕ) : ℝ≥0∞)
      ≤ ((ws₀.length + l.length : ℕ) : ℝ≥0∞) +
          (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    calc (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
          ((ws₀.length + l.length : ℕ) : ℝ≥0∞)
        = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            ((((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) +
              ((ws₀.length + l.length : ℕ) : ℝ≥0∞)) := by
          rw [show (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                ((((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) +
                  ((ws₀.length + l.length : ℕ) : ℝ≥0∞)))
              = (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                  (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
                ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                  ((ws₀.length + l.length : ℕ) : ℝ≥0∞) from by
              rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
          rw [ENNReal.tsum_mul_right, hmass, one_mul]
      _ = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞) := by
          refine tsum_congr fun z => ?_
          by_cases hz : z ∈ support run
          · have hpre : ws₀.length ≤ z.2.1.2.length :=
              (deferredDraw_run_drawn_prefix ids M maxAttempts pk sk oa _ z hz).length_le
            have hpre2 : l.length ≤ z.2.1.1.2.length :=
              deferredDraw_run_signed_prefix ids M maxAttempts pk sk oa _ z hz
            congr 1
            rw [← Nat.cast_add]
            congr 1
            omega
          · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
      _ ≤ ((ws₀.length + l.length : ℕ) : ℝ≥0∞) +
            (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
          have := deferredDraw_run_expected_attemptCount_le ids M maxAttempts pk sk hp₀ hp hAbort
            oa qSrem hQ (((re, l), ws₀), false)
          rwa [← hrun] at this
  have hcancel : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞))
      ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [add_comm] at hsplit
    exact (ENNReal.add_le_add_iff_left (by simp : ((ws₀.length + l.length : ℕ) : ℝ≥0∞) ≠ ∞)).mp
      hsplit
  refine hcancel.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_natCast qSrem, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end scaffold

end EUF_CMA

end FiatShamirWithAbort
