/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.Projections

/-!
# Ghost-layer machinery for Fiat-Shamir with aborts: BodyBounds

Real-versus-reprogrammed signing-body bounds: the within-signing-query
collision budget, per-attempt collision and abort bounds, the deferred-sampling
(lazy) ghost read step and handler, the two body-level cores of the Sign → Prog
hop, and the per-target ghost-membership charge route.

Part of the hybrid signing-body development for the CMA-to-NMA reduction;
`VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies.Bodies` opens the
chain and holds the overview docstring.
-/

public section

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)
variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))

/-! ## Real-versus-reprogrammed signing-body bounds

Quantitative body-level core of the Sign → Prog hop
(`probOutput_hybridExpAtKey_real_le_prog`): run equations unfolding one attempt of the
real signing loop (`fsAbortSignLoop` under the caching random oracle) and of the
reprogramming loop (`progSignBody`), the per-attempt commitment-collision and abort
bounds, the within-signing-query total-variation induction
(`ofReal_tvDist_run_fsAbortSignLoop_progSignBody_le`), and the expected cache-growth
bound for the reprogramming loop (`tsum_probOutput_run_progSignBody_mul_enncard_le`). -/

/-- Expectation of a nonnegative functional under a `pure` computation. -/
lemma tsum_probOutput_pure_mul {β : Type} (y : β) (f : β → ℝ≥0∞) :
    ∑' z, Pr[= z | (pure y : ProbComp β)] * f z = f y := by
  rw [tsum_eq_single y fun z hz => by
    rw [probOutput_eq_zero_of_not_mem_support (by simp [hz]), zero_mul]]
  rw [probOutput_pure_self, one_mul]

/-- Tonelli-style rearrangement: the expectation of a nonnegative functional under a
bind is the outer expectation of the inner expectations. -/
lemma tsum_probOutput_bind_mul {α β : Type} (oa : ProbComp α)
    (g : α → ProbComp β) (f : β → ℝ≥0∞) :
    ∑' z, Pr[= z | oa >>= g] * f z =
      ∑' x, Pr[= x | oa] * ∑' z, Pr[= z | g x] * f z := by
  simp_rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]

/-- Push a constant out of a pointwise expectation bound: a (sub)probability average of
`f ≤ C + g` is at most `C` plus the average of `g`. -/
lemma tsum_probOutput_mul_le_add_of_le {α : Type} (oa : ProbComp α)
    {f g : α → ℝ≥0∞} {C : ℝ≥0∞} (h : ∀ a, f a ≤ C + g a) :
    ∑' a, Pr[= a | oa] * f a ≤ C + ∑' a, Pr[= a | oa] * g a := by
  calc ∑' a, Pr[= a | oa] * f a
      ≤ ∑' a, (Pr[= a | oa] * C + Pr[= a | oa] * g a) :=
        ENNReal.tsum_le_tsum fun a => by rw [← mul_add]; exact mul_le_mul_right (h a) _
    _ = (∑' a, Pr[= a | oa]) * C + ∑' a, Pr[= a | oa] * g a := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ 1 * C + ∑' a, Pr[= a | oa] * g a := by
        gcongr
        exact tsum_probOutput_le_one
    _ = C + ∑' a, Pr[= a | oa] * g a := by rw [one_mul]

/-- `ENNReal` form of `tvDist_bind_left_le`: the lifted TV distance of a bind over a
shared base is at most the base-averaged lifted TV distance of the continuations. -/
lemma ofReal_tvDist_bind_le_tsum {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β) :
    ENNReal.ofReal (tvDist (oa >>= f) (oa >>= g)) ≤
      ∑' x, Pr[= x | oa] * ENNReal.ofReal (tvDist (f x) (g x)) := by
  refine le_trans (ENNReal.ofReal_le_ofReal (tvDist_bind_left_le oa f g)) ?_
  have h_sum_ne_top : (∑' x : α, Pr[= x | oa]) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsum_probOutput_le_one
  have h_summable : Summable fun x : α => Pr[= x | oa].toReal * tvDist (f x) (g x) :=
    Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
      (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _))
      (ENNReal.summable_toReal h_sum_ne_top)
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun x => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)) h_summable]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal probOutput_ne_top]

omit [SampleableType Stmt] in
/-- One-attempt unfolding of the reprogramming loop's cache-level run. -/
lemma run_progSignBody_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (c : (M × Commit →ₒ Chal).QueryCache) :
    (progSignBody ids M pk sk msg (n + 1)).run c =
      ids.commit pk sk >>= fun ws =>
        uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
            | none => (progSignBody ids M pk sk msg n).run (c.cacheQuery (msg, ws.1) ch) := by
  simp only [progSignBody, progSignAttempt, bind_assoc, StateT.run_bind,
    OracleComp.liftM_run_StateT, pure_bind, StateT.run_modify]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => rfl
  | none => rfl

omit [SampleableType Stmt] in
/-- One-attempt unfolding of the real signing loop's cache-level run under the caching
random oracle: commit, take one `roStep` at the commitment point, respond against the
returned challenge, and either return or recurse on the post-step cache. -/
lemma run_simulateQ_fsAbortSignLoop_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (c : (M × Commit →ₒ Chal).QueryCache) :
    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
      (fsAbortSignLoop ids M pk sk msg (n + 1))).run c =
      ids.commit pk sk >>= fun ws =>
        roStep M c (msg, ws.1) >>= fun chc =>
          ids.respond pk sk ws.2 chc.1 >>= fun oz =>
            match oz with
            | some z => pure (some (ws.1, z), chc.2)
            | none =>
                (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
                    (randomOracle : QueryImpl (M × Commit →ₒ Chal)
                      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
                  (fsAbortSignLoop ids M pk sk msg n)).run chc.2 := by
  simp only [fsAbortSignLoop, fsAbortSignAttempt, simulateQ_bind,
    roSim.simulateQ_HasQuery_query, bind_assoc, StateT.run_bind]
  rw [roSim.run_liftM, bind_map_left]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  rw [randomOracle_run_eq_roStep]
  refine congrArg (roStep M c (msg, w) >>= ·) (funext fun chc => ?_)
  rw [roSim.run_liftM, bind_map_left]
  refine congrArg (ids.respond pk sk st chc.1 >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => rfl
  | none => rfl

/-! ### The within-signing-query collision budget -/

/-- Collision budget of one signing query of the Sign → Prog hop, as a function of the
attempt budget `n` and the starting cache size `N`: attempt `a` is reached with
probability at most `p ^ a` and collides with a cached point with probability at most
`(N + a) · ε`. -/
noncomputable def signCollisionBound (ε p : ℝ) (n : ℕ) (N : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal ε * ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ a * (N + a)

@[simp]
lemma signCollisionBound_zero (ε p : ℝ) (N : ℝ≥0∞) :
    signCollisionBound ε p 0 N = 0 := by
  simp [signCollisionBound]

lemma signCollisionBound_succ (ε p : ℝ) (n : ℕ) (N : ℝ≥0∞) :
    signCollisionBound ε p (n + 1) N =
      N * ENNReal.ofReal ε +
        ENNReal.ofReal p * signCollisionBound ε p n (N + 1) := by
  have h : ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ (a + 1) * (N + ↑(a + 1)) =
      ENNReal.ofReal p * ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ a * (N + 1 + ↑a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    push_cast
    ring
  rw [signCollisionBound, signCollisionBound, Finset.sum_range_succ', h]
  push_cast
  ring

lemma signCollisionBound_mono (ε p : ℝ) (n : ℕ) {N N' : ℝ≥0∞} (h : N ≤ N') :
    signCollisionBound ε p n N ≤ signCollisionBound ε p n N' := by
  unfold signCollisionBound
  gcongr

/-- Splitting of the collision budget into a state-free part and a part linear in the
starting cache size, matching the `ζ + R s · β` query-slack shape of
`OracleComp.ProgramLogic.Relational.expectedQuerySlack_expected_resource_le`. -/
lemma signCollisionBound_eq (ε p : ℝ) (n : ℕ) (N : ℝ≥0∞) :
    signCollisionBound ε p n N =
      ENNReal.ofReal ε * ∑ a ∈ Finset.range n, (a : ℝ≥0∞) * ENNReal.ofReal p ^ a +
        N * (ENNReal.ofReal ε * ∑ a ∈ Finset.range n, ENNReal.ofReal p ^ a) := by
  rw [signCollisionBound]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ### Per-attempt collision and abort bounds -/

omit [SampleableType Stmt] [DecidableEq Commit] in
/-- Aggregate per-attempt abort bound: the commit-averaged probability that a fresh
uniform challenge is refused equals the abort probability of one honest execution. -/
lemma tsum_probOutput_commit_mul_abort_le (pk : Stmt) (sk : Wit) {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
        Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch]
      ≤ ENNReal.ofReal p_abort := by
  classical
  refine le_trans (le_of_eq ?_) hAbort
  rw [IdenSchemeWithAbort.honestExecution, probOutput_bind_eq_tsum]
  refine tsum_congr fun ws => ?_
  obtain ⟨cm, st⟩ := ws
  congr 1
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun ch => ?_
  congr 1
  rw [probOutput_bind_eq_tsum, tsum_eq_single (none : Option Resp) ?_]
  · simp [probOutput_pure]
  · rintro (_ | z) hb
    · exact absurd rfl hb
    · simp [probOutput_pure]

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq M] [DecidableEq Commit] in
/-- Commitment-guessing bound for cache hits: under a pointwise commitment-guessing
bound `ε`, one commit lands on a cached point of `c` at message `msg` with probability
at most `enncard c · ε`. -/
lemma probEvent_commit_hit_le (pk : Stmt) (sk : Wit) {ε : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (msg : M) (c : (M × Commit →ₒ Chal).QueryCache) :
    Pr[fun ws : Commit × PrvState => c (msg, ws.1) ≠ none | ids.commit pk sk]
      ≤ QueryCache.enncard c * ENNReal.ofReal ε := by
  classical
  have : DecidableEq Commit := Classical.decEq Commit
  let commitDist : ProbComp Commit := Prod.fst <$> ids.commit pk sk
  let hit : Commit → Prop := fun w => c (msg, w) ≠ none
  let S : Finset Commit := (finSupport commitDist).filter hit
  have h_event :
      Pr[fun ws : Commit × PrvState => c (msg, ws.1) ≠ none | ids.commit pk sk]
        = Pr[hit | commitDist] := by
    simp [commitDist, hit]
  have h_sum : Pr[hit | commitDist] = ∑ w ∈ S, Pr[= w | commitDist] := by
    simp [S, probEvent_eq_sum_filter_finSupport]
  have h_sum_le : ∑ w ∈ S, Pr[= w | commitDist] ≤ ∑ w ∈ S, ENNReal.ofReal ε :=
    Finset.sum_le_sum fun w _ => hGuess w
  have h_card_le : (S.card : ℝ≥0∞) ≤ QueryCache.enncard c := by
    have hex : ∀ w : ↑(S : Set Commit), ∃ v : Chal, c (msg, w.1) = some v := fun w =>
      Option.ne_none_iff_exists'.mp ((Finset.mem_filter.mp w.2).2)
    let cacheEntryOfHit : ↑(S : Set Commit) → c.toSet := fun w =>
      ⟨⟨(msg, w.1), Classical.choose (hex w)⟩, Classical.choose_spec (hex w)⟩
    have h_inj : Function.Injective cacheEntryOfHit := by
      intro w₁ w₂ h
      apply Subtype.ext
      have hdomain : ((msg, w₁.1) : M × Commit) = (msg, w₂.1) :=
        congrArg (fun x : c.toSet => x.1.1) h
      exact congrArg Prod.snd hdomain
    have henc : (S : Set Commit).encard ≤ c.toSet.encard := by
      simpa using Function.Embedding.encard_le ⟨cacheEntryOfHit, h_inj⟩
    have henc_nat : (S.card : ℕ∞) ≤ c.toSet.encard := by simpa using henc
    exact ENat.toENNReal_mono henc_nat
  calc Pr[fun ws : Commit × PrvState => c (msg, ws.1) ≠ none | ids.commit pk sk]
      = Pr[hit | commitDist] := h_event
    _ = ∑ w ∈ S, Pr[= w | commitDist] := h_sum
    _ ≤ ∑ w ∈ S, ENNReal.ofReal ε := h_sum_le
    _ = (S.card : ℝ≥0∞) * ENNReal.ofReal ε := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ QueryCache.enncard c * ENNReal.ofReal ε := mul_le_mul' h_card_le le_rfl

/-! ### Deferred-sampling read step (lazy ghost firing)

The eager ghost handler `ghostHybridImpl … true` pre-populates the ghost cache during
signing and reads it deterministically, so an adversarial read at a ghost point flips the
bad flag with mass `1`. That deterministic flip is *not* amortized by `enncard · ε`, which
is why the charged-step premise of `probEvent_bad_simulateQ_run_le_expectedQuerySlack`
fails for the eager run.

The fix is deferred sampling: postpone each rejected attempt's commitment draw to read
time. A read at point `(msg, w')` then redraws the `pending` deferred commitments and fires
iff one of them equals `w'`. Under the pointwise guessing bound `hGuess`, each redraw lands
on `w'` with probability `≤ ε`, so the union bound over `pending` redraws gives the per-read
charge `pending · ε` — exactly the `R s · ε` shape the accumulator's charged-step premise
demands, with `R s := enncard (ghost cache) = pending`. `lazyGhostFire` is that read step
and `probOutput_lazyGhostFire_true_le` is its charge bound. -/

/-- Deferred-sampling ghost read: draw `pending` fresh commitments and fire iff some draw
equals the adversary's read point `w'`. The lazy counterpart of the eager ghost-domain
membership test in `ghostHybridImpl … true`, with the rejected attempts' commitment draws
postponed to read time. -/
noncomputable def lazyGhostFire (pk : Stmt) (sk : Wit) (w' : Commit) :
    ℕ → ProbComp Bool
  | 0 => pure false
  | n + 1 => do
    let w ← Prod.fst <$> ids.commit pk sk
    let b ← lazyGhostFire pk sk w' n
    pure (decide (w = w') || b)

omit [SampleableType Stmt] [SampleableType Chal] in
/-- **Single-pending deferred-sampling read** (draw-commutation, term form). With
exactly one pending ghost attempt the lazy read `lazyGhostFire … 1` is the deferred draw
`do w ← ids.commit pk sk; pure (decide (w = w'))`: a fresh commitment is sampled at read
time and compared against the adversary's read point `w'`. This is the term-level
draw-commutation that postpones a single rejected attempt's commitment draw to read time;
the eager handler instead reads the *already-sampled* `w` from the ghost cache. -/
lemma lazyGhostFire_one_eq (pk : Stmt) (sk : Wit) (w' : Commit) :
    lazyGhostFire ids pk sk w' 1 =
      ((Prod.fst <$> ids.commit pk sk) >>= fun w => pure (decide (w = w'))) := by
  change (Prod.fst <$> ids.commit pk sk >>= fun w =>
      lazyGhostFire ids pk sk w' 0 >>= fun b => pure (decide (w = w') || b)) = _
  simp only [lazyGhostFire, pure_bind, Bool.or_false]

omit [SampleableType Stmt] [SampleableType Chal] in
/-- **Single-pending lazy fire marginal** (draw-commutation, probability form). The
deferred read fires with probability exactly the commitment law's mass at the read point:
`Pr[fire | lazyGhostFire … 1] = Pr[= w' | Prod.fst <$> ids.commit pk sk]`. This is the
read-time marginal that the body-level deferred-sampling commutation must match against the
eager handler's signing-time draw of the same commitment: the eager run draws `w` while
signing and fires deterministically on a structural ghost hit `w = w'`, whose marginal over
that earlier draw is the *same* `Pr[= w']`. The single-pending case of the Fubini/tsum-swap
that moves the sampling site from signing time to read time. -/
lemma probOutput_lazyGhostFire_one (pk : Stmt) (sk : Wit) (w' : Commit) :
    Pr[= true | lazyGhostFire ids pk sk w' 1] = Pr[= w' | Prod.fst <$> ids.commit pk sk] := by
  rw [lazyGhostFire_one_eq ids pk sk w', probOutput_bind_eq_tsum]
  rw [tsum_eq_single w' ?_]
  · simp [probOutput_pure]
  · intro b hb
    simp [probOutput_pure, hb]

omit [SampleableType Stmt] in
/-- **Eager read bad-fire indicator.** Starting from a state with the bad flag unset, the
eager ghost handler's adversarial random-oracle read at `mc` sets the bad flag with mass
exactly `1` if `mc` lies in the ghost-cache domain and mass `0` otherwise: on a ghost hit
the handler returns `pure (v, (s.1, true))`, and on a ghost miss it runs `roStep` which
leaves the (already-unset) bad flag untouched. This is the deterministic eager flip whose
upstream-averaged marginal the deferred-sampling commutation must reproduce. -/
lemma probOutput_ghostHybridImpl_read_bad
    (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) :
    Pr[fun z : Chal × GhostState M Commit Chal => z.2.2 = true |
        (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run (s, false)] =
      if s.1.2 mc = none then 0 else 1 := by
  simp only [ghostHybridImpl, StateT.run_mk]
  cases hgh : s.1.2 mc with
  | some v =>
      simp only [↓reduceIte]
      simp
  | none =>
      simp [probEvent_eq_zero]

omit [SampleableType Stmt] in
/-- **Single-pending deferred-sampling commutation** (the base case of the deferred-sampling
induction; the multi-pending iteration is `probOutput_eagerMultiReadBad_eq_lazyFire_or`).

The eager handler reads the *already-sampled* ghost key `w` from the ghost cache and fires
the bad flag deterministically iff the adversary's read point `mc` matches the written entry
`(msg, w)`. Marginalizing over the single signing-time commit draw of `w` (which wrote
`(msg, w)` into an initially-empty ghost layer over an arbitrary real layer `re` at challenge
`c`), the eager bad-fire mass equals the deferred read `lazyGhostFire … 1`, in which the same
commitment is *redrawn at read time*. Concretely both equal `Pr[= mc.2 | commit]` when the
read point lies under `msg` (and `0` otherwise): the eager structural hit `w = mc.2` over the
signing-time draw and the lazy fresh draw `w = mc.2` at read time have the *same* marginal.

This is the formal statement that moves the sampling site from signing time (eager) to read
time (lazy) for a single pending key. The averaging over the upstream draw — not the
per-state eager value — is what reproduces the lazy mass: at a *fixed* drawn `w` the eager
read is deterministic `0`/`1`, but its expectation over `w ← commit` is exactly the lazy
`lazyGhostFire … 1` firing probability. The general leaf iterates this peel over the random
number of pending keys (`probOutput_eagerMultiReadBad_eq_lazyFire_or`). -/
lemma probEvent_ghostHybridImpl_read_bad_single_eq_lazyFire
    (pk : Stmt) (sk : Wit) (msg : M) (mc : M × Commit) (hmc : mc.1 = msg)
    (re : (M × Commit →ₒ Chal).QueryCache) (c : Chal) :
    Pr[fun z : Chal × GhostState M Commit Chal => z.2.2 = true |
        (Prod.fst <$> ids.commit pk sk) >>= fun w =>
          (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run
            (((re, (∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery (msg, w) c), []), false)] =
      Pr[= true | lazyGhostFire ids pk sk mc.2 1] := by
  -- Reduce the eager single-write read to its bad-fire indicator, which collapses to
  -- `if w = mc.2 then 1 else 0` (membership of `mc` in the single-entry ghost cache).
  have hind : ∀ w : Commit,
      (if ((((re, (∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery (msg, w) c), [])
            : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M).1.2
              mc = none) then (0 : ℝ≥0∞) else 1) = if w = mc.2 then 1 else 0 := by
    intro w
    by_cases hw : w = mc.2
    · subst hw
      have hmceq : (mc : M × Commit) = (msg, mc.2) := Prod.ext hmc rfl
      conv_lhs => rw [show ((mc : M × Commit)) = (msg, mc.2) from hmceq]
      simp
    · have hne : (mc : M × Commit) ≠ (msg, w) := by
        intro h; exact hw (by rw [← hmc] at h; exact (Prod.ext_iff.mp h).2.symm)
      simp only [QueryCache.cacheQuery_of_ne _ _ hne]
      simp [hw]
  rw [probEvent_bind_eq_tsum]
  simp only [probOutput_ghostHybridImpl_read_bad ids M maxAttempts pk sk mc, hind]
  rw [probOutput_lazyGhostFire_one]
  rw [tsum_eq_single mc.2 (by intro w hw; simp [hw])]
  simp

omit [SampleableType Stmt] in
/-- **Eager multi-pending ghost read marginal** (the deferred-sampling iteration over the
number of pending ghost keys).

The eager read at a ghost cache holding the entries `(msg, w_i)` for `n` signing-time-drawn
keys fires the bad flag iff the adversary's read point `mc` matches one of those `n` entries.
Marginalizing over the `n` signing-time draws (each fresh `w ← Prod.fst <$> ids.commit`, the
ghost cache built over an arbitrary real layer `re` at challenges `c`), the eager bad-fire
mass equals the deferred read `lazyGhostFire … n`, in which all `n` commitments are *redrawn at
read time*.

This is the iteration of the single-pending commutation
`probEvent_ghostHybridImpl_read_bad_single_eq_lazyFire` over the number of pending keys:
the membership event `mc ∈ {(msg, w_i)}` is the union `∃ i, w_i = mc.2`, whose marginal over
iid draws is exactly the union event of `lazyGhostFire`. The induction peels one draw — the
freshly written entry decides one disjunct (`decide (w = mc.2)`), the remaining `n` entries
recurse — matching `lazyGhostFire`'s `decide (w = w') || b` step verbatim.

`eagerMultiReadBad re n` is the eager bad-fire flag at an `n`-pending cache, written as the
deferred draw whose `decide`-or fold tracks the membership; each draw writes `(msg, w)` over
`re` and the read is the deterministic eager indicator
`probOutput_ghostHybridImpl_read_bad`. -/
noncomputable def eagerMultiReadBad (pk : Stmt) (sk : Wit) (msg : M) (mc : M × Commit)
    (re : (M × Commit →ₒ Chal).QueryCache) (c : Chal) :
    ℕ → ProbComp Bool
  | 0 => pure (decide (re mc ≠ none))
  | n + 1 => do
    let w ← Prod.fst <$> ids.commit pk sk
    eagerMultiReadBad pk sk msg mc (re.cacheQuery (msg, w) c) c n

omit [SampleableType Stmt] [SampleableType Chal] in
/-- **Eager multi-pending read = lazy fire (union form)** (the iteration core over the
pending count).

By induction on the pending count `n`, the eager `n`-write membership read over an arbitrary
base layer `re` equals the deferred `lazyGhostFire … n` *or-ed* with the base-layer membership
`re mc ≠ none`. Each induction step peels one signing-time draw `w ← commit`: the freshly
written entry `(msg, w)` contributes the disjunct `decide (w = mc.2)` (since `mc.1 = msg`,
membership of `mc` in the one-key extension `re.cacheQuery (msg, w) c` is `w = mc.2 ∨ mc ∈ re`),
matching `lazyGhostFire`'s `decide (w = w') || b` step verbatim. This is the deferred-sampling
commutation iterated over all pending keys — moving every signing-time draw to read time —
proved entirely locally (no adversary fold). -/
lemma probOutput_eagerMultiReadBad_eq_lazyFire_or
    (pk : Stmt) (sk : Wit) (msg : M) (mc : M × Commit) (hmc : mc.1 = msg) (c : Chal) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      Pr[= true | eagerMultiReadBad ids M pk sk msg mc re c n] =
        Pr[= true | lazyGhostFire ids pk sk mc.2 n >>= fun b =>
          pure (b || decide (re mc ≠ none))] := by
  intro n
  induction n with
  | zero =>
      intro re
      simp [eagerMultiReadBad, lazyGhostFire]
  | succ n ih =>
      intro re
      -- Peel one signing-time draw on both sides and rewrite the membership disjunct.
      have hcache : ∀ w : Commit,
          decide ((re.cacheQuery (msg, w) c) mc ≠ none) =
            (decide (w = mc.2) || decide (re mc ≠ none)) := by
        intro w
        by_cases hw : w = mc.2
        · subst hw
          have hmceq : (mc : M × Commit) = (msg, mc.2) := Prod.ext hmc rfl
          rw [hmceq, QueryCache.cacheQuery_self]
          simp
        · have hne : (mc : M × Commit) ≠ (msg, w) := by
            intro h; exact hw (by rw [← hmc] at h; exact (Prod.ext_iff.mp h).2.symm)
          rw [QueryCache.cacheQuery_of_ne _ _ hne]
          simp [hw]
      -- LHS: `eagerMultiReadBad (n+1)` draws `w` then recurses; apply `ih` on the extended cache.
      rw [show eagerMultiReadBad ids M pk sk msg mc re c (n + 1) =
            (Prod.fst <$> ids.commit pk sk) >>= fun w =>
              eagerMultiReadBad ids M pk sk msg mc (re.cacheQuery (msg, w) c) c n
          from rfl]
      rw [probOutput_bind_eq_tsum]
      -- RHS: `lazyGhostFire (n+1)` draws `w`, then `lazyGhostFire n` and or-s `decide (w = mc.2)`.
      rw [show (lazyGhostFire ids pk sk mc.2 (n + 1) >>= fun b => pure (b || decide (re mc ≠ none)))
            = (Prod.fst <$> ids.commit pk sk) >>= fun w =>
                (lazyGhostFire ids pk sk mc.2 n >>= fun b =>
                  pure (b || decide ((re.cacheQuery (msg, w) c) mc ≠ none)))
          from ?_]
      · rw [probOutput_bind_eq_tsum]
        refine tsum_congr fun w => ?_
        rw [ih (re.cacheQuery (msg, w) c)]
      · -- The two read-time draw shapes agree by `hcache` and Boolean-or associativity.
        rw [show (lazyGhostFire ids pk sk mc.2 (n + 1)) =
              (Prod.fst <$> ids.commit pk sk) >>= fun w =>
                lazyGhostFire ids pk sk mc.2 n >>= fun b => pure (decide (w = mc.2) || b)
            from rfl]
        rw [bind_assoc]
        refine bind_congr fun w => ?_
        rw [bind_assoc]
        refine bind_congr fun b => ?_
        rw [pure_bind, hcache w]
        congr 1
        cases b <;> cases (decide (w = mc.2)) <;> cases (decide (re mc ≠ none)) <;> rfl

omit [SampleableType Stmt] [SampleableType Chal] in
/-- **Eager multi-pending read = lazy fire** (empty base case). With an *empty* base layer
(`re = ∅`, the actual initial real cache of the leaf), the eager `n`-write membership read has
exactly the firing probability of the deferred read `lazyGhostFire … n`: the union over the
`n` signing-time draws equals the union over the `n` read-time redraws. -/
lemma probOutput_eagerMultiReadBad_empty_eq_lazyFire
    (pk : Stmt) (sk : Wit) (msg : M) (mc : M × Commit) (hmc : mc.1 = msg) (c : Chal) (n : ℕ) :
    Pr[= true | eagerMultiReadBad ids M pk sk msg mc
        (∅ : (M × Commit →ₒ Chal).QueryCache) c n] =
      Pr[= true | lazyGhostFire ids pk sk mc.2 n] := by
  rw [probOutput_eagerMultiReadBad_eq_lazyFire_or ids M pk sk msg mc hmc c n]
  congr 1
  rw [show (fun b => pure (b || decide ((∅ : (M × Commit →ₒ Chal).QueryCache) mc ≠ none)))
        = (fun b : Bool => pure b) from funext fun b => by simp]
  rw [bind_pure]

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] in
/-- Boolean-or read shape: appending one fresh `decide (w = w')` flag to a Boolean draw
raises the firing probability by at most `1` (when the fresh flag is set) over the residual
draw. The per-summand step of `probOutput_lazyGhostFire_true_le`. -/
lemma probOutput_bind_or_pure_le (q : Bool) (mb : ProbComp Bool) :
    Pr[= true | mb >>= fun b => pure (q || b)] ≤ (if q then 1 else 0) + Pr[= true | mb] := by
  cases q with
  | true => simp
  | false => simp

omit [SampleableType Stmt] [SampleableType Chal] in
/-- **Charged-step bound for the lazy ghost read.** Under the pointwise commitment-guessing
bound `ε`, the deferred-sampling read `lazyGhostFire … pending` fires with probability at
most `pending · ε`. This is the `R s · ε` charge that makes the charged-step premise of
`probEvent_bad_simulateQ_run_le_expectedQuerySlack` *true* for the lazy run (with
`R s := enncard (ghost cache) = pending`), in contrast to the eager run's deterministic
flip. Proved by a union bound over the `pending` redraws, each bounded by `hGuess`. -/
lemma probOutput_lazyGhostFire_true_le (pk : Stmt) (sk : Wit) {ε : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (w' : Commit) :
    ∀ n : ℕ, Pr[= true | lazyGhostFire ids pk sk w' n] ≤ (n : ℝ≥0∞) * ENNReal.ofReal ε := by
  intro n
  induction n with
  | zero => simp [lazyGhostFire]
  | succ n ih =>
      have hbody : Pr[= true | lazyGhostFire ids pk sk w' (n + 1)] ≤
          Pr[= w' | Prod.fst <$> ids.commit pk sk] +
            Pr[= true | lazyGhostFire ids pk sk w' n] := by
        change Pr[= true | (Prod.fst <$> ids.commit pk sk) >>= fun w =>
            lazyGhostFire ids pk sk w' n >>= fun b => pure (decide (w = w') || b)] ≤ _
        rw [probOutput_bind_eq_tsum]
        calc (∑' w : Commit, Pr[= w | Prod.fst <$> ids.commit pk sk] *
              Pr[= true | lazyGhostFire ids pk sk w' n >>=
                fun b => pure (decide (w = w') || b)])
            ≤ ∑' w : Commit, Pr[= w | Prod.fst <$> ids.commit pk sk] *
                ((if w = w' then 1 else 0) +
                  Pr[= true | lazyGhostFire ids pk sk w' n]) := by
              refine ENNReal.tsum_le_tsum fun w => ?_
              gcongr
              have h := probOutput_bind_or_pure_le (decide (w = w'))
                (lazyGhostFire ids pk sk w' n)
              simp only [decide_eq_true_eq] at h
              exact h
          _ = (∑' w : Commit, Pr[= w | Prod.fst <$> ids.commit pk sk] *
                  (if w = w' then 1 else 0)) +
                (∑' w : Commit, Pr[= w | Prod.fst <$> ids.commit pk sk]) *
                  Pr[= true | lazyGhostFire ids pk sk w' n] := by
              rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
              exact tsum_congr fun w => by ring
          _ ≤ Pr[= w' | Prod.fst <$> ids.commit pk sk] +
                Pr[= true | lazyGhostFire ids pk sk w' n] := by
              gcongr
              · rw [tsum_eq_single w' (by intro b hb; simp [hb]), if_pos rfl, mul_one]
              · exact mul_le_of_le_one_left (zero_le) tsum_probOutput_le_one
      refine hbody.trans ?_
      push_cast
      rw [add_mul, one_mul, add_comm]
      gcongr
      exact hGuess w'

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq M] in
/-- The lazy ghost read fires with probability at most `enncard gh · ε`, where the deferred
attempt count is the ghost cache size. The `R s · ε` charge in the shape consumed by the
accumulator's charged-step premise (`R s := QueryCache.enncard`). -/
lemma probOutput_lazyGhostFire_true_le_enncard (pk : Stmt) (sk : Wit) {ε : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (w' : Commit) (gh : (M × Commit →ₒ Chal).QueryCache)
    (hpending : (gh.toSet.encard.toNat : ℝ≥0∞) ≤ QueryCache.enncard gh) :
    Pr[= true | lazyGhostFire ids pk sk w' gh.toSet.encard.toNat]
      ≤ QueryCache.enncard gh * ENNReal.ofReal ε := by
  refine (probOutput_lazyGhostFire_true_le ids pk sk hGuess w' _).trans ?_
  gcongr

/-! ### Deferred-sampling (lazy) ghost-instrumented hybrid handler

`lazyGhostHybridImpl` is the deferred-sampling counterpart of `ghostHybridImpl … true`.
It carries the *same* layered-cache-plus-flag state `GhostState`, and signs with the same
`ghostSignBody` (so the ghost layer records the same per-attempt programmings and grows by
the same amount). The only change is the adversarial random-oracle read step: instead of
the eager deterministic ghost lookup that flips the bad flag with mass `1`, the read draws
`lazyGhostFire` over the *pending count* `enncard (ghost cache)` and fires the bad flag with
probability `≤ enncard (ghost cache) · ε` (the deferred-sampling charge
`probOutput_lazyGhostFire_true_le_enncard`). The answer to the adversary is taken from the
real layer via `roStep`, independently of the fire draw. This is the handler for which the
charged-step premise of `probEvent_bad_simulateQ_run_le_expectedQuerySlack` holds. -/

/-- Deferred-sampling ghost-instrumented hybrid handler: signs with `ghostSignBody`, answers
uniform queries by forwarding, and answers adversarial random-oracle reads from the real
layer while firing the bad flag lazily (`lazyGhostFire` over the pending ghost count). -/
@[expose] noncomputable def lazyGhostHybridImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (GhostState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      lazyGhostFire ids pk sk mc.2 s.1.1.2.toSet.encard.toNat >>= fun fired =>
        (fun cu => (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || fired))) <$> roStep M s.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1, ((alc.2, msg :: s.1.2), s.2))) <$>
        (ghostSignBody ids M pk sk msg maxAttempts).run s.1.1

omit [SampleableType Stmt] in
/-- The eager (`ghostHybridImpl … true`) and lazy (`lazyGhostHybridImpl`) ghost handlers
are *definitionally identical* on uniform queries: both forward the query and leave the
state untouched. The two handlers differ only in the adversarial random-oracle read step
(`.inl (.inr _)`), where the eager handler reads the pre-populated ghost cache and flips
the bad flag deterministically while the lazy handler answers from the real layer and
fires the flag via the deferred-sampling draw `lazyGhostFire`. -/
lemma lazyGhostHybridImpl_run_unif_eq (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : GhostState M Commit Chal) :
    (lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inl n))).run s =
      (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inl n))).run s := rfl

omit [SampleableType Stmt] in
/-- The eager and lazy ghost handlers are *definitionally identical* on signing queries:
both run `ghostSignBody` on the cache layers, prepend `msg` to the signed-message list, and
leave the bad flag untouched. Together with `lazyGhostHybridImpl_run_unif_eq`, this isolates
the entire eager↔lazy distributional gap to the random-oracle read step. -/
lemma lazyGhostHybridImpl_run_sign_eq (pk : Stmt) (sk : Wit) (msg : M)
    (s : GhostState M Commit Chal) :
    (lazyGhostHybridImpl ids M maxAttempts pk sk (.inr msg)).run s =
      (ghostHybridImpl ids M maxAttempts true pk sk (.inr msg)).run s := rfl

omit [SampleableType Stmt] in
/-- **Bad-flag absorption for the eager run.** Once the bad flag is set, the eager hybrid
run keeps it set: every output of `(simulateQ (ghostHybridImpl … true) oa).run p` from a
state `p` with `p.2 = true` again has its bad flag set. This lifts the per-step monotonicity
`ghostHybridImpl_bad_mono` through the whole free-monad fold. It is the support fact behind
the read-step HIT collapse: at a structural ghost hit the eager read forces the bad flag to
`true` and returns the *real cache untouched*, so the continuation run cannot lower the
charge — its bad mass is the run's success mass. -/
lemma support_simulateQ_ghostHybridImpl_bad
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (M × Option (Commit × Resp)))
    (p : GhostState M Commit Chal) (hp : p.2 = true) :
    ∀ z ∈ support ((simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) oa).run p),
      z.2.2 = true := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure x =>
      intro z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hp
  | query_bind t cont ih =>
      intro z hz
      rw [simulateQ_bind, simulateQ_query, StateT.run_bind, support_bind] at hz
      simp only [OracleQuery.input_query, OracleQuery.cont_query, Set.mem_iUnion] at hz
      obtain ⟨y, hy, hz⟩ := hz
      refine ih y.1 y.2 ?_ z hz
      exact ghostHybridImpl_bad_mono ids M maxAttempts true pk sk t p hp y (by simpa using hy)

omit [SampleableType Stmt] in
/-- **Eager bad mass from a set flag is the run's success mass.** Starting the eager run from
a state whose bad flag is already set, the probability the bad flag is set in the output
equals the (unconditional) probability the run produces *any* output — i.e. the success mass
`1 - probFailure`. Immediate from `support_simulateQ_ghostHybridImpl_bad` via
`probEvent_congr'`: on the support the event `z.2.2 = true` is constantly `True`. This is the
read-step HIT value: after the eager read forces the flag at the committed state `p` (with
the real cache untouched, `z = (v, (p.1, true))`), the continuation `cont v` contributes its
full success mass to the bad charge. -/
lemma probEvent_simulateQ_ghostHybridImpl_bad_eq_true
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (M × Option (Commit × Resp)))
    (p : GhostState M Commit Chal) (hp : p.2 = true) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) oa).run p] =
      Pr[fun _ => True | (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) oa).run p] := by
  refine probEvent_congr' (fun z hz => ?_) rfl
  simp [support_simulateQ_ghostHybridImpl_bad ids M maxAttempts pk sk oa p hp z hz]

omit [SampleableType Stmt] in
/-- **Eager read HIT charge.** At a state `p` whose ghost cache *hits* the adversary's read
point (`p.1.1.2 mc = some v`), the eager read flips the bad flag and returns the real cache
*untouched* as the single output `(v, (p.1, true))`. The contribution of this read to the
telescoped bad average therefore collapses to a single term: the continuation `cont v` run
from `(p.1, true)`, whose bad mass is its full success mass
(`probEvent_simulateQ_ghostHybridImpl_bad_eq_true`). This is the per-state HIT value the
read-step ∑-over-`p` collapse charges; averaging it over the upstream commit draws (the
pushforward law of `p`) is where the eager signing-time hit marginalizes to the lazy
read-time fire mass. -/
lemma tsum_ghostHybridImpl_read_hit_eq
    (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (cont : Chal → OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (M × Option (Commit × Resp)))
    (p : GhostState M Commit Chal) (v : Chal) (hgh : p.1.1.2 mc = some v) :
    (∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          Pr[fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal => w.2.2 = true |
            (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont z.1)).run z.2]) =
      Pr[fun _ => True |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont v)).run (p.1, true)] := by
  have hrun : (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p =
      (pure (v, (p.1, true)) :
        ProbComp (Chal × GhostState M Commit Chal)) := by
    simp only [ghostHybridImpl, StateT.run_mk, hgh, if_pos trivial]
  rw [hrun]
  refine (tsum_probOutput_pure_mul (β := Chal × GhostState M Commit Chal) (v, (p.1, true))
    fun z => Pr[fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal => w.2.2 = true |
      (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont z.1)).run z.2]).trans ?_
  exact probEvent_simulateQ_ghostHybridImpl_bad_eq_true ids M maxAttempts pk sk (cont v)
    (p.1, true) rfl

omit [SampleableType Stmt] in
/-- **Per-state eager read-step inner-sum split.** The telescoped eager read contribution at
a fixed starting state `p` splits by the ghost-domain test `p.1.1.2 mc`:

* on a **HIT** (`some v`) the eager read returns the ghost value with the real cache untouched
  and forces the bad flag, so the inner `∑'z` collapses (by `tsum_ghostHybridImpl_read_hit_eq`)
  to the continuation's full success mass from the flagged state `(p.1, true)`;
* on a **MISS** (`none`) the read runs `roStep` on the real layer leaving the bad flag
  unchanged, so the inner `∑'z` is left untouched.

This is the per-state structural decomposition that isolates the read-step's HIT charge — the
quantity whose `μ`-average against the upstream commit draws carries the deferred-sampling
content. It is the eager-side companion of the lazy read step (`lazyGhostHybridImpl` over the
pending ghost count) and is purely structural (no probabilistic content beyond the HIT
collapse `tsum_ghostHybridImpl_read_hit_eq`). -/
lemma tsum_ghostHybridImpl_read_step_split
    (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (cont : Chal → OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (M × Option (Commit × Resp)))
    (p : GhostState M Commit Chal) :
    (∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          Pr[fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal => w.2.2 = true |
            (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont z.1)).run z.2]) =
      match p.1.1.2 mc with
      | some v => Pr[fun _ => True |
          (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont v)).run (p.1, true)]
      | none => ∑' z : Chal × GhostState M Commit Chal,
          Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
            Pr[fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal => w.2.2 = true |
              (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont z.1)).run z.2] := by
  cases h : p.1.1.2 mc with
  | some v => rw [tsum_ghostHybridImpl_read_hit_eq ids M maxAttempts pk sk mc cont p v h]
  | none => rfl

/-! ### The two body-level cores of the Sign → Prog hop -/

omit [SampleableType Stmt] in
/-- **Within-signing-query TV induction for the Sign → Prog hop.** From a shared
starting cache, the real signing loop (live caching random oracle) and the
all-attempts-reprogramming loop are within total-variation distance
`ε · ∑_{a<n} p ^ a · (|c| + a)`: the two loops agree until an attempt commits to an
already-cached point, attempt `a` is reached only after `a` fresh-challenge rejections
(probability at most `p ^ a` each, by `hAbort`), and at that point the cache holds at
most `|c| + a` entries, each guessed with probability at most `ε` (`hGuess`). -/
lemma ofReal_tvDist_run_fsAbortSignLoop_progSignBody_le (pk : Stmt) (sk : Wit) (msg : M)
    {ε p_abort : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (c : (M × Commit →ₒ Chal).QueryCache),
      ENNReal.ofReal (tvDist
        ((simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          (fsAbortSignLoop ids M pk sk msg n)).run c)
        ((progSignBody ids M pk sk msg n).run c))
        ≤ signCollisionBound ε p_abort n (QueryCache.enncard c) := by
  intro n
  induction n with
  | zero =>
      intro c
      simp [fsAbortSignLoop, progSignBody]
  | succ n ih =>
      intro c
      classical
      rw [run_simulateQ_fsAbortSignLoop_succ, run_progSignBody_succ]
      refine le_trans (ofReal_tvDist_bind_le_tsum _ _ _) ?_
      set B' := signCollisionBound ε p_abort n (QueryCache.enncard c + 1) with hB'
      have key : ∀ ws : Commit × PrvState,
          ENNReal.ofReal (tvDist
            (roStep M c (msg, ws.1) >>= fun chc =>
              ids.respond pk sk ws.2 chc.1 >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), chc.2)
                | none =>
                    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
                        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
                          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
                      (fsAbortSignLoop ids M pk sk msg n)).run chc.2)
            (uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                | none =>
                    (progSignBody ids M pk sk msg n).run (c.cacheQuery (msg, ws.1) ch)))
          ≤ (if c (msg, ws.1) = none then 0 else 1) +
              Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                B' := by
        intro ws
        cases hc : c (msg, ws.1) with
        | some v =>
            rw [if_neg (by simp)]
            exact le_add_right (ENNReal.ofReal_le_one.mpr (tvDist_le_one _ _))
        | none =>
            rw [if_pos rfl, zero_add, roStep_of_none M hc]
            simp only [bind_assoc, pure_bind]
            refine le_trans (ofReal_tvDist_bind_le_tsum _ _ _) ?_
            have hch : ∀ ch : Chal,
                ENNReal.ofReal (tvDist
                  (ids.respond pk sk ws.2 ch >>= fun oz =>
                    match oz with
                    | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                    | none =>
                        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
                            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
                              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
                          (fsAbortSignLoop ids M pk sk msg n)).run
                            (c.cacheQuery (msg, ws.1) ch))
                  (ids.respond pk sk ws.2 ch >>= fun oz =>
                    match oz with
                    | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                    | none =>
                        (progSignBody ids M pk sk msg n).run
                          (c.cacheQuery (msg, ws.1) ch)))
                ≤ Pr[= none | ids.respond pk sk ws.2 ch] * B' := by
              intro ch
              refine le_trans (ofReal_tvDist_bind_le_tsum _ _ _) ?_
              calc ∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
                    ENNReal.ofReal (tvDist _ _)
                  ≤ ∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
                      (if oz = none then B' else 0) := by
                    refine ENNReal.tsum_le_tsum fun oz => mul_le_mul_right ?_ _
                    cases oz with
                    | some z => simp
                    | none =>
                        rw [if_pos rfl]
                        exact le_trans (ih (c.cacheQuery (msg, ws.1) ch))
                          (signCollisionBound_mono ε p_abort n
                            (QueryCache.enncard_cacheQuery_le c (msg, ws.1) ch))
                _ = Pr[= none | ids.respond pk sk ws.2 ch] * B' := by
                    rw [tsum_eq_single (none : Option Resp)
                      fun oz hoz => by simp [hoz]]
                    simp
            calc ∑' ch : Chal, Pr[= ch | uniformSample Chal] *
                  ENNReal.ofReal (tvDist _ _)
                ≤ ∑' ch : Chal, Pr[= ch | uniformSample Chal] *
                    (Pr[= none | ids.respond pk sk ws.2 ch] * B') :=
                  ENNReal.tsum_le_tsum fun ch => mul_le_mul_right (hch ch) _
              _ = Pr[= none | uniformSample Chal >>= fun ch =>
                    ids.respond pk sk ws.2 ch] * B' := by
                  rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
                  exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ENNReal.ofReal (tvDist _ _)
          ≤ ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              ((if c (msg, ws.1) = none then 0 else 1) +
                Pr[= none | uniformSample Chal >>= fun ch =>
                  ids.respond pk sk ws.2 ch] * B') :=
            ENNReal.tsum_le_tsum fun ws => mul_le_mul_right (key ws) _
        _ = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (if c (msg, ws.1) = none then 0 else 1)) +
            ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * B') := by
            simp_rw [mul_add]
            exact ENNReal.tsum_add
        _ ≤ QueryCache.enncard c * ENNReal.ofReal ε + ENNReal.ofReal p_abort * B' := by
            refine add_le_add ?_ ?_
            · refine le_trans (le_of_eq ?_)
                (probEvent_commit_hit_le ids M pk sk hGuess msg c)
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun ws => ?_
              by_cases h : c (msg, ws.1) = none <;> simp [h]
            · calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                    (Pr[= none | uniformSample Chal >>= fun ch =>
                      ids.respond pk sk ws.2 ch] * B')
                  = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                      Pr[= none | uniformSample Chal >>= fun ch =>
                        ids.respond pk sk ws.2 ch]) * B' := by
                    rw [← ENNReal.tsum_mul_right]
                    exact tsum_congr fun ws => (mul_assoc _ _ _).symm
                _ ≤ ENNReal.ofReal p_abort * B' :=
                    mul_le_mul_left
                      (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _
        _ = signCollisionBound ε p_abort (n + 1) (QueryCache.enncard c) :=
            (signCollisionBound_succ ε p_abort n (QueryCache.enncard c)).symm

omit [SampleableType Stmt] in
/-- **Expected cache growth of the reprogramming loop.** Each attempt of `progSignBody`
programs at most one new cache point and the loop continues only on a fresh-challenge
rejection, so the expected size of the final cache is at most `|c| + ∑_{a<n} p ^ a`. -/
lemma tsum_probOutput_run_progSignBody_mul_enncard_le (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (c : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= z | (progSignBody ids M pk sk msg n).run c] * QueryCache.enncard z.2
        ≤ QueryCache.enncard c + ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a := by
  intro n
  induction n with
  | zero =>
      intro c
      simp only [progSignBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro c
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a with hS
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ a =
          1 + ENNReal.ofReal p_abort * S := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => pow_succ' _ _
      rw [run_progSignBody_succ, tsum_probOutput_bind_mul]
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                | none =>
                    (progSignBody ids M pk sk msg n).run (c.cacheQuery (msg, ws.1) ch)] *
              QueryCache.enncard z.2)
          ≤ (QueryCache.enncard c + 1) +
              Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                S := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                | none =>
                    (progSignBody ids M pk sk msg n).run
                      (c.cacheQuery (msg, ws.1) ch)] *
                QueryCache.enncard z.2)
            ≤ (QueryCache.enncard c + 1) +
                Pr[= none | ids.respond pk sk ws.2 ch] * S := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          have h_oz : ∀ oz : Option Resp,
              (∑' z : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= z | (match oz with
                  | some z => pure (some (ws.1, z), c.cacheQuery (msg, ws.1) ch)
                  | none =>
                      (progSignBody ids M pk sk msg n).run
                        (c.cacheQuery (msg, ws.1) ch) :
                  ProbComp (Option (Commit × Resp) ×
                    (M × Commit →ₒ Chal).QueryCache))] *
                  QueryCache.enncard z.2)
              ≤ (QueryCache.enncard c + 1) + (if oz = none then S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), add_zero, tsum_probOutput_pure_mul]
                exact QueryCache.enncard_cacheQuery_le c (msg, ws.1) ch
            | none =>
                rw [if_pos rfl]
                refine le_trans (ih (c.cacheQuery (msg, ws.1) ch)) ?_
                exact add_le_add_left
                  (QueryCache.enncard_cacheQuery_le c (msg, ws.1) ch) S
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
      have : ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
          (Pr[= none | uniformSample Chal >>= fun ch =>
            ids.respond pk sk ws.2 ch] * S)
          ≤ ENNReal.ofReal p_abort * S := by
        calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * S)
            = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                Pr[= none | uniformSample Chal >>= fun ch =>
                  ids.respond pk sk ws.2 ch]) * S := by
              rw [← ENNReal.tsum_mul_right]
              exact tsum_congr fun ws => (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal p_abort * S :=
              mul_le_mul_left
                (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _
      calc QueryCache.enncard c + 1 +
            ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * S)
          ≤ QueryCache.enncard c + 1 + ENNReal.ofReal p_abort * S :=
            add_le_add_right this _
        _ = QueryCache.enncard c + (1 + ENNReal.ofReal p_abort * S) := by
            rw [add_assoc]

omit [SampleableType Stmt] in
/-- One-attempt unfolding of the ghost reprogramming loop's layered-cache run. -/
lemma run_ghostSignBody_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (re gh : (M × Commit →ₒ Chal).QueryCache) :
    (ghostSignBody ids M pk sk msg (n + 1)).run (re, gh) =
      ids.commit pk sk >>= fun ws =>
        uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z =>
                pure (some (ws.1, z),
                  (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
            | none =>
                (ghostSignBody ids M pk sk msg n).run (re, gh.cacheQuery (msg, ws.1) ch) := by
  simp only [ghostSignBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
    pure_bind]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => rfl
  | none => rfl

omit [SampleableType Stmt] in
/-- **Expected ghost-layer growth of the reprogramming loop.** Each rejected attempt of
`ghostSignBody` programs at most one new ghost-cache point; an accepted attempt only
*removes* a point from the ghost layer (`uncacheQuery`). The loop continues only on a
fresh-challenge rejection, so the expected size of the final ghost cache is at most
`|gh| + ∑_{a<n} p ^ a` — the deferred-attempt count that bounds the lazy ghost read. -/
lemma tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
        Pr[= z | (ghostSignBody ids M pk sk msg n).run (re, gh)] * QueryCache.enncard z.2.2
        ≤ QueryCache.enncard gh + ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a := by
  intro n
  induction n with
  | zero =>
      intro re gh
      simp only [ghostSignBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro re gh
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a with hS
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ a =
          1 + ENNReal.ofReal p_abort * S := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => pow_succ' _ _
      rw [run_ghostSignBody_succ, tsum_probOutput_bind_mul]
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : Option (Commit × Resp) ×
              ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z =>
                    pure (some (ws.1, z),
                      (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
                | none =>
                    (ghostSignBody ids M pk sk msg n).run
                      (re, gh.cacheQuery (msg, ws.1) ch)] *
              QueryCache.enncard z.2.2)
          ≤ (QueryCache.enncard gh + 1) +
              Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                S := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : Option (Commit × Resp) ×
                ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z =>
                    pure (some (ws.1, z),
                      (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
                | none =>
                    (ghostSignBody ids M pk sk msg n).run
                      (re, gh.cacheQuery (msg, ws.1) ch)] *
                QueryCache.enncard z.2.2)
            ≤ (QueryCache.enncard gh + 1) +
                Pr[= none | ids.respond pk sk ws.2 ch] * S := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          have h_oz : ∀ oz : Option Resp,
              (∑' z : Option (Commit × Resp) ×
                  ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
                Pr[= z | (match oz with
                  | some z =>
                      pure (some (ws.1, z),
                        (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
                  | none =>
                      (ghostSignBody ids M pk sk msg n).run
                        (re, gh.cacheQuery (msg, ws.1) ch) :
                  ProbComp (Option (Commit × Resp) ×
                    ((M × Commit →ₒ Chal).QueryCache ×
                      (M × Commit →ₒ Chal).QueryCache)))] *
                  QueryCache.enncard z.2.2)
              ≤ (QueryCache.enncard gh + 1) + (if oz = none then S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), add_zero, tsum_probOutput_pure_mul]
                exact le_trans (enncard_uncacheQuery_le M gh (msg, ws.1)) le_self_add
            | none =>
                rw [if_pos rfl]
                refine le_trans (ih re (gh.cacheQuery (msg, ws.1) ch)) ?_
                exact add_le_add_left
                  (QueryCache.enncard_cacheQuery_le gh (msg, ws.1) ch) S
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
      have : ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
          (Pr[= none | uniformSample Chal >>= fun ch =>
            ids.respond pk sk ws.2 ch] * S)
          ≤ ENNReal.ofReal p_abort * S := by
        calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * S)
            = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                Pr[= none | uniformSample Chal >>= fun ch =>
                  ids.respond pk sk ws.2 ch]) * S := by
              rw [← ENNReal.tsum_mul_right]
              exact tsum_congr fun ws => (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal p_abort * S :=
              mul_le_mul_left
                (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _
      calc QueryCache.enncard gh + 1 +
            ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * S)
          ≤ QueryCache.enncard gh + 1 + ENNReal.ofReal p_abort * S :=
            add_le_add_right this _
        _ = QueryCache.enncard gh + (1 + ENNReal.ofReal p_abort * S) := by
            rw [add_assoc]

/-! ### Charge route: per-target ghost-membership increment (sign step)

The eager bad event fires when an adversarial read hits the ghost cache. The charge route
bounds the bad probability by the *averaged* ghost-membership charge of a *fixed* read
target `mc`, tracked inductively across the run. The signing step is the only step that
writes to the ghost layer, and the lemma below is its effect on that per-target charge.

The key correctness move (the one that removes the rejection skew of the eager↔lazy
comparison) is to **drop the rejection event**: a rejected attempt writes `(msg, ws.1)` to
the ghost layer, so it creates a *new* hit at `mc` only when `ws.1 = mc.2` and `msg = mc.1`;
charging that draw against `hGuess` directly gives `Pr[ws.1 = mc.2] ≤ ε` (no `1/Pr[reject]`
conditioning). An *accepted* attempt only `uncacheQuery`-removes a ghost point, so it can
only *decrease* the membership charge. Summed over the `≤ ∑_{a<n} pᵃ` expected attempts the
charge rises by `≤ (∑_{a<n} pᵃ) · ε` above the starting `gh`-membership. -/

/-- **Membership indicator** of a fixed key `mc` in a query cache: `1` if cached, `0`
otherwise. The per-target ghost charge tracked by the charge route. -/
@[expose] noncomputable def memCharge (gh : (M × Commit →ₒ Chal).QueryCache) (mc : M × Commit) :
    ℝ≥0∞ :=
  if gh mc = none then 0 else 1

omit [SampleableType Chal] in
@[simp] lemma memCharge_uncacheQuery_self (gh : (M × Commit →ₒ Chal).QueryCache)
    (q : M × Commit) :
    memCharge M (uncacheQuery M gh q) q = 0 := by
  simp [memCharge, uncacheQuery]

omit [SampleableType Chal] in
/-- `uncacheQuery` cannot increase the membership charge at any target. -/
lemma memCharge_uncacheQuery_le (gh : (M × Commit →ₒ Chal).QueryCache)
    (q mc : M × Commit) :
    memCharge M (uncacheQuery M gh q) mc ≤ memCharge M gh mc := by
  unfold memCharge uncacheQuery
  by_cases hq : mc = q
  · subst hq; simp
  · simp only [if_neg hq, le_refl]

omit [SampleableType Chal] in
/-- A `cacheQuery` write raises the membership charge at `mc` by at most the indicator of the
written key equaling `mc`. -/
lemma memCharge_cacheQuery_le (gh : (M × Commit →ₒ Chal).QueryCache)
    (q : M × Commit) (c : Chal) (mc : M × Commit) :
    memCharge M (gh.cacheQuery q c) mc
      ≤ memCharge M gh mc + (if q = mc then 1 else 0) := by
  unfold memCharge
  by_cases hq : mc = q
  · subst hq
    rw [QueryCache.cacheQuery_self, if_neg (by simp : ¬ (some c = none)), if_pos rfl]
    exact le_add_self
  · have hmcq : gh.cacheQuery q c mc = gh mc := by
      simp only [QueryCache.cacheQuery, Function.update_of_ne hq]
    rw [hmcq]
    exact le_self_add

omit [SampleableType Chal] [SampleableType Stmt] in
/-- **Per-attempt commit-hit bound** at a fixed target: averaging the indicator that a fresh
commit draw `ws.1` lands so that the new ghost write `(msg, ws.1)` equals `mc` is at most
`ofReal ε` — the raw `hGuess` charge, with **no rejection conditioning**. -/
lemma tsum_probOutput_commit_mul_writeHit_le (pk : Stmt) (sk : Wit) (msg : M)
    {ε : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (mc : M × Commit) :
    ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
        (if ((msg, ws.1) : M × Commit) = mc then (1 : ℝ≥0∞) else 0)
      ≤ ENNReal.ofReal ε := by
  classical
  refine le_trans ?_ (hGuess mc.2)
  rw [probOutput_map_eq_tsum_ite (ids.commit pk sk) Prod.fst mc.2]
  refine ENNReal.tsum_le_tsum fun ws => ?_
  obtain ⟨w, st⟩ := ws
  by_cases hhit : ((msg, w) : M × Commit) = mc
  · rw [if_pos hhit, mul_one, if_pos (by rw [← hhit])]
  · rw [if_neg hhit, mul_zero]; exact zero_le

omit [SampleableType Stmt] in
/-- **(a) Sign-step ghost-membership charge increment.** Running `ghostSignBody` for `n`
attempts raises the averaged membership charge at a fixed target `mc` by at most
`(∑_{a<n} pᵃ) · ε` above the charge already present in the starting ghost cache `gh`. The
proof mirrors `tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le`, but tracks the
single-target indicator `memCharge mc` rather than the total `enncard`: an accepted attempt
only removes (`memCharge_uncacheQuery_le`), a rejected attempt's write costs at most the raw
commit-hit charge `ofReal ε` (`tsum_probOutput_commit_mul_writeHit_le`, dropping the
rejection event), and the loop is reached with probability `≤ pᵃ` at attempt `a`. -/
lemma tsum_probOutput_run_ghostSignBody_mul_memCharge_le (pk : Stmt) (sk : Wit) (msg : M)
    {ε p_abort : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (mc : M × Commit) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
        Pr[= z | (ghostSignBody ids M pk sk msg n).run (re, gh)] * memCharge M z.2.2 mc
        ≤ memCharge M gh mc + (∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a)
            * ENNReal.ofReal ε := by
  intro n
  induction n with
  | zero =>
      intro re gh
      simp only [ghostSignBody, StateT.run_pure, tsum_probOutput_pure_mul, Finset.range_zero,
        Finset.sum_empty, zero_mul, add_zero, le_refl]
  | succ n ih =>
      intro re gh
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a with hS
      have hSucc : (∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ a) * ENNReal.ofReal ε =
          ENNReal.ofReal ε + (ENNReal.ofReal p_abort * S) * ENNReal.ofReal ε := by
        rw [Finset.sum_range_succ', pow_zero, add_comm, add_mul, one_mul]
        congr 2
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => pow_succ' _ _
      rw [run_ghostSignBody_succ, tsum_probOutput_bind_mul]
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : Option (Commit × Resp) ×
              ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z =>
                    pure (some (ws.1, z),
                      (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
                | none =>
                    (ghostSignBody ids M pk sk msg n).run
                      (re, gh.cacheQuery (msg, ws.1) ch)] *
              memCharge M z.2.2 mc)
          ≤ (memCharge M gh mc + (if ((msg, ws.1) : M × Commit) = mc then 1 else 0)) +
              Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                (S * ENNReal.ofReal ε) := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : Option (Commit × Resp) ×
                ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z =>
                    pure (some (ws.1, z),
                      (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
                | none =>
                    (ghostSignBody ids M pk sk msg n).run
                      (re, gh.cacheQuery (msg, ws.1) ch)] *
                memCharge M z.2.2 mc)
            ≤ (memCharge M gh mc + (if ((msg, ws.1) : M × Commit) = mc then 1 else 0)) +
                Pr[= none | ids.respond pk sk ws.2 ch] * (S * ENNReal.ofReal ε) := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          have h_oz : ∀ oz : Option Resp,
              (∑' z : Option (Commit × Resp) ×
                  ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
                Pr[= z | (match oz with
                  | some z =>
                      pure (some (ws.1, z),
                        (re.cacheQuery (msg, ws.1) ch, uncacheQuery M gh (msg, ws.1)))
                  | none =>
                      (ghostSignBody ids M pk sk msg n).run
                        (re, gh.cacheQuery (msg, ws.1) ch) :
                  ProbComp (Option (Commit × Resp) ×
                    ((M × Commit →ₒ Chal).QueryCache ×
                      (M × Commit →ₒ Chal).QueryCache)))] *
                  memCharge M z.2.2 mc)
              ≤ (memCharge M gh mc + (if ((msg, ws.1) : M × Commit) = mc then 1 else 0)) +
                  (if oz = none then S * ENNReal.ofReal ε else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (Option.some_ne_none z), add_zero, tsum_probOutput_pure_mul]
                exact le_trans (memCharge_uncacheQuery_le M gh (msg, ws.1) mc) le_self_add
            | none =>
                rw [if_pos rfl]
                refine le_trans (ih re (gh.cacheQuery (msg, ws.1) ch)) ?_
                exact add_le_add (memCharge_cacheQuery_le M gh (msg, ws.1) ch mc) le_rfl
          refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_oz) ?_
          refine add_le_add_right (le_of_eq ?_) _
          rw [tsum_eq_single (none : Option Resp) fun oz hoz => by simp [hoz]]
          simp [mul_comm]
        refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ch) ?_
        refine add_le_add_right (le_of_eq ?_) _
        rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      refine le_trans (ENNReal.tsum_le_tsum fun ws => mul_le_mul_right (h_ws ws) _) ?_
      rw [hSucc]
      rw [show (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ((memCharge M gh mc + (if ((msg, ws.1) : M × Commit) = mc then 1 else 0)) +
              Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                (S * ENNReal.ofReal ε))) =
          ∑' ws : Commit × PrvState, (Pr[= ws | ids.commit pk sk] * memCharge M gh mc +
            (Pr[= ws | ids.commit pk sk] *
              (if ((msg, ws.1) : M × Commit) = mc then 1 else 0) +
            Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
                (S * ENNReal.ofReal ε)))) from tsum_congr fun ws => by ring,
        ENNReal.tsum_add, ENNReal.tsum_add]
      refine add_le_add ?_ (add_le_add ?_ ?_)
      · rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left (zero_le) tsum_probOutput_le_one
      · exact tsum_probOutput_commit_mul_writeHit_le ids M pk sk msg hGuess mc
      · calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              (Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch] * (S * ENNReal.ofReal ε))
            = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                Pr[= none | uniformSample Chal >>= fun ch =>
                  ids.respond pk sk ws.2 ch]) * (S * ENNReal.ofReal ε) := by
              rw [← ENNReal.tsum_mul_right]
              exact tsum_congr fun ws => (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal p_abort * (S * ENNReal.ofReal ε) :=
              mul_le_mul_left (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _
          _ = ENNReal.ofReal p_abort * S * ENNReal.ofReal ε := by rw [mul_assoc]

omit [SampleableType Stmt] in
/-- **(b) Eager read-step charge bound.** At any starting state `p`, the eager read's
contribution to the telescoped bad average is at most the per-target ghost-membership charge
`memCharge (p.1.1.2) mc` *plus* the miss-branch continuation charge.

This is the read-step half of the charge route. On a ghost **hit** (`p.1.1.2 mc = some v`)
the eager read forces the bad flag and the contribution is the continuation success mass
`≤ 1 = memCharge` (the membership indicator is `1`), and the miss branch contributes `0`. On
a **miss** the contribution is exactly the miss-branch continuation and `memCharge = 0`. Thus
the read pays at most `memCharge` above its miss-branch continuation — and the `memCharge`
term is precisely what the averaged charge invariant
(`tsum_probOutput_run_ghostSignBody_mul_memCharge_le`) bounds by `attempts · ε`. Built on the
HIT/MISS split `tsum_ghostHybridImpl_read_step_split`. -/
lemma tsum_ghostHybridImpl_read_step_charge_le
    (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (cont : Chal → OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (M × Option (Commit × Resp)))
    (p : GhostState M Commit Chal) :
    (∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          Pr[fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal => w.2.2 = true |
            (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont z.1)).run z.2])
      ≤ memCharge M p.1.1.2 mc +
          (match p.1.1.2 mc with
            | some _ => 0
            | none => ∑' z : Chal × GhostState M Commit Chal,
                Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
                  Pr[fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal =>
                      w.2.2 = true |
                    (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont z.1)).run
                      z.2]) := by
  rw [tsum_ghostHybridImpl_read_step_split ids M maxAttempts pk sk mc cont p]
  unfold memCharge
  cases h : p.1.1.2 mc with
  | some v =>
      rw [if_neg (by simp), add_zero]
      exact probEvent_le_one
  | none =>
      rw [if_pos rfl, zero_add]

end FiatShamirWithAbort
