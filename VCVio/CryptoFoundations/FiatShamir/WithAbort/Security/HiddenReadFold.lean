/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security.GhostReadCharge

/-!
# EUF-CMA for Fiat-Shamir with aborts: HiddenReadFold

The direct route for the eager ghost-read bad probability: the averaged
multi-key hidden-read fold `hiddenReadList_fold_le_target` reducing to the
multi-key first-fire bound, and the per-query eager↔lazy deferred-sampling coupling
at the ghost-read leaf, with its bookkeeping support lemmas.

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

/-! ## Direct route: averaged multi-key hidden-read fold to the target

The direct route bounds the eager ghost-read bad probability by the multi-key
hidden-target first-fire bound `OracleComp.probEvent_hiddenReadList_le` (`≤ n·(qH+1)·ε`
for `n` ghost keys), then averages the per-key-count bound over the run's key-count law.
The averaging step is the pure-`ℝ≥0∞` arithmetic fold `hiddenReadList_fold_le_target`
below: it takes any sub-probability weight `P : ℕ → ℝ≥0∞` over the number of ghost keys
whose mean is bounded by the expected attempt count `qS/(1-p)` (the
`tsum_probOutput_commit_mul_abort_le` aggregate) and folds the per-count bound
`k·(qH+1)·ε` into the target `qS·(qH+1)·ε/(1-p)`. It is the `[fold]` step of the chain
`Pr[eager bad] ≤ Pr[readManyList …] = Pr[hiddenReadList …] ≤ n·(qH+1)·ε ≤[fold] target`,
consumed by `probEvent_ghostBlind_bad_le_of_fac` once that chain's deferred-sampling
factorization is supplied as the hypothesis `hfac`. The headline instead charges the
ghost-read bound through the first-moment route of
`Security/TapeFactorization.lean`. -/
lemma hiddenReadList_fold_le_target (qS qH : ℕ) (ε p_abort : ℝ) (hp : p_abort < 1)
    (P : ℕ → ℝ≥0∞)
    (hmean : ∑' k : ℕ, P k * (k : ℝ≥0∞) ≤ ENNReal.ofReal (qS / (1 - p_abort))) :
    (∑' k : ℕ, P k * ((k : ℝ≥0∞) * (((qH : ℝ≥0∞) + 1) * ENNReal.ofReal ε)))
      ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  have hqH1 : ((qH : ℝ≥0∞) + 1) = ENNReal.ofReal ((qH : ℝ) + 1) := by
    rw [← ENNReal.ofReal_natCast qH, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by positivity) (by norm_num)]
  have h1 : (∑' k : ℕ, P k * ((k : ℝ≥0∞) * (((qH : ℝ≥0∞) + 1) * ENNReal.ofReal ε)))
      = (∑' k : ℕ, P k * (k : ℝ≥0∞)) * (ENNReal.ofReal ((qH : ℝ) + 1) * ENNReal.ofReal ε) := by
    rw [← ENNReal.tsum_mul_right]; congr 1; ext k; rw [hqH1]; ring
  rw [h1, ← ENNReal.ofReal_mul (by positivity)]
  calc (∑' k : ℕ, P k * (k : ℝ≥0∞)) * ENNReal.ofReal (((qH : ℝ) + 1) * ε)
      ≤ ENNReal.ofReal (qS / (1 - p_abort)) * ENNReal.ofReal (((qH : ℝ) + 1) * ε) := by gcongr
    _ = ENNReal.ofReal (qS / (1 - p_abort) * (((qH : ℝ) + 1) * ε)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
        apply ENNReal.ofReal_le_ofReal; apply le_of_eq; field_simp

omit [SampleableType Stmt] in
/-- **(c) Expected-attempt geometric fold.** The per-signing-query attempt-count mass
`∑_{a<maxAttempts} ofReal p^a` — which counts *all* attempts (each attempt `a` is reached
with probability `≤ pᵃ`, *including* the accepting one) — is bounded by `ofReal (1/(1-p))`.
This is the geometric sum that turns the per-query charge increment of
`tsum_probOutput_run_ghostSignBody_mul_memCharge_le` (factor `∑_{a<maxAttempts} pᵃ`) into the
`1/(1-p)` factor of the target `qS·(qH+1)·ε/(1-p)`. -/
lemma geomAttemptSum_le {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) :
    (∑ a ∈ Finset.range maxAttempts, ENNReal.ofReal p_abort ^ a)
      ≤ ENNReal.ofReal (1 / (1 - p_abort)) := by
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  set S : ℝ := ∑ a ∈ Finset.range maxAttempts, p_abort ^ a with hSdef
  have hg_eq : (∑ a ∈ Finset.range maxAttempts, ENNReal.ofReal p_abort ^ a)
      = ENNReal.ofReal S := by
    rw [hSdef, ENNReal.ofReal_sum_of_nonneg (fun a _ => pow_nonneg hp₀ a)]
    exact Finset.sum_congr rfl fun a _ => by rw [← ENNReal.ofReal_pow hp₀]
  rw [hg_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hSdef, le_div_iff₀ h1p]
  have hmul := geom_sum_mul p_abort maxAttempts
  nlinarith [pow_nonneg hp₀ maxAttempts]

omit [SampleableType Stmt] in
/-- **General geometric attempt-count fold.** For any number of terms `n`, the geometric sum
`∑_{a<n} ofReal p^a` is bounded by `ofReal (1/(1-p))`. The general-`n` companion of
`geomAttemptSum_le` (which fixes `n = maxAttempts`); needed at `n = maxAttempts + 1` for the
attempt-count charge `∑_{a≤maxAttempts} p^a = (reject sum) + 1`. -/
lemma geomSum_le {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (n : ℕ) :
    (∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a)
      ≤ ENNReal.ofReal (1 / (1 - p_abort)) := by
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  have hg_eq : (∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a)
      = ENNReal.ofReal (∑ a ∈ Finset.range n, p_abort ^ a) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => pow_nonneg hp₀ a)]
    exact Finset.sum_congr rfl fun a _ => by rw [← ENNReal.ofReal_pow hp₀]
  rw [hg_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ h1p]
  have hmul := geom_sum_mul p_abort n
  nlinarith [pow_nonneg hp₀ n]

/-! ## Deferred-sampling eager↔lazy coupling (ghost-read leaf) -/

omit [SampleableType Stmt] in
/-- **Uniform-branch per-query coupling for the eager↔lazy ghost handlers.** On a
uniform query both `ghostHybridImpl … true` and `lazyGhostHybridImpl` forward the draw and
leave the state untouched (`lazyGhostHybridImpl_run_unif_eq`), so they are coupled by the
identity coupling on the shared uniform sample with *equal outputs* and the bad-flag
implication preserved verbatim. This is the divergence-free branch of `h_step`. -/
theorem relTriple_ghostHybrid_lazyGhost_unif (pk : Stmt) (sk : Wit)
    (n : unifSpec.Domain) (e l : GhostState M Commit Chal) (hRel : e.2 = true → l.2 = true) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inl n))).run e)
      ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inl n))).run l)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ (p₁.2.2 = true → p₂.2.2 = true)) := by
  classical
  rw [lazyGhostHybridImpl_run_unif_eq ids M maxAttempts pk sk n l]
  simp only [ghostHybridImpl, StateT.run_mk, map_eq_bind_pure_comp]
  refine OracleComp.ProgramLogic.Relational.relTriple_bind
    (OracleComp.ProgramLogic.Relational.relTriple_refl
      ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n)) ?_
  rintro u u' rfl
  exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, hRel⟩

omit [SampleableType Stmt] in
/-- **Signing-branch per-query coupling for the eager↔lazy ghost handlers.** On a
signing query both handlers run the *same* `ghostSignBody` over the layered cache, prepend
`msg` to the signed-message list, and leave the bad flag untouched
(`lazyGhostHybridImpl_run_sign_eq`); they are therefore identical, so coupled by the
identity coupling with equal outputs and the bad-flag implication preserved. This is the
second divergence-free branch of `h_step`. -/
theorem relTriple_ghostHybrid_lazyGhost_sign (pk : Stmt) (sk : Wit)
    (msg : M) (e l : GhostState M Commit Chal) (hRel : e.2 = true → l.2 = true) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((ghostHybridImpl ids M maxAttempts true pk sk (.inr msg)).run e)
      ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inr msg)).run l)
      (fun p₁ p₂ => p₁.2.2 = true → p₂.2.2 = true) := by
  classical
  -- The signing handlers copy the input bad flag to the output (`alc ↦ (…, s.2)`), so the
  -- output bad flag is the *constant* `e.2` on the left and `l.2` on the right, independent of
  -- the `ghostSignBody` draw. Couple the two (possibly differently-cached) `ghostSignBody`
  -- runs by *any* coupling (the product coupling from `relTriple_true`), then map both to
  -- `pure`s whose bad flags are `e.2` / `l.2`; the post is then exactly `hRel`.
  rw [lazyGhostHybridImpl_run_sign_eq ids M maxAttempts pk sk msg l]
  simp only [ghostHybridImpl, StateT.run_mk, map_eq_bind_pure_comp]
  refine OracleComp.ProgramLogic.Relational.relTriple_bind
    (OracleComp.ProgramLogic.Relational.relTriple_true
      ((ghostSignBody ids M pk sk msg maxAttempts).run e.1.1)
      ((ghostSignBody ids M pk sk msg maxAttempts).run l.1.1)) ?_
  rintro a b -
  exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure hRel

/-! ## Measure-level eager↔lazy coupling: support lemmas

The lemmas in this section supply bookkeeping used by `avgBadM_eager_le_lazy_joint`
(the reusable two-measure coupling engine of `Security/CouplingEngine.lean`). Both
handlers agree on uniform and signing steps (`relTriple_ghostHybrid_lazyGhost_unif` /
`relTriple_ghostHybrid_lazyGhost_sign`), so the per-step premises concern the per-step
invariant-preservation at those steps: expected ghost-cache size, flag-preservation,
charge-carry, and charge-K bookkeeping. For the uniform and signing branches both handlers
are definitionally identical (`lazyGhostHybridImpl_run_unif_eq` /
`lazyGhostHybridImpl_run_sign_eq`), so the post-step measures agree and any coupling
invariant is threaded unchanged. -/

open scoped Classical in
/-- **Uniform-handler pushforward identity (inert plumbing).** The uniform branch of
`ghostHybridImpl` is the state-fixing pushforward `(fun u => (u, p)) <$> oa` of the uniform
draw `oa`. Averaging a functional `F` over the post-step `(output, state)` pair therefore
collapses the state coordinate to the fixed `p`: the per-`p` inner sum equals the plain
uniform average of `F (·, p)`. Pure measure-theoretic rearrangement (`ENNReal.tsum_prod'`,
off-diagonal collapse, `probOutput_map_injective` on the injective `(·, p)`); no
probabilistic content. -/
lemma tsum_probOutput_map_state_fixed {R G : Type} (oa : ProbComp R) (p : G)
    (F : R × G → ℝ≥0∞) :
    (∑' z : R × G, Pr[= z | (fun u => (u, p)) <$> oa] * F z)
      = ∑' u : R, Pr[= u | oa] * F (u, p) := by
  classical
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun u => ?_
  rw [tsum_eq_single p ?_]
  · rw [probOutput_map_injective oa (f := fun u => (u, p))
      (fun a b h => (Prod.ext_iff.mp h).1) u]
  · intro g hg
    rw [probOutput_eq_zero_of_not_mem_support, zero_mul]
    intro hmem
    rw [support_map] at hmem
    obtain ⟨u', _, hu'⟩ := hmem
    exact hg (Prod.ext_iff.mp hu').2.symm

omit [SampleableType Stmt] in
/-- Uniform step preserves the per-state expected ghost size: the handler returns `(u, p)`
fixing the state, so the post-step ghost layer is always `p`'s. -/
lemma ghostHybridImpl_unif_expected_enncard (pk : Stmt) (sk : Wit)
    (n : unifSpec.Domain) (p : GhostState M Commit Chal) :
    (∑' z : unifSpec.Range n × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inl n))).run p] *
          QueryCache.enncard (z.2.1.1.2))
      = QueryCache.enncard (p.1.1.2) := by
  classical
  calc (∑' z : unifSpec.Range n × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inl n))).run p] *
          QueryCache.enncard (z.2.1.1.2))
      = ∑' u : unifSpec.Range n,
          Pr[= u | (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n] *
            QueryCache.enncard (p.1.1.2) :=
        tsum_probOutput_map_state_fixed
          ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) p
          (fun z => QueryCache.enncard (z.2.1.1.2))
    _ = QueryCache.enncard (p.1.1.2) := by
        rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

omit [SampleableType Stmt] in
/-- Read step preserves the per-state expected ghost size: the eager read writes only the
*base* cache layer (or flips the bad flag), never the ghost layer. -/
lemma ghostHybridImpl_read_expected_enncard (pk : Stmt) (sk : Wit)
    (mc : M × Commit) (p : GhostState M Commit Chal) :
    (∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          QueryCache.enncard (z.2.1.1.2))
      = QueryCache.enncard (p.1.1.2) := by
  classical
  have hghost : ∀ z : Chal × GhostState M Commit Chal,
      z ∈ support ((ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p) →
      z.2.1.1.2 = p.1.1.2 := by
    intro z hz
    simp only [ghostHybridImpl, StateT.run_mk] at hz
    rcases hgh : p.1.1.2 mc with _ | v
    · simp only [hgh, support_map] at hz
      obtain ⟨cu, _, rfl⟩ := hz; rfl
    · simp only [hgh, ↓reduceIte, support_pure] at hz
      subst hz; rfl
  have hconst : (∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          QueryCache.enncard (z.2.1.1.2))
      = ∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          QueryCache.enncard (p.1.1.2) := by
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support ((ghostHybridImpl ids M maxAttempts true pk sk
        (.inl (.inr mc))).run p)
    · congr 1
      exact congrArg QueryCache.enncard (hghost z hz)
    · have h0 : Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p]
          = 0 := probOutput_eq_zero_of_not_mem_support hz
      rw [h0, zero_mul, zero_mul]
  rw [hconst, ENNReal.tsum_mul_right]
  have hone : (∑' z : Chal × GhostState M Commit Chal,
      Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p]) = 1 := by
    refine tsum_probOutput_eq_one' ?_
    simp only [ghostHybridImpl, StateT.run_mk]
    rcases hgh : p.1.1.2 mc with _ | v
    · rcases p.1.1.1 mc with _ | v' <;> simp [roStep]
    · simp
  rw [hone, one_mul]

omit [SampleableType Stmt] in
/-- Sign step grows the per-state expected ghost size by at most `∑ attempts ≤ 1/(1-p)`: the
signing body's accepted-transcript / rejected-attempt programming writes to the ghost layer
(`tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le` plus the geometric fold). -/
lemma ghostHybridImpl_sign_expected_enncard_le (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (p : GhostState M Commit Chal) :
    (∑' z : Option (Commit × Resp) × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inr msg)).run p] *
          QueryCache.enncard (z.2.1.1.2))
      ≤ QueryCache.enncard (p.1.1.2) + ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  -- The handler maps the `ghostSignBody` output state into the ghost layer; the expected
  -- ghost size of the result equals that of the `ghostSignBody` output's ghost component.
  have hmap : (∑' z : Option (Commit × Resp) × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inr msg)).run p] *
          QueryCache.enncard (z.2.1.1.2))
      = ∑' w : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
        Pr[= w | (ghostSignBody ids M pk sk msg maxAttempts).run p.1.1] *
          QueryCache.enncard (w.2.2) := by
    rw [show (ghostHybridImpl ids M maxAttempts true pk sk (.inr msg)).run p
          = (fun alc => (alc.1, ((alc.2, msg :: p.1.2), p.2))) <$>
            (ghostSignBody ids M pk sk msg maxAttempts).run p.1.1 from rfl]
    -- Reindex the post-step sum over the injective map `alc ↦ (alc.1, ((alc.2, …), …))`.
    set g : Option (Commit × Resp) ×
        ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) →
        Option (Commit × Resp) × GhostState M Commit Chal :=
      fun alc => (alc.1, ((alc.2, msg :: p.1.2), p.2)) with hg
    have hginj : Function.Injective g := by
      intro a b hab
      simp only [hg, Prod.mk.injEq] at hab
      exact Prod.ext hab.1 hab.2.1.1
    refine tsum_eq_tsum_of_ne_zero_bij (fun w => g w.1) ?_ ?_ ?_
    · intro a b hab
      exact Subtype.ext (hginj hab)
    · intro z hz
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
      have hzs : z ∈ support (g <$> (ghostSignBody ids M pk sk msg maxAttempts).run p.1.1) :=
        (mem_support_iff _ z).mpr hz.1
      rw [support_map] at hzs
      obtain ⟨w, hw, rfl⟩ := hzs
      refine ⟨⟨w, ?_⟩, rfl⟩
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or]
      refine ⟨probOutput_ne_zero_of_mem_support hw, ?_⟩
      have heq : ((g w).2.1.1.2) = w.2.2 := rfl
      rw [heq] at hz; exact hz.2
    · rintro ⟨w, hw⟩
      change Pr[= g w | g <$> (ghostSignBody ids M pk sk msg maxAttempts).run p.1.1] *
          QueryCache.enncard ((g w).2.1.1.2)
        = Pr[= w | (ghostSignBody ids M pk sk msg maxAttempts).run p.1.1] *
          QueryCache.enncard (w.2.2)
      rw [probOutput_map_injective _ hginj]
  rw [hmap]
  refine le_trans (tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le ids M pk sk msg
    hAbort maxAttempts p.1.1.1 p.1.1.2) ?_
  gcongr
  exact geomAttemptSum_le maxAttempts hp₀ hp

/-- **Per-state ghost charge accumulator** for the threaded eager-charge bound: the
mass-weighted total size of the ghost cache layer. Linear in the state measure `ν`, preserved
by read/uniform steps (which never write the ghost layer) and grown additively by sign steps
(`tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le`). -/
noncomputable def ghostChargeK (ν : GhostState M Commit Chal → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' p : GhostState M Commit Chal, ν p * QueryCache.enncard (p.1.1.2)

/-- **Averaged ghost-membership charge invariant.** For every read target `mc`, the
`ν`-averaged membership charge at `mc` is dominated by the ghost-size accumulator scaled by
`ofReal ε`. This is the carried invariant of the threaded eager-charge bound: it holds at the
empty-cache Dirac start (`0 ≤ 0`), is preserved by reads (ghost layer untouched) and signs
(a sign step raises the charge by `≤ (attempts)·ε`, matching the enncard growth of
`ghostChargeK` — `ghostHybridImpl_sign_expected_enncard_le`). It is only an *averaged*
fact — pointwise per state it is false, since a single ghost entry costs `1`, not `ε`. -/
def ghostChargeInv (ε : ℝ) (ν : GhostState M Commit Chal → ℝ≥0∞) : Prop :=
  ∀ mc : M × Commit,
    (∑' p : GhostState M Commit Chal, ν p * memCharge M p.1.1.2 mc)
      ≤ ghostChargeK M ν * ENNReal.ofReal ε

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- A step that never writes the ghost layer and preserves the bad flag (uniform forward, or a
signing step — whose handler leaves `s.2` untouched) preserves the per-state expected bad
mass: the post-step flag equals the pre-step flag with probability one (mass `≤ 1`). -/
lemma ghostHybridImpl_flag_preserved_le {γ : Type}
    (run : ProbComp (γ × GhostState M Commit Chal)) (p : GhostState M Commit Chal)
    (hflag : ∀ z ∈ support run, z.2.2 = p.2) :
    (∑' z : γ × GhostState M Commit Chal, Pr[= z | run] * (if z.2.2 = true then 1 else 0))
      ≤ (if p.2 = true then 1 else 0) := by
  classical
  calc (∑' z : γ × GhostState M Commit Chal, Pr[= z | run] * (if z.2.2 = true then 1 else 0))
      = ∑' z : γ × GhostState M Commit Chal, Pr[= z | run] * (if p.2 = true then 1 else 0) := by
        refine tsum_congr fun z => ?_
        by_cases hz : z ∈ support run
        · rw [hflag z hz]
        · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
    _ = (∑' z : γ × GhostState M Commit Chal, Pr[= z | run]) * (if p.2 = true then 1 else 0) := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ (if p.2 = true then 1 else 0) :=
        mul_le_of_le_one_left zero_le tsum_probOutput_le_one

omit [SampleableType Stmt] in
/-- Per-state read-step bad-mass bound: the eager read sets the bad flag only on a ghost hit,
so the expected post-step bad mass is at most the pre-step flag plus the membership charge of
the read target. -/
lemma ghostHybridImpl_read_expected_flag_le (pk : Stmt) (sk : Wit)
    (mc : M × Commit) (p : GhostState M Commit Chal) :
    (∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          (if z.2.2 = true then 1 else 0))
      ≤ (if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc := by
  classical
  -- On a miss the post-step flag is preserved; on a hit it is forced true. In both cases the
  -- post-step flag is `≤ p.2 ∨ (ghost hit at mc)` — captured by `memCharge`.
  have hflag : ∀ z ∈ support ((ghostHybridImpl ids M maxAttempts true pk sk
      (.inl (.inr mc))).run p),
      (if z.2.2 = true then (1 : ℝ≥0∞) else 0)
        ≤ (if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc := by
    intro z hz
    simp only [ghostHybridImpl, StateT.run_mk] at hz
    rcases hgh : p.1.1.2 mc with _ | v
    · -- Miss: flag preserved, `memCharge = 0`.
      simp only [hgh, support_map] at hz
      obtain ⟨cu, -, rfl⟩ := hz
      exact le_add_right le_rfl
    · -- Hit: flag forced true, `memCharge = 1`.
      simp only [hgh, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rw [show memCharge M p.1.1.2 mc = 1 by simp [memCharge, hgh]]
      exact le_add_self
  calc (∑' z : Chal × GhostState M Commit Chal,
          Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
            (if z.2.2 = true then 1 else 0))
      ≤ ∑' z : Chal × GhostState M Commit Chal,
          Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
            ((if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support ((ghostHybridImpl ids M maxAttempts true pk sk
            (.inl (.inr mc))).run p)
        · gcongr; exact hflag z hz
        · refine le_of_eq (mul_eq_zero.mpr (Or.inl ?_)) |>.trans zero_le
          exact probOutput_eq_zero_of_not_mem_support hz
    _ = (∑' z : Chal × GhostState M Commit Chal,
          Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p]) *
          ((if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc) := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ (if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc :=
        mul_le_of_le_one_left zero_le tsum_probOutput_le_one

omit [SampleableType Stmt] in
/-- **`h_carry` premise of the threaded bound for the ghost handler.** The carried bad mass
telescopes across one step, paying the read hit charge `≤ K ν · ofReal ε` on a read step
(via the invariant `ghostChargeInv`). Uniform/sign steps preserve the carried bad mass. -/
lemma avgBadM_ghostHybridImpl_threaded_carry
    (ε p_abort : ℝ) (_hp₀ : 0 ≤ p_abort) (_hp : p_abort < 1) (_hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (_hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (_hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (ν : GhostState M Commit Chal → ℝ≥0∞)
    (_hInv : ghostChargeInv M ε ν)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) :
    (∑' u : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t,
        ∑' p : GhostState M Commit Chal,
          OracleComp.ProgramLogic.Relational.postStepOutM
            (ghostHybridImpl ids M maxAttempts true pk sk) ν t u p *
            (if p.2 = true then 1 else 0))
      ≤ (∑' p : GhostState M Commit Chal, ν p * (if p.2 = true then 1 else 0)) +
          (if (t matches Sum.inl (Sum.inr _)) then
            ghostChargeK M ν * ENNReal.ofReal ε else 0) := by
  classical
  -- Rewrite the telescoped carried-bad mass as the weighted post-step bad mass.
  rw [OracleComp.ProgramLogic.Relational.tsum_tsum_postStepOutM_mul
    (ghostHybridImpl ids M maxAttempts true pk sk) ν t (fun s => if s.2 = true then 1 else 0)]
  rcases t with (n | mc) | msg
  · -- Uniform step: flag preserved.
    rw [if_neg (by simp), add_zero]
    refine ENNReal.tsum_le_tsum fun p => ?_
    gcongr
    refine ghostHybridImpl_flag_preserved_le M _ p ?_
    intro z hz
    simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz; rfl
  · -- Read step: pays the per-target membership charge, bounded via the invariant by `K ν · ε`.
    rw [if_pos (by simp)]
    calc (∑' p : GhostState M Commit Chal, ν p *
            ∑' z : Chal × GhostState M Commit Chal,
              Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
                (if z.2.2 = true then 1 else 0))
        ≤ ∑' p : GhostState M Commit Chal, ν p *
            ((if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc) :=
          ENNReal.tsum_le_tsum fun p => by
            gcongr
            exact ghostHybridImpl_read_expected_flag_le ids M maxAttempts pk sk mc p
      _ = (∑' p : GhostState M Commit Chal, ν p * (if p.2 = true then 1 else 0)) +
            ∑' p : GhostState M Commit Chal, ν p * memCharge M p.1.1.2 mc := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun p => by rw [mul_add]
      _ ≤ (∑' p : GhostState M Commit Chal, ν p * (if p.2 = true then 1 else 0)) +
            ghostChargeK M ν * ENNReal.ofReal ε := by
          gcongr
          exact _hInv mc
  · -- Sign step: the signing handler leaves `s.2` untouched, so the flag is preserved.
    rw [if_neg (by simp), add_zero]
    refine ENNReal.tsum_le_tsum fun p => ?_
    gcongr
    refine ghostHybridImpl_flag_preserved_le M _ p ?_
    intro z hz
    simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz; rfl

omit [SampleableType Stmt] in
/-- **`h_K` premise of the threaded bound for the ghost handler.** The ghost-size accumulator
`ghostChargeK` telescopes across one step, growing by `≤ ofReal (1/(1-p)) · mass ν` on a sign
step (`ghostHybridImpl_sign_expected_enncard_le`); reads and uniform steps preserve it (the
ghost layer is untouched). -/
lemma avgBadM_ghostHybridImpl_threaded_K
    (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (_hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (_hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (ν : GhostState M Commit Chal → ℝ≥0∞)
    (_hInv : ghostChargeInv M ε ν)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) :
    (∑' u : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t,
        ghostChargeK M
          (OracleComp.ProgramLogic.Relational.postStepOutM
            (ghostHybridImpl ids M maxAttempts true pk sk) ν t u))
      ≤ ghostChargeK M ν +
          (if (t matches Sum.inr _) then
            ENNReal.ofReal (1 / (1 - p_abort)) *
              (∑' p : GhostState M Commit Chal, ν p) else 0) := by
  classical
  -- Rewrite `∑'u K(postStepOutM ν t u)` as the weighted post-step charge
  -- for `F := enncard ∘ ghost`.
  have hrw : (∑' u : ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range t,
        ghostChargeK M
          (OracleComp.ProgramLogic.Relational.postStepOutM
            (ghostHybridImpl ids M maxAttempts true pk sk) ν t u))
      = ∑' p : GhostState M Commit Chal, ν p *
          ∑' z : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × GhostState M Commit Chal,
            Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk t).run p] *
              QueryCache.enncard (z.2.1.1.2) := by
    rw [← OracleComp.ProgramLogic.Relational.tsum_tsum_postStepOutM_mul
      (ghostHybridImpl ids M maxAttempts true pk sk) ν t (fun s => QueryCache.enncard s.1.1.2)]
    rfl
  rw [hrw, ghostChargeK]
  -- Per-state inner charge bound, then `tsum`-monotone fold.
  rcases t with (n | mc) | msg
  · -- Uniform step: state untouched, ghost charge preserved.
    rw [if_neg (by simp), add_zero]
    refine ENNReal.tsum_le_tsum fun p => ?_
    exact le_of_eq (congrArg (ν p * ·)
      (ghostHybridImpl_unif_expected_enncard ids M maxAttempts pk sk n p))
  · -- Read step: writes only the base layer, ghost charge preserved.
    rw [if_neg (by simp), add_zero]
    refine ENNReal.tsum_le_tsum fun p => ?_
    exact le_of_eq (congrArg (ν p * ·)
      (ghostHybridImpl_read_expected_enncard ids M maxAttempts pk sk mc p))
  · -- Sign step: ghostSignBody grows the ghost size by `≤ ∑ attempts ≤ 1/(1-p)`.
    rw [if_pos (by simp)]
    rw [mul_comm (ENNReal.ofReal (1 / (1 - p_abort))) _, ← ENNReal.tsum_mul_right,
      ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun p => ?_
    rw [← mul_add]
    gcongr
    exact ghostHybridImpl_sign_expected_enncard_le ids M maxAttempts pk sk msg hAbort hp₀ hp p

end scaffold

end EUF_CMA

end FiatShamirWithAbort
