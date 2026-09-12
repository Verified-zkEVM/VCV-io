/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.AppendQuery

/-! # GPV Hash-and-Sign: Adaptive Sampler-Transport Accumulation

Two GPV instantiations sharing the deterministic `eval`/`isShort` but differing in the
probabilistic trapdoor sampler (a *concrete* finite-precision sampler versus an *ideal* one)
induce EUF-CMA advantages within `qSign · ε` of each other, whenever the two samplers are
within total-variation distance `ε` at every target — per signing query, uniformly in the
random-oracle state.

The accumulation is adaptive: the adversary chooses its signing queries as a function of all
previous oracle answers.  The per-query budget telescopes across the run by the generic
selective identical-until-bad lemma
`OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_queryBoundP_mul`, applied on the
freshness-tracking verify-Bool vehicle (`realGameVerifyFresh`): the signing step of the fresh
flag handler `gpvRealImplFlagFresh` is the only step touching the trapdoor sampler
(`tvDist_run_gpvRealImplFlagFresh_sign_le`), while uniform and random-oracle steps are
implementation-identical across the swap (`gpvRealImplFlagFresh_run_inl_trapdoorSwap`), and
the verification read is sampler-free (`gpvVerifyRead_trapdoorSwap`).

The headline accumulation is `advantage_le_advantage_add_of_trapdoorSample_tvDist` (one-sided,
`ℝ≥0∞` form, the shape consumed by scheme-level security statements) together with the
symmetric two-sided corollary `abs_advantage_toReal_sub_le_of_trapdoorSample_tvDist`.
-/

public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf psf' : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]

/-! ## Per-step invariance and per-step budget under the trapdoor-sampler swap -/

omit [SampleableType Range] [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] in
/-- **The verification read is invariant under a trapdoor-sampler swap.** `gpvVerifyRead`
touches the PSF only through the deterministic `eval`/`isShort`, so two PSFs sharing those
components produce identical verification reads. -/
lemma gpvVerifyRead_trapdoorSwap
    (hEval : ∀ pk x, psf.eval pk x = psf'.eval pk x)
    (hShort : ∀ x, psf.isShort x = psf'.isShort x)
    (pk : PK) (out : M × (Salt × Domain)) :
    gpvVerifyRead psf M Salt pk out = gpvVerifyRead psf' M Salt pk out := by
  obtain ⟨msg, r, s⟩ := out
  simp only [gpvVerifyRead, hEval, hShort]

/-- **Non-signing steps are invariant under a trapdoor-sampler swap.** The uniform and
random-oracle steps of the freshness-tracking real handler `gpvRealImplFlagFresh` never invoke
the trapdoor sampler, so they agree for any two PSFs from every state. -/
lemma gpvRealImplFlagFresh_run_inl_trapdoorSwap (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    (gpvRealImplFlagFresh psf hr M Salt pk sk (.inl q)).run s =
      (gpvRealImplFlagFresh psf' hr M Salt pk sk (.inl q)).run s := by
  rw [gpvRealImplFlagFresh_run_inl, gpvRealImplFlagFresh_run_inl]
  rcases q with n | mc
  · rw [gpvRealImpl_run_unif, gpvRealImpl_run_unif]
  · rw [gpvRealImpl_run_read, gpvRealImpl_run_read]

/-- **Per-signing-step total-variation budget under a trapdoor-sampler swap.** A signing step
of the freshness-tracking real handler shares the fresh salt draw and the lazy random-oracle
step across the swap, and differs only in the trapdoor draw at the resolved target; the shared
final packaging is a `map`, so the step-level distance is at most the per-call sampler
distance `ε`, uniformly in the starting state. -/
lemma tvDist_run_gpvRealImplFlagFresh_sign_le (pk : PK) (sk : SK)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hStep : ∀ c, tvDist (psf.trapdoorSample pk sk c) (psf'.trapdoorSample pk sk c) ≤ ε)
    (msg : M) (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    tvDist ((gpvRealImplFlagFresh psf hr M Salt pk sk (.inr msg)).run s)
      ((gpvRealImplFlagFresh psf' hr M Salt pk sk (.inr msg)).run s) ≤ ε := by
  rw [gpvRealImplFlagFresh_run_inr, gpvRealImplFlagFresh_run_inr]
  refine tvDist_bind_le_of_forall_le _ _ _ ε hε fun r => ?_
  refine tvDist_bind_le_of_forall_le _ _ _ ε hε fun q => ?_
  rw [bind_pure_comp, bind_pure_comp]
  exact le_trans (tvDist_map_le _ _ _) (hStep q.1)

/-! ## The adaptive run-level accumulation -/

/-- **Adaptive run-level accumulation of the per-call sampler budget.** Simulating any
computation making at most `qSign` signing queries on the two freshness-tracking real handlers
— identical except for the trapdoor sampler, whose per-call total-variation distance is at
most `ε` — keeps the joint output-and-state distributions within `qSign · ε`.  The per-query
budgets telescope across the adaptively interleaved query stream by
`tvDist_simulateQ_run_le_queryBoundP_mul`, the handlers agreeing exactly on the uniform and
random-oracle steps. -/
theorem tvDist_run_simulateQ_gpvRealImplFlagFresh_trapdoorSwap_le (pk : PK) (sk : SK)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hStep : ∀ c, tvDist (psf.trapdoorSample pk sk c) (psf'.trapdoorSample pk sk c) ≤ ε)
    {α : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) α)
    {qSign : ℕ} (hqb : oa.IsQueryBoundP (· matches .inr _) qSign)
    (s₀ : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    tvDist ((simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run s₀)
      ((simulateQ (gpvRealImplFlagFresh psf' hr M Salt pk sk) oa).run s₀) ≤ qSign * ε := by
  refine tvDist_simulateQ_run_le_queryBoundP_mul _ _ hε (· matches .inr _) ?_ ?_ oa hqb s₀
  · rintro (q | msg) hSt s
    · simp at hSt
    · exact tvDist_run_gpvRealImplFlagFresh_sign_le psf psf' hr M Salt pk sk hε hStep msg s
  · rintro (q | msg) hSt s
    · exact gpvRealImplFlagFresh_run_inl_trapdoorSwap psf psf' hr M Salt pk sk q s
    · simp at hSt

/-! ## The per-key game hop and the keygen-averaged accumulation -/

/-- **Per-key sampler-transport hop on the freshness verify-Bool game.** At a fixed key pair,
swapping the trapdoor sampler underneath the real freshness verify-Bool game costs at most
`qSign · ε`: the verification read is sampler-free (`gpvVerifyRead_trapdoorSwap`), so both
games simulate the *same* computation on the two handlers, and the run-level accumulation
`tvDist_run_simulateQ_gpvRealImplFlagFresh_trapdoorSwap_le` transports through the winning-Bool
projection and the Bool total-variation bridge. -/
theorem probOutput_realGameVerifyFresh_le_trapdoorSwap_add
    (hEval : ∀ pk x, psf.eval pk x = psf'.eval pk x)
    (hShort : ∀ x, psf.isShort x = psf'.isShort x)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hStep : ∀ c, tvDist (psf.trapdoorSample pk sk c) (psf'.trapdoorSample pk sk c) ≤ ε)
    {qSign : ℕ} (hQ : (adv.main pk).IsQueryBoundP (· matches .inr _) qSign) :
    Pr[= true | realGameVerifyFresh psf hr M Salt adv pk sk]
      ≤ Pr[= true | realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ pk sk]
        + ENNReal.ofReal (qSign * ε) := by
  classical
  set oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      ((M × (Salt × Domain)) × Bool) :=
    adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf' M Salt pk out
    with hoa
  -- The psf-side game simulates the common computation `oa`: the verification read is
  -- invariant under the swap.
  have hgame : realGameVerifyFresh psf hr M Salt adv pk sk =
      𝒮[(fun z : ((M × (Salt × Domain)) × Bool) ×
            (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) =>
          decide (z.1.1.1 ∉ z.2.1.2) && z.1.2) <$>
        (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run
          (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)] := by
    unfold realGameVerifyFresh
    rw [hoa, show (fun out : M × (Salt × Domain) =>
          (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)
        = fun out => (fun v => (out, v)) <$> gpvVerifyRead psf' M Salt pk out from
      funext fun out => by
        rw [gpvVerifyRead_trapdoorSwap psf psf' M Salt hEval hShort pk out]]
  -- The signing-query budget extends over the appended (signing-free) verification read.
  have hqb : oa.IsQueryBoundP (· matches .inr _) qSign :=
    isQueryBoundP_bind hQ (fun out _ => gpvVerifyKont_no_sign psf' M Salt pk out)
  have h_run := tvDist_run_simulateQ_gpvRealImplFlagFresh_trapdoorSwap_le psf psf' hr M Salt
    pk sk hε hStep oa hqb (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)
  -- Game-level total variation: project the joint run through the winning Bool.
  have h_tv : SPMF.tvDist (realGameVerifyFresh psf hr M Salt adv pk sk)
      (realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ pk sk) ≤ qSign * ε := by
    rw [hgame]
    unfold realGameVerifyFresh
    exact le_trans (tvDist_map_le _ _ _) h_run
  -- Transport through the Bool total-variation bridge into the `ℝ≥0∞` inequality.
  have h_loss_nonneg : (0 : ℝ) ≤ qSign * ε := mul_nonneg (Nat.cast_nonneg _) hε
  have habs := abs_probOutput_toReal_sub_le_tvDist
    (realGameVerifyFresh psf hr M Salt adv pk sk)
    (realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ pk sk)
  have h_real : Pr[= true | realGameVerifyFresh psf hr M Salt adv pk sk].toReal ≤
      Pr[= true | realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ pk sk].toReal
        + qSign * ε := by
    have h_le := (abs_le.mp habs).2
    linarith [le_trans h_le h_tv]
  calc Pr[= true | realGameVerifyFresh psf hr M Salt adv pk sk]
      = ENNReal.ofReal
          (Pr[= true | realGameVerifyFresh psf hr M Salt adv pk sk].toReal) :=
        (ENNReal.ofReal_toReal probOutput_ne_top).symm
    _ ≤ ENNReal.ofReal
          (Pr[= true | realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ pk sk].toReal
            + qSign * ε) := ENNReal.ofReal_le_ofReal h_real
    _ = Pr[= true | realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ pk sk]
          + ENNReal.ofReal (qSign * ε) := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg h_loss_nonneg,
          ENNReal.ofReal_toReal probOutput_ne_top]

/-- **Adaptive sampler-transport accumulation for the GPV EUF-CMA advantage.** Swapping the
trapdoor sampler of the GPV scheme — keeping the deterministic `eval`/`isShort` fixed — costs
at most `qSign · ε` in EUF-CMA advantage, when the two samplers are within total-variation
distance `ε` at every target on honestly generated keys and the adversary makes at most
`qSign` signing queries.  The right-hand adversary is the same `main` repackaged at the
swapped scheme; both advantages read the shared random-oracle `runtime`.

The proof averages the per-key hop `probOutput_realGameVerifyFresh_le_trapdoorSwap_add` over
the key generator through the game identification
`advantage_eq_keygen_average_realGameVerifyFresh`; keys outside `support hr.gen` carry no
mass. -/
theorem advantage_le_advantage_add_of_trapdoorSample_tvDist
    (hEval : ∀ pk x, psf.eval pk x = psf'.eval pk x)
    (hShort : ∀ x, psf.isShort x = psf'.isShort x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hStep : ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c,
      tvDist (psf.trapdoorSample pk sk c) (psf'.trapdoorSample pk sk c) ≤ ε)
    (qSign : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hQ : ∀ pk, (adv.main pk).IsQueryBoundP (· matches .inr _) qSign) :
    adv.advantage (runtime M Salt) ≤
      (⟨adv.main⟩ : SignatureAlg.unforgeableAdv
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf' hr M Salt)).advantage (runtime M Salt)
        + ENNReal.ofReal (qSign * ε) := by
  classical
  rw [advantage_eq_keygen_average_realGameVerifyFresh psf hr M Salt adv,
    advantage_eq_keygen_average_realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩,
    probOutput_bind_eq_tsum (𝒮[hr.gen] : SPMF (PK × SK)),
    probOutput_bind_eq_tsum (𝒮[hr.gen] : SPMF (PK × SK))]
  have hper : ∀ x : PK × SK, x ∈ support hr.gen →
      Pr[= true | realGameVerifyFresh psf hr M Salt adv x.1 x.2] ≤
        Pr[= true | realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ x.1 x.2]
          + ENNReal.ofReal (qSign * ε) := fun x hx =>
    probOutput_realGameVerifyFresh_le_trapdoorSwap_add psf psf' hr M Salt hEval hShort adv
      x.1 x.2 hε (hStep x.1 x.2 hx) (hQ x.1)
  calc ∑' x : PK × SK,
        Pr[= x | 𝒮[hr.gen]] * Pr[= true | realGameVerifyFresh psf hr M Salt adv x.1 x.2]
      ≤ ∑' x : PK × SK, (Pr[= x | 𝒮[hr.gen]]
            * Pr[= true | realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ x.1 x.2]
          + Pr[= x | 𝒮[hr.gen]] * ENNReal.ofReal (qSign * ε)) :=
        ENNReal.tsum_le_tsum fun x => by
          by_cases hx : x ∈ support hr.gen
          · rw [← mul_add]; gcongr; exact hper x hx
          · have hzero : Pr[= x | (𝒮[hr.gen] : SPMF (PK × SK))] = 0 :=
              probOutput_eq_zero_of_not_mem_support (mx := hr.gen) hx
            simp [hzero]
    _ = ∑' x : PK × SK, (Pr[= x | 𝒮[hr.gen]]
            * Pr[= true | realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ x.1 x.2])
          + (∑' x : PK × SK, Pr[= x | 𝒮[hr.gen]]) * ENNReal.ofReal (qSign * ε) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ ∑' x : PK × SK, (Pr[= x | 𝒮[hr.gen]]
            * Pr[= true | realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ x.1 x.2])
          + 1 * ENNReal.ofReal (qSign * ε) := by
        gcongr
        exact tsum_probOutput_le_one
    _ = ∑' x : PK × SK, (Pr[= x | 𝒮[hr.gen]]
            * Pr[= true | realGameVerifyFresh psf' hr M Salt ⟨adv.main⟩ x.1 x.2])
          + ENNReal.ofReal (qSign * ε) := by rw [one_mul]

/-- **Two-sided sampler-transport accumulation, real form.** The EUF-CMA advantages of the
same adversary `main` against the two GPV instantiations differ by at most `qSign · ε`: both
one-sided instances of `advantage_le_advantage_add_of_trapdoorSample_tvDist` (the reverse
direction swaps the roles of the two PSFs, with the per-call bound flipped by symmetry of the
total-variation distance). -/
theorem abs_advantage_toReal_sub_le_of_trapdoorSample_tvDist
    (hEval : ∀ pk x, psf.eval pk x = psf'.eval pk x)
    (hShort : ∀ x, psf.isShort x = psf'.isShort x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hStep : ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c,
      tvDist (psf.trapdoorSample pk sk c) (psf'.trapdoorSample pk sk c) ≤ ε)
    (qSign : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hQ : ∀ pk, (adv.main pk).IsQueryBoundP (· matches .inr _) qSign) :
    |(adv.advantage (runtime M Salt)).toReal
      - ((⟨adv.main⟩ : SignatureAlg.unforgeableAdv
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf' hr M Salt)).advantage (runtime M Salt)).toReal| ≤ qSign * ε := by
  have h_loss_nonneg : (0 : ℝ) ≤ qSign * ε := mul_nonneg (Nat.cast_nonneg _) hε
  have h₁ := advantage_le_advantage_add_of_trapdoorSample_tvDist psf psf' hr M Salt
    hEval hShort hε hStep qSign adv hQ
  have h₂ := advantage_le_advantage_add_of_trapdoorSample_tvDist psf' psf hr M Salt
    (fun pk x => (hEval pk x).symm) (fun x => (hShort x).symm) hε
    (fun pk sk hx c => tvDist_comm (psf'.trapdoorSample pk sk c)
      (psf.trapdoorSample pk sk c) ▸ hStep pk sk hx c)
    qSign ⟨adv.main⟩ hQ
  -- Repackaging the same `main` twice returns the original adversary (structure eta).
  have hEta : (⟨(⟨adv.main⟩ : SignatureAlg.unforgeableAdv
        (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf' hr M Salt)).main⟩ : SignatureAlg.unforgeableAdv
        (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt)) = adv := rfl
  rw [hEta] at h₂
  have hC_ne_top : adv.advantage (runtime M Salt) ≠ ⊤ := probOutput_ne_top
  have hI_ne_top : ((⟨adv.main⟩ : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
        psf' hr M Salt)).advantage (runtime M Salt)) ≠ ⊤ := probOutput_ne_top
  have h₁' := ENNReal.toReal_mono
    (by exact ENNReal.add_ne_top.mpr ⟨hI_ne_top, ENNReal.ofReal_ne_top⟩) h₁
  have h₂' := ENNReal.toReal_mono
    (by exact ENNReal.add_ne_top.mpr ⟨hC_ne_top, ENNReal.ofReal_ne_top⟩) h₂
  rw [ENNReal.toReal_add hI_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal h_loss_nonneg] at h₁'
  rw [ENNReal.toReal_add hC_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal h_loss_nonneg] at h₂'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end GPVHashAndSign
