/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.Falcon.PackedFFT
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Min-entropy of the fast Fourier sampler

`Primitives.ffSampling` is a Klein-style sampler: every leaf draws four integers from the
one-dimensional sampler `samplerZ` and every node merges the two half-size outputs, an injective
operation (`Primitives.mergeFFT_injective`). Hence the largest pointwise mass of its output is at
most the product of the largest pointwise masses of the `4 · 2^κ` leaf draws
(`Primitives.probOutput_ffSampling_le`). With the one-dimensional guessing bound
`LatticeCrypto.discreteGaussianPMF_le_one_div_sub_one` this gives the sampler a min-entropy of
`4 · 2^κ · log₂ (σ_min √(2π) - 1)` bits when every leaf standard deviation is at least `σ_min`
(`Primitives.probOutput_ffSampling_le_of_gaussian`); at the Falcon parameter sets that is more
than `4 · 2^κ` bits (`Primitives.probOutput_ffSampling_le_half_pow`).
-/

public section

open OracleComp OracleSpec LatticeCrypto
open scoped ENNReal

namespace Falcon

/-! ## A bind whose continuation can produce the output from at most one input -/

/-- If the first computation has pointwise mass at most `M`, every continuation has pointwise
mass at most `B` at `y`, and at most one input to the continuation can produce `y`, then the
bind has pointwise mass at most `M * B` at `y`. -/
theorem probOutput_bind_le_mul {α β : Type} (mx : ProbComp α) (my : α → ProbComp β) (y : β)
    {M B : ℝ≥0∞} (hM : ∀ x, Pr[= x | mx] ≤ M) (hB : ∀ x, Pr[= y | my x] ≤ B)
    (huniq : ∀ x₁ x₂, Pr[= y | my x₁] ≠ 0 → Pr[= y | my x₂] ≠ 0 → x₁ = x₂) :
    Pr[= y | mx >>= my] ≤ M * B := by
  rw [probOutput_bind_eq_tsum]
  rcases Classical.em (∀ x, Pr[= y | my x] = 0) with h | h
  · simp [h]
  · obtain ⟨x₀, hx₀⟩ := not_forall.mp h
    rw [tsum_eq_single x₀ (fun x hx => ?_)]
    · exact mul_le_mul (hM x₀) (hB x₀) zero_le zero_le
    · rcases Classical.em (Pr[= y | my x] = 0) with hy | hy
      · simp [hy]
      · exact absurd (huniq x x₀ hy hx₀) hx

/-! ## Injectivity of the merge step and of the leaf packing -/

theorem Primitives.mergeFFT_injective {k : ℕ} :
    Function.Injective fun p : RealFFTPoly k × RealFFTPoly k => Primitives.mergeFFT p.1 p.2 := by
  intro p q h
  have := congrArg Primitives.splitFFT h
  simp only [RealFFTPoly.splitFFT_mergeFFT] at this
  exact this

/-- The packed leaf polynomial with real part `a` and imaginary part `b`. -/
@[expose] noncomputable def leafPack (a b : ℤ) : RealFFTPoly 0 :=
  RealFFTPoly.pack (Vector.ofFn fun _ => (a : ℝ)) (Vector.ofFn fun _ => (b : ℝ))

theorem leafPack_re (a b : ℤ) : (leafPack a b).re ⟨0, by norm_num⟩ = a := by
  simp [leafPack]

theorem leafPack_im (a b : ℤ) : (leafPack a b).im ⟨0, by norm_num⟩ = b := by
  simp [leafPack]

theorem leafPack_inj {a b a' b' : ℤ} (h : leafPack a b = leafPack a' b') : a = a' ∧ b = b' := by
  refine ⟨?_, ?_⟩
  · have := congrArg (fun v : RealFFTPoly 0 => v.re ⟨0, by norm_num⟩) h
    rw [leafPack_re, leafPack_re] at this
    exact_mod_cast this
  · have := congrArg (fun v : RealFFTPoly 0 => v.im ⟨0, by norm_num⟩) h
    rw [leafPack_im, leafPack_im] at this
    exact_mod_cast this

/-! ## Leaf standard deviations -/

/-- Every leaf of the Falcon tree carries a standard deviation of at least `σmin`. -/
def FalconTree.LeavesGE : {κ : ℕ} → FalconTree κ → ℝ → Prop
  | _, .leaf σ, σmin => σmin ≤ σ
  | _, .node _ left right, σmin => left.LeavesGE σmin ∧ right.LeavesGE σmin

/-! ## The product bound -/

theorem Primitives.ffSampling_leaf {p : Params} (prims : Primitives p) (t₀ t₁ : RealFFTPoly 0)
    (σ : ℝ) :
    prims.ffSampling 0 (t₀, t₁) (.leaf σ) =
      (prims.samplerZ (t₀.re ⟨0, by norm_num⟩) σ >>= fun a =>
        prims.samplerZ (t₀.im ⟨0, by norm_num⟩) σ >>= fun b =>
          prims.samplerZ (t₁.re ⟨0, by norm_num⟩) σ >>= fun c =>
            prims.samplerZ (t₁.im ⟨0, by norm_num⟩) σ >>= fun d =>
              pure (leafPack a b, leafPack c d)) := rfl

theorem Primitives.ffSampling_node {p : Params} (prims : Primitives p) {k : ℕ}
    (t₀ t₁ : RealFFTPoly (k + 1)) (ℓ : RealFFTPoly (k + 1)) (left right : FalconTree k) :
    prims.ffSampling (k + 1) (t₀, t₁) (.node ℓ left right) =
      (prims.ffSampling k (Primitives.splitFFT t₁) right >>= fun s₁ =>
        prims.ffSampling k
          (Primitives.splitFFT (t₀ + Primitives.adjustTarget ℓ t₁ (Primitives.mergeFFT s₁.1 s₁.2)))
          left >>= fun s₀ =>
          pure (Primitives.mergeFFT s₀.1 s₀.2, Primitives.mergeFFT s₁.1 s₁.2)) := rfl

/-- **Min-entropy of `ffSampling` from the min-entropy of `samplerZ`.** If every call of the
one-dimensional sampler at a standard deviation of at least `σmin` has pointwise mass at most
`M`, then every output of `ffSampling` on a tree whose leaves are at least `σmin` has pointwise
mass at most `M ^ (4 · 2^κ)`: each leaf draws four integers, and the merges are injective. -/
theorem Primitives.probOutput_ffSampling_le {p : Params} (prims : Primitives p) {M : ℝ≥0∞}
    {σmin : ℝ} (hZ : ∀ (μ σ' : ℝ), σmin ≤ σ' → ∀ v : ℤ, Pr[= v | prims.samplerZ μ σ'] ≤ M) :
    ∀ (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ), tree.LeavesGE σmin →
      ∀ z : FFTPair κ, Pr[= z | prims.ffSampling κ t tree] ≤ M ^ (4 * 2 ^ κ)
  | 0, (t₀, t₁), .leaf σ, hl, z => by
    rw [Primitives.ffSampling_leaf]
    have hM' : ∀ (μ : ℝ) (v : ℤ), Pr[= v | prims.samplerZ μ σ] ≤ M := fun μ v => hZ μ σ hl v
    have hmem : ∀ {a b c d : ℤ} {w : FFTPair 0},
        w ∈ support (pure (leafPack a b, leafPack c d) : ProbComp (FFTPair 0)) →
          w = (leafPack a b, leafPack c d) := by
      intro a b c d w hw
      simpa using hw
    have h4 : ∀ a b c : ℤ,
        Pr[= z | (prims.samplerZ (t₁.im ⟨0, by norm_num⟩) σ >>= fun d =>
          pure (leafPack a b, leafPack c d) : ProbComp (FFTPair 0))] ≤ M * 1 := by
      intro a b c
      refine probOutput_bind_le_mul _ _ z (hM' _) (fun _ => probOutput_le_one) ?_
      intro d₁ d₂ h₁ h₂
      rw [ne_eq, probOutput_eq_zero_iff, not_not] at h₁ h₂
      have e := (hmem h₁).symm.trans (hmem h₂)
      exact (leafPack_inj (Prod.mk.inj e).2).2
    have h3 : ∀ a b : ℤ,
        Pr[= z | (prims.samplerZ (t₁.re ⟨0, by norm_num⟩) σ >>= fun c =>
          prims.samplerZ (t₁.im ⟨0, by norm_num⟩) σ >>= fun d =>
            pure (leafPack a b, leafPack c d) : ProbComp (FFTPair 0))] ≤ M * (M * 1) := by
      intro a b
      refine probOutput_bind_le_mul _ _ z (hM' _) (fun c => h4 a b c) ?_
      intro c₁ c₂ h₁ h₂
      rw [ne_eq, probOutput_eq_zero_iff, not_not, mem_support_bind_iff] at h₁ h₂
      obtain ⟨d₁, -, h₁⟩ := h₁
      obtain ⟨d₂, -, h₂⟩ := h₂
      have e := (hmem h₁).symm.trans (hmem h₂)
      exact (leafPack_inj (Prod.mk.inj e).2).1
    have h2 : ∀ a : ℤ,
        Pr[= z | (prims.samplerZ (t₀.im ⟨0, by norm_num⟩) σ >>= fun b =>
          prims.samplerZ (t₁.re ⟨0, by norm_num⟩) σ >>= fun c =>
            prims.samplerZ (t₁.im ⟨0, by norm_num⟩) σ >>= fun d =>
              pure (leafPack a b, leafPack c d) : ProbComp (FFTPair 0))] ≤
          M * (M * (M * 1)) := by
      intro a
      refine probOutput_bind_le_mul _ _ z (hM' _) (fun b => h3 a b) ?_
      intro b₁ b₂ h₁ h₂
      rw [ne_eq, probOutput_eq_zero_iff, not_not, mem_support_bind_iff] at h₁ h₂
      obtain ⟨c₁, -, h₁⟩ := h₁
      obtain ⟨c₂, -, h₂⟩ := h₂
      rw [mem_support_bind_iff] at h₁ h₂
      obtain ⟨d₁, -, h₁⟩ := h₁
      obtain ⟨d₂, -, h₂⟩ := h₂
      have e := (hmem h₁).symm.trans (hmem h₂)
      exact (leafPack_inj (Prod.mk.inj e).1).2
    have h1 : Pr[= z | (prims.samplerZ (t₀.re ⟨0, by norm_num⟩) σ >>= fun a =>
        prims.samplerZ (t₀.im ⟨0, by norm_num⟩) σ >>= fun b =>
          prims.samplerZ (t₁.re ⟨0, by norm_num⟩) σ >>= fun c =>
            prims.samplerZ (t₁.im ⟨0, by norm_num⟩) σ >>= fun d =>
              pure (leafPack a b, leafPack c d) : ProbComp (FFTPair 0))] ≤
          M * (M * (M * (M * 1))) := by
      refine probOutput_bind_le_mul _ _ z (hM' _) (fun a => h2 a) ?_
      intro a₁ a₂ h₁ h₂
      rw [ne_eq, probOutput_eq_zero_iff, not_not, mem_support_bind_iff] at h₁ h₂
      obtain ⟨b₁, -, h₁⟩ := h₁
      obtain ⟨b₂, -, h₂⟩ := h₂
      rw [mem_support_bind_iff] at h₁ h₂
      obtain ⟨c₁, -, h₁⟩ := h₁
      obtain ⟨c₂, -, h₂⟩ := h₂
      rw [mem_support_bind_iff] at h₁ h₂
      obtain ⟨d₁, -, h₁⟩ := h₁
      obtain ⟨d₂, -, h₂⟩ := h₂
      have e := (hmem h₁).symm.trans (hmem h₂)
      exact (leafPack_inj (Prod.mk.inj e).1).1
    calc Pr[= z | _] ≤ M * (M * (M * (M * 1))) := h1
      _ = M ^ (4 * 2 ^ 0) := by ring
  | k + 1, (t₀, t₁), .node ℓ left right, hl, z => by
    rw [Primitives.ffSampling_node]
    obtain ⟨hlL, hlR⟩ := hl
    have ihR := fun t => Primitives.probOutput_ffSampling_le prims hZ k t right hlR
    have ihL := fun t => Primitives.probOutput_ffSampling_le prims hZ k t left hlL
    have hinner : ∀ s₁ : FFTPair k,
        Pr[= z | (prims.ffSampling k
          (Primitives.splitFFT (t₀ + Primitives.adjustTarget ℓ t₁ (Primitives.mergeFFT s₁.1 s₁.2)))
          left >>= fun s₀ =>
          pure (Primitives.mergeFFT s₀.1 s₀.2, Primitives.mergeFFT s₁.1 s₁.2) :
            ProbComp (FFTPair (k + 1)))] ≤ M ^ (4 * 2 ^ k) * 1 := by
      intro s₁
      refine probOutput_bind_le_mul _ _ z (ihL _) (fun _ => probOutput_le_one) ?_
      intro s₀ s₀' h₁ h₂
      rw [ne_eq, probOutput_eq_zero_iff, not_not, support_pure, Set.mem_singleton_iff] at h₁ h₂
      have e := Prod.mk.inj (h₁.symm.trans h₂)
      exact Primitives.mergeFFT_injective e.1
    refine le_trans (probOutput_bind_le_mul _ _ z (ihR _) hinner ?_) ?_
    · intro s₁ s₁' h₁ h₂
      rw [ne_eq, probOutput_eq_zero_iff, not_not, mem_support_bind_iff] at h₁ h₂
      obtain ⟨s₀, -, h₁⟩ := h₁
      obtain ⟨s₀', -, h₂⟩ := h₂
      rw [support_pure, Set.mem_singleton_iff] at h₁ h₂
      have e := Prod.mk.inj (h₁.symm.trans h₂)
      exact Primitives.mergeFFT_injective e.2
    · rw [mul_one, ← pow_add, show 4 * 2 ^ k + 4 * 2 ^ k = 4 * 2 ^ (k + 1) by ring]

/-! ## Instantiation at the exact discrete Gaussian -/

/-- If `samplerZ` is the exact discrete Gaussian at every standard deviation `σ' ≥ σmin`, then
its pointwise mass is at most `1 / (σmin √(2π) - 1)` (`discreteGaussianPMF_le_one_div_sub_one`,
monotone in the standard deviation). -/
theorem probOutput_samplerZ_le_of_gaussian {p : Params} (prims : Primitives p) {σmin : ℝ}
    (hσmin : 1 < σmin * Real.sqrt (2 * Real.pi))
    (hZ : ∀ (μ σ' : ℝ), σmin ≤ σ' → ∀ v : ℤ,
      Pr[= v | prims.samplerZ μ σ'] = ENNReal.ofReal (discreteGaussianPMF σ' μ v))
    (μ σ' : ℝ) (hσ' : σmin ≤ σ') (v : ℤ) :
    Pr[= v | prims.samplerZ μ σ'] ≤
      ENNReal.ofReal (1 / (σmin * Real.sqrt (2 * Real.pi) - 1)) := by
  rw [hZ μ σ' hσ' v]
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hprod : σmin * Real.sqrt (2 * Real.pi) ≤ σ' * Real.sqrt (2 * Real.pi) :=
    mul_le_mul_of_nonneg_right hσ' hsqrt.le
  have hσ'sqrt : 1 < σ' * Real.sqrt (2 * Real.pi) := lt_of_lt_of_le hσmin hprod
  have hσ'pos : 0 < σ' := by
    by_contra h
    have : σ' * Real.sqrt (2 * Real.pi) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hsqrt.le
    linarith
  refine ENNReal.ofReal_le_ofReal (le_trans
    (discreteGaussianPMF_le_one_div_sub_one σ' μ hσ'pos hσ'sqrt v) ?_)
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- **Min-entropy of `ffSampling` at the exact discrete Gaussian.** With an exact
one-dimensional Gaussian sampler and every leaf standard deviation at least `σmin`, every output
has pointwise mass at most `(1 / (σmin √(2π) - 1)) ^ (4 · 2^κ)`. -/
theorem Primitives.probOutput_ffSampling_le_of_gaussian {p : Params} (prims : Primitives p)
    {σmin : ℝ} (hσmin : 1 < σmin * Real.sqrt (2 * Real.pi))
    (hZ : ∀ (μ σ' : ℝ), σmin ≤ σ' → ∀ v : ℤ,
      Pr[= v | prims.samplerZ μ σ'] = ENNReal.ofReal (discreteGaussianPMF σ' μ v))
    (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ) (hl : tree.LeavesGE σmin) (z : FFTPair κ) :
    Pr[= z | prims.ffSampling κ t tree] ≤
      ENNReal.ofReal (1 / (σmin * Real.sqrt (2 * Real.pi) - 1)) ^ (4 * 2 ^ κ) :=
  Primitives.probOutput_ffSampling_le prims
    (probOutput_samplerZ_le_of_gaussian prims hσmin hZ) κ t tree hl z

/-- Once `σmin √(2π) ≥ 3`, each leaf draw has mass at most `1/2`, so the sampler has at least
`4 · 2^κ` bits of min-entropy. -/
theorem Primitives.probOutput_ffSampling_le_half_pow {p : Params} (prims : Primitives p)
    {σmin : ℝ} (h3 : 3 ≤ σmin * Real.sqrt (2 * Real.pi))
    (hZ : ∀ (μ σ' : ℝ), σmin ≤ σ' → ∀ v : ℤ,
      Pr[= v | prims.samplerZ μ σ'] = ENNReal.ofReal (discreteGaussianPMF σ' μ v))
    (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ) (hl : tree.LeavesGE σmin) (z : FFTPair κ) :
    Pr[= z | prims.ffSampling κ t tree] ≤ ENNReal.ofReal (1 / 2) ^ (4 * 2 ^ κ) := by
  refine le_trans
    (Primitives.probOutput_ffSampling_le_of_gaussian prims (by linarith) hZ κ t tree hl z) ?_
  have hreal : 1 / (σmin * Real.sqrt (2 * Real.pi) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (a := 2) (b := σmin * Real.sqrt (2 * Real.pi) - 1) (by norm_num)
      (by linarith)
  gcongr

/-- The Falcon-512 minimum standard deviation clears the `1/2`-per-draw threshold. -/
theorem falcon512_sigmaMin_sqrt_two_pi_ge_three :
    3 ≤ falcon512.sigmaMin * Real.sqrt (2 * Real.pi) := by
  have hpi := Real.pi_gt_three
  have h6 : (2.44 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hs : falcon512.sigmaMin = (12778336969128337 : ℝ) / 10000000000000000 := rfl
  rw [hs]
  nlinarith [h6]

/-- The Falcon-1024 minimum standard deviation clears the `1/2`-per-draw threshold. -/
theorem falcon1024_sigmaMin_sqrt_two_pi_ge_three :
    3 ≤ falcon1024.sigmaMin * Real.sqrt (2 * Real.pi) := by
  have hpi := Real.pi_gt_three
  have h6 : (2.44 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hs : falcon1024.sigmaMin = (1298280334344292 : ℝ) / 1000000000000000 := rfl
  rw [hs]
  nlinarith [h6]

end Falcon

end
