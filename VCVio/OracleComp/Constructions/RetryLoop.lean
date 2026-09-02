/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.EvalDist.TVDist

/-! # First-Success Retry Loops and their Total-Variation Theory

A *rejection sampler* is an attempt `attempt : ProbComp (Option α)` that either accepts,
returning `some a`, or rejects, returning `none`.  Running it until the first acceptance,
with a budget of `n` attempts, is `firstSome attempt n`; `retryToDefault` reads the loop as
a total `ProbComp α` by falling back to `default` when the budget is exhausted.

Two facts about such loops are needed to price a rejection sampler against an idealization.

* `tvDist_firstSome_le_geometric` — per-attempt closeness accumulates geometrically.  If two
  attempts are within total-variation distance `ζ` and the second rejects with probability at
  most `q`, the `n`-attempt loops are within `ζ · (1 + q + ⋯ + q^(n-1))`, hence within
  `ζ / (1 - q)` for every budget once `q < 1`.

* `tvDist_retryToDefault_le_pow` — a loop whose attempt *resamples* (`ResamplesTo`: replacing
  a rejection by a fresh draw from `cond` reproduces `cond`'s law, the defining property of
  rejection sampling) is within `q ^ n` of `cond` at budget `n`.  All of the error is the
  budget-exhaustion mass.

Together these separate the two costs a rejection loop carries — the per-attempt
approximation error and the exhaustion probability — instead of charging the whole rejection
rate to the approximation term.
-/

@[expose] public section

open OracleComp ENNReal

namespace ProbComp

variable {α : Type}

/-! ## The loop -/

/-- Run `attempt` up to `n` times, returning the first acceptance, or `none` if the budget is
exhausted. -/
def firstSome (attempt : ProbComp (Option α)) : ℕ → ProbComp (Option α)
  | 0 => pure none
  | n + 1 => attempt >>= fun r =>
      match r with
      | some a => pure (some a)
      | none => firstSome attempt n

@[simp] lemma firstSome_zero (attempt : ProbComp (Option α)) :
    firstSome attempt 0 = pure none := rfl

lemma firstSome_succ (attempt : ProbComp (Option α)) (n : ℕ) :
    firstSome attempt (n + 1) =
      attempt >>= fun r =>
        match r with
        | some a => pure (some a)
        | none => firstSome attempt n := rfl

/-- The retry loop read as a total computation: fall back to `default` when the attempt budget
is exhausted.  The fallback carries all of the loop's deviation from an ideal sampler
(`tvDist_retryToDefault_le_pow`). -/
noncomputable def retryToDefault [Inhabited α]
    (attempt : ProbComp (Option α)) (n : ℕ) : ProbComp α :=
  (fun o => o.getD default) <$> firstSome attempt n

@[simp] lemma retryToDefault_zero [Inhabited α] (attempt : ProbComp (Option α)) :
    retryToDefault attempt 0 = pure default := by
  simp [retryToDefault, firstSome]

lemma retryToDefault_succ [Inhabited α] (attempt : ProbComp (Option α)) (n : ℕ) :
    retryToDefault attempt (n + 1) =
      attempt >>= fun r =>
        match r with
        | some a => pure a
        | none => retryToDefault attempt n := by
  rw [retryToDefault, firstSome_succ, map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun r => ?_
  cases r with
  | some a => simp
  | none => rw [retryToDefault, map_eq_bind_pure_comp]

/-! ## Per-attempt closeness accumulates geometrically -/

/-- **Gluing per-attempt simulation across a first-success retry loop.**  If two optional
samplers are within total-variation distance `ζ` and the second rejects with probability at
most `q`, then the `n`-attempt retry loops are within `ζ · (1 + q + ⋯ + q^(n-1))`.  With
`q < 1` this is at most `ζ / (1 - q)` for every budget.

Each hybrid step couples one more attempt, and attempt `j` is only reached when the first `j`
attempts of the second loop all rejected — which is where the geometric factor comes from. -/
lemma tvDist_firstSome_le_geometric (a₁ a₂ : ProbComp (Option α))
    {ζ q : ℝ} (hζ : tvDist a₁ a₂ ≤ ζ) (hq : Pr[= none | a₂].toReal ≤ q) (hq0 : 0 ≤ q) :
    ∀ n : ℕ, tvDist (firstSome a₁ n) (firstSome a₂ n) ≤ ζ * ∑ j ∈ Finset.range n, q ^ j
  | 0 => by simp [firstSome]
  | (n + 1) => by
    have hζ0 : 0 ≤ ζ := le_trans (tvDist_nonneg a₁ a₂) hζ
    have ih := tvDist_firstSome_le_geometric a₁ a₂ hζ hq hq0 n
    have hGeomNonneg : (0 : ℝ) ≤ ∑ j ∈ Finset.range n, q ^ j :=
      Finset.sum_nonneg fun j _ => pow_nonneg hq0 j
    set k₁ : Option α → ProbComp (Option α) := fun r =>
      match r with
      | some a => pure (some a)
      | none => firstSome a₁ n with hk₁
    set k₂ : Option α → ProbComp (Option α) := fun r =>
      match r with
      | some a => pure (some a)
      | none => firstSome a₂ n with hk₂
    have hterm : ∀ b : Option α, b ≠ (none : Option α) →
        Pr[= b | a₂].toReal * tvDist (k₁ b) (k₂ b) = 0 := by
      intro b hb
      match b, hb with
      | some a, _ => simp [hk₁, hk₂]
    have hStep : tvDist (a₂ >>= k₁) (a₂ >>= k₂) ≤
        Pr[= none | a₂].toReal * tvDist (firstSome a₁ n) (firstSome a₂ n) := by
      refine le_trans (tvDist_bind_left_le a₂ k₁ k₂) (le_of_eq ?_)
      rw [tsum_eq_single (none : Option α) hterm]
    calc
      tvDist (firstSome a₁ (n + 1)) (firstSome a₂ (n + 1))
          = tvDist (a₁ >>= k₁) (a₂ >>= k₂) := by
            rw [firstSome_succ, firstSome_succ]
      _ ≤ tvDist (a₁ >>= k₁) (a₂ >>= k₁) + tvDist (a₂ >>= k₁) (a₂ >>= k₂) :=
            tvDist_triangle _ _ _
      _ ≤ ζ + Pr[= none | a₂].toReal * tvDist (firstSome a₁ n) (firstSome a₂ n) :=
            add_le_add (le_trans (tvDist_bind_right_le k₁ a₁ a₂) hζ) hStep
      _ ≤ ζ + q * (ζ * ∑ j ∈ Finset.range n, q ^ j) :=
            add_le_add le_rfl (mul_le_mul hq ih (tvDist_nonneg _ _) hq0)
      _ = ζ * ∑ j ∈ Finset.range (n + 1), q ^ j := by
            have hsum : ∑ j ∈ Finset.range (n + 1), q ^ j =
                q * (∑ j ∈ Finset.range n, q ^ j) + 1 := by
              rw [Finset.sum_range_succ', Finset.mul_sum]
              simp [pow_succ']
            rw [hsum]
            ring

/-- The geometric accumulation in closed form: for a rejection probability `q < 1` the loop
error is at most `ζ / (1 - q)` at every attempt budget. -/
lemma tvDist_firstSome_le_div (a₁ a₂ : ProbComp (Option α))
    {ζ q : ℝ} (hζ : tvDist a₁ a₂ ≤ ζ) (hq : Pr[= none | a₂].toReal ≤ q)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    tvDist (firstSome a₁ n) (firstSome a₂ n) ≤ ζ / (1 - q) := by
  have hζ0 : 0 ≤ ζ := le_trans (tvDist_nonneg a₁ a₂) hζ
  have hlt : (0 : ℝ) < 1 - q := by linarith
  refine le_trans (tvDist_firstSome_le_geometric a₁ a₂ hζ hq hq0 n) ?_
  have key : (∑ j ∈ Finset.range n, q ^ j) * (1 - q) = 1 - q ^ n := by
    have h := geom_sum_mul q n
    nlinarith [h]
  have hle : (∑ j ∈ Finset.range n, q ^ j) ≤ 1 / (1 - q) := by
    rw [le_div_iff₀ hlt, key]
    nlinarith [pow_nonneg hq0 n]
  calc ζ * ∑ j ∈ Finset.range n, q ^ j ≤ ζ * (1 / (1 - q)) :=
        mul_le_mul_of_nonneg_left hle hζ0
    _ = ζ / (1 - q) := by ring

/-- The total reading of the loop is no further apart than the optional one: `retryToDefault`
is a deterministic image of `firstSome`. -/
lemma tvDist_retryToDefault_le_firstSome [Inhabited α] (a₁ a₂ : ProbComp (Option α)) (n : ℕ) :
    tvDist (retryToDefault a₁ n) (retryToDefault a₂ n) ≤
      tvDist (firstSome a₁ n) (firstSome a₂ n) :=
  tvDist_map_le _ _ _

/-- Geometric accumulation for the total reading of the loop: the closed-form companion of
`tvDist_firstSome_le_div`. -/
lemma tvDist_retryToDefault_le_div [Inhabited α] (a₁ a₂ : ProbComp (Option α))
    {ζ q : ℝ} (hζ : tvDist a₁ a₂ ≤ ζ) (hq : Pr[= none | a₂].toReal ≤ q)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    tvDist (retryToDefault a₁ n) (retryToDefault a₂ n) ≤ ζ / (1 - q) :=
  le_trans (tvDist_retryToDefault_le_firstSome a₁ a₂ n)
    (tvDist_firstSome_le_div a₁ a₂ hζ hq hq0 hq1 n)

/-! ## Rejection resampling and the exhaustion-only error -/

/-- **Rejection resampling.**  Replacing a rejection of `attempt` by a fresh draw from `cond`
reproduces `cond`'s own law.  This is the defining property of a rejection sampler for `cond`:
the accepted outputs of `attempt` are distributed as `cond` conditioned on acceptance, and the
rejection event carries no information about the eventual value. -/
def ResamplesTo (attempt : ProbComp (Option α)) (cond : ProbComp α) : Prop :=
  𝒮[attempt >>= fun o =>
      match o with
      | some v => (pure v : ProbComp α)
      | none => cond] = 𝒮[cond]

/-- **The retry loop deviates from its target only by the exhaustion mass.**  For an attempt
that resamples to `cond` and rejects with probability at most `q`, the `n`-attempt loop is
within `q ^ n` of `cond` in total variation.

This is what separates the two costs of a rejection sampler: the loop is *exactly* right up to
running out of attempts, so the rejection rate itself is never charged to an approximation
budget — only `q ^ n` is. -/
theorem tvDist_retryToDefault_le_pow [Inhabited α]
    (attempt : ProbComp (Option α)) (cond : ProbComp α) {q : ℝ}
    (hres : ResamplesTo attempt cond)
    (hq : Pr[= none | attempt].toReal ≤ q) (hq0 : 0 ≤ q) :
    ∀ n : ℕ, tvDist (retryToDefault attempt n) cond ≤ q ^ n
  | 0 => by simpa using tvDist_le_one (pure (default : α) : ProbComp α) cond
  | (n + 1) => by
    have ih := tvDist_retryToDefault_le_pow attempt cond hres hq hq0 n
    set g : Option α → ProbComp α := fun o =>
      match o with
      | some v => pure v
      | none => retryToDefault attempt n with hg
    set gInf : Option α → ProbComp α := fun o =>
      match o with
      | some v => pure v
      | none => cond with hgInf
    -- The resampling branch is exactly `cond`.
    have hzero : tvDist (attempt >>= gInf) cond = 0 := by
      rw [tvDist_eq_zero_iff]; exact hres
    -- Only the rejection branch contributes to the loop-versus-resampling gap.
    have hterm : ∀ b : Option α, b ≠ (none : Option α) →
        Pr[= b | attempt].toReal * tvDist (g b) (gInf b) = 0 := by
      intro b hb
      match b, hb with
      | some a, _ => simp [hg, hgInf]
    have hStep : tvDist (attempt >>= g) (attempt >>= gInf) ≤
        Pr[= none | attempt].toReal * tvDist (retryToDefault attempt n) cond := by
      refine le_trans (tvDist_bind_left_le attempt g gInf) (le_of_eq ?_)
      rw [tsum_eq_single (none : Option α) hterm]
    calc tvDist (retryToDefault attempt (n + 1)) cond
        = tvDist (attempt >>= g) cond := by rw [retryToDefault_succ]
      _ ≤ tvDist (attempt >>= g) (attempt >>= gInf) + tvDist (attempt >>= gInf) cond :=
          tvDist_triangle _ _ _
      _ ≤ Pr[= none | attempt].toReal * tvDist (retryToDefault attempt n) cond + 0 := by
          rw [hzero]; exact add_le_add hStep le_rfl
      _ ≤ q * q ^ n := by
          rw [add_zero]
          exact mul_le_mul hq ih (tvDist_nonneg _ _) hq0
      _ = q ^ (n + 1) := by ring

/-! ## Uniform rejection sampling -/

/-- **Uniform rejection sampling resamples to the accept-conditional.** Drawing `δ` uniformly
from a finite type and accepting `F δ` exactly when `P δ` resamples to the uniform draw over the
accepting `δ`, mapped through `F`: replacing a rejection by a fresh draw from that conditional
reproduces the conditional. -/
theorem ResamplesTo.uniform_filter {D : Type} [Fintype D] [SampleableType D]
    (P : D → Prop) [DecidablePred P] [Nonempty {δ : D // P δ}] (F : D → α) :
    ResamplesTo ((fun δ => if P δ then some (F δ) else none) <$> ($ᵗ D))
      ((fun δ : {δ // P δ} => F δ.1) <$>
        (@uniformSample {δ // P δ} (SampleableType.ofFintype _))) := by
  have _ : DecidableEq α := Classical.decEq α
  let _ : SampleableType {δ : D // P δ} := SampleableType.ofFintype _
  set cond : ProbComp α := (fun δ : {δ : D // P δ} => F δ.1) <$> ($ᵗ {δ : D // P δ}) with hcond
  unfold ResamplesTo
  -- Replacing a rejection by a draw from `cond` is: draw `δ`, return `F δ` if accepted, else
  -- draw from `cond`.
  have hbind : ((fun δ => if P δ then some (F δ) else none) <$> ($ᵗ D) >>= fun o =>
      match o with
      | some v => (pure v : ProbComp α)
      | none => cond) =
      ($ᵗ D >>= fun δ => if P δ then pure (F δ) else cond) := by
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    refine bind_congr fun δ => ?_
    split_ifs <;> rfl
  rw [hbind]
  refine evalSPMF_ext fun x => ?_
  -- The counts: `N` box points, `K` accepted, `M` accepted with image `x`.
  set N : ℕ := Fintype.card D with hN
  set K : ℕ := Fintype.card {δ : D // P δ} with hK
  set M : ℕ := Fintype.card {δ : D // P δ ∧ F δ = x} with hM
  have hK0 : 0 < K := Fintype.card_pos
  have hKN : K ≤ N := Fintype.card_subtype_le _
  -- The conditional puts mass `M / K` on `x`.
  have hp : Pr[= x | cond] = (M : ℝ≥0∞) / K := by
    rw [hcond, probOutput_map, probEvent_uniformSample, ← Fintype.card_subtype, hM, hK]
    congr 2
    exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter P fun δ => F δ = x)
  -- The resampled attempt puts mass `(M + (N − K) · M / K) / N` on `x`.
  rw [probOutput_bind_eq_sum_fintype]
  simp only [probOutput_uniformSample]
  have hterm : ∀ δ : D, Pr[= x | (if P δ then pure (F δ) else cond : ProbComp α)] =
      (if P δ ∧ F δ = x then 1 else 0) + (if P δ then 0 else (M : ℝ≥0∞) / K) := by
    intro δ
    by_cases hδ : P δ
    · simp [hδ, probOutput_pure, eq_comm]
    · simp [hδ, hp]
  simp only [hterm, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_boole, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    nsmul_eq_mul]
  have hMcard : ((Finset.univ.filter fun δ : D => P δ ∧ F δ = x).card : ℝ≥0∞) = M := by
    rw [hM, Fintype.card_subtype]
  have hNKcard : ((Finset.univ.filter fun δ : D => ¬P δ).card : ℝ≥0∞) = (N : ℝ≥0∞) - K := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, ← hK, ← hN]
    exact ENNReal.natCast_sub N K
  rw [hMcard, hNKcard, ← hN, hp]
  -- The identity `N⁻¹ · (M + (N − K) · M / K) = M / K`, in the reals.
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le hK0 hKN).ne'
  have hK0' : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK0.ne'
  have hMK : ((M : ℝ≥0∞) / K) ≠ ⊤ := ENNReal.div_ne_top (by simp) hK0'
  have hprod : ((N : ℝ≥0∞) - K) * ((M : ℝ≥0∞) / K) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.sub_ne_top (by simp)) hMK
  have h1 : (N : ℝ≥0∞)⁻¹ * M ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hN0) (ENNReal.natCast_ne_top M)
  have h2 : (N : ℝ≥0∞)⁻¹ * (((N : ℝ≥0∞) - K) * ((M : ℝ≥0∞) / K)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hN0) hprod
  refine (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) hMK).mp ?_
  rw [ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_div,
    ENNReal.toReal_sub_of_le (by exact_mod_cast hKN) (ENNReal.natCast_ne_top N)]
  simp only [ENNReal.toReal_natCast]
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK0
  have hN' : (0 : ℝ) < N := lt_of_lt_of_le hK' (by exact_mod_cast hKN)
  field_simp
  ring

end ProbComp
