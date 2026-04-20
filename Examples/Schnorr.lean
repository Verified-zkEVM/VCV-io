/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.ProgramLogic.Tactics.Unary

/-!
# Schnorr Sigma Protocol

Standard Schnorr Σ-protocol for proof of knowledge of discrete logarithm
over a cyclic group, formalized using `Module F G`.

## Mathematical setup

- `F` : scalar field (e.g. `ZMod p` for a prime-order group)
- `G` : group of elements with `[AddCommGroup G]` and `[Module F G]`
- `g : G` : fixed public generator

## Protocol

Given public key `pk : G` with witness `sk : F` satisfying `sk • g = pk`:

1. **Commit**: sample `r ← F`, output `(r • g, r)` as `(R, r)`
2. **Challenge**: receive `c ← F` (full-field challenge)
3. **Respond**: `z = r + c * sk`
4. **Verify**: check `z • g = R + c • pk`

This matches the textbook Schnorr protocol. In multiplicative notation,
verification is `g^z = R · pk^c`.

## Security properties

- **Completeness**: trivial from `Module` axioms (`add_smul`, `mul_smul`)
- **Special soundness**: from two accepting transcripts with distinct challenges,
  extract `sk = (z₁ - z₂) * (c₁ - c₂)⁻¹` using field division
- **HVZK**: simulator picks `c, z ← F`, computes `R = z • g - c • pk`;
  distribution matches via change of variables
-/

open OracleSpec OracleComp SigmaProtocol
open scoped ENNReal

namespace Schnorr

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (G : Type) [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

/-- Standard Schnorr Σ-protocol for knowledge of discrete log.
Challenge space is the full scalar field `F`. -/
def sigma (g : G) : SigmaProtocol G F G F F F
    (fun pk sk => decide (sk • g = pk)) where
  commit _pk _sk := do
    let r ← $ᵗ F
    return (r • g, r)
  respond _pk sk sc c := pure (sc + c * sk)
  verify pk R c z := decide (z • g = R + c • pk)
  sim _pk := $ᵗ G
  extract c₁ z₁ c₂ z₂ := pure ((z₁ - z₂) * (c₁ - c₂)⁻¹)

/-! ## Security properties -/

omit [Fintype F] [DecidableEq F] in
/-- Completeness: an honest prover with valid witness always produces an accepting transcript.
Follows from `add_smul` and `mul_smul`. -/
theorem sigma_complete (g : G) :
    PerfectlyComplete (sigma F G g) := by
  intro pk sk h
  have h_eq : sk • g = pk := of_decide_eq_true h
  simp only [sigma, pure_bind]
  have hverify : ∀ (r c : F), (r + c * sk) • g = r • g + c • pk := by
    intro r c; rw [add_smul, mul_smul, h_eq]
  simp [hverify]

omit [Fintype F] [DecidableEq F] in
/-- Special soundness: from two accepting transcripts `(R, c₁, z₁)` and `(R, c₂, z₂)` with
`c₁ ≠ c₂`, the extracted witness `(z₁ - z₂) * (c₁ - c₂)⁻¹` satisfies the relation. -/
theorem sigma_speciallySound (g : G) :
    SpeciallySound (sigma F G g) := by
  intro pk R c₁ c₂ z₁ z₂ h_ne h_v1 h_v2 w h_w
  dsimp [sigma] at *
  simp only [support_pure, Set.mem_singleton_iff] at h_w
  subst h_w
  simp only [decide_eq_true_eq] at h_v1 h_v2 ⊢
  have h_sub : (z₁ - z₂) • g = (c₁ - c₂) • pk := by
    rw [sub_smul, sub_smul, h_v1, h_v2, add_sub_add_left_eq_sub]
  have h_ne' : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr h_ne
  calc ((z₁ - z₂) * (c₁ - c₂)⁻¹) • g
      = (c₁ - c₂)⁻¹ • ((z₁ - z₂) • g) := by rw [mul_comm, mul_smul]
    _ = (c₁ - c₂)⁻¹ • ((c₁ - c₂) • pk) := by rw [h_sub]
    _ = ((c₁ - c₂)⁻¹ * (c₁ - c₂)) • pk := by rw [← mul_smul]
    _ = (1 : F) • pk := by rw [inv_mul_cancel₀ h_ne']
    _ = pk := one_smul F pk

/-- Full transcript simulator: pick `c, z ← F`, compute commitment from verification equation. -/
def simTranscript (g : G) (pk : G) : ProbComp (G × F × F) := do
  let c ← $ᵗ F
  let z ← $ᵗ F
  return (z • g - c • pk, c, z)

omit [Fintype F] [DecidableEq F] in
/-- Honest-verifier zero-knowledge: the real transcript distribution equals the simulated one.
The proof swaps sampling order and uses uniformity of `F` to reindex via the bijection
`r ↦ r + c * sk`. -/
theorem sigma_hvzk (g : G) [Finite F] :
    PerfectHVZK (sigma F G g) (simTranscript F G g) := by
  let _ : Fintype F := Fintype.ofFinite F
  intro pk sk h_sk
  have h_eq : sk • g = pk := of_decide_eq_true h_sk
  apply evalDist_ext
  intro t
  trans Pr[= t | do
    let c ← ($ᵗ F)
    let r ← ($ᵗ F)
    pure (((r + c * sk) • g - c • pk, c, r + c * sk) : G × F × F)]
  · simp only [SigmaProtocol.realTranscript, sigma]
    vcstep rw
    simp [h_eq, add_smul, mul_smul, add_sub_cancel_right]
  · refine probOutput_bind_congr' ($ᵗ F) t ?_
    intro c
    simpa [simTranscript, map_eq_bind_pure_comp, bind_assoc, pure_bind] using
      (probOutput_bind_bijective_uniform_cross
        (α := F) (β := F)
        (f := fun r => r + c * sk)
        (hf := by
          constructor
          · intro r₁ r₂ h
            exact add_right_cancel h
          · intro z
            refine ⟨z - c * sk, ?_⟩
            simp [sub_eq_add_neg, add_left_comm, add_comm])
        (g := fun z => pure ((z • g - c • pk, c, z) : G × F × F))
        t)

omit [Fintype F] [DecidableEq F] in
/-- Closed-form for the Schnorr `realTranscript`: the real transcript is the joint
distribution of `(r • g, c, r + c * sk)` where `r, c ← $ᵗ F` are sampled *independently*.
This is the form in which the commitment `r • g` and the challenge `c` are literally
independent (by sampling order), making conditional uniformity trivial. -/
private lemma realTranscript_eq_indep (g : G) (pk : G) (sk : F) :
    SigmaProtocol.realTranscript (sigma F G g) pk sk =
      (do
        let r ← $ᵗ F
        let c ← $ᵗ F
        pure ((r • g, c, r + c * sk) : G × F × F)) := by
  simp only [SigmaProtocol.realTranscript, sigma, bind_assoc, pure_bind]

omit [DecidableEq F] in
/-- **`simCommitPredictability` for Schnorr.** With the standard bijection hypothesis
`hg : Function.Bijective (· • g : F → G)` (`F` acts simply transitively on `G`, so `g`
generates the group), the simulator's commit marginal is uniform over `G`, giving
predictability `β = 1/|F|` (equivalently `1/|G|`).

Proof: for any fixed challenge `c`, the response map `z ↦ z • g - c • pk : F → G` is a
bijection (composition of `· • g` with translation), so `(z • g - c • pk)` is uniform on
`G` when `z ← $ᵗ F`. Averaging over `c ← $ᵗ F` preserves uniformity, and uniformity on
`G` gives probability `1/|G| = 1/|F|` for any specific output. -/
theorem sigma_simCommitPredictability (g : G)
    (hg : Function.Bijective (· • g : F → G)) :
    SigmaProtocol.simCommitPredictability (sigma F G g) (simTranscript F G g)
      ((Fintype.card F : ℝ≥0∞)⁻¹) := by
  classical
  letI : Fintype G := Fintype.ofBijective _ hg
  intro pk c₀
  have hcard_FG : Fintype.card G = Fintype.card F := (Fintype.card_of_bijective hg).symm
  have hinv_eq : (Fintype.card F : ℝ≥0∞)⁻¹ = (Fintype.card G : ℝ≥0∞)⁻¹ := by rw [hcard_FG]
  have hbij_c : ∀ c : F, Function.Bijective (fun z : F => z • g - c • pk) := fun c =>
    (Equiv.subRight (c • pk)).bijective.comp hg
  have h_commit_uniform :
      evalDist (Prod.fst <$> simTranscript F G g pk) = evalDist ($ᵗ G) := by
    apply evalDist_ext
    intro x
    have h_rewrite : (Prod.fst <$> simTranscript F G g pk) =
        (do let c ← ($ᵗ F); let z ← ($ᵗ F); pure (z • g - c • pk) : ProbComp G) := by
      simp [simTranscript, map_bind]
    rw [h_rewrite, probOutput_bind_eq_tsum]
    have h_inner_const : ∀ c : F,
        Pr[= x | (do let z ← ($ᵗ F); pure (z • g - c • pk) : ProbComp G)] =
          (Fintype.card G : ℝ≥0∞)⁻¹ := by
      intro c
      have h_map : (do let z ← ($ᵗ F); pure (z • g - c • pk) : ProbComp G) =
          (fun z : F => z • g - c • pk) <$> ($ᵗ F) := by
        simp [map_eq_bind_pure_comp]
      rw [h_map,
        probOutput_map_bijective_uniform_cross F (f := fun z : F => z • g - c • pk) (hbij_c c),
        probOutput_uniformSample (α := G)]
    simp_rw [h_inner_const]
    rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul,
      probOutput_uniformSample (α := G)]
  have h_eq : probOutput (Prod.fst <$> simTranscript F G g pk) c₀ =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
    rw [probOutput_def, h_commit_uniform, ← probOutput_def,
      probOutput_uniformSample (α := G), hcard_FG]
  exact h_eq.le

omit [DecidableEq F] in
/-- **`simChalUniformGivenCommit` for Schnorr.** The proof reduces to the joint distribution
of independently-sampled `r, c ← $ᵗ F` via perfect HVZK and the closed form
`realTranscript_eq_indep`. The commitment `r • g` and challenge `c` are then literally
independent (by sampling order), so the joint factors as `Pr[commit = c₀] * (1/|F|)`. -/
theorem sigma_simChalUniformGivenCommit (g : G) :
    simChalUniformGivenCommit (sigma F G g) (simTranscript F G g) := by
  classical
  intro pk sk hsk c₀ ch₀
  have hHVZK := sigma_hvzk F G g pk sk hsk
  have hReal := realTranscript_eq_indep F G g pk sk
  set ind : ProbComp (G × F × F) := do
    let r ← $ᵗ F
    let c ← $ᵗ F
    pure (r • g, c, r + c * sk) with hind_def
  have hSimEqIndep : evalDist (simTranscript F G g pk) = evalDist ind := by
    rw [← hHVZK, hReal]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hSimEqIndep,
      probEvent_congr' (fun _ _ => Iff.rfl) hSimEqIndep]
  -- Now both sides are `probEvent` over the explicit independent form.
  have hcard_ne_zero : (Fintype.card F : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := F)
  have hcard_ne_top : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- Define `M` = the per-`r` commit-marginal sum.
  set M : ℝ≥0∞ := ∑' r : F, (Fintype.card F : ℝ≥0∞)⁻¹ *
      (if r • g = c₀ then (1 : ℝ≥0∞) else 0) with hM_def
  -- Compute the joint probability.
  have hjoint :
      Pr[fun t : G × F × F => t.1 = c₀ ∧ t.2.1 = ch₀ | ind] =
        (Fintype.card F : ℝ≥0∞)⁻¹ * M := by
    rw [hind_def, probEvent_bind_eq_tsum, hM_def, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [probOutput_uniformSample, probEvent_bind_eq_tsum]
    rw [show (∑' c : F,
              Pr[= c | $ᵗ F] *
                Pr[fun t : G × F × F => t.1 = c₀ ∧ t.2.1 = ch₀ |
                  (pure ((r • g, c, r + c * sk) : G × F × F) : ProbComp _)]) =
            (Fintype.card F : ℝ≥0∞)⁻¹ *
              (if r • g = c₀ then (1 : ℝ≥0∞) else 0) by
      simp_rw [probOutput_uniformSample, probEvent_pure]
      rw [ENNReal.tsum_mul_left]
      congr 1
      by_cases hr : r • g = c₀
      · simp only [hr, true_and]
        rw [tsum_eq_single ch₀]
        · simp
        · intro c hc
          simp [hc]
      · simp [hr]]
  -- Compute the marginal probability.
  have hmarg :
      Pr[fun t : G × F × F => t.1 = c₀ | ind] = M := by
    rw [hind_def, probEvent_bind_eq_tsum, hM_def]
    refine tsum_congr fun r => ?_
    rw [probOutput_uniformSample, probEvent_bind_eq_tsum]
    rw [show (∑' c : F,
              Pr[= c | $ᵗ F] *
                Pr[fun t : G × F × F => t.1 = c₀ |
                  (pure ((r • g, c, r + c * sk) : G × F × F) : ProbComp _)]) =
            (if r • g = c₀ then (1 : ℝ≥0∞) else 0) by
      simp_rw [probOutput_uniformSample, probEvent_pure]
      by_cases hr : r • g = c₀
      · simp only [hr, if_true]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_const,
          ENat.card_eq_coe_fintype_card, mul_one, ENat.toENNReal_coe,
          ENNReal.inv_mul_cancel hcard_ne_zero hcard_ne_top]
      · simp [hr]]
  rw [hjoint, hmarg, mul_comm]

end Schnorr
