/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.FiatShamir
import VCVio.ProgramLogic.Tactics

/-!
# Schnorr Sigma Protocol over Hard Homogeneous Spaces

Defines the simplest (single-bit challenge) Schnorr-like Σ-protocol for knowledge of
discrete log in an additive torsor, and states the standard security properties.

## Protocol

Given `(x₀, pk) : P × P` with witness `sk : G` satisfying `sk +ᵥ x₀ = pk`:

1. **Commit**: sample `r ← G`, output `(r +ᵥ pk, r)` as `(PC, SC)`
2. **Challenge**: receive `b : Bool`
3. **Respond**: if `b` then `r` else `r + sk`
4. **Verify**: check `z +ᵥ (if b then pk else x₀) = PC`

Special soundness extracts `sk = z₂ - z₁` from two accepting transcripts with
`b₁ = true, b₂ = false`.
-/

set_option autoImplicit false

open OracleSpec OracleComp SigmaProtocol

variable (G P : Type)
  [AddCommGroup G] [AddTorsor G P]
  [SampleableType G] [SampleableType P] [DecidableEq P]

/-- Schnorr-like Σ-protocol over an HHS (additive torsor). Challenge space is `Bool`. -/
def schnorrSigma : SigmaProtocol (P × P) G P G Bool G
    (fun stmt sk => decide (sk +ᵥ stmt.1 = stmt.2)) where
  commit stmt _sk := do
    let r ← $ᵗ G
    return (r +ᵥ stmt.2, r)
  respond _stmt sk sc b := pure (if b then sc else sc + sk)
  verify stmt pc b z := if b then decide (z +ᵥ stmt.2 = pc) else decide (z +ᵥ stmt.1 = pc)
  sim _stmt := $ᵗ P
  extract b₁ z₁ _b₂ z₂ := pure (if b₁ then z₂ - z₁ else z₁ - z₂)

/-! ## Security properties -/

/-- Completeness: an honest prover with witness `sk` always produces an accepting transcript. -/
theorem schnorrSigma_complete :
    PerfectlyComplete (schnorrSigma G P) := by
  intro (x₀, pk) sk h
  have h_eq : sk +ᵥ x₀ = pk := of_decide_eq_true h
  dsimp [PerfectlyComplete, schnorrSigma]
  rw [← one_le_probOutput_iff, OracleComp.ProgramLogic.probOutput_eq_wp_indicator]
  game_wp
  simp [h_eq, add_vadd]
  rw [ENNReal.tsum_mul_right, HasEvalPMF.tsum_probOutput_eq_one, one_mul]
  have hcard :
      {x ∈ ({true, false} : Finset Bool) |
        if x = true then x = true ∨ sk +ᵥ pk = pk else x = false ∨ x₀ = pk}.card = 2 := by
    have hfilter :
        {x ∈ ({true, false} : Finset Bool) |
          if x = true then x = true ∨ sk +ᵥ pk = pk else x = false ∨ x₀ = pk} =
          ({true, false} : Finset Bool) := by
      ext x
      fin_cases x <;> simp
    rw [hfilter]
    simp
  rw [hcard]
  have htwo : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 := by
    exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  simp [htwo]

/-- Special soundness: from two accepting transcripts with different challenges, subtract the
responses to recover a witness sending `x₀` to `pk`. -/
theorem schnorrSigma_speciallySound :
    SpeciallySound (schnorrSigma G P) := by
  intro (x₀, pk) pc b₁ b₂ z₁ z₂ h_b h_v1 h_v2 w h_w
  dsimp [schnorrSigma] at *
  simp only [support_pure, Set.mem_singleton_iff] at h_w
  subst h_w
  revert h_b h_v1 h_v2
  cases b₁ <;> cases b₂ <;> simp <;> intro h1 h2
  · calc (z₁ - z₂) +ᵥ x₀
      _ = (-z₂ + z₁) +ᵥ x₀ := by rw [sub_eq_add_neg, add_comm]
      _ = -z₂ +ᵥ (z₁ +ᵥ x₀) := by rw [add_vadd]
      _ = -z₂ +ᵥ pc := by rw [h1]
      _ = -z₂ +ᵥ (z₂ +ᵥ pk) := by rw [← h2]
      _ = (-z₂ + z₂) +ᵥ pk := by rw [← add_vadd]
      _ = (0 : G) +ᵥ pk := by rw [neg_add_cancel]
      _ = pk := by rw [zero_vadd]
  · calc (z₂ - z₁) +ᵥ x₀
      _ = (-z₁ + z₂) +ᵥ x₀ := by rw [sub_eq_add_neg, add_comm]
      _ = -z₁ +ᵥ (z₂ +ᵥ x₀) := by rw [add_vadd]
      _ = -z₁ +ᵥ pc := by rw [h2]
      _ = -z₁ +ᵥ (z₁ +ᵥ pk) := by rw [← h1]
      _ = (-z₁ + z₁) +ᵥ pk := by rw [← add_vadd]
      _ = (0 : G) +ᵥ pk := by rw [neg_add_cancel]
      _ = pk := by rw [zero_vadd]

/-- Full transcript simulator: pick `b`, pick `z`, compute commitment from verification eq. -/
noncomputable def schnorrSimTranscript (stmt : P × P) : ProbComp (P × Bool × G) := do
  let b ← $ᵗ Bool
  let z ← $ᵗ G
  let pc := if b then z +ᵥ stmt.2 else z +ᵥ stmt.1
  return (pc, b, z)

/-- Honest-verifier zero-knowledge: after swapping the sampling order, match the real and
simulated transcript distributions pointwise, using uniformity to reindex the `false` branch. -/
theorem schnorrSigma_hvzk :
    HVZK (schnorrSigma G P) (schnorrSimTranscript G P) := by
  intro (x₀, pk) sk h_sk
  have h_eq : sk +ᵥ x₀ = pk := of_decide_eq_true h_sk
  simp only [schnorrSigma, schnorrSimTranscript, bind_assoc, pure_bind]
  apply evalDist_ext; intro t
  have hswap :
      Pr[= t | (do
        let r ← ($ᵗ G : ProbComp G)
        let b ← ($ᵗ Bool : ProbComp Bool)
        pure (r +ᵥ pk, b, if b then r else r + sk))] =
      Pr[= t | (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let r ← ($ᵗ G : ProbComp G)
        pure (r +ᵥ pk, b, if b then r else r + sk))] := by
    prob_swap
  rw [hswap]
  refine probOutput_bind_congr' ($ᵗ Bool : ProbComp Bool) t ?_
  intro b; cases b
  case false =>
    simp only [ite_false, Bool.false_eq_true]
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    simp only [show ∀ r : G,
        (r +ᵥ pk, false, r + sk) = ((r + sk) +ᵥ x₀, false, r + sk) from
      fun r => by rw [← h_eq, add_vadd]]
    calc
      ∑' r : G,
          Pr[= r | ($ᵗ G : ProbComp G)] *
            Pr[= t | (pure (((r + sk) +ᵥ x₀, false, r + sk) : P × Bool × G) : ProbComp _)] =
        ∑' r : G,
          Pr[= r + sk | ($ᵗ G : ProbComp G)] *
            Pr[= t | (pure (((r + sk) +ᵥ x₀, false, r + sk) : P × Bool × G) : ProbComp _)] := by
          refine tsum_congr fun r => ?_
          congr 1
          change
            Pr[= r | (SampleableType.selectElem : ProbComp G)] =
              Pr[= r + sk | (SampleableType.selectElem : ProbComp G)]
          exact (inferInstance : SampleableType G).probOutput_selectElem_eq r (r + sk)
      _ =
        ∑' z : G,
          Pr[= z | ($ᵗ G : ProbComp G)] *
            Pr[= t | (pure ((z +ᵥ x₀, false, z) : P × Bool × G) : ProbComp _)] := by
          simpa [add_vadd] using
            (Equiv.tsum_eq (Equiv.addRight sk)
              (fun z : G =>
                Pr[= z | ($ᵗ G : ProbComp G)] *
                  Pr[= t | (pure ((z +ᵥ x₀, false, z) : P × Bool × G) : ProbComp _)]))
  case true =>
    simp only [ite_true]
