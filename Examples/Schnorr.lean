/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.FiatShamir
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
    let c ← ($ᵗ F : ProbComp F)
    let r ← ($ᵗ F : ProbComp F)
    pure (((r + c * sk) • g - c • pk, c, r + c * sk) : G × F × F)]
  · simp only [SigmaProtocol.realTranscript, sigma]
    vcstep rw
    simp [h_eq, add_smul, mul_smul, add_sub_cancel_right]
  · refine probOutput_bind_congr' ($ᵗ F : ProbComp F) t ?_
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

end Schnorr
