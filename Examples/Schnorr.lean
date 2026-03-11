/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.FiatShamir
import VCVio.ProgramLogic.Tactics

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

set_option autoImplicit false

open OracleSpec OracleComp SigmaProtocol

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (G : Type) [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

/-- Standard Schnorr Σ-protocol for knowledge of discrete log.
Challenge space is the full scalar field `F`. -/
def schnorrSigma (g : G) : SigmaProtocol G F G F F F
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
theorem schnorrSigma_complete (g : G) :
    PerfectlyComplete (schnorrSigma F G g) := by
  intro pk sk h
  have h_eq : sk • g = pk := of_decide_eq_true h
  simp only [schnorrSigma, pure_bind]
  have hverify : ∀ (r c : F), (r + c * sk) • g = r • g + c • pk := by
    intro r c; rw [add_smul, mul_smul, h_eq]
  simp [hverify]

omit [Fintype F] [DecidableEq F] in
/-- Special soundness: from two accepting transcripts `(R, c₁, z₁)` and `(R, c₂, z₂)` with
`c₁ ≠ c₂`, the extracted witness `(z₁ - z₂) * (c₁ - c₂)⁻¹` satisfies the relation. -/
theorem schnorrSigma_speciallySound (g : G) :
    SpeciallySound (schnorrSigma F G g) := by
  intro pk R c₁ c₂ z₁ z₂ h_ne h_v1 h_v2 w h_w
  dsimp [schnorrSigma] at *
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
def schnorrSimTranscript (g : G) (pk : G) : ProbComp (G × F × F) := do
  let c ← $ᵗ F
  let z ← $ᵗ F
  return (z • g - c • pk, c, z)

/-- Honest-verifier zero-knowledge: the real transcript distribution equals the simulated one.
The proof swaps sampling order and uses uniformity of `F` to reindex via the bijection
`r ↦ r + c * sk`. -/
theorem schnorrSigma_hvzk (g : G) :
    HVZK (schnorrSigma F G g) (schnorrSimTranscript F G g) := by
  intro pk sk h_sk
  have h_eq : sk • g = pk := of_decide_eq_true h_sk
  simp only [schnorrSigma, schnorrSimTranscript, bind_assoc, pure_bind]
  apply evalDist_ext; intro t
  qvcgen_step rw
  qvcgen_step rw congr' as ⟨c⟩
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simp only [show ∀ r : F,
      (r • g, c, r + c * sk) =
        ((r + c * sk) • g - c • pk, c, r + c * sk) from
    fun r => by rw [add_smul, mul_smul, h_eq, add_sub_cancel_right]]
  calc
    ∑' r : F,
        Pr[= r | ($ᵗ F : ProbComp F)] *
          Pr[= t | (pure (((r + c * sk) • g - c • pk, c, r + c * sk) : G × F × F) :
            ProbComp _)] =
      ∑' r : F,
        Pr[= r + c * sk | ($ᵗ F : ProbComp F)] *
          Pr[= t | (pure (((r + c * sk) • g - c • pk, c, r + c * sk) : G × F × F) :
            ProbComp _)] := by
        refine tsum_congr fun r => ?_
        congr 1
        change
          Pr[= r | (SampleableType.selectElem : ProbComp F)] =
            Pr[= r + c * sk | (SampleableType.selectElem : ProbComp F)]
        exact (inferInstance : SampleableType F).probOutput_selectElem_eq r (r + c * sk)
    _ =
      ∑' z : F,
        Pr[= z | ($ᵗ F : ProbComp F)] *
          Pr[= t | (pure ((z • g - c • pk, c, z) : G × F × F) : ProbComp _)] := by
        simpa using
          (Equiv.tsum_eq (Equiv.addRight (c * sk))
            (fun z : F =>
              Pr[= z | ($ᵗ F : ProbComp F)] *
                Pr[= t | (pure ((z • g - c • pk, c, z) : G × F × F) : ProbComp _)]))
