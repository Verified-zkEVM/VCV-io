/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.Schnorr
import Examples.SchnorrExtractorRuntime
import VCVio.CryptoFoundations.FiatShamir
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# Schnorr Signature via Fiat-Shamir

The Schnorr digital signature scheme is obtained by applying the Fiat-Shamir
transform to the Schnorr Σ-protocol with the discrete-log generable relation.

## Construction

Given `Module F G`, a generator `g : G`, and a bijection proof
`hg : Function.Bijective (· • g : F → G)`:

- **Key generation**: sample `sk ← $ᵗ F`, output `(pk, sk) = (sk • g, sk)`
- **Sign**: commit `R = r • g`, hash `c = H(m, R)`, respond `z = r + c * sk`
- **Verify**: check `z • g = R + c • pk` via the random oracle

## Security

- **Completeness** follows from `schnorrSigma_complete` via `FiatShamir.perfectlyCorrect`.
- **EUF-CMA** security is proved from the generic Fiat-Shamir reduction theorem
  `FiatShamir.euf_cma_bound`.
-/


open OracleComp OracleSpec DiffieHellman

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (G : Type) [AddCommGroup G] [Module F G] [Fintype G] [SampleableType G] [DecidableEq G]

/-- Schnorr signature scheme: Fiat-Shamir applied to the Schnorr Σ-protocol
with the discrete-log generable relation. -/
def schnorrSignature (g : G) (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M] :
    SignatureAlg (OracleComp (unifSpec + (M × G →ₒ F)))
      (M := M) (PK := G) (SK := F) (S := G × F) :=
  FiatShamir (schnorrSigma F G g) (dlogGenerable g hg) M

section extractor

variable {M : Type} [DecidableEq M]

/-- Deterministic Schnorr-signature extractor postprocessing on value-carrying fork outputs.

The fork payload records two forged signatures together with the original and replacement hash
values at the chosen random-oracle query. The extractor succeeds exactly when the two forgeries
target the same message, have the same commitment, and verify against two distinct challenges. -/
def schnorrSignatureExtractCandidateFromForkValues (g pk : G) :
    Option ((M × (G × F)) × F × (M × (G × F)) × F) → Option F
  | none => none
  | some ((msg₁, (R₁, z₁)), c₁, (msg₂, (R₂, z₂)), c₂) =>
      if _hmsg : msg₁ = msg₂ then
        if _hR : R₁ = R₂ then
          if _hω : c₁ = c₂ then
            none
          else if (schnorrSigma F G g).verify pk R₁ c₁ z₁ = true ∧
              (schnorrSigma F G g).verify pk R₂ c₂ z₂ = true then
            some ((z₁ - z₂) * (c₁ - c₂)⁻¹)
          else
            none
        else
          none
      else
        none

section

omit [Fintype G]
omit [Fintype F]

/-- If the Schnorr-signature fork postprocessing returns `some sk`, then `sk` is a valid
discrete-log witness for the public key `pk`.

The theorem isolates the cryptographic content of the Pointcheval-Stern postprocessing step:
once a fork produces two Schnorr signatures on the same message with distinct hash challenges,
the witness extracted from those signatures is sound. -/
theorem schnorrSignatureExtractCandidateFromForkValues_sound (g pk : G)
    {res : Option ((M × (G × F)) × F × (M × (G × F)) × F)}
    {sk : F}
    (hsk :
      schnorrSignatureExtractCandidateFromForkValues (F := F) (G := G) g pk res = some sk) :
    sk • g = pk := by
  cases res with
  | none =>
      simp [schnorrSignatureExtractCandidateFromForkValues] at hsk
  | some data =>
      rcases data with ⟨⟨msg₁, R₁, z₁⟩, c₁, ⟨msg₂, R₂, z₂⟩, c₂⟩
      by_cases hmsg : msg₁ = msg₂
      · by_cases hR : R₁ = R₂
        · by_cases hω : c₁ = c₂
          · simp [schnorrSignatureExtractCandidateFromForkValues, hmsg, hR, hω] at hsk
          · have hsk' :
                ((schnorrSigma F G g).verify pk R₂ c₁ z₁ = true ∧
                  (schnorrSigma F G g).verify pk R₂ c₂ z₂ = true) ∧
                (z₁ - z₂) * (c₁ - c₂)⁻¹ = sk := by
              simpa [schnorrSignatureExtractCandidateFromForkValues, hmsg, hR, hω] using hsk
            rcases hsk' with ⟨hAnd, hskEq⟩
            have hv₁ : z₁ • g = R₂ + c₁ • pk := by
              simpa [schnorrSigma] using hAnd.1
            have hv₂ : z₂ • g = R₂ + c₂ • pk := by
              simpa [schnorrSigma] using hAnd.2
            have hv₁' : z₁ • g = R₁ + c₁ • pk := by
              simpa [hR] using hv₁
            have hv₂' : z₂ • g = R₁ + c₂ • pk := by
              simpa [hR] using hv₂
            have hsound :
                (((z₁ - z₂) * (c₁ - c₂)⁻¹ : F) • g) = pk :=
              schnorrExtractFormula_sound (F := F) (G := G) g (hc := hω) hv₁' hv₂'
            rwa [hskEq] at hsound
        · simp [schnorrSignatureExtractCandidateFromForkValues, hmsg, hR] at hsk
      · simp [schnorrSignatureExtractCandidateFromForkValues, hmsg] at hsk

/-- Any witness in the support of the Schnorr-signature fork postprocessing is valid. -/
theorem schnorrSignatureExtractCandidateFromForkValues_sound_of_mem_support
    (g pk : G)
    {m : Type → Type} [Monad m] [LawfulMonad m] [HasEvalSet m]
    {oa : m (Option ((M × (G × F)) × F × (M × (G × F)) × F))} {sk : F}
    (hsk :
      some sk ∈
        support (schnorrSignatureExtractCandidateFromForkValues (F := F) (G := G) g pk <$> oa)) :
    sk • g = pk := by
  rw [support_map] at hsk
  rcases hsk with ⟨res, _, hres⟩
  exact schnorrSignatureExtractCandidateFromForkValues_sound
    (F := F) (G := G) (M := M) g pk (by simpa using hres)

end

end extractor

omit [DecidableEq F] in
/-- Completeness of the Schnorr signature follows from completeness of the
underlying Schnorr Σ-protocol via the generic Fiat-Shamir completeness theorem. -/
theorem schnorrSignature_complete (g : G) (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M] :
    SignatureAlg.PerfectlyComplete
      (schnorrSignature F G g hg M)
      (FiatShamir.runtime (Commit := G) (Chal := F) M) :=
  FiatShamir.perfectlyCorrect _ _ M (schnorrSigma_complete F G g)

/-- Pointcheval-Stern style EUF-CMA reduction for Schnorr signatures.

The corrected statement includes:
* an explicit bound on random-oracle queries by the adversary;
* an explicit DLog reduction target;
* the standard forking-lemma loss term `eps * (eps / (q + 1) - 1 / |F|)`.

This matches the intended Schnorr security theorem much more closely than the
old placeholder `adv.advantage ≤ sorry`. -/
theorem schnorrSignature_euf_cma (g : G) (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M]
    (adv : SignatureAlg.unforgeableAdv (schnorrSignature F G g hg M))
    (qBound : ℕ)
    (hQ : ∀ pk, FiatShamir.hashQueryBound (M := M) (Commit := G) (Chal := F)
      (oa := adv.main pk) qBound) :
    ∃ reduction : DLogAdversary F G,
      adv.advantage (FiatShamir.runtime (Commit := G) (Chal := F) M) *
          (adv.advantage (FiatShamir.runtime (Commit := G) (Chal := F) M) /
            (qBound + 1 : ENNReal) - FiatShamir.challengeSpaceInv F) ≤
        Pr[= true | dlogExp g reduction] := by
  obtain ⟨red, hred⟩ := FiatShamir.euf_cma_bound (schnorrSigma F G g) (dlogGenerable g hg) M
    (schnorrSigma_speciallySound F G g) (schnorrSimTranscript F G g)
    (schnorrSigma_hvzk F G g) adv qBound hQ
  refine ⟨fun _ pk => red pk, hred.trans (le_of_eq ?_)⟩
  simp only [hardRelationExp, dlogExp]
  rw [show Pr[= true | ($ᵗ G : ProbComp G) >>= fun pk =>
        red pk >>= fun sk => pure (decide (sk • g = pk))] =
      Pr[= true | ((· • g) <$> ($ᵗ F : ProbComp F)) >>= fun pk =>
        red pk >>= fun sk => pure (decide (sk • g = pk))] from by
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    congr 1; ext pk; congr 1
    exact (probOutput_map_bijective_uniform_cross F (· • g) hg pk).symm,
    map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp, pure_bind]
  exact probOutput_bind_congr' _ true fun x =>
    probOutput_bind_congr' _ true fun sk => by simp [hg.1.eq_iff]
