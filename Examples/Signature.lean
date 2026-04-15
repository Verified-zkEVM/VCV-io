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

- **Completeness** follows from `Schnorr.sigma_complete` via `FiatShamir.perfectlyCorrect`.
- **EUF-CMA** security is proved from the generic Fiat-Shamir reduction theorem
  `FiatShamir.euf_cma_bound`.
-/


open OracleComp OracleSpec DiffieHellman

namespace Schnorr

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (G : Type) [AddCommGroup G] [Module F G] [Fintype G] [SampleableType G] [DecidableEq G]

/-- Schnorr signature scheme: Fiat-Shamir applied to the Schnorr Σ-protocol
with the discrete-log generable relation. -/
def signature (g : G) (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M] :
    SignatureAlg (OracleComp (unifSpec + (M × G →ₒ F)))
      (M := M) (PK := G) (SK := F) (S := G × F) :=
  FiatShamir (Schnorr.sigma F G g) (dlogGenerable g hg) M

section extractor

variable {M : Type} [DecidableEq M]

/-- Deterministic Schnorr-signature extractor postprocessing on value-carrying fork outputs.

The fork payload records two forged signatures together with the original and replacement hash
values at the chosen random-oracle query. The extractor succeeds exactly when the two forgeries
target the same message, have the same commitment, and verify against two distinct challenges.

Delegates to `Schnorr.extractCandidate` after checking message equality. -/
def signatureExtractCandidate (g pk : G) :
    Option ((M × (G × F)) × F × (M × (G × F)) × F) → Option F
  | none => none
  | some ((msg₁, sig₁), c₁, (msg₂, sig₂), c₂) =>
      if msg₁ = msg₂ then
        Schnorr.extractCandidate F G g pk (some (sig₁, c₁, sig₂, c₂))
      else
        none

section

omit [Fintype G] [Fintype F] [SampleableType F] [SampleableType G]

/-- If the Schnorr-signature fork postprocessing returns `some sk`, then `sk` is a valid
discrete-log witness for the public key `pk`. Follows from `Schnorr.extractCandidate_sound`. -/
theorem signatureExtractCandidate_sound (g pk : G)
    {res : Option ((M × (G × F)) × F × (M × (G × F)) × F)}
    {sk : F}
    (hsk : signatureExtractCandidate (F := F) (G := G) g pk res = some sk) :
    sk • g = pk := by
  cases res with
  | none => simp [signatureExtractCandidate] at hsk
  | some data =>
      rcases data with ⟨⟨msg₁, sig₁⟩, c₁, ⟨msg₂, sig₂⟩, c₂⟩
      simp only [signatureExtractCandidate] at hsk
      split at hsk
      · exact extractCandidate_sound F G g pk hsk
      · simp at hsk

/-- Any witness in the support of the Schnorr-signature fork postprocessing is valid. -/
theorem signatureExtractCandidate_sound_of_mem_support
    (g pk : G)
    {m : Type → Type} [Monad m] [LawfulMonad m] [HasEvalSet m]
    {oa : m (Option ((M × (G × F)) × F × (M × (G × F)) × F))} {sk : F}
    (hsk :
      some sk ∈
        support (signatureExtractCandidate (F := F) (G := G) g pk <$> oa)) :
    sk • g = pk := by
  rw [support_map] at hsk
  rcases hsk with ⟨res, _, hres⟩
  exact signatureExtractCandidate_sound
    (F := F) (G := G) (M := M) g pk hres

end

end extractor

omit [DecidableEq F] in
/-- Completeness of the Schnorr signature follows from completeness of the
underlying Schnorr Σ-protocol via the generic Fiat-Shamir completeness theorem. -/
theorem signature_complete (g : G) (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M] :
    SignatureAlg.PerfectlyComplete
      (signature F G g hg M)
      (FiatShamir.runtime (Commit := G) (Chal := F) M) :=
  FiatShamir.perfectlyCorrect _ _ M (Schnorr.sigma_complete F G g)

/-- Pointcheval-Stern style EUF-CMA reduction for Schnorr signatures.

The bound includes:
* explicit bounds on signing-oracle and random-oracle queries by the adversary;
* an explicit DLog reduction target;
* the standard forking-lemma loss term `eps * (eps / (qH + 1) - 1 / |F|)`.

Because Schnorr has perfect HVZK (`ζ_zk = 0`), the simulation loss vanishes and the
CMA advantage coincides with the NMA advantage. -/
theorem signature_euf_cma (g : G) (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M]
    (adv : SignatureAlg.unforgeableAdv (signature F G g hg M))
    (qS qH : ℕ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (Commit := G) (Chal := F)
      (S' := G × F) (oa := adv.main pk) qS qH) :
    ∃ reduction : DLogAdversary F G,
      let eps := adv.advantage (FiatShamir.runtime (Commit := G) (Chal := F) M) -
        ENNReal.ofReal (qS * (0 : ℝ))
      eps * (eps / (qH + 1 : ENNReal) - FiatShamir.challengeSpaceInv F) ≤
        Pr[= true | dlogExp g reduction] := by
  obtain ⟨red, hred⟩ := FiatShamir.euf_cma_bound (Schnorr.sigma F G g) (dlogGenerable g hg) M
    (Schnorr.sigma_speciallySound F G g) (Schnorr.simTranscript F G g)
    (ζ_zk := 0) le_rfl
    ((SigmaProtocol.perfectHVZK_iff_hvzk_zero _ _).mp (Schnorr.sigma_hvzk F G g))
    adv qS qH hQ
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

end Schnorr
