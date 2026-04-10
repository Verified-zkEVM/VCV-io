/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.Schnorr
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
- **EUF-CMA** security is stated with `sorry` (the generic bound in `FiatShamir` is
  itself incomplete, pending the full forking lemma).
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

omit [DecidableEq F] in
/-- Completeness of the Schnorr signature follows from completeness of the
underlying Schnorr Σ-protocol via the generic Fiat-Shamir completeness theorem. -/
theorem schnorrSignature_complete (g : G) (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M] :
    SignatureAlg.PerfectlyComplete
      (schnorrSignature F G g hg M)
      (FiatShamir.runtime (PC := G) (Ω := F) M) :=
  FiatShamir.perfectlyCorrect _ _ M (schnorrSigma_complete F G g)

/-- Pointcheval-Stern style EUF-CMA reduction for Schnorr signatures.

The bound includes:
* explicit bounds on signing-oracle and random-oracle queries by the adversary;
* an explicit DLog reduction target;
* the standard forking-lemma loss term `eps * (eps / (qH + 1) - 1 / |F|)`.

Because Schnorr has perfect HVZK (`ζ_zk = 0`), the simulation loss vanishes and the
CMA advantage coincides with the NMA advantage. -/
theorem schnorrSignature_euf_cma (g : G) (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M]
    (adv : SignatureAlg.unforgeableAdv (schnorrSignature F G g hg M))
    (qS qH : ℕ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (PC := G) (Ω := F)
      (S' := G × F) (oa := adv.main pk) qS qH) :
    ∃ reduction : DLogAdversary F G,
      let eps := adv.advantage (FiatShamir.runtime (PC := G) (Ω := F) M) -
        ENNReal.ofReal (qS * (0 : ℝ))
      eps * (eps / (qH + 1 : ENNReal) - FiatShamir.challengeSpaceInv F) ≤
        Pr[= true | dlogExp g reduction] := by
  obtain ⟨red, hred⟩ := FiatShamir.euf_cma_bound (schnorrSigma F G g) (dlogGenerable g hg) M
    (schnorrSigma_speciallySound F G g) (schnorrSimTranscript F G g)
    (ζ_zk := 0) le_rfl
    ((SigmaProtocol.perfectHVZK_iff_hvzk_zero _ _).mp (schnorrSigma_hvzk F G g))
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
