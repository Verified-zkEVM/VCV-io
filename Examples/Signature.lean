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

set_option autoImplicit false

open OracleComp OracleSpec DiffieHellman

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (G : Type) [AddCommGroup G] [Module F G] [Fintype G] [SampleableType G] [DecidableEq G]

/-- Schnorr signature scheme: Fiat-Shamir applied to the Schnorr Σ-protocol
with the discrete-log generable relation. -/
def schnorrSignature (g : G) (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M] :=
  FiatShamir (schnorrSigma F G g) (dlogGenerable g hg) M

omit [DecidableEq F] in
/-- Completeness of the Schnorr signature follows from completeness of the
underlying Schnorr Σ-protocol via the generic Fiat-Shamir completeness theorem. -/
theorem schnorrSignature_complete (g : G) (hg : Function.Bijective (· • g : F → G))
    (M : Type) [DecidableEq M] :
    SignatureAlg.PerfectlyComplete (schnorrSignature F G g hg M) :=
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
    (hQ : ∀ pk, FiatShamir.hashQueryBound (M := M) (PC := G) (Ω := F)
      (oa := adv.main pk) qBound) :
    ∃ reduction : DLogAdversary F G,
      adv.advantage *
          (adv.advantage / (qBound + 1 : ENNReal) - FiatShamir.challengeSpaceInv F) ≤
        Pr[= true | dlogExp g reduction] := by
  sorry
