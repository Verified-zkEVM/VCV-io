/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLKEM.KEM
import LatticeCrypto.HardnessAssumptions.LearningWithErrors
import VCVio.CryptoFoundations.FujisakiOkamoto.Composed
import VCVio.CryptoFoundations.AsymmEncAlg.IND_CPA.Oracle

/-!
# ML-KEM Security

This file states the high-level security theorems for ML-KEM, following FIPS 203 Section 3.2
and the modular Fujisaki-Okamoto analysis from HHK17 (TCC 2017, ePrint 2017/604).

The security of ML-KEM reduces to three ingredients:

1. **MLWE hardness** → K-PKE is IND-CPA secure (Section 2)
2. **K-PKE δ-correctness** → decapsulation failure probability is negligible (Section 1)
3. **PRF security of J** → implicit rejection is indistinguishable from random (Section 3)

The proof follows the structure:
1. K-PKE is IND-CPA secure assuming the decisional MLWE problem is hard.
2. The Fujisaki-Okamoto transform (T-transform + U-transform with implicit rejection)
   converts IND-CPA security of K-PKE into IND-CCA2 security of ML-KEM.

The composed FO bound (HHK17 Corollary) gives:

  `Adv^{IND-CCA}_{ML-KEM}(A) ≤ 2·Adv^{IND-CPA}_{K-PKE}(B₁) + 2·Adv^{IND-CPA}_{K-PKE}(B₂)
      + Adv^{PRF}_J(C) + (2qHK+3)·δ + 2·(2qHK+2)·ε_msg`

where `δ` is the K-PKE correctness error, `ε_msg = 1/|M| = 2⁻²⁵⁶` is the message entropy,
and `qHK` bounds the adversary's combined hash/key-derivation queries.

Substituting the MLWE reduction for the IND-CPA terms yields the final bound in terms of
MLWE + PRF + correctness parameters.

## References

- NIST FIPS 203, Section 3.2 (security properties)
- HHK17: A Modular Analysis of the Fujisaki-Okamoto Transformation (TCC 2017)
- CRYSTALS-KYBER (TCHES 2018), Section 3 (security analysis)
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal AsymmEncAlg

namespace MLKEM

variable (params : Params) (ring : NTTRingOps) (encoding : Encoding params)
  (prims : Primitives params encoding)

/-! ### K-PKE δ-Correctness -/

section Correctness

variable [SampleableType Coins]

/-- **K-PKE δ-correctness.**

For honestly generated keys, decryption recovers the encrypted plaintext with probability
at least `1 - δ`. The failure probability `δ` depends on the noise distribution parameters
(η₁, η₂) and compression parameters (d_u, d_v); concrete values are given in FIPS 203 Table 1:

- ML-KEM-512:  δ ≈ 2⁻¹³⁸·⁸
- ML-KEM-768:  δ ≈ 2⁻¹⁶⁴·⁸
- ML-KEM-1024: δ ≈ 2⁻¹⁷⁴·⁸ -/
theorem kpke_deltaCorrect (δ : ℝ≥0∞) :
    (KPKE.asExplicitCoins params ring encoding prims).deltaCorrect δ := by
  sorry

end Correctness

/-! ### K-PKE IND-CPA from MLWE -/

section KPKE_IND_CPA

variable [DecidableEq Message] [SampleableType Coins]

/-- **K-PKE IND-CPA security from MLWE (FIPS 203, CRYSTALS-KYBER Section 3).**

For any IND-CPA adversary `A` against K-PKE, there exists a decisional MLWE adversary `B`
such that:

  `Adv^{IND-CPA}_{K-PKE}(A) ≤ Adv^{MLWE}_{k,η₁}(B)`

The reduction works by embedding the MLWE challenge `(A, t)` as the K-PKE public key:
- In the real game, `t = A·s + e` (honest key generation)
- In the MLWE game, `t` is either `A·s + e` (real) or uniform (random)

When `t` is uniform, the ciphertext carries no information about which of the two challenge
messages was encrypted, so the adversary's advantage is 0. The gap between the two cases
is exactly the MLWE advantage.

The MLWE problem instance is parameterized abstractly; the concrete instantiation uses
`k×k` matrices over `T_q` with secrets and errors sampled from `CBD(η₁)` in the NTT domain. -/
theorem kpke_ind_cpa_security
    (mlwe : LearningWithErrors.Problem
      (TqMatrix params.k params.k) (TqVec params.k) (TqVec params.k)) :
    ∀ (cpaAdv : (KPKE.asExplicitCoins params ring encoding prims).toAsymmEncAlg.IND_CPA_adversary),
    ∃ (mlweAdv : LearningWithErrors.Adversary mlwe),
      (IND_CPA_advantage cpaAdv).toReal ≤
        |LearningWithErrors.advantage mlwe mlweAdv| := by
  sorry

end KPKE_IND_CPA

/-! ### ML-KEM IND-CCA Security -/

section IND_CCA

variable [DecidableEq Message] [DecidableEq (KPKE.Ciphertext params encoding)]
  [SampleableType Message] [SampleableType Coins] [SampleableType SharedSecret]

/-- The PRF scheme modeling the implicit-rejection function `J(z ‖ c)` from FIPS 203.

The key space is `Seed32` (the fallback seed `z` stored in the decapsulation key), the domain
is the ciphertext type, and the range is `SharedSecret`. -/
def prfJ : PRFScheme Seed32 (KPKE.Ciphertext params encoding) SharedSecret where
  keygen := $ᵗ Seed32
  eval z c := prims.jReject z c.uEncoded c.vEncoded

/-- The Fujisaki-Okamoto-constructed KEM scheme derived from K-PKE with implicit rejection via J.

This is ML-KEM viewed through the HHK17 framework: encryption coins and shared keys are derived
from random oracles `H₁ : M →ₒ R` (coins) and `H₂ : M →ₒ K` (key derivation), with the key
derivation input being just the message (`kdInput m c = m`). Implicit rejection uses the PRF `J`.

In the concrete ML-KEM instantiation, both `H₁` and `H₂` are derived from a single hash function
`G(m ‖ H(ek))`, which can be modeled via `FujisakiOkamoto.singleRO`. The two-RO formulation is
used here because the composed FO security bound (`FujisakiOkamoto.IND_CCA_bound`) is stated for
this variant. -/
abbrev foKEMScheme :=
  FujisakiOkamoto
    (KPKE.asExplicitCoins params ring encoding prims)
    (fun (m : Message) (_c : KPKE.Ciphertext params encoding) => m)
    (FujisakiOkamoto.implicitRejection (prfJ params encoding prims))

/-- **Main ML-KEM IND-CCA Security Theorem (FIPS 203 + HHK17).**

For any IND-CCA adversary `A` against ML-KEM making at most `qHK` combined
hash/key-derivation queries, there exist:
- Two IND-CPA adversaries `B₁, B₂` against K-PKE
- A PRF adversary `C` against J
- An MLWE adversary `D`

such that:

  `Adv^{IND-CCA}_{ML-KEM}(A) ≤ 2·Adv^{MLWE}(D) + 2·Adv^{MLWE}(D')
      + Adv^{PRF}_J(C) + (2qHK+3)·δ + 2·(2qHK+2)·ε_msg`

where `δ` is the K-PKE correctness error and `ε_msg = 2⁻²⁵⁶`.

The proof composes three reductions:
1. **FO transform** (HHK17 Corollary): IND-CCA of the FO-constructed KEM reduces to
   IND-CPA of K-PKE + PRF security of J + correctness + message entropy.
2. **IND-CPA → MLWE**: Each IND-CPA term reduces to an MLWE advantage.
3. **Concrete parameters**: `ε_msg = 1/|Message| = 2⁻²⁵⁶` and `δ` from FIPS 203 Table 1. -/
theorem ind_cca_security
    (mlwe : LearningWithErrors.Problem
      (TqMatrix params.k params.k) (TqVec params.k) (TqVec params.k))
    (correctnessBound epsMsg : ℝ) (qHK : ℕ) :
    ∀ (adv : (foKEMScheme params ring encoding prims).IND_CCA_Adversary),
    ∃ (mlweAdv₁ mlweAdv₂ : LearningWithErrors.Adversary mlwe)
      (prfAdv : PRFScheme.PRFAdversary (KPKE.Ciphertext params encoding) SharedSecret),
      (foKEMScheme params ring encoding prims).IND_CCA_Advantage adv ≤
        2 * |LearningWithErrors.advantage mlwe mlweAdv₁| +
        2 * |LearningWithErrors.advantage mlwe mlweAdv₂| +
        PRFScheme.prfAdvantage (prfJ params encoding prims) prfAdv +
        ((2 * qHK + 3 : ℕ) : ℝ) * correctnessBound +
        2 * ((2 * qHK + 2 : ℕ) : ℝ) * epsMsg := by
  sorry

end IND_CCA

end MLKEM
