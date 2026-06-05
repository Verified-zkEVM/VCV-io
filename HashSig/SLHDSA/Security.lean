/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import HashSig.SLHDSA.Scheme
import HashSig.SLHDSA.WotsChecksum
import VCVio.CryptoFoundations.PRF
import VCVio.CryptoFoundations.TweakableHash
import VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget

/-!
# SLH-DSA Security (EUF-CMA)

The high-level EUF-CMA security statement for SLH-DSA, in the additive-reduction form of the
SPHINCS+ / FIPS 205 analysis: the forgery advantage is bounded by the sum of

- the pseudorandomness advantage against `PRF_msg` (the message randomizer) and `PRF`
  (secret-value derivation),
- the single-function multi-target preimage advantage against `F` (FORS leaves and WOTS+ chains),
- the single-function multi-target target-collision advantage against `H` (the FORS and XMSS
  Merkle layers), and
- an `H_msg` index-collision interleaving loss `slhdsaInterleavingLoss qS qH`.

The combinatorial core of the WOTS+ step (no chain-advancing forgery) is the proved
`SLHDSA.WotsChecksum.wots_fullDigits_incomparable`; the Merkle tree-binding step routes through
`VCVio.CryptoFoundations.MerkleTree.Inductive` extractability; and the multi-target / PRF
surfaces are `VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget` and
`VCVio.CryptoFoundations.PRF`. The functions `F`/`H`/`T_ℓ` of `Primitives` instantiate the
`VCVio.CryptoFoundations.TweakableHash` abstraction against which these notions are stated.

**This is a placeholder statement** (the additive structure mirrors the SPHINCS+ theorem, but
`slhdsaInterleavingLoss` is a stand-in for the precise `H_msg` collision term, and the proof is
deferred — exactly as `LatticeCrypto.MLDSA.Security.euf_cma_security` is currently a placeholder
with a `sorry` proof).

## References

- Bernstein, Hülsing, Kölbl, Niederhagen, Rijneveld, Schwabe, "The SPHINCS+ Signature Framework"
- NIST FIPS 205, §10 (security)
-/


open OracleComp OracleSpec ENNReal

namespace SLHDSA

variable {p : Params} (prims : Primitives p)

/-- Placeholder for the `H_msg` index-collision / interleaving slack in the EUF-CMA bound
(`qS` signing queries, `qH` random-oracle queries), analogous to `MLDSA.cmaToNmaLoss`. The
precise term is the FORS-index collision probability over the digest space; it is left as a
stand-in pending the full proof. -/
noncomputable def slhdsaInterleavingLoss (qS qH : ℕ) : ℝ≥0∞ := (qS * (qS + qH) : ℕ)

open scoped Classical in
/-- **EUF-CMA security of SLH-DSA (placeholder statement).**

For every EUF-CMA adversary against `slhdsaAlg` making at most `qS` signing and `qH`
random-oracle queries, there exist reductions to the message/secret PRFs, multi-target preimage
resistance of `F`, multi-target target-collision resistance of `H`, such that the forgery
advantage is bounded by the sum of their advantages plus the `H_msg` interleaving loss.

The proof composes (1) a CMA→NMA hop replacing the `PRF_msg` randomizer with a random oracle,
(2) WOTS+ one-wayness using the proved incomparability lemma
`WotsChecksum.wots_fullDigits_incomparable` to force a chain preimage (SM-PRE of `F`),
(3) XMSS/hypertree binding via `MerkleTree.Inductive` extractability (SM-TCR of `H`), and
(4) FORS few-time security (SM-PRE of `F` + Merkle extractability). It is deferred (`sorry`),
mirroring the current state of `MLDSA.Security`. -/
theorem slhdsa_euf_cma_security
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
    [SampleableType prims.Y] [DecidableEq prims.Y]
    (prfMsg : PRFScheme prims.SkPrf (prims.Y × List Byte) prims.Y)
    (prfSk : PRFScheme prims.SkSeed Adrs prims.Y)
    (forsPre wotsOw : MultiTarget.PreimageProblem prims.Y prims.Y)
    (forsTcr xmssTcr : MultiTarget.TcrProblem Adrs (prims.Y × prims.Y) prims.Y)
    (qS qH : ℕ) :
    ∀ (adv : SignatureAlg.unforgeableAdv (slhdsaAlg prims)),
    ∃ (advPrfMsg : PRFScheme.PRFAdversary (prims.Y × List Byte) prims.Y)
      (advPrfSk : PRFScheme.PRFAdversary Adrs prims.Y)
      (advForsPre : MultiTarget.PreimageAdversary forsPre)
      (advForsTcr : MultiTarget.TcrAdversary forsTcr)
      (advWotsOw : MultiTarget.PreimageAdversary wotsOw)
      (advXmssTcr : MultiTarget.TcrAdversary xmssTcr),
      adv.advantage ProbCompRuntime.probComp ≤
          ENNReal.ofReal (prfMsg.prfAdvantage advPrfMsg)
        + ENNReal.ofReal (prfSk.prfAdvantage advPrfSk)
        + MultiTarget.preimageAdvantage advForsPre
        + MultiTarget.tcrAdvantage advForsTcr
        + MultiTarget.preimageAdvantage advWotsOw
        + MultiTarget.tcrAdvantage advXmssTcr
        + slhdsaInterleavingLoss qS qH := by
  sorry

end SLHDSA
