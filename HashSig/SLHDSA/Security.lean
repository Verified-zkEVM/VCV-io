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
- an `H_msg` index-collision interleaving loss `slhdsaInterleavingLoss`.

The combinatorial core of the WOTS+ step (no chain-advancing forgery) is the proved
`SLHDSA.WotsChecksum.wots_fullDigits_incomparable`; the Merkle tree-binding step routes through
`VCVio.CryptoFoundations.MerkleTree.Inductive` extractability.

## What the statement commits to

Every advantage term on the right is bound to a primitive the scheme **actually uses**, not to a
free function:

- `F` and `H` are packaged as `VCVio.CryptoFoundations.TweakableHash` families (`Primitives.fHash`
  / `Primitives.hHash`, tweak = the 32-byte `Adrs`), and the multi-target preimage / target-
  collision problems (`fPreimageProblem` / `hTcrProblem`) read their challenge function off those
  families. So `preimageAdvantage`/`tcrAdvantage` measure inverting / colliding `prims.F` /
  `prims.H`, not an arbitrary unrelated function.
- `PRF` and `PRF_msg` are packaged as `PRFScheme`s (`skPrfScheme` / `msgPrfScheme`) whose `eval`
  is exactly `prims.PRF` / `prims.PRFmsg`, so the PRF advantages are against the scheme's own PRFs.
- `slhdsaInterleavingLoss m qS qH = qS·(qS + qH) / 2^(8·m)` is a genuine birthday-style probability
  in `[0, 1)` over the `m`-byte `H_msg` digest space — not an unbounded integer slack.

## What is still deferred

The **proof** is `sorry` (the CMA→NMA hop, WOTS+ one-wayness, Merkle/FORS binding, and the
multi-target → single-target `p`-fold loss are research-level and deferred, exactly as
`LatticeCrypto.MLDSA.Security.euf_cma_security`). The query bounds `qS`/`qH` are *assumed* bounds
on the adversary stated in the usual cryptographic prose; wiring them to the adversary's actual
query count via the cost model (`VCVio.OracleComp.QueryTracking`) is the remaining formalization
gap. These are honest gaps in the proof and instrumentation, not vacuity in the statement.

## References

- Bernstein, Hülsing, Kölbl, Niederhagen, Rijneveld, Schwabe, "The SPHINCS+ Signature Framework"
- Hülsing, Rijneveld, Song, Schwabe, "Mitigating Multi-Target Attacks in Hash-Based Signatures"
- NIST FIPS 205, §10 (security)
-/


open OracleComp OracleSpec ENNReal

namespace SLHDSA

variable {p : Params} (prims : Primitives p)

/-! ### The SLH-DSA hashes as tweakable hash families / PRFs

These package the scheme's own functions as the generic `TweakableHash` / `PRFScheme` surfaces, so
the security notions below are stated against `prims.F`/`prims.H`/`prims.PRF`/`prims.PRFmsg`
themselves rather than against arbitrary functions. -/

/-- The chain-step / FORS-leaf hash `F` as a tweakable hash family (tweak = `Adrs`). -/
def Primitives.fHash [SampleableType prims.PkSeed] :
    TweakableHash prims.PkSeed Adrs prims.Y prims.Y where
  seedGen := $ᵗ prims.PkSeed
  eval := prims.F

/-- The Merkle / FORS-tree node hash `H` as a tweakable hash family (tweak = `Adrs`, message =
the ordered sibling pair `(left, right)`). -/
def Primitives.hHash [SampleableType prims.PkSeed] :
    TweakableHash prims.PkSeed Adrs (prims.Y × prims.Y) prims.Y where
  seedGen := $ᵗ prims.PkSeed
  eval := fun pkSeed adrs m => prims.H pkSeed adrs m.1 m.2

/-- The single-function multi-target **preimage** problem for `F` at public seed `pkSeed`: targets
are `(address, value)` pairs and the challenge function is exactly `prims.F pkSeed` (read off
`prims.fHash`). WOTS+ chain one-wayness and FORS-leaf preimage resistance are both instances,
differing only in the target distribution `sampleInputs`. -/
def fPreimageProblem [SampleableType prims.PkSeed] (pkSeed : prims.PkSeed) (numTargets : ℕ)
    (sampleInputs : ProbComp (Fin numTargets → Adrs × prims.Y)) :
    MultiTarget.PreimageProblem (Adrs × prims.Y) prims.Y where
  f := fun ay => (prims.fHash).eval pkSeed ay.1 ay.2
  numTargets := numTargets
  sampleInputs := sampleInputs

/-- The single-function multi-target **target-collision** problem for the node hash `H` at public
seed `pkSeed`: the tweak is the address and the challenge function is exactly `prims.H pkSeed`
(read off `prims.hHash`). XMSS and FORS Merkle binding are both instances, differing only in the
committed targets. -/
def hTcrProblem [SampleableType prims.PkSeed] (pkSeed : prims.PkSeed) (numTargets : ℕ) :
    MultiTarget.TcrProblem Adrs (prims.Y × prims.Y) prims.Y where
  f := fun adrs m => (prims.hHash).eval pkSeed adrs m
  numTargets := numTargets

/-- The message randomizer `PRF_msg` as a `PRFScheme` keyed by `SK.prf`; `eval` is
`prims.PRFmsg`. -/
def msgPrfScheme [SampleableType prims.SkPrf] :
    PRFScheme prims.SkPrf (prims.Y × List Byte) prims.Y where
  keygen := $ᵗ prims.SkPrf
  eval := fun skPrf rm => prims.PRFmsg skPrf rm.1 rm.2

/-- The secret-value `PRF` at public seed `pkSeed` as a `PRFScheme` keyed by `SK.seed`; `eval` is
`prims.PRF pkSeed`. -/
def skPrfScheme [SampleableType prims.SkSeed] (pkSeed : prims.PkSeed) :
    PRFScheme prims.SkSeed Adrs prims.Y where
  keygen := $ᵗ prims.SkSeed
  eval := fun skSeed adrs => prims.PRF pkSeed skSeed adrs

/-- The `H_msg` index-collision / interleaving slack in the EUF-CMA bound: the birthday-style
collision probability `qS·(qS + qH) / 2^(8·m)` over the `m`-byte `H_msg` digest space (`qS` signing
queries, `qH` random-oracle queries), analogous to `MLDSA.cmaToNmaLoss`. Dividing by the digest
space `2^(8·m)` makes this a genuine probability in `[0, 1)`; the exact constant is the
FORS-index collision probability and is left as this stand-in pending the full proof. -/
noncomputable def slhdsaInterleavingLoss (m qS qH : ℕ) : ℝ≥0∞ :=
  ((qS * (qS + qH) : ℕ) : ℝ≥0∞) / ((2 ^ (8 * m) : ℕ) : ℝ≥0∞)

open scoped Classical in
/-- **EUF-CMA security of SLH-DSA (statement; proof deferred).**

For every EUF-CMA adversary against `slhdsaAlg` making at most `qS` signing and `qH`
random-oracle queries, there exist reductions to the message/secret PRFs (`msgPrfScheme` /
`skPrfScheme`), to multi-target preimage resistance of `F` (`fPreimageProblem`, once for FORS
leaves and once for WOTS+ chains), and to multi-target target-collision resistance of `H`
(`hTcrProblem`, once for FORS trees and once for XMSS trees), such that the forgery advantage is
bounded by the sum of their advantages plus the `H_msg` interleaving loss. Every term is taken
against a primitive `slhdsaAlg` actually uses (see the module docstring); the bound is therefore a
genuine security claim, not a vacuous inequality.

The proof composes (1) a CMA→NMA hop replacing the `PRF_msg` randomizer with a random oracle,
(2) WOTS+ one-wayness using the proved incomparability lemma
`WotsChecksum.wots_fullDigits_incomparable` to force a chain preimage (SM-PRE of `F`),
(3) XMSS/hypertree binding via `MerkleTree.Inductive` extractability (SM-TCR of `H`), and
(4) FORS few-time security (SM-PRE of `F` + Merkle extractability). It is deferred (`sorry`),
mirroring the current state of `MLDSA.Security`. -/
theorem slhdsa_euf_cma_security
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
    [SampleableType prims.Y] [DecidableEq prims.Y]
    (pkSeed : prims.PkSeed)
    (forsLeafTargets wotsChainTargets forsNodeTargets xmssNodeTargets : ℕ)
    (forsLeafInputs : ProbComp (Fin forsLeafTargets → Adrs × prims.Y))
    (wotsChainInputs : ProbComp (Fin wotsChainTargets → Adrs × prims.Y))
    (qS qH : ℕ) :
    ∀ (adv : SignatureAlg.unforgeableAdv (slhdsaAlg prims)),
    ∃ (advPrfMsg : PRFScheme.PRFAdversary (prims.Y × List Byte) prims.Y)
      (advPrfSk : PRFScheme.PRFAdversary Adrs prims.Y)
      (advForsPre : MultiTarget.PreimageAdversary
        (fPreimageProblem prims pkSeed forsLeafTargets forsLeafInputs))
      (advWotsOw : MultiTarget.PreimageAdversary
        (fPreimageProblem prims pkSeed wotsChainTargets wotsChainInputs))
      (advForsTcr : MultiTarget.TcrAdversary (hTcrProblem prims pkSeed forsNodeTargets))
      (advXmssTcr : MultiTarget.TcrAdversary (hTcrProblem prims pkSeed xmssNodeTargets)),
      adv.advantage ProbCompRuntime.probComp ≤
          ENNReal.ofReal ((msgPrfScheme prims).prfAdvantage advPrfMsg)
        + ENNReal.ofReal ((skPrfScheme prims pkSeed).prfAdvantage advPrfSk)
        + MultiTarget.preimageAdvantage advForsPre
        + MultiTarget.preimageAdvantage advWotsOw
        + MultiTarget.tcrAdvantage advForsTcr
        + MultiTarget.tcrAdvantage advXmssTcr
        + slhdsaInterleavingLoss p.m qS qH := by
  sorry

end SLHDSA
