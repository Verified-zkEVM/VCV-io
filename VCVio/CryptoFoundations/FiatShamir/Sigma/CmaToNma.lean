/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.Sigma
import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import VCVio.CryptoFoundations.FiatShamir.QueryBounds

/-!
# CMA-to-NMA reduction for Fiat-Shamir on Σ-protocols

This file packages the CMA-to-NMA half of the Pointcheval-Stern / Bellare-Neven
EUF-CMA security reduction for Fiat-Shamir-on-Σ-protocols as a single,
stand-alone theorem `hashAndSign_cma_to_nma_bound`.

`Sigma/Security.lean`'s `euf_cma_to_nma` is now a thin specialization of this
lemma: pass the same Σ-protocol `σ`, the HVZK simulator `simTranscript`, the
quantitative HVZK / commit-predictability / verify-predictability bounds, and
the CMA adversary; receive an NMA adversary and the bound

  `adv.advantage ≤ Fork.advantage σ hr M nmaAdv qH
                    + qS · ζ_zk
                    + qS · (qS + qH) · β
                    + δ_verify`.

This bound is **tight** in the joint-coupling sense: a single per-step ε for
HVZK and a single union-bounded programming-collision event, instead of the
chain-decomposed bound in older formulations.

## Reuse beyond Σ-protocols

The proof structure is generic in the underlying Σ-protocol (and, with mild
adjustments, in any hash-and-sign signature scheme): the CMA-to-NMA cost is
universally `qS · ζ_zk + qS · (qS + qH) · β + δ_v` for any HVZK simulator
satisfying the three quantitative properties. Falcon's GPV instantiation
(`Falcon/Scheme.lean`) and ML-DSA's signing layer (`MLDSA/Signature.lean`)
both target this lemma's shape; this file is the canonical home for the
generic reduction.

Currently, the lemma is `sorry`-bearing pending the joint-coupling proof body
(plan: see `.ignore/fs-cma-rewrite-plan.md`, Day 4-5). The signature is
locked, so call sites can already specialize against it.

## NMA reduction structure

The NMA adversary `nmaAdv` constructed by this lemma is the standard
"simulated CMA": run the CMA adversary's main computation, replacing the real
signing oracle with the HVZK simulator and programming the random oracle
to be consistent with the simulated signatures. The final
`(message, signature)` output is repackaged with the live NMA-side cache.

## Bound interpretation

* `Fork.advantage σ hr M nmaAdv qH`: the forking-lemma advantage in the NMA
  game (paid by `euf_nma_bound`).
* `qS · ζ_zk`: per-signing-query HVZK loss. **Tight**: the chain-decomposition
  bound has `qS · (qS + qH + 1) · ζ_zk` here, but the joint coupling pays only
  the per-step `ζ_zk` `qS` times.
* `qS · (qS + qH) · β`: programming-collision bad event probability. **Tight**:
  joint coupling counts the bad event once (sim-side), not on both sides.
* `δ_verify`: scheme-specific bound on the probability that an unprogrammed RO
  point happens to verify (`SigmaProtocol.verifyChallengePredictability`).

The looser per-side accounting in older proofs corresponds to applying this
lemma twice in sequence and adding the bounds; the savings versus that play
are exactly `qS · (qS + qH) · ζ_zk + qS · (qS + qH) · β`.
-/

universe u v

open OracleComp OracleSpec

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

/-- **Hash-and-sign CMA-to-NMA reduction (joint-coupling form).**

Given a Σ-protocol `σ` with an HVZK simulator `simTranscript` satisfying:

* `HVZK simTranscript ζ_zk`: per-call statistical distance ≤ `ζ_zk` between
  real and simulated transcripts;
* `simChalUniformGivenCommit simTranscript`: conditional uniformity of the
  challenge given the commitment under the simulator (used to discharge the
  programming step);
* `simCommitPredictability simTranscript β`: per-call commit-marginal
  unpredictability ≤ `β` (used to bound the programming-collision event);
* `verifyChallengePredictability δ_v`: per-call upper bound `δ_v` on the
  probability that an unprogrammed RO answer happens to satisfy `verify`.

For any CMA adversary `adv` against `FiatShamir σ hr M` making at most `qS`
sign-oracle queries and `qH` random-oracle queries, there exists a managed-RO
NMA adversary `nmaAdv` with the same RO-query budget and CMA-advantage upper
bound

  `adv.advantage (runtime M)
      ≤ Fork.advantage σ hr M nmaAdv qH
        + ofReal (qS · ζ_zk)
        + qS · (qS + qH) · β
        + δ_verify`.

The `nmaAdv` is the standard "simulated CMA": run `adv.main pk`, replace the
signing oracle with the HVZK simulator, program the random oracle on each
simulated signature.

**Status (2026-04 rewrite):** statement locked, body is `sorry` pending the
joint-coupling proof using
`OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_qSeps_plus_probEvent_output_bad`
and `OracleComp.ProgramLogic.Relational.programming_collision_bound_qP_qH_β`. -/
theorem hashAndSign_cma_to_nma_bound
    [DecidableEq M] [DecidableEq Commit]
    [Fintype Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simTranscript ζ_zk)
    (hChalU : σ.simChalUniformGivenCommit simTranscript)
    (β : ENNReal)
    (hCommit : σ.simCommitPredictability simTranscript β)
    (δ_verify : ENNReal)
    (hVerify : σ.verifyChallengePredictability δ_verify)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ nmaAdv : SignatureAlg.managedRoNmaAdv
        (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M),
      (∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := nmaAdv.main pk) qH) ∧
      adv.advantage (runtime M) ≤
        Fork.advantage σ hr M nmaAdv qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * (qS + qH) * β +
          δ_verify := by
  sorry

end FiatShamir
