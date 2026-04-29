/-
Copyright (c) 2024 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import VCVio.CryptoFoundations.FiatShamir.Sigma.Reductions

/-!
# EUF-CMA security of the Fiat-Shamir Σ-protocol transform

End-to-end security reduction, packaged as three theorems:

- `euf_cma_to_nma`: CMA-to-NMA via HVZK simulation. The reduction wraps the
  source CMA adversary so the final verification challenge is part of the
  forkable transcript, absorbing the signing-query loss into
  `qS · ζ_zk + qS · (qS + qH) · β`. The wrapped adversary issues `qH + 1`
  random-oracle queries (source's `qH` plus the appended verifier-point query),
  but the bound is stated with `Fork.advantage` at fork slot parameter `qH`:
  the framework's `Fin (qH + 1)` indexing in `Fork.forkPoint qH` provides
  exactly the right number of slots for the wrapped adversary.
- `euf_nma_bound`: NMA-to-extraction via `Fork.replayForkingBound` and special
  soundness, producing a reduction to `hardRelationExp`.
- `euf_cma_bound`: the combined bound, instantiating `euf_cma_to_nma` into
  `euf_nma_bound`. The replay-forking denominator is `qH + 1`.
-/

universe u v

open OracleComp OracleSpec

open scoped OracleSpec.PrimitiveQuery

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

omit [SampleableType Stmt] [SampleableType Wit] in
/-- **CMA-to-NMA reduction via HVZK simulation and managed random-oracle programming.**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists a managed-RO NMA adversary `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{fork-NMA}_{qH}(B)
      + ofReal (qS · ζ_zk) + qS · (qS + qH) · β`

where `β` is the simulator's commit-predictability bound and the right-hand
fork advantage is `Fork.advantage σ hr M B qH` at slot parameter `qH`. The
wrapped adversary `B` issues `qH + 1` random-oracle queries (the source's `qH`
plus an appended verifier-point query); the framework's `Fin (qH + 1)`
indexing in `Fork.forkPoint qH` provides the matching `qH + 1` forkable slots.
This step is independent of special soundness and the forking lemma. -/
theorem euf_cma_to_nma
    [DecidableEq M] [DecidableEq Commit]
    [Finite Chal] [Inhabited Chal] [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simTranscript ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simTranscript β)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ nmaAdv : SignatureAlg.managedRoNmaAdv
        (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M),
      adv.advantage (runtime M) ≤
        Fork.advantage σ hr M nmaAdv qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * (qS + qH) * β :=
  cma_to_nma_advantage_bound (σ := σ) (hr := hr) (M := M)
    simTranscript ζ_zk hζ_zk hHVZK β hPredSim adv qS qH hQ

omit [SampleableType Stmt] in
/-- **NMA-to-extraction via the forking lemma and special soundness.**

For any managed-RO NMA adversary `B` and any fork slot parameter `qH`, there
exists a witness-extraction reduction such that:

  `Adv^{fork-NMA}_{qH}(B) · (Adv^{fork-NMA}_{qH}(B) / (qH + 1) - 1/|Ω|)
      ≤ Pr[extraction succeeds]`

Here `Adv^{fork-NMA}_{qH}(B)` is `Fork.advantage`: it counts exactly the
managed-RO executions whose forgery already verifies from challenge values
present in the adversary's managed cache or in the live hash-query log recorded
by `Fork.runTrace`. The parameter `qH` is the fork slot parameter (the size of
the `Fin (qH + 1)` candidate-position set), not a separate query bound on `B`. -/
theorem euf_nma_bound
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) :
    ∃ reduction : Stmt → ProbComp Wit,
      (Fork.advantage σ hr M nmaAdv qH *
          (Fork.advantage σ hr M nmaAdv qH / (qH + 1 : ENNReal) -
            challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] :=
  nma_to_hard_relation_bound (σ := σ) (hr := hr) (M := M) hss hss_nf nmaAdv qH

omit [SampleableType Stmt] in
/-- **Combined EUF-CMA bound (Pointcheval-Stern with quantitative HVZK, β-parametric).**

Composes `euf_cma_to_nma` and `euf_nma_bound`:

1. Replace the signing oracle with the HVZK simulator and route the final
   verification challenge through the live RO via the verify-wrapped NMA
   adversary. This loses `qS·ζ_zk + qS·(qS+qH)·β`. The wrapped adversary
   issues `qH + 1` random-oracle queries; the bound is taken at fork slot
   parameter `qH`, which exposes exactly `qH + 1` slots in
   `Fork.forkPoint qH : Option (Fin (qH + 1))`.
2. Apply the forking lemma to the resulting forkable managed-RO NMA experiment.
   The replay-fork denominator is `qH + 1`.

The combined bound is:

  `(ε - qS·ζ_zk - qS·(qS+qH)·β) ·
      ((ε - qS·ζ_zk - qS·(qS+qH)·β) / (qH + 1) - 1/|Ω|)
    ≤ Pr[extraction succeeds]`

where `ε = Adv^{EUF-CMA}(A)`. The ENNReal subtraction truncates at zero, so the
bound is trivially satisfied when the simulation loss exceeds the advantage. -/
theorem euf_cma_bound
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hhvzk : σ.HVZK simTranscript ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simTranscript β)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      let eps := adv.advantage (runtime M) -
        (ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * (qS + qH) * β)
      (eps * (eps / (qH + 1 : ENNReal) - challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  haveI : DecidableEq M := Classical.decEq M
  haveI : DecidableEq Commit := Classical.decEq Commit
  obtain ⟨nmaAdv, hAdv⟩ := euf_cma_to_nma σ hr M simTranscript
    ζ_zk hζ_zk hhvzk β hPredSim adv qS qH hQ
  obtain ⟨reduction, hRed⟩ := euf_nma_bound σ hr M hss hss_nf nmaAdv qH
  refine ⟨reduction, le_trans ?_ hRed⟩
  have hle : adv.advantage (runtime M) -
      (ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
        (qS : ENNReal) * (qS + qH) * β) ≤
      Fork.advantage σ hr M nmaAdv qH :=
    tsub_le_iff_right.mpr (by simpa [add_assoc] using hAdv)
  exact mul_le_mul' hle (tsub_le_tsub_right (ENNReal.div_le_div_right hle _) _)

end FiatShamir
