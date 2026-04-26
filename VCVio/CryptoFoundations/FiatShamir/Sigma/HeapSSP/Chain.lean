/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FiatShamir.Sigma.HeapSSP.Hop5

/-!
# HeapSSP chain: top-level EUF-CMA-to-Fork bound

Endpoint of the HeapSSP-style Fiat-Shamir EUF-CMA proof. The Hop5
managed-RO bridge lives in `HeapSSP.Hop5`; this file assembles
H1+H2+H3+H4+H5 as the book-level reduction chain.
-/

universe u

open ENNReal OracleSpec OracleComp ProbComp VCVio.HeapSSP
  OracleComp.ProgramLogic.Relational

namespace FiatShamir.HeapSSP

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable [DecidableEq M] [DecidableEq Commit]
  [SampleableType Chal] [Finite Chal] [Inhabited Chal]

/-! ### Top-level chain: H1 + H2 + H3 + H4 + H5 -/

omit [SampleableType Stmt] [SampleableType Wit] in
/-- **Top-level HeapSSP chain** — tight EUF-CMA-to-Fork bound.

HeapSSP-native counterpart of `FiatShamir.euf_cma_to_nma`
(see `Sigma/Security.lean`). The chain is:

  `H1` (drop-fresh)                     +0
    ≤ `H2` (`unforgeableExpNoFresh = cmaReal.runProb signedAdv`)   +0
    ≤ `H3` (identical-until-bad, HVZK + cache-collision)
          +`qS · ζ_zk + qS · (qS + qH) · β`
    = `H4` (`cmaSim = cmaToNma.link nma`)           +0
    ≤ `H5` (fork + fresh-challenge)
          +`Fork.advantage σ hr M (nmaAdvFromCma …) qH + δ_verify`

Summing the per-hop slacks delivers the tight bound:

  `adv.advantage (runtime M)  ≤
    Fork.advantage σ hr M (nmaAdvFromCma …) qH
      + ENNReal.ofReal (qS · ζ_zk)
      + qS · (qS + qH) · β
      + δ_verify`.

The final Fiat-Shamir verification query is factored as a no-sign-cost
suffix (`verifyFreshComp`) after candidate production. It still executes in
the Boolean game consumed by H5, but it does not inflate the H3 cache-growth
budget for signing-query replacements.

Downstream, composing with `FiatShamir.euf_nma_bound` (the forking
lemma with special soundness) yields `FiatShamir.euf_cma_bound`. -/
theorem cma_advantage_le_fork_bound
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simT ζ_zk)
    (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simT β)
    (δ_verify : ENNReal)
    (hVerifyGuess : SigmaProtocol.verifyChallengePredictability σ δ_verify)
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
          (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β +
          δ_verify := by
  refine ⟨nmaAdvFromCma σ hr M adv simT,
    nmaAdvFromCma_nmaHashQueryBound σ hr M adv simT qS qH hQ, ?_⟩
  set A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool :=
    signedFreshAdv σ hr M adv with hA_def
  set Apre : OracleComp (cmaSpec M Commit Chal Resp Stmt)
      ((Stmt × (M × (Commit × Resp))) × List M) :=
    signedCandidateAdv σ hr M adv with hApre_def
  have hA_bound : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) A qS (qH + 1) := by
    rw [hA_def]
    exact signedFreshAdv_cmaSignHashQueryBound (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv qS qH hQ
  have hApre_bound : cmaSignHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) Apre qS qH := by
    rw [hApre_def]
    exact signedCandidateAdv_cmaSignHashQueryBound (σ := σ) (hr := hr) (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) adv qS qH hQ
  have hQB : OracleComp.IsQueryBound A qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b) :=
    cmaSignHashQueryBound_to_costly (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (A := A) hA_bound
  have hQBpre : OracleComp.IsQueryBound Apre qS
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b) :=
    cmaSignHashQueryBound_to_costly (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (A := Apre) hApre_bound
  have hQBHpre : OracleComp.IsQueryBound Apre qH
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then 0 < b else True)
      (fun t b => if IsHashQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) t then b - 1 else b) :=
    cmaSignHashQueryBound_to_hash (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (A := Apre) hApre_bound
  have hCommit : σ.simCommitPredictability simT β := hPredSim
  have hζ_zk_lt : ENNReal.ofReal ζ_zk < ∞ := ENNReal.ofReal_lt_top
  have hHVZK' : σ.HVZK simT (ENNReal.ofReal ζ_zk).toReal := by
    rwa [ENNReal.toReal_ofReal hζ_zk]
  have hH3_abs :
      ENNReal.ofReal
          (((cmaReal M Commit Chal σ hr).runProb A).boolDistAdvantage
            ((cmaSim M Commit Chal hr simT).runProb A))
        ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β := by
    set φ := cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit) with hφ
    set G := Package.implConjugate (cmaReal M Commit Chal σ hr).impl φ with hG
    have h_cost_candidate :
        expectedSCost G
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) Apre qS
            (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
          ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
            + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β := by
      simpa [hG, hφ] using
        cmaSignEpsCore_expectedSCost_le M Commit Chal σ hr (ENNReal.ofReal ζ_zk) β
          Apre qS qH hQBpre hQBHpre
    have h_cost_bind :
        expectedSCost G
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) A qS
            (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
          =
        expectedSCost G
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) Apre qS
            (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false) := by
      rw [hA_def, hApre_def, signedFreshAdv]
      exact expectedSCost_bind_eq_of_right_zero G
        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β)
        (signedCandidateAdv σ hr M adv)
        (verifyFreshComp (σ := σ) (hr := hr) (M := M)
          (Commit := Commit) (Chal := Chal) (Resp := Resp))
        (fun x q p => verifyFreshComp_expectedSCost_eq_zero (σ := σ) (hr := hr)
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
          (G := G) (ε := cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) x q p)
        qS (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
    have h_cost_full :
        expectedSCost
            (Package.implConjugate (cmaReal M Commit Chal σ hr).impl
              (cmaHeapStateEquiv M Commit Chal (Stmt := Stmt) (Wit := Wit)))
            (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
              (Resp := Resp) (Stmt := Stmt))
            (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) A qS
            (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
          ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
            + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β := by
      have hc :
          expectedSCost G
              (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
                (Resp := Resp) (Stmt := Stmt))
              (cmaSignEpsCore (ENNReal.ofReal ζ_zk) β) A qS
              (cmaInitData M Commit Chal (Stmt := Stmt) (Wit := Wit), false)
            ≤ (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
              + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β := by
        rw [h_cost_bind]
        exact h_cost_candidate
      simpa [hG, hφ] using hc
    simpa [VCVio.HeapSSP.Package.advantage] using
      cmaReal_cmaSim_advantage_le_H3_bound_of_expectedSCost M Commit Chal σ hr simT
        (ENNReal.ofReal ζ_zk) β hζ_zk_lt hHVZK' hCommit A qS
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β)
        hQB h_cost_full
  have hH3_prob : Pr[= true | (cmaReal M Commit Chal σ hr).runProb A] ≤
      Pr[= true | (cmaSim M Commit Chal hr simT).runProb A] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
    le_trans
      (ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
        ((cmaReal M Commit Chal σ hr).runProb A)
        ((cmaSim M Commit Chal hr simT).runProb A))
      (add_le_add le_rfl hH3_abs)
  have hH4 := cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma M Commit Chal hr simT
    (A := A)
  have hH4_pr : Pr[= true | (cmaSim M Commit Chal hr simT).runProb A] =
      Pr[= true |
        (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
          ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A)] :=
    probOutput_congr rfl (congrArg evalDist hH4)
  have hH5' :
      Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A)] ≤
        Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH + δ_verify := by
    rw [hA_def]
    exact H5_fork_bound σ hr M adv simT qS qH hQ
      δ_verify hVerifyGuess
  have hH1H2 : adv.advantage (FiatShamir.runtime M) ≤
      Pr[= true | (cmaReal M Commit Chal σ hr).runProb A] := by
    rw [hA_def]
    exact cma_advantage_le_runProb_cmaRealFresh (M := M) σ hr adv
  calc adv.advantage (FiatShamir.runtime M)
      ≤ Pr[= true | (cmaReal M Commit Chal σ hr).runProb A] := hH1H2
    _ ≤ Pr[= true | (cmaSim M Commit Chal hr simT).runProb A] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) := hH3_prob
    _ = Pr[= true |
          (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            ((cmaToNma (Stmt := Stmt) M Commit Chal simT).shiftLeft A)] +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) := by
        rw [hH4_pr]
    _ ≤ (Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH + δ_verify) +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk
          + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
        add_le_add hH5' le_rfl
    _ = Fork.advantage σ hr M (nmaAdvFromCma σ hr M adv simT) qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β +
          δ_verify := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (qS : ℝ)),
            show ENNReal.ofReal (qS : ℝ) = (qS : ENNReal) from
              ENNReal.ofReal_natCast _]
        ring

end FiatShamir.HeapSSP
