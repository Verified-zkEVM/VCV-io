/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort
import VCVio.CryptoFoundations.FiatShamir.QueryBounds

/-!
# EUF-CMA security of Fiat-Shamir with aborts

Statistical CMA-to-NMA reduction for the Fiat-Shamir-with-aborts transform,
matching Theorem 3 of Barbosa et al. (CRYPTO 2023). Instantiates
`FiatShamir.signHashQueryBound` at the with-aborts signature type and exposes
`cmaToNmaLoss` plus `euf_cma_bound` / `euf_cma_bound_perfectHVZK`.

The scheme-specific NMA-to-hard-problem reduction lives with each concrete
scheme (e.g. `MLDSA.nma_security`).
-/

universe u v

open OracleComp OracleSpec
open scoped BigOperators

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section EUF_CMA

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

/-- The exact classical ROM statistical loss from the Fiat-Shamir-with-aborts
CMA-to-NMA reduction (Theorem 3, CRYPTO 2023), parameterized by the HVZK simulator
error `ζ_zk`.

The paper proves

`Adv_EUF-CMA(A) ≤ Adv_EUF-NMA(B)
  + 2·qS·(qH+1)·ε/(1-p)
  + qS·ε·(qS+1)/(2·(1-p)^2)
  + qS·ζ_zk
  + δ`

where:
- `qS`: number of signing-oracle queries
- `qH`: number of adversarial random-oracle queries
- `ε`: commitment-guessing bound
- `p`: effective abort probability
- `ζ_zk`: total-variation error of the HVZK simulator for one signing transcript
- `δ`: regularity failure probability

The `qH + 1` term comes from applying the paper's hybrid bounds to the forging
experiment, which adds one final verification query to the random oracle. -/
noncomputable def cmaToNmaLoss (qS qH : ℕ) (ε p ζ_zk δ : ℝ) (_hp : p < 1) : ℝ :=
  2 * qS * (qH + 1) * ε / (1 - p) +
  qS * ε * (qS + 1) / (2 * (1 - p) ^ 2) +
  qS * ζ_zk +
  δ

/-- **CMA-to-NMA reduction for Fiat-Shamir with aborts (Theorem 3, CRYPTO 2023).**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists an NMA reduction such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{EUF-NMA}(B) + L`

The reduction uses:
1. The quantitative HVZK simulator `sim` to answer signing queries without the secret key
2. Commitment recoverability `recover` to map between the standard and commitment-recoverable
   variants of the signature scheme
3. Nested hybrid arguments over ROM reprogramming (accepted and rejected transcripts)

The statistical loss `L` involves the commitment guessing probability `ε`, the effective
abort probability `p`, the simulator error `ζ_zk`, the regularity failure probability `δ`,
and the query bounds `qS`, `qH`; it is captured here by `cmaToNmaLoss`.

The scheme-specific reduction from NMA to computational assumptions (e.g., MLWE +
SelfTargetMSIS for ML-DSA) is stated separately; see `MLDSA.nma_security` and
`MLDSA.euf_cma_security`.

**WARNING: this is a placeholder statement, not the final theorem.** The current shape is
unsound as written: `ε` and `δ : ℝ` are unconstrained signed reals (only `0 ≤ ζ_zk` and
`p_abort < 1` are assumed). Choosing `ε`, `δ` very negative drives `cmaToNmaLoss` into
`(-∞, 0)`; `ENNReal.ofReal` clamps to `0`; the bound collapses to
`adv.advantage ≤ Pr[hard relation reduction]` with no statistical slack, which is generally
false for any non-trivially-secure hard relation. In the final statement `ε` and `δ` should
be nonnegative (e.g. `ℝ≥0` or constrained by `0 ≤ ε`, `0 ≤ δ` hypotheses), and `p_abort`
should additionally be `0 ≤ p_abort` so the divisors `1 - p` and `(1 - p)²` carry their
intended sign. The proof is intentionally deferred. -/
theorem euf_cma_bound
    (hc : ids.Complete)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
    (ζ_zk : ℝ)
    (hζ : 0 ≤ ζ_zk)
    (hhvzk : ids.HVZK sim ζ_zk)
    (recover : Stmt → Chal → Resp → Commit)
    (hcr : ids.CommitmentRecoverable recover)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))
    (qS qH : ℕ) (ε p_abort δ : ℝ) (hp : p_abort < 1)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      adv.advantage (runtime M) ≤
        Pr[= true | hardRelationExp hr reduction] +
          ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  let _ := hc
  let _ := hζ
  let _ := hhvzk
  let _ := hcr
  let _ := hQ
  sorry

/-- Perfect-HVZK special case of `euf_cma_bound`, where the simulator contributes no
`qS · ζ_zk` loss term.

**WARNING: this is a placeholder statement, not the final theorem.** It inherits the
unsoundness of `euf_cma_bound` (unconstrained signed `ε`, `δ : ℝ`); see that theorem's
docstring. -/
theorem euf_cma_bound_perfectHVZK
    (hc : ids.Complete)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
    (hhvzk : ids.PerfectHVZK sim)
    (recover : Stmt → Chal → Resp → Commit)
    (hcr : ids.CommitmentRecoverable recover)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))
    (qS qH : ℕ) (ε p_abort δ : ℝ) (hp : p_abort < 1)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      adv.advantage (runtime M) ≤
        Pr[= true | hardRelationExp hr reduction] +
          ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort 0 δ hp) := by
  simpa using
    (euf_cma_bound (ids := ids) (M := M) (maxAttempts := maxAttempts)
      (hc := hc) (sim := sim) (ζ_zk := 0) (hζ := le_rfl)
      (hhvzk := (IdenSchemeWithAbort.perfectHVZK_iff_hvzk_zero ids sim).mp hhvzk)
      (recover := recover) (hcr := hcr) (adv := adv)
      (qS := qS) (qH := qH) (ε := ε) (p_abort := p_abort) (δ := δ) (hp := hp)
      (hQ := hQ))

end EUF_CMA

end FiatShamirWithAbort
