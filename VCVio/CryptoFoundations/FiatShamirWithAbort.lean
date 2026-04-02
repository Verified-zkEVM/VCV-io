/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.IdenSchemeWithAbort
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.HasQuery
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.BundledSemantics
/-!
# Fiat-Shamir with Aborts Transform

This file defines the Fiat-Shamir with aborts transform, which converts an identification
scheme with aborts (`IdenSchemeWithAbort`) into a signature scheme (`SignatureAlg`). Unlike
the standard Fiat-Shamir transform (`FiatShamir`), signing involves a **retry loop**: the
prover commits, hashes (message, commitment) to get a challenge, attempts to respond, and if
the response aborts, restarts from scratch.

This is the transform used by ML-DSA (CRYSTALS-Dilithium, FIPS 204).

## Main Definitions

- `fsAbortSignLoop`: the retry loop with early return
- `FiatShamirWithAbort`: the signature scheme produced by the transform
- `FiatShamirWithAbort.euf_cma_bound`: EUF-CMA security statement (proof is future work)

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246)
- EasyCrypt `FSabort.eca`, `SimplifiedScheme.ec`
- NIST FIPS 204, Algorithms 2 (ML-DSA.Sign) and 3 (ML-DSA.Verify)
-/

universe v


open OracleComp OracleSpec

variable {S W W' St C Z : Type}
  {p : S → W → Bool}
  [SampleableType S] [SampleableType W]
  [DecidableEq W'] [SampleableType C]

/-- Signing retry loop with early return for the Fiat-Shamir with aborts transform.

Tries up to `n` commit-hash-respond cycles:
1. Commit to get `(w', st)`
2. Hash `(msg, w')` via the random oracle to get challenge `c`
3. Attempt to respond; if `some z`, return immediately; if `none` (abort), decrement
   the counter and retry.

Returns `none` only when all `n` attempts abort. -/
def fsAbortSignLoop (ids : IdenSchemeWithAbort S W W' St C Z p)
    {m : Type → Type v} [Monad m]
    (M : Type) [DecidableEq M] [MonadLiftT ProbComp m] [HasQuery (M × W' →ₒ C) m]
    (pk : S) (sk : W) (msg : M) :
    ℕ → m (Option (W' × Z))
  | 0 => return none
  | n + 1 => do
    let (w', st) ← (monadLift (ids.commit pk sk : ProbComp _) : m _)
    let c ← HasQuery.query (spec := (M × W' →ₒ C)) (msg, w')
    let oz ← (monadLift (ids.respond pk sk st c : ProbComp _) : m _)
    match oz with
    | some z => return some (w', z)
    | none => fsAbortSignLoop ids M pk sk msg n

/-- The Fiat-Shamir with aborts transform applied to an identification scheme with aborts.
Produces a signature scheme in the random oracle model.

The signing algorithm runs `fsAbortSignLoop` (up to `maxAttempts` iterations) with
early return on the first non-aborting response.

The type parameters are:
- `M`: message space
- `W'`: public commitment (included in signature for verification)
- `C`: challenge space (range of the hash/random oracle)
- `Z`: response space
- `S` / `W`: statement / witness (= public key / secret key) -/
def FiatShamirWithAbort
    {m : Type → Type v} [Monad m]
    (ids : IdenSchemeWithAbort S W W' St C Z p)
    (hr : GenerableRelation S W p) (M : Type) [DecidableEq M]
    [MonadLiftT ProbComp m] [HasQuery (M × W' →ₒ C) m]
    (maxAttempts : ℕ) :
    SignatureAlg m
      (M := M) (PK := S) (SK := W) (S := Option (W' × Z)) where
  keygen := monadLift hr.gen
  sign := fun pk sk msg => fsAbortSignLoop ids M pk sk msg maxAttempts
  verify := fun pk msg sig => do
    match sig with
    | none => return false
    | some (w', z) =>
      let c ← HasQuery.query (spec := (M × W' →ₒ C)) (msg, w')
      pure (ids.verify pk w' c z)

namespace FiatShamirWithAbort

variable (ids : IdenSchemeWithAbort S W W' St C Z p)
  (hr : GenerableRelation S W p)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

/-- Runtime bundle for the Fiat-Shamir-with-aborts random-oracle world. -/
noncomputable def runtime :
    ProbCompRuntime (OracleComp (unifSpec + (M × W' →ₒ C))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (M × W' →ₒ C) (StateT ((M × W' →ₒ C).QueryCache) ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

section EUF_CMA

/-- Structural query bound for Fiat-Shamir-with-aborts EUF-CMA adversaries:
uniform-sampling queries are unrestricted, while `qS` and `qH` bound signing-oracle
and random-oracle queries respectively. -/
def signHashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (M × W' →ₒ C)) + (M →ₒ S')) α)
    (qS qH : ℕ) : Prop :=
  OracleComp.IsQueryBound oa (qS, qH)
    (fun t b => match t, b with
      | .inl (.inl _), _ => True
      | .inl (.inr _), (_, qH') => 0 < qH'
      | .inr _, (qS', _) => 0 < qS')
    (fun t b => match t, b with
      | .inl (.inl _), b' => b'
      | .inl (.inr _), (qS', qH') => (qS', qH' - 1)
      | .inr _, (qS', qH') => (qS' - 1, qH'))

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
`MLDSA.euf_cma_security`. -/
theorem euf_cma_bound [DecidableEq Z]
    (hc : ids.Complete)
    (sim : S → ProbComp (Option (W' × C × Z)))
    (ζ_zk : ℝ)
    (hζ : 0 ≤ ζ_zk)
    (hhvzk : ids.HVZK sim ζ_zk)
    (recover : S → C → Z → W')
    (hcr : ids.CommitmentRecoverable recover)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × W' →ₒ C))) ids hr M maxAttempts))
    (qS qH : ℕ) (ε p_abort δ : ℝ) (hp : p_abort < 1)
    (hQ : ∀ pk, signHashQueryBound M
      (S' := Option (W' × Z)) (oa := adv.main pk) qS qH) :
    ∃ reduction : S → ProbComp W,
      adv.advantage (runtime M) ≤
        Pr[= true | hardRelationExp (r := p) reduction] +
          ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  let _ := hc
  let _ := hζ
  let _ := hhvzk
  let _ := hcr
  let _ := hQ
  sorry

/-- Perfect-HVZK special case of `euf_cma_bound`, where the simulator contributes no
`qS · ζ_zk` loss term. -/
theorem euf_cma_bound_perfectHVZK [DecidableEq Z]
    (hc : ids.Complete)
    (sim : S → ProbComp (Option (W' × C × Z)))
    (hhvzk : ids.PerfectHVZK sim)
    (recover : S → C → Z → W')
    (hcr : ids.CommitmentRecoverable recover)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × W' →ₒ C))) ids hr M maxAttempts))
    (qS qH : ℕ) (ε p_abort δ : ℝ) (hp : p_abort < 1)
    (hQ : ∀ pk, signHashQueryBound M
      (S' := Option (W' × Z)) (oa := adv.main pk) qS qH) :
    ∃ reduction : S → ProbComp W,
      adv.advantage (runtime M) ≤
        Pr[= true | hardRelationExp (r := p) reduction] +
          ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort 0 δ hp) := by
  simpa using
    (euf_cma_bound (ids := ids) (hr := hr) (M := M) (maxAttempts := maxAttempts)
      (hc := hc) (sim := sim) (ζ_zk := 0) (hζ := le_rfl)
      (hhvzk := (IdenSchemeWithAbort.perfectHVZK_iff_hvzk_zero ids sim).mp hhvzk)
      (recover := recover) (hcr := hcr) (adv := adv)
      (qS := qS) (qH := qH) (ε := ε) (p_abort := p_abort) (δ := δ) (hp := hp)
      (hQ := hQ))

end EUF_CMA

end FiatShamirWithAbort
