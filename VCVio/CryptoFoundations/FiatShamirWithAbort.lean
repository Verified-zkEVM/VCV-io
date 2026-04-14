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
import VCVio.OracleComp.QueryTracking.QueryRuntime
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.BundledSemantics
import Mathlib.Analysis.SpecificLimits.Basic
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

universe u v


open OracleComp OracleSpec
open scoped BigOperators

variable {S W W' St C Z : Type}
  {p : S → W → Bool}

/-- One signing attempt for the Fiat-Shamir-with-aborts transform.

This performs a single commit-hash-respond cycle and returns the public commitment together with
either a response or an abort marker. Unlike [`fsAbortSignLoop`], it never retries internally. -/
def fsAbortSignAttempt (ids : IdenSchemeWithAbort S W W' St C Z p)
    {m : Type → Type v} [Monad m]
    (M : Type) [MonadLiftT ProbComp m] [HasQuery (M × W' →ₒ C) m]
    (pk : S) (sk : W) (msg : M) :
    m (W' × Option Z) := do
  let (w', st) ← (monadLift (ids.commit pk sk : ProbComp _) : m _)
  let c ← HasQuery.query (spec := (M × W' →ₒ C)) (msg, w')
  let oz ← (monadLift (ids.respond pk sk st c : ProbComp _) : m _)
  pure (w', oz)

/-- Signing retry loop with early return for the Fiat-Shamir with aborts transform.

Tries up to `n` commit-hash-respond cycles:
1. Commit to get `(w', st)`
2. Hash `(msg, w')` via the random oracle to get challenge `c`
3. Attempt to respond; if `some z`, return immediately; if `none` (abort), decrement
   the counter and retry.

Returns `none` only when all `n` attempts abort. -/
def fsAbortSignLoop (ids : IdenSchemeWithAbort S W W' St C Z p)
    {m : Type → Type v} [Monad m]
    (M : Type) [MonadLiftT ProbComp m] [HasQuery (M × W' →ₒ C) m]
    (pk : S) (sk : W) (msg : M) :
    ℕ → m (Option (W' × Z))
  | 0 => return none
  | n + 1 => do
    let (w', oz) ← fsAbortSignAttempt ids M pk sk msg
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
    [SampleableType S] [SampleableType W]
    (hr : GenerableRelation S W p) (M : Type)
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

section runtime

variable (M : Type) [DecidableEq M] [DecidableEq W'] [SampleableType C]

/-- Runtime bundle for the Fiat-Shamir-with-aborts random-oracle world. -/
noncomputable def runtime :
    ProbCompRuntime (OracleComp (unifSpec + (M × W' →ₒ C))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (M × W' →ₒ C) (StateT ((M × W' →ₒ C).QueryCache) ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

end runtime

section costAccounting

variable (ids : IdenSchemeWithAbort S W W' St C Z p) (M : Type)

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

private lemma signAttempt_run_formula_withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (costFn : M × W' → ω) :
    WriterT.run
        (HasQuery.withAddCost
          (fun [HasQuery (M × W' →ₒ C) (AddWriterT ω m)] =>
            fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
          runtime costFn) =
      (fun attempt : W' × Option Z =>
        (attempt, Multiplicative.ofAdd (costFn (msg, attempt.1)))) <$>
        HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime := by
  suffices h :
      (do
        let a ← WriterT.run (monadLift (ids.commit pk sk) : AddWriterT ω m (W' × St))
        let c ← runtime.impl (msg, a.1.1)
        let z ← WriterT.run (monadLift (ids.respond pk sk a.1.2 c) : AddWriterT ω m (Option Z))
        pure ((a.1.1, z.1), a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2))) =
      (do
        let a ← (monadLift (ids.commit pk sk) : m (W' × St))
        let c ← runtime.impl (msg, a.1)
        let z ← (monadLift (ids.respond pk sk a.2 c) : m (Option Z))
        pure ((a.1, z), Multiplicative.ofAdd (costFn (msg, a.1)))) by
    simpa [HasQuery.inRuntime, HasQuery.withAddCost, fsAbortSignAttempt,
      QueryRuntime.withAddCost_impl, AddWriterT.addTell] using h
  change (do
      let a ← WriterT.run (monadLift ((monadLift (ids.commit pk sk) : m (W' × St))) :
        AddWriterT ω m (W' × St))
      let c ← runtime.impl (msg, a.1.1)
      let z ← WriterT.run (monadLift ((monadLift (ids.respond pk sk a.1.2 c) : m (Option Z))) :
        AddWriterT ω m (Option Z))
      pure ((a.1.1, z.1), a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2))) = _
  simp [bind_map_left]

private lemma signAttempt_outputs_formula_withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (costFn : M × W' → ω) :
    AddWriterT.outputs
        (HasQuery.withAddCost
          (fun [HasQuery (M × W' →ₒ C) (AddWriterT ω m)] =>
            fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
          runtime costFn) =
      HasQuery.inRuntime
        (fun [HasQuery (M × W' →ₒ C) m] =>
          fsAbortSignAttempt (m := m) ids M pk sk msg)
        runtime := by
  rw [AddWriterT.outputs, signAttempt_run_formula_withAddCost, Functor.map_map]
  simp

private lemma signAttempt_costs_formula_withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (costFn : M × W' → ω) :
    AddWriterT.costs
        (HasQuery.withAddCost
          (fun [HasQuery (M × W' →ₒ C) (AddWriterT ω m)] =>
            fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
          runtime costFn) =
      (fun attempt ↦ costFn (msg, attempt.1)) <$>
        HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime := by
  simp only [AddWriterT.costs, signAttempt_run_formula_withAddCost, Functor.map_map,
    toAdd_ofAdd]

private lemma signAttempt_run_formula_withUnitCost
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) :
    WriterT.run
        (HasQuery.withUnitCost
          (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
            fsAbortSignAttempt (m := AddWriterT ℕ m) ids M pk sk msg)
          runtime) =
      (fun attempt : W' × Option Z => (attempt, Multiplicative.ofAdd 1)) <$>
        HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime := by
  simpa [HasQuery.withUnitCost] using
    signAttempt_run_formula_withAddCost
      (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
      (costFn := fun _ ↦ (1 : ℕ))

/-- A single signing attempt has query cost determined by its output: the returned commitment
`w'` is exactly the random-oracle query point. -/
theorem signAttempt_usesCostAsQueryCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (costFn : M × W' → ω) :
    HasQuery.UsesCostAs
      (fun [HasQuery (M × W' →ₒ C) (AddWriterT ω m)] =>
        fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
      runtime costFn (fun attempt ↦ costFn (msg, attempt.1)) := by
  rw [HasQuery.UsesCostAs, AddWriterT.costsAs_iff]
  rw [signAttempt_outputs_formula_withAddCost
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
    (costFn := costFn)]
  exact signAttempt_costs_formula_withAddCost
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
    (costFn := costFn)

/-- The expected weighted query cost of one signing attempt is the expectation of the queried
commitment cost over the attempt output distribution. -/
theorem signAttempt_expectedQueryCost_eq_outputExpectation
    {ω : Type} [AddMonoid ω] [HasEvalSPMF m]
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (costFn : M × W' → ω) (val : ω → ENNReal) :
    ExpectedQueryCost[
      fsAbortSignAttempt ids M pk sk msg in runtime by costFn via val
    ] =
      ∑' attempt : W' × Option Z,
        Pr[= attempt | HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime] * val (costFn (msg, attempt.1)) := by
  calc
    ExpectedQueryCost[
      fsAbortSignAttempt ids M pk sk msg in runtime by costFn via val
    ] =
      ∑' attempt : W' × Option Z,
        Pr[= attempt | AddWriterT.outputs
          (HasQuery.withAddCost
            (fun [HasQuery (M × W' →ₒ C) (AddWriterT ω m)] =>
              fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
            runtime costFn)] * val (costFn (msg, attempt.1)) := by
          exact HasQuery.expectedQueryCost_eq_tsum_outputs_of_usesCostAs
            (oa := fun [HasQuery (M × W' →ₒ C) (AddWriterT ω m)] =>
              fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
            (runtime := runtime) (costFn := costFn) (f := fun attempt ↦ costFn (msg, attempt.1))
            (val := val)
            (signAttempt_usesCostAsQueryCost
              (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
              (msg := msg) (costFn := costFn))
    _ = ∑' attempt : W' × Option Z,
          Pr[= attempt | HasQuery.inRuntime
            (fun [HasQuery (M × W' →ₒ C) m] =>
              fsAbortSignAttempt (m := m) ids M pk sk msg)
            runtime] * val (costFn (msg, attempt.1)) := by
          rw [signAttempt_outputs_formula_withAddCost
            (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
            (msg := msg) (costFn := costFn)]

section queryBounds

variable [HasEvalSet m]

private lemma signAttempt_usesWeightedQueryCostAtMost
    {κ : Type} [AddCommMonoid κ] [PartialOrder κ] [IsOrderedAddMonoid κ]
    [CanonicallyOrderedAdd κ]
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (costFn : M × W' → κ) (w : κ) (hcost : ∀ t, costFn t ≤ w) :
    HasQuery.UsesCostAtMost
      (fun [HasQuery (M × W' →ₒ C) (AddWriterT κ m)] =>
        fsAbortSignAttempt (m := AddWriterT κ m) ids M pk sk msg)
      runtime costFn w := by
  change AddWriterT.PathwiseCostAtMost
    (do
      let a ← (monadLift (ids.commit pk sk : ProbComp (W' × St)) : AddWriterT κ m (W' × St))
      let c ← (runtime.withAddCost costFn).impl (msg, a.1)
      let oz ← (monadLift (ids.respond pk sk a.2 c : ProbComp (Option Z)) :
        AddWriterT κ m (Option Z))
      pure (a.1, oz))
    w
  have hCommit :
      AddWriterT.PathwiseCostAtMost
        (monadLift (ids.commit pk sk : ProbComp (W' × St)) : AddWriterT κ m (W' × St))
        0 :=
    AddWriterT.pathwiseCostAtMost_probCompLift (m := m) (ω := κ) (ids.commit pk sk)
  have hQuery :
      ∀ a : W' × St,
        AddWriterT.PathwiseCostAtMost ((runtime.withAddCost costFn).impl (msg, a.1)) w := by
    intro a
    exact AddWriterT.pathwiseCostAtMost_of_hasCost
      (HasQuery.hasCost_withAddCost_query
        (runtime := runtime) (costFn := costFn) (t := (msg, a.1)))
      (hcost (msg, a.1))
  have hRespond :
      ∀ a : W' × St, ∀ c : C,
        AddWriterT.PathwiseCostAtMost
          (monadLift (ids.respond pk sk a.2 c : ProbComp (Option Z)) :
            AddWriterT κ m (Option Z))
          0 := by
    intro a c
    exact AddWriterT.pathwiseCostAtMost_probCompLift
      (m := m) (ω := κ) (ids.respond pk sk a.2 c)
  have hPure :
      ∀ a : W' × St, ∀ oz : Option Z,
        AddWriterT.PathwiseCostAtMost (pure (a.1, oz) : AddWriterT κ m (W' × Option Z)) 0 := by
    intro a oz
    exact AddWriterT.pathwiseCostAtMost_pure (m := m) (ω := κ) (x := (a.1, oz))
  simpa [zero_add, add_comm] using
    (AddWriterT.pathwiseCostAtMost_bind (w₁ := 0) (w₂ := w) hCommit
      (fun a ↦ by
        simpa [zero_add, add_comm] using
          (AddWriterT.pathwiseCostAtMost_bind (w₁ := w) (w₂ := 0) (hQuery a)
            (fun c ↦ by
              simpa [zero_add] using
                (AddWriterT.pathwiseCostAtMost_bind (w₁ := 0) (w₂ := 0) (hRespond a c)
                  (fun oz ↦ hPure a oz))))))

/-- The retry loop makes weighted query cost at most `n • w` when each query costs at most `w`.
-/
theorem fsAbortSignLoop_usesWeightedQueryCostAtMost
    {κ : Type} [AddCommMonoid κ] [PartialOrder κ] [IsOrderedAddMonoid κ]
    [CanonicallyOrderedAdd κ]
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (costFn : M × W' → κ) (w : κ) (hcost : ∀ t, costFn t ≤ w) :
    ∀ n,
      HasQuery.UsesCostAtMost
        (fun [HasQuery (M × W' →ₒ C) (AddWriterT κ m)] =>
          fsAbortSignLoop (m := AddWriterT κ m) ids M pk sk msg n)
        runtime costFn (n • w)
  | 0 => by
      simpa [HasQuery.UsesCostAtMost, HasQuery.withAddCost, fsAbortSignLoop] using
        (AddWriterT.pathwiseCostAtMost_pure
          (m := m) (ω := κ) (x := (none : Option (W' × Z))))
  | n + 1 => by
      have hStep := signAttempt_usesWeightedQueryCostAtMost
        (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
        (msg := msg) (costFn := costFn) (w := w) hcost
      have hRec := fsAbortSignLoop_usesWeightedQueryCostAtMost
        (runtime := runtime) (pk := pk) (sk := sk)
        (msg := msg) (costFn := costFn) (w := w) hcost n
      let cont : W' × Option Z → AddWriterT κ m (Option (W' × Z)) := fun attempt =>
        match attempt.2 with
        | some z => pure (some (attempt.1, z))
        | none =>
            HasQuery.withAddCost
              (fun [HasQuery (M × W' →ₒ C) (AddWriterT κ m)] =>
                fsAbortSignLoop (m := AddWriterT κ m) ids M pk sk msg n)
              runtime costFn
      have hCont : ∀ attempt, AddWriterT.PathwiseCostAtMost (cont attempt) (n • w) := by
        intro attempt
        cases hAttempt : attempt.2 with
        | some z =>
            simpa only [cont, hAttempt] using
              (AddWriterT.pathwiseCostAtMost_mono
                (AddWriterT.pathwiseCostAtMost_pure
                  (m := m) (ω := κ) (x := (some (attempt.1, z) : Option (W' × Z))))
                (zero_le _))
        | none =>
            simpa [cont, hAttempt, HasQuery.UsesCostAtMost] using hRec
      simpa [HasQuery.UsesCostAtMost, HasQuery.withAddCost, fsAbortSignLoop, succ_nsmul',
        fsAbortSignAttempt, cont] using
        (AddWriterT.pathwiseCostAtMost_bind (w₁ := w) (w₂ := n • w) hStep hCont)

section schemeCost

variable [SampleableType S] [SampleableType W]
variable (hr : GenerableRelation S W p)

/-- Signing makes weighted query cost at most `maxAttempts • w` when each query costs at most
`w`. -/
theorem sign_usesWeightedQueryCostAtMost
    {κ : Type} [AddCommMonoid κ] [PartialOrder κ] [IsOrderedAddMonoid κ]
    [CanonicallyOrderedAdd κ]
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (costFn : M × W' → κ) (w : κ) (hcost : ∀ t, costFn t ≤ w) (maxAttempts : ℕ) :
    QueryCost[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime by costFn
    ] ≤ maxAttempts • w := by
  change HasQuery.UsesCostAtMost
    (fun [HasQuery (M × W' →ₒ C) (AddWriterT κ m)] =>
      fsAbortSignLoop (m := AddWriterT κ m) ids M pk sk msg maxAttempts)
    runtime costFn (maxAttempts • w)
  exact fsAbortSignLoop_usesWeightedQueryCostAtMost
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
    (costFn := costFn) (w := w) hcost maxAttempts

/-- Unit-cost specialization: signing makes at most `maxAttempts` random-oracle queries. -/
theorem sign_usesAtMostMaxAttemptsQueries
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (maxAttempts : ℕ) :
    QueryCost[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤ maxAttempts := by
  simpa [nsmul_eq_mul] using
    (sign_usesWeightedQueryCostAtMost
      (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
      (msg := msg) (costFn := fun _ ↦ (1 : ℕ)) (w := 1) (hcost := fun _ ↦ le_rfl)
      (maxAttempts := maxAttempts))

end schemeCost

end queryBounds

section expectedCost

variable [HasEvalSPMF m]

section schemeCost

variable [SampleableType S] [SampleableType W]
variable (hr : GenerableRelation S W p)

/-- Tail-sum formula for the expected number of signing queries in Fiat-Shamir with aborts.

The random variable on the right is the unit-cost query count of the signer. The event `i < q`
means that the signer performed at least `i + 1` random-oracle queries, equivalently that the
`(i + 1)`-st signing attempt was reached. Since the signer performs at most `maxAttempts`
iterations, the infinite tail sum truncates to `Finset.range maxAttempts`. -/
theorem sign_expectedQueries_eq_sum_reachedAttemptProbabilities
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] =
      ∑ i ∈ Finset.range maxAttempts,
        Pr[ fun q ↦ i < q |
          HasQuery.queryCountDist
            (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
              (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
            runtime] := by
  letI : HasEvalSet m := HasEvalSPMF.toHasEvalSet
  exact HasQuery.expectedQueries_eq_sum_tail_probs_of_usesAtMostQueries
    (oa := fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
    (runtime := runtime) (n := maxAttempts)
    (sign_usesAtMostMaxAttemptsQueries
      (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
      (msg := msg) (maxAttempts := maxAttempts))

/-- Expected weighted query cost of signing is bounded by the worst-case `maxAttempts • w`
budget whenever every query costs at most `w`. -/
theorem sign_expectedQueryCost_le
    {κ : Type} [AddCommMonoid κ] [PartialOrder κ] [IsOrderedAddMonoid κ]
    [CanonicallyOrderedAdd κ]
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (costFn : M × W' → κ) (w : κ) (val : κ → ENNReal)
    (hcost : ∀ t, costFn t ≤ w) (hval : Monotone val) (maxAttempts : ℕ) :
    ExpectedQueryCost[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime by costFn via val
    ] ≤ val (maxAttempts • w) := by
  let _ : HasEvalSet m := HasEvalSPMF.toHasEvalSet
  exact HasQuery.expectedQueryCost_le_of_usesCostAtMost
    (sign_usesWeightedQueryCostAtMost
      (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
      (msg := msg) (costFn := costFn) (w := w) hcost (maxAttempts := maxAttempts))
    hval

/-- Unit-cost specialization: the expected number of signing queries is at most `maxAttempts`. -/
theorem sign_expectedQueries_le
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤ maxAttempts := by
  letI : HasEvalSet m := HasEvalSPMF.toHasEvalSet
  exact HasQuery.expectedQueries_le_of_usesAtMostQueries
    (sign_usesAtMostMaxAttemptsQueries
      (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
      (msg := msg) (maxAttempts := maxAttempts))

end schemeCost

end expectedCost

end costAccounting

section expectedCostPMF

variable (ids : IdenSchemeWithAbort S W W' St C Z p) (M : Type)

variable {m : Type → Type u} [Monad m] [MonadLiftT ProbComp m]

private lemma signLoop_inRuntime_succ
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) (n : ℕ) :
    HasQuery.inRuntime
      (fun [HasQuery (M × W' →ₒ C) m] =>
        fsAbortSignLoop (m := m) ids M pk sk msg (n + 1))
      runtime
    =
      (do
        let attempt ← HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime
        match attempt.2 with
        | some z => pure (some (attempt.1, z))
        | none =>
            HasQuery.inRuntime
              (fun [HasQuery (M × W' →ₒ C) m] =>
                fsAbortSignLoop (m := m) ids M pk sk msg n)
              runtime) := by
  rfl

section

variable [LawfulMonad m]

private lemma signLoop_queryCountDist_succ
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) (n : ℕ) :
    HasQuery.queryCountDist
      (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1))
      runtime
    =
      (do
        let attempt ← HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime
        match attempt.2 with
        | some _ => pure 1
        | none =>
            let recCosts :=
              HasQuery.queryCountDist
                (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
                  fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
                runtime
            Nat.succ <$> recCosts) := by
  change AddWriterT.costs
      (do
        let attempt ← HasQuery.withUnitCost
          (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
            fsAbortSignAttempt (m := AddWriterT ℕ m) ids M pk sk msg)
          runtime
        match attempt.2 with
        | some z => pure (some (attempt.1, z))
        | none =>
            HasQuery.withUnitCost
              (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
                fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
              runtime) = _
  rw [AddWriterT.costs_def, WriterT.run_bind]
  rw [signAttempt_run_formula_withUnitCost
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)]
  simp only [bind_map_left, map_bind, Functor.map_map, Prod.map_snd, toAdd_mul, toAdd_ofAdd]
  refine bind_congr (m := m) ?_
  intro attempt
  cases attempt.2 with
  | some z =>
      simp
  | none =>
      simp [HasQuery.queryCountDist, HasQuery.queryCostDist, HasQuery.withUnitCost,
        HasQuery.withAddCost, AddWriterT.costs, add_comm]

end

variable [HasEvalPMF m]

/-- The probability that a single Fiat-Shamir-with-aborts signing attempt aborts. -/
noncomputable abbrev signAttemptAbortProbability
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) : ENNReal :=
  Pr[ fun attempt ↦ attempt.2 = none |
    HasQuery.inRuntime
      (fun [HasQuery (M × W' →ₒ C) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime]

private lemma signLoop_probNone_succ
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) (n : ℕ) :
    Pr[= none |
      HasQuery.inRuntime
        (fun [HasQuery (M × W' →ₒ C) m] =>
          fsAbortSignLoop (m := m) ids M pk sk msg (n + 1))
        runtime] =
      Pr[ fun attempt ↦ attempt.2 = none |
        HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime] *
      Pr[= none |
        HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg n)
          runtime] := by
  set attemptComp : m (W' × Option Z) :=
    HasQuery.inRuntime
      (fun [HasQuery (M × W' →ₒ C) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime
  set recLoop : m (Option (W' × Z)) :=
    HasQuery.inRuntime
      (fun [HasQuery (M × W' →ₒ C) m] =>
        fsAbortSignLoop (m := m) ids M pk sk msg n)
      runtime
  rw [signLoop_inRuntime_succ (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
    (msg := msg) (n := n)]
  change Pr[= none |
      attemptComp >>= fun attempt =>
        match attempt.2 with
        | some z => pure (some (attempt.1, z))
        | none => recLoop] =
    Pr[ fun attempt ↦ attempt.2 = none | attemptComp] * Pr[= none | recLoop]
  rw [probOutput_bind_eq_tsum]
  calc
    ∑' attempt : W' × Option Z,
        Pr[= attempt | attemptComp] *
          Pr[= none |
            match attempt.2 with
            | some z => pure (some (attempt.1, z))
            | none => recLoop]
      = ∑' attempt : W' × Option Z,
          Pr[= attempt | attemptComp] *
            (if attempt.2 = none then Pr[= none | recLoop] else 0) := by
              refine tsum_congr fun attempt => ?_
              cases hAttempt : attempt.2 with
              | some z =>
                  simp
              | none =>
                  simp
    _ = ∑' attempt : W' × Option Z,
          (if attempt.2 = none then Pr[= attempt | attemptComp] else 0) * Pr[= none | recLoop] := by
            refine tsum_congr fun attempt => ?_
            by_cases hAttempt : attempt.2 = none <;> simp [hAttempt, mul_comm]
    _ = (∑' attempt : W' × Option Z, if attempt.2 = none then Pr[= attempt | attemptComp] else 0)
          * Pr[= none | recLoop] := by
            rw [ENNReal.tsum_mul_right]
    _ = Pr[ fun attempt ↦ attempt.2 = none | attemptComp] * Pr[= none | recLoop] := by
            simp [probEvent_eq_tsum_indicator, Set.indicator, Set.mem_setOf_eq]

section

variable [LawfulMonad m]

private lemma signLoop_queryTailProbability_zero
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) (n : ℕ) :
    Pr[ fun q ↦ 0 < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
          fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1))
        runtime] = 1 := by
  set attemptComp : m (W' × Option Z) :=
    HasQuery.inRuntime
      (fun [HasQuery (M × W' →ₒ C) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime
  set recCosts : m ℕ :=
    HasQuery.queryCountDist (m := m)
      (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
      runtime
  rw [signLoop_queryCountDist_succ (ids := ids) (M := M) (runtime := runtime) (pk := pk)
    (sk := sk) (msg := msg) (n := n)]
  change Pr[ fun q ↦ 0 < q |
      attemptComp >>= fun attempt =>
        match attempt.2 with
        | some _ => pure 1
        | none => Nat.succ <$> recCosts] = 1
  rw [probEvent_bind_of_const (r := 1)]
  · simp
  · intro attempt _
    cases hAttempt : attempt.2 with
    | some z =>
        simp
    | none =>
        simp [probEvent_map]

private lemma signLoop_queryTailProbability_succ
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) (i n : ℕ) :
    Pr[ fun q ↦ i + 1 < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
          fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1))
        runtime] =
      Pr[ fun attempt ↦ attempt.2 = none |
        HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime] *
      Pr[ fun q ↦ i < q |
        HasQuery.queryCountDist
          (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
            fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
          runtime] := by
  set attemptComp : m (W' × Option Z) :=
    HasQuery.inRuntime
      (fun [HasQuery (M × W' →ₒ C) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime
  set recCosts : m ℕ :=
    HasQuery.queryCountDist (m := m)
      (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
      runtime
  let cont : W' × Option Z → m ℕ := fun attempt =>
    match attempt.2 with
    | some _ => pure 1
    | none => Nat.succ <$> recCosts
  rw [signLoop_queryCountDist_succ (ids := ids) (M := M) (runtime := runtime) (pk := pk)
    (sk := sk) (msg := msg) (n := n)]
  change Pr[ fun q ↦ i + 1 < q |
      attemptComp >>= cont] =
    Pr[ fun attempt ↦ attempt.2 = none | attemptComp] *
      Pr[ fun q ↦ i < q | recCosts]
  rw [probEvent_bind_eq_tsum]
  calc
    ∑' attempt : W' × Option Z,
        Pr[= attempt | attemptComp] * Pr[ fun q ↦ i + 1 < q | cont attempt]
      = ∑' attempt : W' × Option Z,
          Pr[= attempt | attemptComp] *
            (if attempt.2 = none then Pr[ fun q ↦ i < q | recCosts] else 0) := by
              refine tsum_congr fun attempt => ?_
              cases hAttempt : attempt.2 with
              | some z =>
                  simp [cont, hAttempt]
              | none =>
                  have hs :
                      Pr[ fun q ↦ i + 1 < q | Nat.succ <$> recCosts] =
                        Pr[ fun q ↦ i < q | recCosts] := by
                    have hpred : ((fun q ↦ i + 1 < q) ∘ Nat.succ) = fun q ↦ i < q := by
                      funext q
                      exact propext (show Nat.succ i < Nat.succ q ↔ i < q from
                        Nat.succ_lt_succ_iff)
                    calc
                      Pr[ fun q ↦ i + 1 < q | Nat.succ <$> recCosts]
                        = Pr[ ((fun q ↦ i + 1 < q) ∘ Nat.succ) | recCosts] := by
                            rw [probEvent_map]
                      _ = Pr[ fun q ↦ i < q | recCosts] := by
                            rw [hpred]
                  rw [show cont attempt = Nat.succ <$> recCosts by simp [cont, hAttempt]]
                  rw [hs]
                  simp
    _ = ∑' attempt : W' × Option Z,
          (if attempt.2 = none then Pr[= attempt | attemptComp] else 0) *
            Pr[ fun q ↦ i < q | recCosts] := by
              refine tsum_congr fun attempt => ?_
              by_cases hAttempt : attempt.2 = none <;> simp [hAttempt, mul_comm]
    _ = (∑' attempt : W' × Option Z, if attempt.2 = none then Pr[= attempt | attemptComp] else 0)
          * Pr[ fun q ↦ i < q | recCosts] := by
            rw [ENNReal.tsum_mul_right]
    _ = Pr[ fun attempt ↦ attempt.2 = none | attemptComp] *
          Pr[ fun q ↦ i < q | recCosts] := by
            simp [probEvent_eq_tsum_indicator, Set.indicator, Set.mem_setOf_eq]

private theorem signLoop_queryTailProbability_eq_probNonePrefix
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) :
    ∀ i extra,
      Pr[ fun q ↦ i < q |
        HasQuery.queryCountDist
          (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
            fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + extra + 1))
          runtime] =
      Pr[= none |
        HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime]
  | 0, extra => by
      have hzero :
          Pr[ fun q ↦ 0 < q |
            HasQuery.queryCountDist
              (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
                fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (0 + extra + 1))
              runtime] = 1 := by
        simpa [Nat.zero_add] using
          signLoop_queryTailProbability_zero
            (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
            (msg := msg) (n := extra)
      calc
        Pr[ fun q ↦ 0 < q |
          HasQuery.queryCountDist
            (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
              fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (0 + extra + 1))
            runtime] = 1 := hzero
      _ = Pr[= none |
            HasQuery.inRuntime
              (fun [HasQuery (M × W' →ₒ C) m] =>
                fsAbortSignLoop (m := m) ids M pk sk msg 0)
              runtime] := by
            simp [HasQuery.inRuntime, fsAbortSignLoop]
  | i + 1, extra => by
      have hstep :
          Pr[ fun q ↦ i + 1 < q |
            HasQuery.queryCountDist
              (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
                fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + 1 + extra + 1))
              runtime] =
            Pr[ fun attempt ↦ attempt.2 = none |
              HasQuery.inRuntime
                (fun [HasQuery (M × W' →ₒ C) m] =>
                  fsAbortSignAttempt (m := m) ids M pk sk msg)
                runtime] *
            Pr[ fun q ↦ i < q |
              HasQuery.queryCountDist
                (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
                  fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + extra + 1))
                runtime] := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          signLoop_queryTailProbability_succ
            (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
            (msg := msg) (i := i) (n := i + extra + 1)
      calc
        Pr[ fun q ↦ i + 1 < q |
          HasQuery.queryCountDist
            (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
              fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + 1 + extra + 1))
            runtime]
          =
            Pr[ fun attempt ↦ attempt.2 = none |
              HasQuery.inRuntime
                (fun [HasQuery (M × W' →ₒ C) m] =>
                  fsAbortSignAttempt (m := m) ids M pk sk msg)
                runtime] *
            Pr[ fun q ↦ i < q |
              HasQuery.queryCountDist
                (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
                  fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + extra + 1))
                runtime] := hstep
        _ =
            Pr[ fun attempt ↦ attempt.2 = none |
              HasQuery.inRuntime
                (fun [HasQuery (M × W' →ₒ C) m] =>
                  fsAbortSignAttempt (m := m) ids M pk sk msg)
                runtime] *
            Pr[= none |
              HasQuery.inRuntime
                (fun [HasQuery (M × W' →ₒ C) m] =>
                  fsAbortSignLoop (m := m) ids M pk sk msg i)
                runtime] := by
                  rw [signLoop_queryTailProbability_eq_probNonePrefix
                    (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
                    (i := i) (extra := extra)]
        _ = Pr[= none |
              HasQuery.inRuntime
                (fun [HasQuery (M × W' →ₒ C) m] =>
                  fsAbortSignLoop (m := m) ids M pk sk msg (i + 1))
                runtime] := by
                  symm
                  simpa using
                    signLoop_probNone_succ
                      (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
                      (msg := msg) (n := i)

end

private theorem signLoop_probNone_eq_signAttemptAbortProbability_pow
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) :
    ∀ i,
      Pr[= none |
        HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime] =
        (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i
  | 0 => by
      simp [signAttemptAbortProbability, HasQuery.inRuntime, fsAbortSignLoop]
  | i + 1 => by
      calc
        Pr[= none |
          HasQuery.inRuntime
            (fun [HasQuery (M × W' →ₒ C) m] =>
              fsAbortSignLoop (m := m) ids M pk sk msg (i + 1))
            runtime] =
          signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg *
            Pr[= none |
              HasQuery.inRuntime
                (fun [HasQuery (M × W' →ₒ C) m] =>
                  fsAbortSignLoop (m := m) ids M pk sk msg i)
                runtime] := by
                  simpa [signAttemptAbortProbability] using
                    signLoop_probNone_succ
                      (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
                      (msg := msg) (n := i)
        _ =
          signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg *
            (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
              rw [signLoop_probNone_eq_signAttemptAbortProbability_pow
                (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) i]
        _ =
          (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ (i + 1) := by
              simp [pow_succ']

section

/-- The probability that the first `i` signing attempts all abort is the `i`-th power of the
single-attempt abort probability. -/
theorem sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) (i : ℕ) :
    Pr[= none |
      HasQuery.inRuntime
        (fun [HasQuery (M × W' →ₒ C) m] =>
          fsAbortSignLoop (m := m) ids M pk sk msg i)
        runtime] =
      (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
  exact signLoop_probNone_eq_signAttemptAbortProbability_pow
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) i

end

variable [LawfulMonad m]

section schemeCost

variable [SampleableType S] [SampleableType W]
variable (hr : GenerableRelation S W p)

/-- The probability that signing makes more than `i` random-oracle queries is exactly the
probability that the first `i` signing attempts all abort.

Equivalently, the event `i < q` for the signer query count is the event that the retry loop of
length `i` returns `none`, meaning that the `(i + 1)`-st attempt is reached. -/
theorem sign_queryTailProbability_eq_probAllFirstAttemptsAbort
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    {i maxAttempts : ℕ} (hi : i < maxAttempts) :
    Pr[ fun q ↦ i < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
          (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
        runtime] =
      Pr[= none |
        HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime] := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_lt hi
  change Pr[ fun q ↦ i < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
          fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + extra + 1))
        runtime] =
      Pr[= none |
        HasQuery.inRuntime
          (fun [HasQuery (M × W' →ₒ C) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime]
  exact signLoop_queryTailProbability_eq_probNonePrefix
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
    (i := i) (extra := extra)

/-- The probability that signing makes more than `i` oracle queries is the `i`-th power of the
single-attempt abort probability, as long as `i < maxAttempts`. -/
theorem sign_queryTailProbability_eq_signAttemptAbortProbability_pow
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    {i maxAttempts : ℕ} (hi : i < maxAttempts) :
    Pr[ fun q ↦ i < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
          (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
        runtime] =
      (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
  rw [sign_queryTailProbability_eq_probAllFirstAttemptsAbort
    (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
    (msg := msg) (hi := hi)]
  exact sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) i

/-- The expected number of signing queries is the sum, over prefixes of the retry loop, of the
probability that every attempt in the prefix aborts. -/
theorem sign_expectedQueries_eq_sum_abortPrefixProbabilities
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] =
      ∑ i ∈ Finset.range maxAttempts,
        Pr[= none |
          HasQuery.inRuntime
            (fun [HasQuery (M × W' →ₒ C) m] =>
              fsAbortSignLoop (m := m) ids M pk sk msg i)
            runtime] := by
  calc
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] =
      ∑ i ∈ Finset.range maxAttempts,
        Pr[ fun q ↦ i < q |
          HasQuery.queryCountDist
            (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
              (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
            runtime] := by
              exact sign_expectedQueries_eq_sum_reachedAttemptProbabilities
                (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
                (msg := msg) (maxAttempts := maxAttempts)
    _ = ∑ i ∈ Finset.range maxAttempts,
          Pr[= none |
            HasQuery.inRuntime
              (fun [HasQuery (M × W' →ₒ C) m] =>
                fsAbortSignLoop (m := m) ids M pk sk msg i)
              runtime] := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact sign_queryTailProbability_eq_probAllFirstAttemptsAbort
              (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
              (msg := msg) (hi := by exact Finset.mem_range.mp hi)

/-- The expected number of signing queries is the finite geometric sum of the one-step abort
probability. -/
theorem sign_expectedQueries_eq_sum_signAttemptAbortProbability_powers
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] =
      ∑ i ∈ Finset.range maxAttempts,
        (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
  calc
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] =
      ∑ i ∈ Finset.range maxAttempts,
        Pr[= none |
          HasQuery.inRuntime
            (fun [HasQuery (M × W' →ₒ C) m] =>
              fsAbortSignLoop (m := m) ids M pk sk msg i)
            runtime] := by
              exact sign_expectedQueries_eq_sum_abortPrefixProbabilities
                (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
                (msg := msg) (maxAttempts := maxAttempts)
    _ = ∑ i ∈ Finset.range maxAttempts,
          (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow
              (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) i

/-- Tail probabilities for the signer query count are bounded by the corresponding power of the
single-attempt abort probability. -/
theorem sign_queryTailProbability_le_signAttemptAbortProbability_pow
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (i maxAttempts : ℕ) :
    Pr[ fun q ↦ i < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
          (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
        runtime] ≤
      (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
  letI : HasEvalSPMF m := HasEvalPMF.toHasEvalSPMF
  letI : HasEvalSet m := HasEvalSPMF.toHasEvalSet
  by_cases hi : i < maxAttempts
  · rw [sign_queryTailProbability_eq_signAttemptAbortProbability_pow
      (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
      (msg := msg) (hi := hi)]
  · have hzero :
        Pr[ fun q ↦ i < q |
          HasQuery.queryCountDist
            (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
              (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
            runtime] = 0 := by
        refine probEvent_eq_zero ?_
        intro c hc
        have hc' : c ∈ support
            (AddWriterT.costs
              (HasQuery.withUnitCost
                (fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
                  (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
                runtime)) := by
          simpa [HasQuery.queryCountDist, HasQuery.queryCostDist, HasQuery.withUnitCost,
            HasQuery.withAddCost] using hc
        rw [AddWriterT.costs_def, support_map] at hc'
        rcases hc' with ⟨z, hz, rfl⟩
        exact not_lt_of_ge <|
          le_trans
            (sign_usesAtMostMaxAttemptsQueries
              (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
              (msg := msg) (maxAttempts := maxAttempts) z hz)
            (Nat.le_of_not_lt hi)
    rw [hzero]
    exact zero_le _

/-- The expected number of signing queries is bounded by the infinite geometric series generated by
the single-attempt abort probability. -/
theorem sign_expectedQueries_le_tsum_signAttemptAbortProbability_powers
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤
      ∑' i : ℕ, (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
  letI : HasEvalSPMF m := HasEvalPMF.toHasEvalSPMF
  letI : HasEvalSet m := HasEvalSPMF.toHasEvalSet
  exact HasQuery.expectedQueries_le_tsum_of_tail_probs_le
    (oa := fun [HasQuery (M × W' →ₒ C) (AddWriterT ℕ m)] =>
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
    (runtime := runtime)
    (a := fun i ↦ (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i)
    (fun i ↦ sign_queryTailProbability_le_signAttemptAbortProbability_pow
      (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
      (msg := msg) (i := i) (maxAttempts := maxAttempts))

/-- If the single-attempt abort probability is bounded by `q`, then the expected number of signing
queries is bounded by the corresponding geometric series. -/
theorem sign_expectedQueries_le_geometric_of_signAttemptAbortProbability_le
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (maxAttempts : ℕ) {q : ENNReal}
    (hq : signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg ≤ q) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤
      (1 - q)⁻¹ := by
  calc
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤
      ∑' i : ℕ, (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
          exact sign_expectedQueries_le_tsum_signAttemptAbortProbability_powers
            (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
            (msg := msg) (maxAttempts := maxAttempts)
    _ ≤ ∑' i : ℕ, q ^ i := by
          refine ENNReal.tsum_le_tsum fun i ↦ ?_
          exact ENNReal.pow_le_pow_left hq
    _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q

/-- Specializing the geometric upper bound to the actual one-step abort probability yields the
canonical infinite geometric upper bound on expected query count. -/
theorem sign_expectedQueries_le_geometric
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤
      (1 - signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg)⁻¹ := by
  exact sign_expectedQueries_le_geometric_of_signAttemptAbortProbability_le
    (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
    (msg := msg) (maxAttempts := maxAttempts) le_rfl

/-- Verification has expected weighted query cost equal to the cost of the single verification
query when a signature is present, and `0` when the signature is `none`. -/
theorem verify_expectedQueryCost_eq
    {ω : Type} [AddMonoid ω] [Preorder ω]
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (msg : M) (sig : Option (W' × Z))
    (costFn : M × W' → ω) (val : ω → ENNReal) (hval : Monotone val) (maxAttempts : ℕ) :
    ExpectedQueryCost[
      (FiatShamirWithAbort ids hr M maxAttempts).verify pk msg sig in runtime by costFn via val
    ] =
      match sig with
      | none => val 0
      | some (w', _) => val (costFn (msg, w')) := by
  cases sig with
  | none =>
      letI : DecidableEq ω := Classical.decEq ω
      simp [FiatShamirWithAbort, HasQuery.expectedQueryCost, AddWriterT.expectedCost,
        HasQuery.withAddCost]
  | some pair =>
      rcases pair with ⟨w', z⟩
      exact HasQuery.expectedQueryCost_eq_of_usesCostExactly
        (by
          change Cost[
            HasQuery.withAddCost
              (fun [HasQuery (M × W' →ₒ C) (AddWriterT ω m)] =>
                (FiatShamirWithAbort (m := AddWriterT ω m) ids hr M maxAttempts).verify pk msg
                  (some (w', z)))
              runtime costFn
          ] = costFn (msg, w')
          rw [AddWriterT.hasCost_iff]
          simp [FiatShamirWithAbort, HasQuery.withAddCost, QueryRuntime.withAddCost_impl,
            AddWriterT.outputs, AddWriterT.costs, AddWriterT.addTell])
        hval

end schemeCost

end expectedCostPMF

section EUF_CMA

variable [SampleableType S] [SampleableType W]
variable [DecidableEq W'] [SampleableType C]
variable (ids : IdenSchemeWithAbort S W W' St C Z p)
  (hr : GenerableRelation S W p)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

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
    (euf_cma_bound (ids := ids) (M := M) (maxAttempts := maxAttempts)
      (hc := hc) (sim := sim) (ζ_zk := 0) (hζ := le_rfl)
      (hhvzk := (IdenSchemeWithAbort.perfectHVZK_iff_hvzk_zero ids sim).mp hhvzk)
      (recover := recover) (hcr := hcr) (adv := adv)
      (qS := qS) (qH := qH) (ε := ε) (p_abort := p_abort) (δ := δ) (hp := hp)
      (hQ := hQ))

end EUF_CMA

end FiatShamirWithAbort
