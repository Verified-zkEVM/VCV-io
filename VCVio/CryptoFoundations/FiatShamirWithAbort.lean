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

section signAttemptCore

variable (ids : IdenSchemeWithAbort S W W' St C Z p) (M : Type)

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]
variable {ω : Type} [AddMonoid ω]

private lemma fst_map_signAttempt_core
    (runtime : QueryRuntime (M × W' →ₒ C) m) (pk : S) (sk : W) (msg : M) :
    (do
      let a ← WriterT.run (monadLift (ids.commit pk sk) : AddWriterT ω m (W' × St))
      let c ← runtime.impl (msg, a.1.1)
      (fun z : Option Z × Multiplicative ω => (a.1.1, z.1)) <$>
        WriterT.run (monadLift (ids.respond pk sk a.1.2 c) : AddWriterT ω m (Option Z))) =
    (do
      let a ← (monadLift (ids.commit pk sk) : m (W' × St))
      let c ← runtime.impl (msg, a.1)
      Prod.mk a.1 <$> (monadLift (ids.respond pk sk a.2 c) : m (Option Z))) := by
  change (do
      let a ← WriterT.run (monadLift ((monadLift (ids.commit pk sk) : m (W' × St))) :
        AddWriterT ω m (W' × St))
      let c ← runtime.impl (msg, a.1.1)
      (fun z : Option Z × Multiplicative ω => (a.1.1, z.1)) <$>
        WriterT.run
          (monadLift ((monadLift (ids.respond pk sk a.1.2 c) : m (Option Z))) :
            AddWriterT ω m (Option Z))) =
    (do
      let a ← (monadLift (ids.commit pk sk) : m (W' × St))
      let c ← runtime.impl (msg, a.1)
      Prod.mk a.1 <$> (monadLift (ids.respond pk sk a.2 c) : m (Option Z)))
  simp [bind_map_left]

private lemma snd_map_signAttempt_core_withAddCost
    (runtime : QueryRuntime (M × W' →ₒ C) m) (costFn : M × W' → ω)
    (pk : S) (sk : W) (msg : M) :
    (do
      let a ← WriterT.run (monadLift (ids.commit pk sk) : AddWriterT ω m (W' × St))
      let c ← runtime.impl (msg, a.1.1)
      (fun z : Option Z × Multiplicative ω =>
        a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2)) <$>
        WriterT.run (monadLift (ids.respond pk sk a.1.2 c) : AddWriterT ω m (Option Z))) =
    (do
      let a ← (monadLift (ids.commit pk sk) : m (W' × St))
      let c ← runtime.impl (msg, a.1)
      (fun _ ↦ Multiplicative.ofAdd (costFn (msg, a.1))) <$>
        (monadLift (ids.respond pk sk a.2 c) : m (Option Z))) := by
  change (do
      let a ← WriterT.run (monadLift ((monadLift (ids.commit pk sk) : m (W' × St))) :
        AddWriterT ω m (W' × St))
      let c ← runtime.impl (msg, a.1.1)
      (fun z : Option Z × Multiplicative ω =>
        a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2)) <$>
        WriterT.run
          (monadLift ((monadLift (ids.respond pk sk a.1.2 c) : m (Option Z))) :
            AddWriterT ω m (Option Z))) =
    (do
      let a ← (monadLift (ids.commit pk sk) : m (W' × St))
      let c ← runtime.impl (msg, a.1)
      (fun _ ↦ Multiplicative.ofAdd (costFn (msg, a.1))) <$>
        (monadLift (ids.respond pk sk a.2 c) : m (Option Z)))
  simp [bind_map_left]

end signAttemptCore

section costAccounting

variable (ids : IdenSchemeWithAbort S W W' St C Z p) (M : Type)

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

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
  suffices h :
      (do
        let a ← WriterT.run (monadLift (ids.commit pk sk) : AddWriterT ω m (W' × St))
        let c ← runtime.impl (msg, a.1.1)
        (fun z : Option Z × Multiplicative ω => (a.1.1, z.1)) <$>
          WriterT.run (monadLift (ids.respond pk sk a.1.2 c) : AddWriterT ω m (Option Z))) =
      (do
        let a ← (monadLift (ids.commit pk sk) : m (W' × St))
        let c ← runtime.impl (msg, a.1)
        Prod.mk a.1 <$> (monadLift (ids.respond pk sk a.2 c) : m (Option Z))) by
    simpa [HasQuery.inRuntime, HasQuery.withAddCost, fsAbortSignAttempt, AddWriterT.outputs,
      QueryRuntime.withAddCost_impl, AddWriterT.addTell]
      using h
  exact fst_map_signAttempt_core
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)

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
  suffices h :
      (do
        let a ← WriterT.run (monadLift (ids.commit pk sk) : AddWriterT ω m (W' × St))
        let c ← runtime.impl (msg, a.1.1)
        (fun z : Option Z × Multiplicative ω =>
          a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2)) <$>
          WriterT.run (monadLift (ids.respond pk sk a.1.2 c) : AddWriterT ω m (Option Z))) =
      (do
        let a ← (monadLift (ids.commit pk sk) : m (W' × St))
        let c ← runtime.impl (msg, a.1)
        (fun _ ↦ Multiplicative.ofAdd (costFn (msg, a.1))) <$>
          (monadLift (ids.respond pk sk a.2 c) : m (Option Z))) by
    simpa [HasQuery.inRuntime, HasQuery.withAddCost, fsAbortSignAttempt, AddWriterT.costs,
      QueryRuntime.withAddCost_impl, AddWriterT.addTell]
      using h
  exact snd_map_signAttempt_core_withAddCost
    (ids := ids) (M := M) (runtime := runtime) (costFn := costFn)
    (pk := pk) (sk := sk) (msg := msg)

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

section expectedCostPMF

variable [HasEvalPMF m]

section schemeCost

variable [SampleableType S] [SampleableType W]
variable (hr : GenerableRelation S W p)

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

end costAccounting

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
