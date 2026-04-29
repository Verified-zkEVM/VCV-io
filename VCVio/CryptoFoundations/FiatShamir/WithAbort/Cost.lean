/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort
import VCVio.OracleComp.QueryTracking.QueryCost

/-!
# Cost accounting for Fiat-Shamir with aborts

Exact per-query-class cost accounting for `fsAbortSignLoop` and
`FiatShamirWithAbort.sign`/`verify`. Each lemma characterises the weighted
query cost or the number of hash queries made by one signing/verification
invocation; the expected-value versions live in
`FiatShamir.WithAbort.ExpectedCost`.
-/

universe u v

open OracleComp OracleSpec
open scoped BigOperators

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section costAccounting

variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel) (M : Type)

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

private lemma signAttempt_run_formula_withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) :
    WriterT.run
        (HasQuery.Program.withAddCost
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
            fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
          runtime costFn) =
      (fun attempt : Commit × Option Resp =>
        (attempt, Multiplicative.ofAdd (costFn (msg, attempt.1)))) <$>
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime := by
  suffices h :
      (do
        let a ← WriterT.run (monadLift (ids.commit pk sk) : AddWriterT ω m (Commit × PrvState))
        let c ← runtime (msg, a.1.1)
        let z ← WriterT.run (monadLift (ids.respond pk sk a.1.2 c) : AddWriterT ω m (Option Resp))
        pure ((a.1.1, z.1), a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2))) =
      (do
        let a ← (monadLift (ids.commit pk sk) : m (Commit × PrvState))
        let c ← runtime (msg, a.1)
        let z ← (monadLift (ids.respond pk sk a.2 c) : m (Option Resp))
        pure ((a.1, z), Multiplicative.ofAdd (costFn (msg, a.1)))) by
    simpa [HasQuery.Program.eval, HasQuery.Program.withAddCost, fsAbortSignAttempt,
      QueryImpl.withAddCost_apply, AddWriterT.addTell] using h
  change (do
      let a ← WriterT.run (monadLift ((monadLift (ids.commit pk sk) : m (Commit × PrvState))) :
        AddWriterT ω m (Commit × PrvState))
      let c ← runtime (msg, a.1.1)
      let z ← WriterT.run (monadLift ((monadLift (ids.respond pk sk a.1.2 c) : m (Option Resp))) :
        AddWriterT ω m (Option Resp))
      pure ((a.1.1, z.1), a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2))) = _
  simp [bind_map_left]

private lemma signAttempt_outputs_formula_withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) :
    AddWriterT.outputs
        (HasQuery.Program.withAddCost
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
            fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
          runtime costFn) =
      HasQuery.Program.eval
        (fun [HasQuery (M × Commit →ₒ Chal) m] =>
          fsAbortSignAttempt (m := m) ids M pk sk msg)
        runtime := by
  rw [AddWriterT.outputs, signAttempt_run_formula_withAddCost, Functor.map_map]
  simp

private lemma signAttempt_costs_formula_withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) :
    AddWriterT.costs
        (HasQuery.Program.withAddCost
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
            fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
          runtime costFn) =
      (fun attempt ↦ costFn (msg, attempt.1)) <$>
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime := by
  simp only [AddWriterT.costs, signAttempt_run_formula_withAddCost, Functor.map_map,
    toAdd_ofAdd]

lemma signAttempt_run_formula_withUnitCost
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) :
    WriterT.run
        (HasQuery.Program.withUnitCost
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
            fsAbortSignAttempt (m := AddWriterT ℕ m) ids M pk sk msg)
          runtime) =
      (fun attempt : Commit × Option Resp => (attempt, Multiplicative.ofAdd 1)) <$>
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime := by
  simpa [HasQuery.Program.withUnitCost] using
    signAttempt_run_formula_withAddCost
      (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
      (costFn := fun _ ↦ (1 : ℕ))

/-- A single signing attempt has query cost determined by its output: the returned commitment
`w'` is exactly the random-oracle query point. -/
theorem signAttempt_usesCostAsQueryCost {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) :
    HasQuery.UsesCostAs
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) (val : ω → ENNReal) :
    ExpectedQueryCost[
      fsAbortSignAttempt ids M pk sk msg in runtime by costFn via val
    ] =
      ∑' attempt : Commit × Option Resp,
        Pr[= attempt | HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime] * val (costFn (msg, attempt.1)) := by
  calc
    ExpectedQueryCost[
      fsAbortSignAttempt ids M pk sk msg in runtime by costFn via val
    ] =
      ∑' attempt : Commit × Option Resp,
        Pr[= attempt | AddWriterT.outputs
          (HasQuery.Program.withAddCost
            (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
              fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
            runtime costFn)] * val (costFn (msg, attempt.1)) := by
          exact HasQuery.expectedQueryCost_eq_tsum_outputs_of_usesCostAs
            (oa := fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
              fsAbortSignAttempt (m := AddWriterT ω m) ids M pk sk msg)
            (runtime := runtime) (costFn := costFn) (f := fun attempt ↦ costFn (msg, attempt.1))
            (val := val)
            (signAttempt_usesCostAsQueryCost
              (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
              (msg := msg) (costFn := costFn))
    _ = ∑' attempt : Commit × Option Resp,
          Pr[= attempt | HasQuery.Program.eval
            (fun [HasQuery (M × Commit →ₒ Chal) m] =>
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → κ) (w : κ) (hcost : ∀ t, costFn t ≤ w) :
    HasQuery.UsesCostAtMost
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT κ m)] =>
        fsAbortSignAttempt (m := AddWriterT κ m) ids M pk sk msg)
      runtime costFn w := by
  change AddWriterT.PathwiseCostAtMost
    (do
      let a ←
        (monadLift (ids.commit pk sk : ProbComp (Commit × PrvState)) :
          AddWriterT κ m (Commit × PrvState))
      let c ← (runtime.withAddCost costFn) (msg, a.1)
      let oz ← (monadLift (ids.respond pk sk a.2 c : ProbComp (Option Resp)) :
        AddWriterT κ m (Option Resp))
      pure (a.1, oz))
    w
  have hCommit :
      AddWriterT.PathwiseCostAtMost
        (monadLift (ids.commit pk sk : ProbComp (Commit × PrvState)) :
          AddWriterT κ m (Commit × PrvState))
        0 :=
    AddWriterT.pathwiseCostAtMost_probCompLift (m := m) (ω := κ) (ids.commit pk sk)
  have hQuery :
      ∀ a : Commit × PrvState,
        AddWriterT.PathwiseCostAtMost ((runtime.withAddCost costFn) (msg, a.1)) w := by
    intro a
    exact AddWriterT.pathwiseCostAtMost_of_hasCost
      (HasQuery.hasCost_withAddCost_query
        (runtime := runtime) (costFn := costFn) (t := (msg, a.1)))
      (hcost (msg, a.1))
  have hRespond :
      ∀ a : Commit × PrvState, ∀ c : Chal,
        AddWriterT.PathwiseCostAtMost
          (monadLift (ids.respond pk sk a.2 c : ProbComp (Option Resp)) :
            AddWriterT κ m (Option Resp))
          0 := by
    intro a c
    exact AddWriterT.pathwiseCostAtMost_probCompLift
      (m := m) (ω := κ) (ids.respond pk sk a.2 c)
  have hPure :
      ∀ a : Commit × PrvState, ∀ oz : Option Resp,
        AddWriterT.PathwiseCostAtMost
          (pure (a.1, oz) : AddWriterT κ m (Commit × Option Resp)) 0 := by
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → κ) (w : κ) (hcost : ∀ t, costFn t ≤ w) :
    ∀ n,
      HasQuery.UsesCostAtMost
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT κ m)] =>
          fsAbortSignLoop (m := AddWriterT κ m) ids M pk sk msg n)
        runtime costFn (n • w)
  | 0 => by
      simpa [HasQuery.UsesCostAtMost, HasQuery.Program.withAddCost, fsAbortSignLoop] using
        (AddWriterT.pathwiseCostAtMost_pure
          (m := m) (ω := κ) (x := (none : Option (Commit × Resp))))
  | n + 1 => by
      have hStep := signAttempt_usesWeightedQueryCostAtMost
        (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
        (msg := msg) (costFn := costFn) (w := w) hcost
      have hRec := fsAbortSignLoop_usesWeightedQueryCostAtMost
        (runtime := runtime) (pk := pk) (sk := sk)
        (msg := msg) (costFn := costFn) (w := w) hcost n
      let cont : Commit × Option Resp → AddWriterT κ m (Option (Commit × Resp)) := fun attempt =>
        match attempt.2 with
        | some z => pure (some (attempt.1, z))
        | none =>
            HasQuery.Program.withAddCost
              (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT κ m)] =>
                fsAbortSignLoop (m := AddWriterT κ m) ids M pk sk msg n)
              runtime costFn
      have hCont : ∀ attempt, AddWriterT.PathwiseCostAtMost (cont attempt) (n • w) := by
        intro attempt
        cases hAttempt : attempt.2 with
        | some z =>
            simpa only [cont, hAttempt] using
              (AddWriterT.pathwiseCostAtMost_mono
                (AddWriterT.pathwiseCostAtMost_pure
                  (m := m) (ω := κ) (x := (some (attempt.1, z) : Option (Commit × Resp))))
                (zero_le _))
        | none =>
            simpa [cont, hAttempt, HasQuery.UsesCostAtMost] using hRec
      simpa [HasQuery.UsesCostAtMost, HasQuery.Program.withAddCost, fsAbortSignLoop, succ_nsmul',
        fsAbortSignAttempt, cont] using
        (AddWriterT.pathwiseCostAtMost_bind (w₁ := w) (w₂ := n • w) hStep hCont)

section schemeCost

variable (hr : GenerableRelation Stmt Wit rel)

/-- Signing makes weighted query cost at most `maxAttempts • w` when each query costs at most
`w`. -/
theorem sign_usesWeightedQueryCostAtMost
    {κ : Type} [AddCommMonoid κ] [PartialOrder κ] [IsOrderedAddMonoid κ]
    [CanonicallyOrderedAdd κ]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → κ) (w : κ) (hcost : ∀ t, costFn t ≤ w) (maxAttempts : ℕ) :
    QueryCost[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime by costFn
    ] ≤ maxAttempts • w := by
  change HasQuery.UsesCostAtMost
    (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT κ m)] =>
      fsAbortSignLoop (m := AddWriterT κ m) ids M pk sk msg maxAttempts)
    runtime costFn (maxAttempts • w)
  exact fsAbortSignLoop_usesWeightedQueryCostAtMost
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
    (costFn := costFn) (w := w) hcost maxAttempts

/-- Unit-cost specialization: signing makes at most `maxAttempts` random-oracle queries. -/
theorem sign_usesAtMostMaxAttemptsQueries
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
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

variable (hr : GenerableRelation Stmt Wit rel)

/-- Tail-sum formula for the expected number of signing queries in Fiat-Shamir with aborts.

The random variable on the right is the unit-cost query count of the signer. The event `i < q`
means that the signer performed at least `i + 1` random-oracle queries, equivalently that the
`(i + 1)`-st signing attempt was reached. Since the signer performs at most `maxAttempts`
iterations, the infinite tail sum truncates to `Finset.range maxAttempts`. -/
theorem sign_expectedQueries_eq_sum_reachedAttemptProbabilities
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] =
      ∑ i ∈ Finset.range maxAttempts,
        Pr[ fun q ↦ i < q |
          HasQuery.queryCountDist
            (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
              (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
            runtime] := by
  letI : HasEvalSet m := HasEvalSPMF.toHasEvalSet
  exact HasQuery.expectedQueries_eq_sum_tail_probs_of_usesAtMostQueries
    (oa := fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → κ) (w : κ) (val : κ → ENNReal)
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
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

end FiatShamirWithAbort
