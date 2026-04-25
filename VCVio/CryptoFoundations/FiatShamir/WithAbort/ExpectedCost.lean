/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort.Cost
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Expected-cost PMF theorems for Fiat-Shamir with aborts

Expected random-oracle query costs of `fsAbortSignLoop` and
`FiatShamirWithAbort.sign`/`verify`, stated as `tsum` identities over the
induced output distributions. These drive the aggregate runtime bounds used
in the security proof.
-/

universe u v

open OracleComp OracleSpec
open scoped BigOperators

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section expectedCostPMF

variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel) (M : Type)

variable {m : Type → Type u} [Monad m] [MonadLiftT ProbComp m]

private lemma signLoop_inRuntime_succ
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ) :
    HasQuery.Program.eval
      (fun [HasQuery (M × Commit →ₒ Chal) m] =>
        fsAbortSignLoop (m := m) ids M pk sk msg (n + 1))
      runtime
    =
      (do
        let attempt ← HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime
        match attempt.2 with
        | some z => pure (some (attempt.1, z))
        | none =>
            HasQuery.Program.eval
              (fun [HasQuery (M × Commit →ₒ Chal) m] =>
                fsAbortSignLoop (m := m) ids M pk sk msg n)
              runtime) := by
  rfl

section

variable [LawfulMonad m]

private lemma signLoop_queryCountDist_succ
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ) :
    HasQuery.queryCountDist
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1))
      runtime
    =
      (do
        let attempt ← HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime
        match attempt.2 with
        | some _ => pure 1
        | none =>
            let recCosts :=
              HasQuery.queryCountDist
                (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
                  fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
                runtime
            Nat.succ <$> recCosts) := by
  change AddWriterT.costs
      (do
        let attempt ← HasQuery.Program.withUnitCost
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
            fsAbortSignAttempt (m := AddWriterT ℕ m) ids M pk sk msg)
          runtime
        match attempt.2 with
        | some z => pure (some (attempt.1, z))
        | none =>
            HasQuery.Program.withUnitCost
              (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
                fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
              runtime) = _
  rw [AddWriterT.costs_def, WriterT.run_bind]
  rw [signAttempt_run_formula_withUnitCost
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)]
  simp only [bind_map_left, map_bind, Functor.map_map, toAdd_mul, toAdd_ofAdd]
  refine bind_congr (m := m) ?_
  intro attempt
  cases attempt.2 with
  | some z =>
      simp
  | none =>
      simp [HasQuery.queryCountDist, HasQuery.queryCostDist, HasQuery.Program.withUnitCost,
        HasQuery.Program.withAddCost, AddWriterT.costs, add_comm]
      rfl

end

variable [HasEvalPMF m]

/-- The probability that a single Fiat-Shamir-with-aborts signing attempt aborts. -/
noncomputable abbrev signAttemptAbortProbability
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) : ENNReal :=
  Pr[ fun attempt ↦ attempt.2 = none |
    HasQuery.Program.eval
      (fun [HasQuery (M × Commit →ₒ Chal) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime]

private lemma signLoop_probNone_succ
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ) :
    Pr[= none |
      HasQuery.Program.eval
        (fun [HasQuery (M × Commit →ₒ Chal) m] =>
          fsAbortSignLoop (m := m) ids M pk sk msg (n + 1))
        runtime] =
      Pr[ fun attempt ↦ attempt.2 = none |
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime] *
      Pr[= none |
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg n)
          runtime] := by
  set attemptComp : m (Commit × Option Resp) :=
    HasQuery.Program.eval
      (fun [HasQuery (M × Commit →ₒ Chal) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime
  set recLoop : m (Option (Commit × Resp)) :=
    HasQuery.Program.eval
      (fun [HasQuery (M × Commit →ₒ Chal) m] =>
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
    ∑' attempt : Commit × Option Resp,
        Pr[= attempt | attemptComp] *
          Pr[= none |
            match attempt.2 with
            | some z => pure (some (attempt.1, z))
            | none => recLoop]
      = ∑' attempt : Commit × Option Resp,
          Pr[= attempt | attemptComp] *
            (if attempt.2 = none then Pr[= none | recLoop] else 0) := by
              refine tsum_congr fun attempt => ?_
              cases hAttempt : attempt.2 with
              | some z =>
                  simp
              | none =>
                  simp
    _ = ∑' attempt : Commit × Option Resp,
          (if attempt.2 = none then Pr[= attempt | attemptComp] else 0) * Pr[= none | recLoop] := by
            refine tsum_congr fun attempt => ?_
            by_cases hAttempt : attempt.2 = none <;> simp [hAttempt, mul_comm]
    _ =
      (∑' attempt : Commit × Option Resp,
          if attempt.2 = none then Pr[= attempt | attemptComp] else 0)
        * Pr[= none | recLoop] := by
            rw [ENNReal.tsum_mul_right]
    _ = Pr[ fun attempt ↦ attempt.2 = none | attemptComp] * Pr[= none | recLoop] := by
            simp [probEvent_eq_tsum_indicator, Set.indicator, Set.mem_setOf_eq]

section

variable [LawfulMonad m]

private lemma signLoop_queryTailProbability_zero
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ) :
    Pr[ fun q ↦ 0 < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
          fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1))
        runtime] = 1 := by
  set attemptComp : m (Commit × Option Resp) :=
    HasQuery.Program.eval
      (fun [HasQuery (M × Commit →ₒ Chal) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime
  set recCosts : m ℕ :=
    HasQuery.queryCountDist (m := m)
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (i n : ℕ) :
    Pr[ fun q ↦ i + 1 < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
          fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1))
        runtime] =
      Pr[ fun attempt ↦ attempt.2 = none |
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignAttempt (m := m) ids M pk sk msg)
          runtime] *
      Pr[ fun q ↦ i < q |
        HasQuery.queryCountDist
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
            fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
          runtime] := by
  set attemptComp : m (Commit × Option Resp) :=
    HasQuery.Program.eval
      (fun [HasQuery (M × Commit →ₒ Chal) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime
  set recCosts : m ℕ :=
    HasQuery.queryCountDist (m := m)
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
      runtime
  let cont : Commit × Option Resp → m ℕ := fun attempt =>
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
    ∑' attempt : Commit × Option Resp,
        Pr[= attempt | attemptComp] * Pr[ fun q ↦ i + 1 < q | cont attempt]
      = ∑' attempt : Commit × Option Resp,
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
    _ = ∑' attempt : Commit × Option Resp,
          (if attempt.2 = none then Pr[= attempt | attemptComp] else 0) *
            Pr[ fun q ↦ i < q | recCosts] := by
              refine tsum_congr fun attempt => ?_
              by_cases hAttempt : attempt.2 = none <;> simp [hAttempt, mul_comm]
    _ =
      (∑' attempt : Commit × Option Resp,
          if attempt.2 = none then Pr[= attempt | attemptComp] else 0)
        * Pr[ fun q ↦ i < q | recCosts] := by
            rw [ENNReal.tsum_mul_right]
    _ = Pr[ fun attempt ↦ attempt.2 = none | attemptComp] *
          Pr[ fun q ↦ i < q | recCosts] := by
            simp [probEvent_eq_tsum_indicator, Set.indicator, Set.mem_setOf_eq]

private theorem signLoop_queryTailProbability_eq_probNonePrefix
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ i extra,
      Pr[ fun q ↦ i < q |
        HasQuery.queryCountDist
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
            fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + extra + 1))
          runtime] =
      Pr[= none |
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime]
  | 0, extra => by
      have hzero :
          Pr[ fun q ↦ 0 < q |
            HasQuery.queryCountDist
              (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
                fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (0 + extra + 1))
              runtime] = 1 := by
        simpa [Nat.zero_add] using
          signLoop_queryTailProbability_zero
            (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
            (msg := msg) (n := extra)
      calc
        Pr[ fun q ↦ 0 < q |
          HasQuery.queryCountDist
            (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
              fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (0 + extra + 1))
            runtime] = 1 := hzero
      _ = Pr[= none |
            HasQuery.Program.eval
              (fun [HasQuery (M × Commit →ₒ Chal) m] =>
                fsAbortSignLoop (m := m) ids M pk sk msg 0)
              runtime] := by
            simp [HasQuery.Program.eval, fsAbortSignLoop]
  | i + 1, extra => by
      have hstep :
          Pr[ fun q ↦ i + 1 < q |
            HasQuery.queryCountDist
              (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
                fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + 1 + extra + 1))
              runtime] =
            Pr[ fun attempt ↦ attempt.2 = none |
              HasQuery.Program.eval
                (fun [HasQuery (M × Commit →ₒ Chal) m] =>
                  fsAbortSignAttempt (m := m) ids M pk sk msg)
                runtime] *
            Pr[ fun q ↦ i < q |
              HasQuery.queryCountDist
                (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
                  fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + extra + 1))
                runtime] := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          signLoop_queryTailProbability_succ
            (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
            (msg := msg) (i := i) (n := i + extra + 1)
      calc
        Pr[ fun q ↦ i + 1 < q |
          HasQuery.queryCountDist
            (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
              fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + 1 + extra + 1))
            runtime]
          =
            Pr[ fun attempt ↦ attempt.2 = none |
              HasQuery.Program.eval
                (fun [HasQuery (M × Commit →ₒ Chal) m] =>
                  fsAbortSignAttempt (m := m) ids M pk sk msg)
                runtime] *
            Pr[ fun q ↦ i < q |
              HasQuery.queryCountDist
                (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
                  fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + extra + 1))
                runtime] := hstep
        _ =
            Pr[ fun attempt ↦ attempt.2 = none |
              HasQuery.Program.eval
                (fun [HasQuery (M × Commit →ₒ Chal) m] =>
                  fsAbortSignAttempt (m := m) ids M pk sk msg)
                runtime] *
            Pr[= none |
              HasQuery.Program.eval
                (fun [HasQuery (M × Commit →ₒ Chal) m] =>
                  fsAbortSignLoop (m := m) ids M pk sk msg i)
                runtime] := by
                  rw [signLoop_queryTailProbability_eq_probNonePrefix
                    (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
                    (i := i) (extra := extra)]
        _ = Pr[= none |
              HasQuery.Program.eval
                (fun [HasQuery (M × Commit →ₒ Chal) m] =>
                  fsAbortSignLoop (m := m) ids M pk sk msg (i + 1))
                runtime] := by
                  symm
                  simpa using
                    signLoop_probNone_succ
                      (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
                      (msg := msg) (n := i)

end

private theorem signLoop_probNone_eq_signAttemptAbortProbability_pow
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ i,
      Pr[= none |
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime] =
        (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i
  | 0 => by
      simp [signAttemptAbortProbability, HasQuery.Program.eval, fsAbortSignLoop]
  | i + 1 => by
      calc
        Pr[= none |
          HasQuery.Program.eval
            (fun [HasQuery (M × Commit →ₒ Chal) m] =>
              fsAbortSignLoop (m := m) ids M pk sk msg (i + 1))
            runtime] =
          signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg *
            Pr[= none |
              HasQuery.Program.eval
                (fun [HasQuery (M × Commit →ₒ Chal) m] =>
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) (i : ℕ) :
    Pr[= none |
      HasQuery.Program.eval
        (fun [HasQuery (M × Commit →ₒ Chal) m] =>
          fsAbortSignLoop (m := m) ids M pk sk msg i)
        runtime] =
      (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
  exact signLoop_probNone_eq_signAttemptAbortProbability_pow
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) i

end

variable [LawfulMonad m]

section schemeCost

variable (hr : GenerableRelation Stmt Wit rel)

/-- The probability that signing makes more than `i` random-oracle queries is exactly the
probability that the first `i` signing attempts all abort.

Equivalently, the event `i < q` for the signer query count is the event that the retry loop of
length `i` returns `none`, meaning that the `(i + 1)`-st attempt is reached. -/
theorem sign_queryTailProbability_eq_probAllFirstAttemptsAbort
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    {i maxAttempts : ℕ} (hi : i < maxAttempts) :
    Pr[ fun q ↦ i < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
          (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
        runtime] =
      Pr[= none |
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime] := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_lt hi
  change Pr[ fun q ↦ i < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
          fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + extra + 1))
        runtime] =
      Pr[= none |
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime]
  exact signLoop_queryTailProbability_eq_probNonePrefix
    (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)
    (i := i) (extra := extra)

/-- The probability that signing makes more than `i` oracle queries is the `i`-th power of the
single-attempt abort probability, as long as `i < maxAttempts`. -/
theorem sign_queryTailProbability_eq_signAttemptAbortProbability_pow
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    {i maxAttempts : ℕ} (hi : i < maxAttempts) :
    Pr[ fun q ↦ i < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] =
      ∑ i ∈ Finset.range maxAttempts,
        Pr[= none |
          HasQuery.Program.eval
            (fun [HasQuery (M × Commit →ₒ Chal) m] =>
              fsAbortSignLoop (m := m) ids M pk sk msg i)
            runtime] := by
  calc
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] =
      ∑ i ∈ Finset.range maxAttempts,
        Pr[ fun q ↦ i < q |
          HasQuery.queryCountDist
            (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
              (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
            runtime] := by
              exact sign_expectedQueries_eq_sum_reachedAttemptProbabilities
                (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
                (msg := msg) (maxAttempts := maxAttempts)
    _ = ∑ i ∈ Finset.range maxAttempts,
          Pr[= none |
            HasQuery.Program.eval
              (fun [HasQuery (M × Commit →ₒ Chal) m] =>
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
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
          HasQuery.Program.eval
            (fun [HasQuery (M × Commit →ₒ Chal) m] =>
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (i maxAttempts : ℕ) :
    Pr[ fun q ↦ i < q |
      HasQuery.queryCountDist
        (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
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
            (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
              (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
            runtime] = 0 := by
        refine probEvent_eq_zero ?_
        intro c hc
        have hc' : c ∈ support
            (AddWriterT.costs
              (HasQuery.Program.withUnitCost
                (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
                  (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
                runtime)) := by
          simpa [HasQuery.queryCountDist, HasQuery.queryCostDist, HasQuery.Program.withUnitCost,
            HasQuery.Program.withAddCost] using hc
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (maxAttempts : ℕ) :
    ExpectedQueries[
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg in runtime
    ] ≤
      ∑' i : ℕ, (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i := by
  letI : HasEvalSPMF m := HasEvalPMF.toHasEvalSPMF
  letI : HasEvalSet m := HasEvalSPMF.toHasEvalSet
  exact HasQuery.expectedQueries_le_tsum_of_tail_probs_le
    (oa := fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
      (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
    (runtime := runtime)
    (a := fun i ↦ (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i)
    (fun i ↦ sign_queryTailProbability_le_signAttemptAbortProbability_pow
      (ids := ids) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
      (msg := msg) (i := i) (maxAttempts := maxAttempts))

/-- If the single-attempt abort probability is bounded by `q`, then the expected number of signing
queries is bounded by the corresponding geometric series. -/
theorem sign_expectedQueries_le_geometric_of_signAttemptAbortProbability_le
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
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
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (msg : M)
    (sig : Option (Commit × Resp))
    (costFn : M × Commit → ω) (val : ω → ENNReal) (hval : Monotone val) (maxAttempts : ℕ) :
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
        HasQuery.Program.withAddCost]
  | some pair =>
      rcases pair with ⟨w', z⟩
      exact HasQuery.expectedQueryCost_eq_of_usesCostExactly
        (by
          change Cost[
            HasQuery.Program.withAddCost
              (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
                (FiatShamirWithAbort (m := AddWriterT ω m) ids hr M maxAttempts).verify pk msg
                  (some (w', z)))
              runtime costFn
          ] = costFn (msg, w')
          rw [AddWriterT.hasCost_iff]
          simp [FiatShamirWithAbort, HasQuery.Program.withAddCost, QueryImpl.withAddCost_apply,
            AddWriterT.outputs, AddWriterT.costs, AddWriterT.addTell])
        hval

end schemeCost

end expectedCostPMF

end FiatShamirWithAbort
