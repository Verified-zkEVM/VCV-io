/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.IdenSchemeWithAbort
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.HasQuery.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Fiat-Shamir-with-aborts transform

Signing variant of Fiat-Shamir used by lattice schemes such as ML-DSA. On
input `(pk, sk, msg)` the prover runs a commit-hash-respond loop up to
`maxAttempts` times, returning the first non-aborting transcript or `none`
if every attempt aborts.

This file holds the scheme definition, the random-oracle runtime bundle, and
the core cache invariant that drives the correctness proof. Cost-accounting
lemmas, expected-cost PMFs, and the EUF-CMA security statement live in the
`FiatShamir.WithAbort.Cost`, `FiatShamir.WithAbort.ExpectedCost`, and
`FiatShamir.WithAbort.Security` submodules.

## References

- Barbosa et al., *Fixing and Mechanizing the Security Proof of Fiat-Shamir
  with Aborts and Dilithium*, CRYPTO 2023 (ePrint 2023/246)
- EasyCrypt `FSabort.eca`, `SimplifiedScheme.ec`
- NIST FIPS 204, Algorithms 2 (ML-DSA.Sign) and 3 (ML-DSA.Verify)
-/

universe u v

open OracleComp OracleSpec
open scoped BigOperators

variable {Stmt Wit Commit PrvState Chal Resp : Type}
  {rel : Stmt → Wit → Bool}

/-- One signing attempt for the Fiat-Shamir-with-aborts transform.

This performs a single commit-hash-respond cycle and returns the public commitment together with
either a response or an abort marker. Unlike [`fsAbortSignLoop`], it never retries internally. -/
def fsAbortSignAttempt (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    {m : Type → Type v} [Monad m]
    (M : Type) [MonadLiftT ProbComp m] [HasQuery (M × Commit →ₒ Chal) m]
    (pk : Stmt) (sk : Wit) (msg : M) :
    m (Commit × Option Resp) := do
  let (w', st) ← (monadLift (ids.commit pk sk : ProbComp _) : m _)
  let c ← HasQuery.query (spec := (M × Commit →ₒ Chal)) (msg, w')
  let oz ← (monadLift (ids.respond pk sk st c : ProbComp _) : m _)
  pure (w', oz)

/-- Signing retry loop with early return for the Fiat-Shamir with aborts transform.

Tries up to `n` commit-hash-respond cycles:
1. Commit to get `(w', st)`
2. Hash `(msg, w')` via the random oracle to get challenge `c`
3. Attempt to respond; if `some z`, return immediately; if `none` (abort), decrement
   the counter and retry.

Returns `none` only when all `n` attempts abort. -/
def fsAbortSignLoop (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    {m : Type → Type v} [Monad m]
    (M : Type) [MonadLiftT ProbComp m] [HasQuery (M × Commit →ₒ Chal) m]
    (pk : Stmt) (sk : Wit) (msg : M) :
    ℕ → m (Option (Commit × Resp))
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
- `Commit`: public commitment (included in signature for verification)
- `Chal`: challenge space (range of the hash/random oracle)
- `Resp`: response space
- `Stmt` / `Wit`: statement / witness (= public key / secret key) -/
def FiatShamirWithAbort
    {m : Type → Type v} [Monad m]
    (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) (M : Type)
    [MonadLiftT ProbComp m] [HasQuery (M × Commit →ₒ Chal) m]
    (maxAttempts : ℕ) :
    SignatureAlg m
      (M := M) (PK := Stmt) (SK := Wit) (S := Option (Commit × Resp)) where
  keygen := monadLift hr.gen
  sign := fun pk sk msg => fsAbortSignLoop ids M pk sk msg maxAttempts
  verify := fun pk msg sig => do
    match sig with
    | none => return false
    | some (w', z) =>
      let c ← HasQuery.query (spec := (M × Commit →ₒ Chal)) (msg, w')
      pure (ids.verify pk w' c z)

namespace FiatShamirWithAbort

section runtime

variable (M : Type) [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]

/-- Runtime bundle for the Fiat-Shamir-with-aborts random-oracle world. -/
noncomputable def runtime :
    ProbCompRuntime (OracleComp (unifSpec + (M × Commit →ₒ Chal))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (M × Commit →ₒ Chal) (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

end runtime

section correctness

variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

omit hr in
variable [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- When the simulated signing loop produces `some (w, z)`, the random-oracle cache
contains a challenge `c` at `(msg, w)` satisfying `ids.verify pk w c z = true`.

This is proved by induction on the loop counter: each abort iteration preserves the
invariant (the cache only grows), and a successful iteration writes exactly the challenge
used in verification. -/
lemma fsAbortSignLoop_cache_invariant
    (ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))
    (hro : ro = randomOracle)
    (hc : ids.Complete) {pk : Stmt} {sk : Wit} (hrel : rel pk sk = true)
    (msg : M) (n : ℕ) (s₀ : (M × Commit →ₒ Chal).QueryCache)
    (w : Commit) (z : Resp) (s : (M × Commit →ₒ Chal).QueryCache)
    (hsup : (some (w, z), s) ∈ support
      ((simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
        (fsAbortSignLoop ids M pk sk msg n)).run s₀)) :
    ∃ c : Chal, s (msg, w) = some c ∧ ids.verify pk w c z = true := by
  subst hro
  set impl := unifFwdImpl (M × Commit →ₒ Chal) +
    (randomOracle : QueryImpl (M × Commit →ₒ Chal) _)
  have hSimQuery : ∀ (q : M × Commit),
      simulateQ impl (HasQuery.query q) =
        (randomOracle : QueryImpl (M × Commit →ₒ Chal) _) q :=
    roSim.simulateQ_HasQuery_query _
  induction n generalizing s₀ with
  | zero =>
    simp [fsAbortSignLoop, simulateQ_pure, StateT.run_pure, support_pure] at hsup
  | succ n ih =>
    simp only [fsAbortSignLoop, simulateQ_bind] at hsup
    rw [StateT.run_bind] at hsup
    obtain ⟨⟨⟨w_a, oz⟩, s₁⟩, h_attempt, h_rest⟩ :=
      (mem_support_bind_iff _ _ _).mp hsup
    cases oz with
    | none => exact ih s₁ (by simpa using h_rest)
    | some z_a =>
      have h_rest' : (some (w, z), s) = (some (w_a, z_a), s₁) := by
        simpa using h_rest
      obtain ⟨h1, hs⟩ := Prod.mk.inj h_rest'
      subst hs
      rw [Option.some.injEq] at h1
      obtain ⟨hw, hz⟩ := Prod.mk.inj h1
      subst hw; subst hz
      simp only [fsAbortSignAttempt, simulateQ_bind,
        hSimQuery, simulateQ_pure] at h_attempt
      rw [StateT.run_bind] at h_attempt
      obtain ⟨⟨⟨w_cm, st⟩, s_cm⟩, h_commit, h2⟩ :=
        (mem_support_bind_iff _ _ _).mp h_attempt
      rw [StateT.run_bind] at h2
      obtain ⟨⟨c_q, s_ro⟩, h_query, h3⟩ :=
        (mem_support_bind_iff _ _ _).mp h2
      rw [StateT.run_bind] at h3
      obtain ⟨⟨oz_r, s_resp⟩, h_respond, h4⟩ :=
        (mem_support_bind_iff _ _ _).mp h3
      simp only [StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at h4
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
      change _ ∈ support ((simulateQ impl
        (liftM (ids.commit pk sk))).run s₀) at h_commit
      rw [roSim.run_liftM, support_map] at h_commit
      obtain ⟨⟨w_c, st_c⟩, h_cm_mem, h_cm_eq⟩ := h_commit
      simp only [Prod.mk.injEq] at h_cm_eq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h_cm_eq
      dsimp only [Prod.fst, Prod.snd] at h_query h_respond
      change _ ∈ support ((simulateQ impl
        (liftM (ids.respond pk sk st_c c_q))).run s_ro) at h_respond
      rw [roSim.run_liftM, support_map] at h_respond
      obtain ⟨resp_val, h_rsp_mem, h_rsp_eq⟩ := h_respond
      simp only [Prod.mk.injEq] at h_rsp_eq
      obtain ⟨h_oz, h_s_eq⟩ := h_rsp_eq
      subst h_s_eq
      refine ⟨c_q, ?_, ?_⟩
      · simp only [randomOracle, QueryImpl.withCaching_apply,
          StateT.run_bind, StateT.run_get, pure_bind] at h_query
        cases hs : s₀ (msg, w_c) with
        | some c_cached =>
          simp only [hs, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at h_query
          rw [h_query.2, hs, h_query.1]
        | none =>
          simp only [hs, StateT.run_bind] at h_query
          obtain ⟨⟨_, _⟩, _, h_cache⟩ :=
            (mem_support_bind_iff _ _ _).mp h_query
          dsimp at h_cache
          obtain ⟨rfl, rfl⟩ := h_cache
          exact QueryCache.cacheQuery_self _ (msg, w_c) c_q
      · apply ids.verify_of_complete hc hrel
        rw [IdenSchemeWithAbort.honestExecution, support_bind]
        refine Set.mem_iUnion₂.mpr ⟨(w_c, st_c), h_cm_mem, ?_⟩
        rw [support_bind]
        refine Set.mem_iUnion₂.mpr ⟨c_q, mem_support_uniformSample _, ?_⟩
        rw [h_oz] at h_rsp_mem
        simp only [support_bind, Set.mem_iUnion₂,
          support_pure, Set.mem_singleton_iff]
        exact ⟨some z, h_rsp_mem, by simp [Option.map]⟩

variable [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- When the random-oracle cache already contains the challenge for `(msg, w)`,
verification of signature `(w, z)` deterministically returns `true`. -/
lemma verify_eq_true_of_cached
    (ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))
    (hro : ro = randomOracle)
    (pk : Stmt) (msg : M) (maxAttempts : ℕ) (w : Commit) (z : Resp)
    (cache : (M × Commit →ₒ Chal).QueryCache)
    (c : Chal) (hcached : cache (msg, w) = some c)
    (hverify : ids.verify pk w c z = true) :
    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
      ((FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts).verify pk msg (some (w, z)))).run' cache =
    (pure true : ProbComp Bool) := by
  subst hro
  simp only [FiatShamirWithAbort, simulateQ_bind,
    roSim.simulateQ_HasQuery_query, simulateQ_pure]
  change Prod.fst <$>
    (((randomOracle : QueryImpl (M × Commit →ₒ Chal) _) (msg, w) >>=
      fun c => pure (ids.verify pk w c z)).run cache) = _
  rw [StateT.run_bind]
  simp only [randomOracle, QueryImpl.withCaching_apply,
    StateT.run_bind, StateT.run_get, monad_norm, hcached,
    StateT.run_pure, hverify, Function.comp_apply]

/-- Correctness of the Fiat-Shamir with aborts signature scheme: the canonical
keygen-sign-verify execution succeeds with probability at least `1 - δ`, where `δ` bounds
the per-key probability that signing aborts (returns `none`).

When the underlying IDS is complete, any non-aborting signature verifies correctly (by RO
consistency and `IdenSchemeWithAbort.verify_of_complete`). So the only source of
verification failure is signing abort, and the completeness error equals the abort probability.

The hypothesis `h_abort` bounds the abort probability for each valid key pair separately.
It can be discharged using `sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow`,
which gives `Pr[sign = none] = signAttemptAbortProbability ^ maxAttempts` for fixed keys.

Unlike the CRYPTO 2023 paper and EasyCrypt formalization (which use an unbounded signing loop
and do not state a correctness theorem), this formulation uses a bounded loop with
`maxAttempts` iterations, matching FIPS 204 Algorithm 7 (ML-DSA.Sign_internal). -/
theorem correct
    [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
    (hc : ids.Complete) (maxAttempts : ℕ) (δ : ENNReal)
    (h_abort : ∀ (pk : Stmt) (sk : Wit), rel pk sk = true →
      ∀ msg : M,
        Pr[= none | (runtime M).evalDist
          ((FiatShamirWithAbort
            (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
            ids hr M maxAttempts).sign pk sk msg)] ≤ δ) :
    SignatureAlg.Complete
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts) (runtime M) δ := by
  intro msg
  open scoped Classical in
  let ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := randomOracle
  let impl := unifFwdImpl (M × Commit →ₒ Chal) + ro
  set sigAlg := FiatShamirWithAbort
    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts
  set signVerify : Stmt → Wit → ProbComp Bool := fun pk sk =>
    StateT.run' (simulateQ impl (do
      let sig ← sigAlg.sign pk sk msg
      sigAlg.verify pk msg sig)) ∅
  set signOnly : Stmt → Wit → ProbComp (Option (Commit × Resp)) := fun pk sk =>
    StateT.run' (simulateQ impl (sigAlg.sign pk sk msg)) ∅
  suffices hRewrite :
      (runtime M).evalDist (do
        let (pk, sk) ← sigAlg.keygen
        let sig ← sigAlg.sign pk sk msg
        sigAlg.verify pk msg sig) =
      𝒟[do
        let (pk, sk) ← hr.gen
        signVerify pk sk] by
    rw [hRewrite]
    apply SignatureAlg.probOutput_bind_ge_of_forall_support
    intro ⟨pk, sk⟩ hmem
    have hrel : rel pk sk = true := hr.gen_sound pk sk hmem
    have habort := h_abort pk sk hrel msg
    have habort' : Pr[= none | 𝒟[signOnly pk sk]] ≤ δ := by
      convert habort using 2
    have hnoFail : Pr[⊥ | signVerify pk sk] = 0 := HasEvalPMF.probFailure_eq_zero _
    rw [show (1 : ENNReal) - δ = 1 - δ from rfl]
    calc
      Pr[= true | signVerify pk sk]
        = 1 - Pr[= false | signVerify pk sk] := by
          rw [probOutput_true_eq_sub, hnoFail, tsub_zero]
      _ ≥ 1 - Pr[= none | 𝒟[signOnly pk sk]] := by
          apply tsub_le_tsub_left _ 1
          set S := (simulateQ impl (sigAlg.sign pk sk msg)).run ∅
          have hSV : signVerify pk sk = S >>= fun p =>
              (simulateQ impl (sigAlg.verify pk msg p.1)).run' p.2 := by
            change (simulateQ impl (do
                let sig ← sigAlg.sign pk sk msg
                sigAlg.verify pk msg sig)).run' ∅ = _
            rw [simulateQ_bind]
            change Prod.fst <$> ((simulateQ impl (sigAlg.sign pk sk msg) >>=
                fun sig => simulateQ impl (sigAlg.verify pk msg sig)).run ∅) = _
            rw [StateT.run_bind, map_bind]; rfl
          have hSO : Pr[= none | 𝒟[signOnly pk sk]] =
              Pr[= none | Prod.fst <$> S] := by rfl
          rw [hSV, probOutput_bind_eq_tsum, hSO, probOutput_map_eq_tsum]
          refine ENNReal.tsum_le_tsum fun p => ?_
          cases hp : p.1 with
          | none =>
              gcongr
              rw [probOutput_pure_self]
              exact probOutput_le_one
          | some wz =>
              by_cases hmem : p ∈ support S
              · obtain ⟨w', z⟩ := wz
                have hCacheInv := fsAbortSignLoop_cache_invariant ids M
                  ro rfl hc hrel msg maxAttempts ∅ w' z p.2
                  (by rwa [show p = (p.1, p.2) from rfl, hp] at hmem)
                obtain ⟨c₀, hcached, hverify⟩ := hCacheInv
                have hVerifyTrue :
                    Pr[= false | (simulateQ impl
                      (sigAlg.verify pk msg (some (w', z)))).run' p.2] = 0 := by
                  rw [verify_eq_true_of_cached ids hr M ro rfl pk msg maxAttempts
                    w' z p.2 c₀ hcached hverify]
                  simp [probOutput_pure]
                simp only [probOutput_pure, reduceCtorEq, ↓reduceIte,
                  hVerifyTrue, mul_zero, le_refl]
              · simp [probOutput_eq_zero_of_not_mem_support hmem]
      _ ≥ 1 - δ := tsub_le_tsub_left habort' 1
  change 𝒟[(simulateQ impl (do
      let (pk, sk) ← sigAlg.keygen
      let sig ← sigAlg.sign pk sk msg
      sigAlg.verify pk msg sig)).run' ∅] =
    𝒟[do
      let (pk, sk) ← hr.gen
      signVerify pk sk]
  simp only [sigAlg, signVerify, FiatShamirWithAbort, simulateQ_bind]
  congr 1
  rw [roSim.run'_liftM_bind]

end correctness

end FiatShamirWithAbort
