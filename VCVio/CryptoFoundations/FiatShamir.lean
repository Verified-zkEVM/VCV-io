/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.HasQuery
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.QueryTracking.QueryRuntime
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.BundledSemantics
import VCVio.ProgramLogic.Tactics.Unary

/-!
# Fiat-Shamir Transform

This file defines a basic version of the Fiat-Shamir transform on sigma protocols.
For simplicity we construct signature schemes rather than general proofs of knowledge.
-/

universe u v

open OracleComp OracleSpec

variable {X W PC SC Ω P : Type}
    {p : X → W → Bool} [SampleableType X] [SampleableType W]

/-- Given a Σ-protocol and a generable relation, the Fiat-Shamir transform produces a
signature scheme. The signing algorithm commits, queries the random oracle on (message,
commitment), and then responds to the challenge. -/
def FiatShamir
    {m : Type → Type v} [Monad m]
    (sigmaAlg : SigmaProtocol X W PC SC Ω P p)
    (hr : GenerableRelation X W p) (M : Type)
    [MonadLiftT ProbComp m] [HasQuery (M × PC →ₒ Ω) m] :
    SignatureAlg m
      (M := M) (PK := X) (SK := W) (S := PC × P) where
  keygen := monadLift hr.gen
  sign := fun pk sk msg => do
    let (c, e) ← (monadLift (sigmaAlg.commit pk sk) : m _)
    let r ← HasQuery.query (spec := (M × PC →ₒ Ω)) (msg, c)
    let s ← (monadLift (sigmaAlg.respond pk sk e r) : m _)
    pure (c, s)
  verify := fun pk msg (c, s) => do
    let r' ← HasQuery.query (spec := (M × PC →ₒ Ω)) (msg, c)
    pure (sigmaAlg.verify pk c r' s)

namespace FiatShamir

variable {X W PC SC Ω P : Type} {p : X → W → Bool}

section semantics

variable (M : Type)
variable [DecidableEq M] [DecidableEq PC] [SampleableType Ω]

/-- Runtime bundle for the Fiat-Shamir random-oracle world. -/
noncomputable def runtime :
    ProbCompRuntime (OracleComp (unifSpec + (M × PC →ₒ Ω))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (M × PC →ₒ Ω) (StateT ((M × PC →ₒ Ω).QueryCache) ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

end semantics

section naturality

variable [SampleableType X] [SampleableType W]
variable (σ : SigmaProtocol X W PC SC Ω P p) (hr : GenerableRelation X W p)
  (M : Type)

variable {m : Type → Type u} [Monad m]
  {n : Type → Type v} [Monad n]
  [MonadLiftT ProbComp m] [MonadLiftT ProbComp n]
  [HasQuery (M × PC →ₒ Ω) m] [HasQuery (M × PC →ₒ Ω) n]

/-- Fiat-Shamir is natural in any oracle semantics morphism that preserves both random-oracle
queries and public-randomness lifting.

This is the basic coherence theorem behind the generic/concrete split:

 - define Fiat-Shamir once over `HasQuery`
- specialize it in one monad
- transport it along a query-preserving monad morphism into another analysis monad

If the morphism also commutes with the designated `ProbComp` lift, then transporting the generic
construction agrees with re-instantiating the construction directly in the target monad. -/
theorem map_construction
    (F : HasQuery.QueryHom (M × PC →ₒ Ω) m n)
    (hLift : HasQuery.PreservesProbCompLift (m := m) (n := n) F.toMonadHom) :
    SignatureAlg.map F.toMonadHom (FiatShamir (m := m) σ hr M) =
      FiatShamir (m := n) σ hr M := by
  apply SignatureAlg.ext
  · simpa [FiatShamir, liftM, MonadLiftT.monadLift, -QueryRuntime.toHasQuery_query]
      using hLift hr.gen
  · funext pk sk msg
    have hCommit :
        F.toMonadHom (monadLift (σ.commit pk sk) : m (PC × SC)) =
          (monadLift (σ.commit pk sk) : n (PC × SC)) :=
      hLift (σ.commit pk sk)
    have hRespond :
        ∀ e r, F.toMonadHom (monadLift (σ.respond pk sk e r) : m P) =
          (monadLift (σ.respond pk sk e r) : n P) :=
      fun e r => hLift (σ.respond pk sk e r)
    simp [FiatShamir, hCommit, hRespond, HasQuery.map_query, -QueryRuntime.toHasQuery_query]
  · funext pk msg sig
    cases sig
    simp [FiatShamir, HasQuery.map_query, -QueryRuntime.toHasQuery_query]

end naturality

section signCore

variable (σ : SigmaProtocol X W PC SC Ω P p) (M : Type)

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]
variable {ω : Type} [AddMonoid ω]

private lemma fst_map_sign_core
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (sk : W) (msg : M) :
    (do
      let a ← WriterT.run (monadLift (σ.commit pk sk) : AddWriterT ω m (PC × SC))
      let r ← runtime.impl (msg, a.1.1)
      (fun z : P × Multiplicative ω => (a.1.1, z.1)) <$>
        WriterT.run (monadLift (σ.respond pk sk a.1.2 r) : AddWriterT ω m P)) =
    (do
      let a ← (monadLift (σ.commit pk sk) : m (PC × SC))
      let r ← runtime.impl (msg, a.1)
      Prod.mk a.1 <$> (monadLift (σ.respond pk sk a.2 r) : m P)) := by
  change (do
      let a ← WriterT.run (monadLift ((monadLift (σ.commit pk sk) : m (PC × SC))) :
        AddWriterT ω m (PC × SC))
      let r ← runtime.impl (msg, a.1.1)
      (fun z : P × Multiplicative ω => (a.1.1, z.1)) <$>
        WriterT.run (monadLift ((monadLift (σ.respond pk sk a.1.2 r) : m P)) : AddWriterT ω m P)) =
    (do
      let a ← (monadLift (σ.commit pk sk) : m (PC × SC))
      let r ← runtime.impl (msg, a.1)
      Prod.mk a.1 <$> (monadLift (σ.respond pk sk a.2 r) : m P))
  simp [bind_map_left]

private lemma snd_map_sign_core_withAddCost
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (costFn : M × PC → ω)
    (pk : X) (sk : W) (msg : M) :
    (do
      let a ← WriterT.run (monadLift (σ.commit pk sk) : AddWriterT ω m (PC × SC))
      let r ← runtime.impl (msg, a.1.1)
      (fun z : P × Multiplicative ω =>
        a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2)) <$>
        WriterT.run (monadLift (σ.respond pk sk a.1.2 r) : AddWriterT ω m P)) =
    (do
      let a ← (monadLift (σ.commit pk sk) : m (PC × SC))
      let r ← runtime.impl (msg, a.1)
      (fun _ ↦ Multiplicative.ofAdd (costFn (msg, a.1))) <$>
        (monadLift (σ.respond pk sk a.2 r) : m P)) := by
  change (do
      let a ← WriterT.run (monadLift ((monadLift (σ.commit pk sk) : m (PC × SC))) :
        AddWriterT ω m (PC × SC))
      let r ← runtime.impl (msg, a.1.1)
      (fun z : P × Multiplicative ω =>
        a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2)) <$>
        WriterT.run (monadLift ((monadLift (σ.respond pk sk a.1.2 r) : m P)) : AddWriterT ω m P)) =
    (do
      let a ← (monadLift (σ.commit pk sk) : m (PC × SC))
      let r ← runtime.impl (msg, a.1)
      (fun _ ↦ Multiplicative.ofAdd (costFn (msg, a.1))) <$>
        (monadLift (σ.respond pk sk a.2 r) : m P))
  simp [bind_map_left]

end signCore

section costAccounting

variable [SampleableType X] [SampleableType W]
variable (σ : SigmaProtocol X W PC SC Ω P p) (hr : GenerableRelation X W p)
  (M : Type)

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

private lemma sign_outputs_formula_withUnitCost
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (sk : W) (msg : M) :
    AddWriterT.outputs
        (HasQuery.withUnitCost
          (fun [HasQuery (M × PC →ₒ Ω) (AddWriterT ℕ m)] =>
            (FiatShamir (m := AddWriterT ℕ m) σ hr M).sign pk sk msg)
          runtime) =
      HasQuery.inRuntime
        (fun [HasQuery (M × PC →ₒ Ω) m] =>
          (FiatShamir (m := m) σ hr M).sign pk sk msg)
        runtime := by
  suffices h :
      (do
        let a ← WriterT.run (monadLift (σ.commit pk sk) : AddWriterT ℕ m (PC × SC))
        let r ← runtime.impl (msg, a.1.1)
        (fun z : P × Multiplicative ℕ => (a.1.1, z.1)) <$>
          WriterT.run (monadLift (σ.respond pk sk a.1.2 r) : AddWriterT ℕ m P)) =
      (do
        let a ← (monadLift (σ.commit pk sk) : m (PC × SC))
        let r ← runtime.impl (msg, a.1)
        Prod.mk a.1 <$> (monadLift (σ.respond pk sk a.2 r) : m P)) by
    simpa [HasQuery.inRuntime, HasQuery.withUnitCost, AddWriterT.outputs, FiatShamir,
      QueryRuntime.withUnitCost_impl, AddWriterT.addTell]
      using h
  exact fst_map_sign_core (σ := σ) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)

private lemma sign_outputs_formula_withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (sk : W) (msg : M)
    (costFn : M × PC → ω) :
    AddWriterT.outputs
        (HasQuery.withAddCost
          (fun [HasQuery (M × PC →ₒ Ω) (AddWriterT ω m)] =>
            (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
          runtime costFn) =
      HasQuery.inRuntime
        (fun [HasQuery (M × PC →ₒ Ω) m] =>
          (FiatShamir (m := m) σ hr M).sign pk sk msg)
        runtime := by
  suffices h :
      (do
        let a ← WriterT.run (monadLift (σ.commit pk sk) : AddWriterT ω m (PC × SC))
        let r ← runtime.impl (msg, a.1.1)
        (fun z : P × Multiplicative ω => (a.1.1, z.1)) <$>
          WriterT.run (monadLift (σ.respond pk sk a.1.2 r) : AddWriterT ω m P)) =
      (do
        let a ← (monadLift (σ.commit pk sk) : m (PC × SC))
        let r ← runtime.impl (msg, a.1)
        Prod.mk a.1 <$> (monadLift (σ.respond pk sk a.2 r) : m P)) by
    simpa [HasQuery.inRuntime, HasQuery.withAddCost, AddWriterT.outputs, FiatShamir,
      QueryRuntime.withAddCost_impl, AddWriterT.addTell]
      using h
  exact fst_map_sign_core (σ := σ) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)

private lemma sign_costs_formula_withUnitCost
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (sk : W) (msg : M) :
    AddWriterT.costs
        (HasQuery.withUnitCost
          (fun [HasQuery (M × PC →ₒ Ω) (AddWriterT ℕ m)] =>
            (FiatShamir (m := AddWriterT ℕ m) σ hr M).sign pk sk msg)
          runtime) =
      (fun _ ↦ 1) <$>
        HasQuery.inRuntime
          (fun [HasQuery (M × PC →ₒ Ω) m] =>
            (FiatShamir (m := m) σ hr M).sign pk sk msg)
          runtime := by
  suffices h :
      (do
        let a ← WriterT.run (monadLift (σ.commit pk sk) : AddWriterT ℕ m (PC × SC))
        let r ← runtime.impl (msg, a.1.1)
        (fun z : P × Multiplicative ℕ => a.2 * (Multiplicative.ofAdd 1 * z.2)) <$>
          WriterT.run (monadLift (σ.respond pk sk a.1.2 r) : AddWriterT ℕ m P)) =
      (do
        let a ← (monadLift (σ.commit pk sk) : m (PC × SC))
        let r ← runtime.impl (msg, a.1)
        (fun _ ↦ Multiplicative.ofAdd 1) <$> (monadLift (σ.respond pk sk a.2 r) : m P)) by
    simpa [HasQuery.inRuntime, HasQuery.withUnitCost, AddWriterT.costs, FiatShamir,
      QueryRuntime.withUnitCost_impl, AddWriterT.addTell]
      using h
  exact snd_map_sign_core_withAddCost
    (σ := σ) (runtime := runtime) (costFn := fun _ ↦ (1 : ℕ))
    (pk := pk) (sk := sk) (msg := msg)

private lemma sign_costs_formula_withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (sk : W) (msg : M)
    (costFn : M × PC → ω) :
    AddWriterT.costs
        (HasQuery.withAddCost
          (fun [HasQuery (M × PC →ₒ Ω) (AddWriterT ω m)] =>
            (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
          runtime costFn) =
      (fun sig ↦ costFn (msg, sig.1)) <$>
        HasQuery.inRuntime
          (fun [HasQuery (M × PC →ₒ Ω) m] =>
            (FiatShamir (m := m) σ hr M).sign pk sk msg)
          runtime := by
  suffices h :
      (do
        let a ← WriterT.run (monadLift (σ.commit pk sk) : AddWriterT ω m (PC × SC))
        let r ← runtime.impl (msg, a.1.1)
        (fun z : P × Multiplicative ω =>
          a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2)) <$>
          WriterT.run (monadLift (σ.respond pk sk a.1.2 r) : AddWriterT ω m P)) =
      (do
        let a ← (monadLift (σ.commit pk sk) : m (PC × SC))
        let r ← runtime.impl (msg, a.1)
        (fun _ ↦ Multiplicative.ofAdd (costFn (msg, a.1))) <$>
          (monadLift (σ.respond pk sk a.2 r) : m P)) by
    simpa [HasQuery.inRuntime, HasQuery.withAddCost, AddWriterT.costs, FiatShamir,
      QueryRuntime.withAddCost_impl, AddWriterT.addTell]
      using h
  exact snd_map_sign_core_withAddCost
    (σ := σ) (runtime := runtime) (costFn := costFn)
    (pk := pk) (sk := sk) (msg := msg)

/-- Fiat-Shamir signing has query cost determined by its output: the signature `(c, s)` records
the unique queried commitment `c`, so the total weighted query cost is exactly
`costFn (msg, c)`. -/
theorem sign_usesCostAsQueryCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (sk : W) (msg : M)
    (costFn : M × PC → ω) :
    HasQuery.UsesCostAs
      (fun [HasQuery (M × PC →ₒ Ω) (AddWriterT ω m)] =>
        (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
      runtime costFn (fun sig ↦ costFn (msg, sig.1)) := by
  rw [HasQuery.UsesCostAs, AddWriterT.costsAs_iff]
  rw [sign_outputs_formula_withAddCost
    (σ := σ) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
    (msg := msg) (costFn := costFn)]
  exact sign_costs_formula_withAddCost
    (σ := σ) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
    (msg := msg) (costFn := costFn)

/-- Fiat-Shamir signing has expected weighted query cost equal to the expectation of the queried
commitment cost over the output signature distribution. -/
theorem sign_expectedQueryCost_eq_outputExpectation {ω : Type} [AddMonoid ω] [HasEvalSPMF m]
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (sk : W) (msg : M)
    (costFn : M × PC → ω) (val : ω → ENNReal) :
    ExpectedQueryCost[
      (FiatShamir σ hr M).sign pk sk msg in runtime by costFn via val
    ] =
      ∑' sig : PC × P,
        Pr[= sig | HasQuery.inRuntime
          (fun [HasQuery (M × PC →ₒ Ω) m] =>
            (FiatShamir (m := m) σ hr M).sign pk sk msg)
          runtime] * val (costFn (msg, sig.1)) := by
  calc
    ExpectedQueryCost[
      (FiatShamir σ hr M).sign pk sk msg in runtime by costFn via val
    ] =
      ∑' sig : PC × P,
        Pr[= sig | AddWriterT.outputs
          (HasQuery.withAddCost
            (fun [HasQuery (M × PC →ₒ Ω) (AddWriterT ω m)] =>
              (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
            runtime costFn)] * val (costFn (msg, sig.1)) :=
          HasQuery.expectedQueryCost_eq_tsum_outputs_of_usesCostAs
            (oa := fun [HasQuery (M × PC →ₒ Ω) (AddWriterT ω m)] =>
              (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
            (runtime := runtime) (costFn := costFn) (f := fun sig ↦ costFn (msg, sig.1))
            (val := val)
            (sign_usesCostAsQueryCost
              (σ := σ) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
              (msg := msg) (costFn := costFn))
    _ = ∑' sig : PC × P,
          Pr[= sig | HasQuery.inRuntime
            (fun [HasQuery (M × PC →ₒ Ω) m] =>
              (FiatShamir (m := m) σ hr M).sign pk sk msg)
            runtime] * val (costFn (msg, sig.1)) := by
          rw [sign_outputs_formula_withAddCost
            (σ := σ) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
            (msg := msg) (costFn := costFn)]

/-- Fiat-Shamir signing makes exactly one random-oracle query under unit-cost instrumentation. -/
theorem sign_usesExactlyOneQuery
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (sk : W) (msg : M) :
    Queries[ (FiatShamir σ hr M).sign pk sk msg in runtime ] = 1 := by
  change Cost[
    HasQuery.withUnitCost
      (fun [HasQuery (M × PC →ₒ Ω) (AddWriterT ℕ m)] =>
        (FiatShamir (m := AddWriterT ℕ m) σ hr M).sign pk sk msg)
      runtime
  ] = 1
  rw [AddWriterT.HasCost, AddWriterT.CostsAs]
  rw [sign_outputs_formula_withUnitCost (σ := σ) (hr := hr) (M := M)
    (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)]
  exact sign_costs_formula_withUnitCost (σ := σ) (hr := hr) (M := M)
    (runtime := runtime) (pk := pk) (sk := sk) (msg := msg)

/-- Fiat-Shamir verification incurs exactly the weighted cost assigned to the single
random-oracle query on `(msg, sig.1)`. -/
theorem verify_usesExactQueryCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (msg : M) (sig : PC × P)
    (costFn : M × PC → ω) :
    QueryCost[ (FiatShamir σ hr M).verify pk msg sig in runtime by costFn ] =
      costFn (msg, sig.1) := by
  rcases sig with ⟨c, s⟩
  change Cost[
    HasQuery.withAddCost
      (fun [HasQuery (M × PC →ₒ Ω) (AddWriterT ω m)] =>
        (FiatShamir (m := AddWriterT ω m) σ hr M).verify pk msg (c, s))
      runtime costFn
  ] = costFn (msg, c)
  rw [AddWriterT.hasCost_iff]
  simp [HasQuery.withAddCost, FiatShamir, QueryRuntime.withAddCost_impl,
    AddWriterT.outputs, AddWriterT.costs, AddWriterT.addTell]

/-- Fiat-Shamir verification has expected weighted query cost equal to the weight of its single
random-oracle query. -/
theorem verify_expectedQueryCost_eq {ω : Type} [AddMonoid ω] [Preorder ω] [HasEvalPMF m]
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (msg : M) (sig : PC × P)
    (costFn : M × PC → ω) (val : ω → ENNReal) (hval : Monotone val) :
    ExpectedQueryCost[
      (FiatShamir σ hr M).verify pk msg sig in runtime by costFn via val
    ] = val (costFn (msg, sig.1)) :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (verify_usesExactQueryCost
      (σ := σ) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (msg := msg)
      (sig := sig) (costFn := costFn))
    hval

/-- Fiat-Shamir verification makes exactly one random-oracle query under unit-cost
instrumentation. -/
theorem verify_usesExactlyOneQuery
    (runtime : QueryRuntime (M × PC →ₒ Ω) m) (pk : X) (msg : M) (sig : PC × P) :
    Queries[ (FiatShamir σ hr M).verify pk msg sig in runtime ] = 1 := by
  simpa [HasQuery.UsesExactlyQueries] using
    (verify_usesExactQueryCost
      (ω := ℕ) (σ := σ) (hr := hr) (M := M) (runtime := runtime) (pk := pk)
      (msg := msg) (sig := sig) (costFn := fun _ ↦ 1))

attribute [simp] sign_usesExactlyOneQuery verify_usesExactlyOneQuery

end costAccounting

section bounds

variable (M : Type)

/-- Structural bound that counts only random-oracle queries in a Fiat-Shamir
EUF-CMA adversary. Uniform-sampling and signing-oracle queries are unrestricted. -/
def hashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (M × PC →ₒ Ω)) + (M →ₒ S')) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBound oa Q
    (fun t b => match t with
      | .inl (.inl _) | .inr _ => True
      | .inl (.inr _) => 0 < b)
    (fun t b => match t with
      | .inl (.inl _) | .inr _ => b
      | .inl (.inr _) => b - 1)

/-- Structural query bound for Fiat-Shamir EUF-CMA adversaries that tracks both
signing-oracle queries (`qS`) and random-oracle queries (`qH`).
Uniform-sampling queries are unrestricted. -/
def signHashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (M × PC →ₒ Ω)) + (M →ₒ S')) α)
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

/-- Structural bound on random-oracle queries for an NMA adversary (no signing oracle).
Uniform-sampling queries are unrestricted. -/
def nmaHashQueryBound {α : Type}
    (oa : OracleComp (unifSpec + (M × PC →ₒ Ω)) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBound oa Q
    (fun t b => match t with
      | .inl _ => True
      | .inr _ => 0 < b)
    (fun t b => match t with
      | .inl _ => b
      | .inr _ => b - 1)

/-- Reciprocal of the finite challenge-space size. -/
noncomputable def challengeSpaceInv (challenge : Type) [Fintype challenge] : ENNReal :=
  (Fintype.card challenge : ENNReal)⁻¹

end bounds

section security

variable [SampleableType X] [SampleableType W]
variable (σ : SigmaProtocol X W PC SC Ω P p) (hr : GenerableRelation X W p)
  (M : Type)

/-- Completeness of the Fiat-Shamir signature scheme follows from completeness of the
underlying Σ-protocol. -/
theorem perfectlyCorrect [DecidableEq M] [DecidableEq PC] [SampleableType Ω]
    (hc : σ.PerfectlyComplete) :
    SignatureAlg.PerfectlyComplete
      (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M)
      (runtime M) := by
  intro msg
  classical
  let ro : QueryImpl (M × PC →ₒ Ω)
      (StateT ((M × PC →ₒ Ω).QueryCache) ProbComp) := randomOracle
  let idImpl := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT ((M × PC →ₒ Ω).QueryCache) ProbComp)
  have hleft :
      ∀ {α : Type} (oa : ProbComp α),
        simulateQ (idImpl + ro) (OracleComp.liftComp oa (unifSpec + (M × PC →ₒ Ω))) =
          simulateQ idImpl oa := by
    intro α oa
    simpa using
      (QueryImpl.simulateQ_add_liftComp_left (impl₁' := idImpl) (impl₂' := ro) oa)
  have hrun :
      ∀ {α : Type} (oa : ProbComp α) (s : (M × PC →ₒ Ω).QueryCache),
        (simulateQ idImpl oa).run s = (fun x => (x, s)) <$> oa := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure x =>
        intro s
        simp
    | query_bind t oa ih =>
        intro s
        change
          (do
            let a ← (liftM (query t) : ProbComp (unifSpec.Range t))
            (simulateQ idImpl (oa a)).run s) =
            (do
              let a ← liftM (query t)
              (fun x => (x, s)) <$> oa a)
        have hfun :
            (fun a => (simulateQ idImpl (oa a)).run s) =
              (fun a => (fun x => (x, s)) <$> oa a) := by
          funext a
          exact ih a s
        simp [hfun]
  have hrunLift :
      ∀ {α : Type} (oa : ProbComp α) (s : (M × PC →ₒ Ω).QueryCache),
        (simulateQ (idImpl + ro) (liftM oa)).run s = (fun x => (x, s)) <$> oa := by
    intro α oa s
    rw [show simulateQ (idImpl + ro) (liftM oa) = simulateQ idImpl oa by
      simpa using hleft oa]
    simpa using hrun oa s
  change
    Pr[= true | (runtime M).evalDist (do
      let (pk, sk) ← (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M).keygen
      let sig ← (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M).sign pk sk msg
      (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M).verify pk msg sig)] = 1
  rw [show (runtime M).evalDist (do
      let (pk, sk) ← (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M).keygen
      let sig ← (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M).sign pk sk msg
      (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M).verify pk msg sig) =
        evalDist (do
          let (pk, sk) ← hr.gen
          let (c, e) ← σ.commit pk sk
          let r ← $ᵗ Ω
          let s ← σ.respond pk sk e r
          pure (σ.verify pk c r s)) by
    change evalDist (StateT.run' (simulateQ (idImpl + ro) (do
        let (pk, sk) ← (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M).keygen
        let sig ← (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M).sign pk sk msg
        (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M).verify pk msg sig)) ∅) = _
    dsimp only [FiatShamir]
    have hquery :
        ∀ q : M × PC,
          HasQuery.query
              (spec := (M × PC →ₒ Ω))
              (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) q =
            (query (spec := unifSpec + (M × PC →ₒ Ω)) (Sum.inr q) :
              OracleComp (unifSpec + (M × PC →ₒ Ω)) Ω) := by
      intro q
      exact congrArg
        (fun z => (liftM z : OracleComp (unifSpec + (M × PC →ₒ Ω)) Ω))
        (OracleQuery.liftM_add_right_query
          (spec₁ := unifSpec) (spec₂ := (M × PC →ₒ Ω)) q)
    simp_rw [hquery]
    simp only [simulateQ_bind, simulateQ_pure, simulateQ_query,
      QueryImpl.add_apply_inr,
      OracleQuery.cont_query, OracleQuery.input_query, id_map]
    have hpeel : ∀ {α β : Type} (oa : ProbComp α)
        (rest : α → StateT ((M × PC →ₒ Ω).QueryCache) ProbComp β)
        (s : (M × PC →ₒ Ω).QueryCache),
        (simulateQ (idImpl + ro) (liftM oa) >>= rest).run' s =
          oa >>= fun x => (rest x).run' s := by
      intro α β oa rest s
      change Prod.fst <$> ((simulateQ (idImpl + ro) (liftM oa) >>= rest).run s) =
        oa >>= fun x => Prod.fst <$> (rest x).run s
      rw [StateT.run_bind, hrunLift]
      simp [map_bind]
    simp_rw [hpeel]
    have hlift : ∀ {α : Type} (x : ProbComp α) (s : (M × PC →ₒ Ω).QueryCache),
        (liftM x : StateT _ ProbComp α).run s = x >>= fun a => pure (a, s) := by
      intro α x s
      simp only [liftM, MonadLiftT.monadLift,
        show OracleComp.liftComp x unifSpec = x from monadLift_eq_self x,
        MonadLift.monadLift, StateT.run_lift]
    have hmod : ∀ {α : Type}
        (f : (M × PC →ₒ Ω).QueryCache → α × (M × PC →ₒ Ω).QueryCache)
        (s : (M × PC →ₒ Ω).QueryCache),
        (modifyGet f : StateT _ ProbComp α).run s = pure (f s) := by
      intro α f s
      simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.run]
    have hro_miss : ∀ {β : Type} (q : M × PC)
        (rest : Ω → StateT ((M × PC →ₒ Ω).QueryCache) ProbComp β),
        (ro q >>= rest).run' ∅ =
          $ᵗ Ω >>= fun r =>
            (rest r).run' ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r) := by
      intro β q rest
      change Prod.fst <$> ((ro q >>= rest).run ∅) =
        $ᵗ Ω >>= fun r =>
          Prod.fst <$> (rest r).run ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r)
      simp only [ro, randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
        StateT.run_get, pure_bind, uniformSampleImpl, bind_assoc, map_bind,
        liftM, MonadLiftT.monadLift,
        MonadLift.monadLift, StateT.run_lift, hmod]
    simp only [bind_assoc, pure_bind]
    simp_rw [hpeel, hro_miss, hpeel]
    have hro_hit : ∀ {β : Type} (q : M × PC) (r : Ω)
        (rest : Ω → StateT ((M × PC →ₒ Ω).QueryCache) ProbComp β),
        (ro q >>= rest).run' ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r) =
          (rest r).run' ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r) := by
      intro β q r rest
      change Prod.fst <$> ((ro q >>= rest).run
          ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r)) =
        Prod.fst <$> (rest r).run
          ((∅ : (M × PC →ₒ Ω).QueryCache).cacheQuery q r)
      rw [StateT.run_bind]
      simp only [ro, randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
        StateT.run_get, pure_bind, QueryCache.cacheQuery_self, StateT.run_pure]
    simp_rw [hro_hit]
    have hpure_run' : ∀ {α : Type} (a : α) (s : (M × PC →ₒ Ω).QueryCache),
        (pure a : StateT _ ProbComp α).run' s = (pure a : ProbComp α) := by
      intro α a s
      change Prod.fst <$> (pure (a, s) : ProbComp _) = pure a
      simp [map_pure]
    simp_rw [hpure_run']]
  change
    Pr[= true | (do
      let (pk, sk) ← hr.gen
      let (c, e) ← σ.commit pk sk
      let r ← $ᵗ Ω
      let s ← σ.respond pk sk e r
      pure (σ.verify pk c r s) : ProbComp Bool)] = 1
  vcstep
  vcstep using (fun x => OracleComp.ProgramLogic.propInd (x ∈ support hr.gen))
  · simpa [OracleComp.ProgramLogic.propInd] using
      OracleComp.ProgramLogic.triple_support (oa := hr.gen)
  · intro x
    rcases x with ⟨pk, sk⟩
    by_cases hx : (pk, sk) ∈ support hr.gen
    · have hrel : p pk sk = true := hr.gen_sound pk sk hx
      simpa [OracleComp.ProgramLogic.propInd, hx] using
        (OracleComp.ProgramLogic.triple_probOutput_eq_one
          (oa := do
            let (c, e) ← σ.commit pk sk
            let r ← $ᵗ Ω
            let s ← σ.respond pk sk e r
            pure (σ.verify pk c r s))
          (x := true) (h := by simpa using hc pk sk hrel))
    · simpa [OracleComp.ProgramLogic.propInd, hx] using
        (OracleComp.ProgramLogic.triple_zero
          (oa := do
            let (c, e) ← σ.commit pk sk
            let r ← $ᵗ Ω
            let s ← σ.respond pk sk e r
            pure (σ.verify pk c r s))
          (post := fun y => if y = true then 1 else 0))

/-- **CMA-to-NMA reduction via HVZK simulation.**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists an NMA adversary `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{EUF-NMA}(B) + qS · ζ_zk`

The NMA adversary `B` is constructed by replacing every signing-oracle answer with a
simulated transcript produced by the HVZK simulator. Each replacement introduces at most
`ζ_zk` total-variation distance, and a hybrid argument over `qS` queries yields the
additive loss.

This step is independent of special soundness and the forking lemma; those are handled
by `euf_nma_bound`. -/
theorem euf_cma_to_nma
    [DecidableEq M] [DecidableEq PC] [DecidableEq P] [SampleableType Ω]
    (simTranscript : X → ProbComp (PC × Ω × P))
    (ζ_zk : ℝ) (_hζ : 0 ≤ ζ_zk)
    (_hhvzk : σ.HVZK simTranscript ζ_zk)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M))
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (PC := PC) (Ω := Ω)
      (S' := PC × P) (oa := adv.main pk) qS qH) :
    ∃ nmaAdv : SignatureAlg.eufNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M),
      adv.advantage (runtime M) ≤
        nmaAdv.advantage (runtime M) + ENNReal.ofReal (qS * ζ_zk) := by
  sorry

set_option linter.unusedDecidableInType false
/-- **NMA-to-extraction via the forking lemma and special soundness.**

For any EUF-NMA adversary `B` making at most `qH` random-oracle queries, there exists a
witness-extraction reduction such that:

  `Adv^{EUF-NMA}(B) · (Adv^{EUF-NMA}(B) / (qH + 1) - 1/|Ω|) ≤ Pr[extraction succeeds]`

The proof (future work) runs `B` twice with the same random tape but different random-oracle
answers after a randomly chosen fork point. When both runs forge at the same hash query with
distinct challenges, special soundness extracts a valid witness. -/
theorem euf_nma_bound
    [DecidableEq M] [DecidableEq PC] [DecidableEq P] [SampleableType Ω]
    (_hss : σ.SpeciallySound)
    [Fintype Ω]
    (nmaAdv : SignatureAlg.eufNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M))
    (qH : ℕ)
    (_hQ : ∀ pk, nmaHashQueryBound (M := M) (PC := PC) (Ω := Ω)
      (oa := nmaAdv.main pk) qH) :
    ∃ reduction : X → ProbComp W,
      (nmaAdv.advantage (runtime M) *
          (nmaAdv.advantage (runtime M) / (qH + 1 : ENNReal) - challengeSpaceInv Ω)) ≤
        Pr[= true | hardRelationExp (r := p) reduction] := by
  sorry

/-- **Combined EUF-CMA bound (Pointcheval-Stern with quantitative HVZK).**

Composes `euf_cma_to_nma` and `euf_nma_bound`:

1. Replace the signing oracle with the HVZK simulator, losing `qS · ζ_zk`.
2. Apply the forking lemma to the resulting NMA adversary.

The combined bound is:

  `(ε - qS·ζ_zk) · ((ε - qS·ζ_zk) / (qH+1) - 1/|Ω|) ≤ Pr[extraction succeeds]`

where `ε = Adv^{EUF-CMA}(A)`. The ENNReal subtraction truncates at zero, so
the bound is trivially satisfied when the simulation loss exceeds the advantage. -/
theorem euf_cma_bound
    [DecidableEq M] [DecidableEq PC] [DecidableEq P] [SampleableType Ω]
    (hss : σ.SpeciallySound)
    [Fintype Ω]
    (simTranscript : X → ProbComp (PC × Ω × P))
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk)
    (hhvzk : σ.HVZK simTranscript ζ_zk)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × PC →ₒ Ω))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (PC := PC) (Ω := Ω)
      (S' := PC × P) (oa := adv.main pk) qS qH) :
    ∃ reduction : X → ProbComp W,
      let eps := adv.advantage (runtime M) - ENNReal.ofReal (qS * ζ_zk)
      (eps * (eps / (qH + 1 : ENNReal) - challengeSpaceInv Ω)) ≤
        Pr[= true | hardRelationExp (r := p) reduction] := by
  let _ := hss
  let _ := hζ
  let _ := hhvzk
  let _ := hQ
  sorry

end security

end FiatShamir
