/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.CryptoFoundations.Fork
import VCVio.CryptoFoundations.ReplayFork
import VCVio.OracleComp.HasQuery
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
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

variable {Stmt Wit Commit PrvState Chal Resp : Type}
    {rel : Stmt → Wit → Bool} [SampleableType Stmt] [SampleableType Wit]

/-- Given a Σ-protocol and a generable relation, the Fiat-Shamir transform produces a
signature scheme. The signing algorithm commits, queries the random oracle on (message,
commitment), and then responds to the challenge. -/
def FiatShamir
    {m : Type → Type v} [Monad m]
    (sigmaAlg : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (hr : GenerableRelation Stmt Wit rel) (M : Type)
    [MonadLiftT ProbComp m] [HasQuery (M × Commit →ₒ Chal) m] :
    SignatureAlg m
      (M := M) (PK := Stmt) (SK := Wit) (S := Commit × Resp) where
  keygen := monadLift hr.gen
  sign := fun pk sk msg => do
    let (c, e) ← (monadLift (sigmaAlg.commit pk sk) : m _)
    let r ← HasQuery.query (spec := (M × Commit →ₒ Chal)) (msg, c)
    let s ← (monadLift (sigmaAlg.respond pk sk e r) : m _)
    pure (c, s)
  verify := fun pk msg (c, s) => do
    let r' ← HasQuery.query (spec := (M × Commit →ₒ Chal)) (msg, c)
    pure (sigmaAlg.verify pk c r' s)

namespace FiatShamir

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section semantics

variable (M : Type)
variable [SampleableType Chal]

open scoped Classical in
/-- Runtime bundle for the Fiat-Shamir random-oracle world. -/
noncomputable def runtime :
    ProbCompRuntime (OracleComp (unifSpec + (M × Commit →ₒ Chal))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (M × Commit →ₒ Chal) (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

end semantics

section naturality

variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable {m : Type → Type u} [Monad m]
  {n : Type → Type v} [Monad n]
  [MonadLiftT ProbComp m] [MonadLiftT ProbComp n]
  [HasQuery (M × Commit →ₒ Chal) m] [HasQuery (M × Commit →ₒ Chal) n]

/-- Fiat-Shamir is natural in any oracle semantics morphism that preserves both random-oracle
queries and public-randomness lifting.

This is the basic coherence theorem behind the generic/concrete split:

 - define Fiat-Shamir once over `HasQuery`
- specialize it in one monad
- transport it along a query-preserving monad morphism into another analysis monad

If the morphism also commutes with the designated `ProbComp` lift, then transporting the generic
construction agrees with re-instantiating the construction directly in the target monad. -/
theorem map_construction
    (F : HasQuery.QueryHom (M × Commit →ₒ Chal) m n)
    (hLift : HasQuery.PreservesProbCompLift (m := m) (n := n) F.toMonadHom) :
    SignatureAlg.map F.toMonadHom (FiatShamir (m := m) σ hr M) =
      FiatShamir (m := n) σ hr M := by
  apply SignatureAlg.ext
  · simpa [FiatShamir, liftM, MonadLiftT.monadLift, -QueryRuntime.toHasQuery_query]
      using hLift hr.gen
  · funext pk sk msg
    have hCommit :
        F.toMonadHom (monadLift (σ.commit pk sk) : m (Commit × PrvState)) =
          (monadLift (σ.commit pk sk) : n (Commit × PrvState)) :=
      hLift (σ.commit pk sk)
    have hRespond :
        ∀ e r, F.toMonadHom (monadLift (σ.respond pk sk e r) : m Resp) =
          (monadLift (σ.respond pk sk e r) : n Resp) :=
      fun e r => hLift (σ.respond pk sk e r)
    simp [FiatShamir, hCommit, hRespond, HasQuery.map_query, -QueryRuntime.toHasQuery_query]
  · funext pk msg sig
    cases sig
    simp [FiatShamir, HasQuery.map_query, -QueryRuntime.toHasQuery_query]

end naturality

section costAccounting

variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

private lemma sign_outputs_formula_withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) :
    AddWriterT.outputs
        (HasQuery.withAddCost
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
            (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
          runtime costFn) =
      HasQuery.inRuntime
        (fun [HasQuery (M × Commit →ₒ Chal) m] =>
          (FiatShamir (m := m) σ hr M).sign pk sk msg)
        runtime := by
  suffices h :
      (do
        let a ← WriterT.run (monadLift (σ.commit pk sk) : AddWriterT ω m (Commit × PrvState))
        let r ← runtime.impl (msg, a.1.1)
        (fun z : Resp × Multiplicative ω => (a.1.1, z.1)) <$>
          WriterT.run (monadLift (σ.respond pk sk a.1.2 r) : AddWriterT ω m Resp)) =
      (do
        let a ← (monadLift (σ.commit pk sk) : m (Commit × PrvState))
        let r ← runtime.impl (msg, a.1)
        Prod.mk a.1 <$> (monadLift (σ.respond pk sk a.2 r) : m Resp)) by
    simpa [HasQuery.inRuntime, HasQuery.withAddCost, AddWriterT.outputs, FiatShamir,
      QueryRuntime.withAddCost_impl, AddWriterT.addTell] using h
  change (do
      let a ← WriterT.run (monadLift ((monadLift (σ.commit pk sk) : m (Commit × PrvState))) :
        AddWriterT ω m (Commit × PrvState))
      let r ← runtime.impl (msg, a.1.1)
      (fun z : Resp × Multiplicative ω => (a.1.1, z.1)) <$>
        WriterT.run (monadLift ((monadLift (σ.respond pk sk a.1.2 r) : m Resp)) :
          AddWriterT ω m Resp)) = _
  simp [bind_map_left]

private lemma sign_costs_formula_withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) :
    AddWriterT.costs
        (HasQuery.withAddCost
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
            (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
          runtime costFn) =
      (fun sig ↦ costFn (msg, sig.1)) <$>
        HasQuery.inRuntime
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            (FiatShamir (m := m) σ hr M).sign pk sk msg)
          runtime := by
  suffices h :
      (do
        let a ← WriterT.run (monadLift (σ.commit pk sk) : AddWriterT ω m (Commit × PrvState))
        let r ← runtime.impl (msg, a.1.1)
        (fun z : Resp × Multiplicative ω =>
          a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2)) <$>
          WriterT.run (monadLift (σ.respond pk sk a.1.2 r) : AddWriterT ω m Resp)) =
      (do
        let a ← (monadLift (σ.commit pk sk) : m (Commit × PrvState))
        let r ← runtime.impl (msg, a.1)
        (fun _ ↦ Multiplicative.ofAdd (costFn (msg, a.1))) <$>
          (monadLift (σ.respond pk sk a.2 r) : m Resp)) by
    simpa [HasQuery.inRuntime, HasQuery.withAddCost, AddWriterT.costs, FiatShamir,
      QueryRuntime.withAddCost_impl, AddWriterT.addTell] using h
  change (do
      let a ← WriterT.run (monadLift ((monadLift (σ.commit pk sk) : m (Commit × PrvState))) :
        AddWriterT ω m (Commit × PrvState))
      let r ← runtime.impl (msg, a.1.1)
      (fun z : Resp × Multiplicative ω =>
        a.2 * (Multiplicative.ofAdd (costFn (msg, a.1.1)) * z.2)) <$>
        WriterT.run (monadLift ((monadLift (σ.respond pk sk a.1.2 r) : m Resp)) :
          AddWriterT ω m Resp)) = _
  simp [bind_map_left]

/-- Fiat-Shamir signing has query cost determined by its output: the signature `(c, s)` records
the unique queried commitment `c`, so the total weighted query cost is exactly
`costFn (msg, c)`. -/
theorem sign_usesCostAsQueryCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) :
    HasQuery.UsesCostAs
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
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
    (runtime : QueryRuntime (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) (val : ω → ENNReal) :
    ExpectedQueryCost[
      (FiatShamir σ hr M).sign pk sk msg in runtime by costFn via val
    ] =
      ∑' sig : Commit × Resp,
        Pr[= sig | HasQuery.inRuntime
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            (FiatShamir (m := m) σ hr M).sign pk sk msg)
          runtime] * val (costFn (msg, sig.1)) := by
  calc
    ExpectedQueryCost[
      (FiatShamir σ hr M).sign pk sk msg in runtime by costFn via val
    ] =
      ∑' sig : Commit × Resp,
        Pr[= sig | AddWriterT.outputs
          (HasQuery.withAddCost
            (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
              (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
            runtime costFn)] * val (costFn (msg, sig.1)) :=
          HasQuery.expectedQueryCost_eq_tsum_outputs_of_usesCostAs
            (oa := fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
              (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
            (runtime := runtime) (costFn := costFn) (f := fun sig ↦ costFn (msg, sig.1))
            (val := val)
            (sign_usesCostAsQueryCost
              (σ := σ) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
              (msg := msg) (costFn := costFn))
    _ = ∑' sig : Commit × Resp,
          Pr[= sig | HasQuery.inRuntime
            (fun [HasQuery (M × Commit →ₒ Chal) m] =>
              (FiatShamir (m := m) σ hr M).sign pk sk msg)
            runtime] * val (costFn (msg, sig.1)) := by
          rw [sign_outputs_formula_withAddCost
            (σ := σ) (hr := hr) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
            (msg := msg) (costFn := costFn)]

/-- Fiat-Shamir signing makes exactly one random-oracle query under unit-cost instrumentation. -/
theorem sign_usesExactlyOneQuery
    (runtime : QueryRuntime (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) :
    Queries[ (FiatShamir σ hr M).sign pk sk msg in runtime ] = 1 := by
  simpa [HasQuery.withUnitCost] using
    sign_usesCostAsQueryCost (σ := σ) (hr := hr) (M := M) (runtime := runtime)
      (pk := pk) (sk := sk) (msg := msg) (costFn := fun _ ↦ (1 : ℕ))

/-- Fiat-Shamir verification incurs exactly the weighted cost assigned to the single
random-oracle query on `(msg, sig.1)`. -/
theorem verify_usesExactQueryCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime (M × Commit →ₒ Chal) m) (pk : Stmt) (msg : M) (sig : Commit × Resp)
    (costFn : M × Commit → ω) :
    QueryCost[ (FiatShamir σ hr M).verify pk msg sig in runtime by costFn ] =
      costFn (msg, sig.1) := by
  rcases sig with ⟨c, s⟩
  change Cost[
    HasQuery.withAddCost
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
        (FiatShamir (m := AddWriterT ω m) σ hr M).verify pk msg (c, s))
      runtime costFn
  ] = costFn (msg, c)
  rw [AddWriterT.hasCost_iff]
  simp [HasQuery.withAddCost, FiatShamir, QueryRuntime.withAddCost_impl,
    AddWriterT.outputs, AddWriterT.costs, AddWriterT.addTell]

/-- Fiat-Shamir verification has expected weighted query cost equal to the weight of its single
random-oracle query. -/
theorem verify_expectedQueryCost_eq {ω : Type} [AddMonoid ω] [Preorder ω] [HasEvalPMF m]
    (runtime : QueryRuntime (M × Commit →ₒ Chal) m) (pk : Stmt) (msg : M)
    (sig : Commit × Resp) (costFn : M × Commit → ω) (val : ω → ENNReal) (hval : Monotone val) :
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
    (runtime : QueryRuntime (M × Commit →ₒ Chal) m) (pk : Stmt) (msg : M)
    (sig : Commit × Resp) :
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
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ S')) α) (Q : ℕ) : Prop :=
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
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ S')) α)
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
    (oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBound oa Q
    (fun t b => match t with
      | .inl _ => True
      | .inr _ => 0 < b)
    (fun t b => match t with
      | .inl _ => b
      | .inr _ => b - 1)

@[simp]
lemma nmaHashQueryBound_query_bind_iff {α : Type}
    (t : (unifSpec + (M × Commit →ₒ Chal)).Domain)
    (oa : (unifSpec + (M × Commit →ₒ Chal)).Range t →
      OracleComp (unifSpec + (M × Commit →ₒ Chal)) α)
    (Q : ℕ) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := liftM (query (spec := unifSpec + (M × Commit →ₒ Chal)) t) >>= oa) Q ↔
      (match t with
      | .inl _ => True
      | .inr _ => 0 < Q) ∧
      ∀ u,
        nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := oa u) (match t with
            | .inl _ => Q
            | .inr _ => Q - 1) := by
  cases t with
  | inl n =>
      simpa [nmaHashQueryBound] using
        (OracleComp.isQueryBound_query_bind_iff
          (spec := unifSpec + (M × Commit →ₒ Chal))
          (α := α) (t := Sum.inl n) (mx := oa) (b := Q)
          (canQuery := fun t b => match t with
            | .inl _ => True
            | .inr _ => 0 < b)
          (cost := fun t b => match t with
            | .inl _ => b
            | .inr _ => b - 1))
  | inr mc =>
      simpa [nmaHashQueryBound] using
        (OracleComp.isQueryBound_query_bind_iff
          (spec := unifSpec + (M × Commit →ₒ Chal))
          (α := α) (t := Sum.inr mc) (mx := oa) (b := Q)
          (canQuery := fun t b => match t with
            | .inl _ => True
            | .inr _ => 0 < b)
          (cost := fun t b => match t with
            | .inl _ => b
            | .inr _ => b - 1))

@[simp]
lemma nmaHashQueryBound_query_iff
    (t : (unifSpec + (M × Commit →ₒ Chal)).Domain) (Q : ℕ) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := liftM (query (spec := unifSpec + (M × Commit →ₒ Chal)) t)) Q ↔
      match t with
      | .inl _ => True
      | .inr _ => 0 < Q := by
  cases t with
  | inl n =>
      simpa [nmaHashQueryBound] using
        (OracleComp.isQueryBound_query_iff
          (spec := unifSpec + (M × Commit →ₒ Chal))
          (t := Sum.inl n) (b := Q)
          (canQuery := fun t b => match t with
            | .inl _ => True
            | .inr _ => 0 < b)
          (cost := fun t b => match t with
            | .inl _ => b
            | .inr _ => b - 1))
  | inr mc =>
      simpa [nmaHashQueryBound] using
        (OracleComp.isQueryBound_query_iff
          (spec := unifSpec + (M × Commit →ₒ Chal))
          (t := Sum.inr mc) (b := Q)
          (canQuery := fun t b => match t with
            | .inl _ => True
            | .inr _ => 0 < b)
          (cost := fun t b => match t with
            | .inl _ => b
            | .inr _ => b - 1))

lemma nmaHashQueryBound_mono {α : Type}
    {oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α} {Q₁ Q₂ : ℕ}
    (h : nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁)
    (hQ : Q₁ ≤ Q₂) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₂ := by
  induction oa using OracleComp.inductionOn generalizing Q₁ Q₂ with
  | pure _ =>
      trivial
  | query_bind t mx ih =>
      rw [nmaHashQueryBound_query_bind_iff] at h ⊢
      cases t with
      | inl n =>
          exact ⟨trivial, fun u => ih u (h.2 u) hQ⟩
      | inr mc =>
          exact ⟨Nat.lt_of_lt_of_le h.1 hQ, fun u => ih u (h.2 u) (Nat.sub_le_sub_right hQ 1)⟩

lemma nmaHashQueryBound_bind {α β : Type}
    {oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α}
    {ob : α → OracleComp (unifSpec + (M × Commit →ₒ Chal)) β}
    {Q₁ Q₂ : ℕ}
    (h1 : nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁)
    (h2 : ∀ x,
      nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := ob x) Q₂) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := oa >>= ob) (Q₁ + Q₂) := by
  induction oa using OracleComp.inductionOn generalizing Q₁ with
  | pure x =>
      simpa [pure_bind] using
        (nmaHashQueryBound_mono (M := M) (Commit := Commit) (Chal := Chal)
          (oa := ob x) (Q₁ := Q₂) (Q₂ := Q₁ + Q₂) (h := h2 x) (hQ := by omega))
  | query_bind t mx ih =>
      rw [nmaHashQueryBound_query_bind_iff] at h1
      rw [bind_assoc, nmaHashQueryBound_query_bind_iff]
      cases t with
      | inl n =>
          refine ⟨trivial, fun u => ?_⟩
          simpa using ih u (h1.2 u)
      | inr mc =>
          refine ⟨Nat.add_pos_left h1.1 _, fun u => ?_⟩
          have h3 := ih u (h1.2 u)
          have hEq : (Q₁ - 1) + Q₂ = Q₁ + Q₂ - 1 := by omega
          simpa [hEq] using h3

lemma nmaHashQueryBound_liftComp_zero {α : Type}
    (oa : ProbComp α) :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := OracleComp.liftComp oa (unifSpec + (M × Commit →ₒ Chal))) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      trivial
  | query_bind t mx ih =>
      rw [OracleComp.liftComp_bind]
      refine nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
        (oa := OracleComp.liftComp
          (liftM (query (spec := unifSpec) t) : OracleComp unifSpec _)
          (unifSpec + (M × Commit →ₒ Chal)))
        (ob := fun u => OracleComp.liftComp (mx u) (unifSpec + (M × Commit →ₒ Chal)))
        (Q₁ := 0) (Q₂ := 0) ?_ ?_
      · simpa using
          (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
            (.inl t) 0).2 trivial
      · intro u
        exact ih u

/-- Reciprocal of the finite challenge-space size. -/
noncomputable def challengeSpaceInv (challenge : Type) [Fintype challenge] : ENNReal :=
  (Fintype.card challenge : ENNReal)⁻¹

end bounds

section security

variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

open scoped Classical in
/-- Completeness of the Fiat-Shamir signature scheme follows from completeness of the
underlying Σ-protocol. -/
theorem perfectlyCorrect [SampleableType Chal]
    (hc : σ.PerfectlyComplete) :
    SignatureAlg.PerfectlyComplete
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)
      (runtime M) := by
  intro msg
  let ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := randomOracle
  let impl := unifFwdImpl (M × Commit →ₒ Chal) + ro
  have hSimQuery : ∀ (q : M × Commit),
      simulateQ impl (HasQuery.query q) = ro q :=
    roSim.simulateQ_HasQuery_query ro
  change
    Pr[= true | (runtime M).evalDist (do
      let (pk, sk) ←
        (FiatShamir
          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).keygen
      let sig ←
        (FiatShamir
          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).sign pk sk msg
      (FiatShamir
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify pk msg sig)] = 1
  rw [show (runtime M).evalDist (do
      let (pk, sk) ←
        (FiatShamir
          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).keygen
      let sig ←
        (FiatShamir
          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).sign pk sk msg
      (FiatShamir
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify pk msg sig) =
        evalDist (do
          let (pk, sk) ← hr.gen
          let (c, e) ← σ.commit pk sk
          let r ← $ᵗ Chal
          let s ← σ.respond pk sk e r
          pure (σ.verify pk c r s)) by
    change evalDist (StateT.run' (simulateQ impl (do
        let (pk, sk) ←
          (FiatShamir
            (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).keygen
        let sig ←
          (FiatShamir
            (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).sign pk sk msg
        (FiatShamir
          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
            pk msg sig)) ∅) = _
    dsimp only [FiatShamir]
    simp only [simulateQ_bind, simulateQ_pure, hSimQuery]
    have hpeel : ∀ {α β : Type} (oa : ProbComp α)
        (rest : α → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp β)
        (s : (M × Commit →ₒ Chal).QueryCache),
        (simulateQ impl (liftM oa) >>= rest).run' s =
          oa >>= fun x => (rest x).run' s :=
      fun oa rest s => roSim.run'_liftM_bind ro oa rest s
    simp_rw [hpeel]
    have hlift : ∀ {α : Type} (x : ProbComp α) (s : (M × Commit →ₒ Chal).QueryCache),
        (liftM x : StateT _ ProbComp α).run s = x >>= fun a => pure (a, s) := by
      intro α x s
      simp only [liftM, MonadLiftT.monadLift,
        show OracleComp.liftComp x unifSpec = x from monadLift_eq_self x,
        MonadLift.monadLift, StateT.run_lift]
    have hmod : ∀ {α : Type}
        (f : (M × Commit →ₒ Chal).QueryCache → α × (M × Commit →ₒ Chal).QueryCache)
        (s : (M × Commit →ₒ Chal).QueryCache),
        (modifyGet f : StateT _ ProbComp α).run s = pure (f s) := by
      intro α f s
      simp only [modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.run]
    have hro_miss : ∀ {β : Type} (q : M × Commit)
        (rest : Chal → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp β),
        (ro q >>= rest).run' ∅ =
          $ᵗ Chal >>= fun r =>
            (rest r).run' ((∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery q r) := by
      intro β q rest
      change Prod.fst <$> ((ro q >>= rest).run ∅) =
        $ᵗ Chal >>= fun r =>
          Prod.fst <$> (rest r).run ((∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery q r)
      simp only [ro, randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
        StateT.run_get, pure_bind, uniformSampleImpl, bind_assoc, map_bind,
        liftM, MonadLiftT.monadLift,
        MonadLift.monadLift, StateT.run_lift, hmod]
    simp only [bind_assoc, pure_bind]
    simp_rw [hpeel, hro_miss, hpeel]
    have hro_hit : ∀ {β : Type} (q : M × Commit) (r : Chal)
        (rest : Chal → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp β),
        (ro q >>= rest).run' ((∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery q r) =
          (rest r).run' ((∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery q r) := by
      intro β q r rest
      change Prod.fst <$> ((ro q >>= rest).run
          ((∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery q r)) =
        Prod.fst <$> (rest r).run
          ((∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery q r)
      rw [StateT.run_bind]
      simp only [ro, randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
        StateT.run_get, pure_bind, QueryCache.cacheQuery_self, StateT.run_pure]
    simp_rw [hro_hit]
    have hpure_run' : ∀ {α : Type} (a : α) (s : (M × Commit →ₒ Chal).QueryCache),
        (pure a : StateT _ ProbComp α).run' s = (pure a : ProbComp α) := by
      intro α a s
      change Prod.fst <$> (pure (a, s) : ProbComp _) = pure a
      simp [map_pure]
    simp_rw [hpure_run']]
  change
    Pr[= true | (do
      let (pk, sk) ← hr.gen
      let (c, e) ← σ.commit pk sk
      let r ← $ᵗ Chal
      let s ← σ.respond pk sk e r
      pure (σ.verify pk c r s) : ProbComp Bool)] = 1
  vcstep
  vcstep using (fun x => OracleComp.ProgramLogic.propInd (x ∈ support hr.gen))
  · simpa [OracleComp.ProgramLogic.propInd] using
      OracleComp.ProgramLogic.triple_support (oa := hr.gen)
  · intro x
    rcases x with ⟨pk, sk⟩
    by_cases hx : (pk, sk) ∈ support hr.gen
    · have hrel : rel pk sk = true := hr.gen_sound pk sk hx
      simpa [OracleComp.ProgramLogic.propInd, hx] using
        (OracleComp.ProgramLogic.triple_probOutput_eq_one
          (oa := do
            let (c, e) ← σ.commit pk sk
            let r ← $ᵗ Chal
            let s ← σ.respond pk sk e r
            pure (σ.verify pk c r s))
          (x := true) (h := by simpa using hc pk sk hrel))
    · simpa [OracleComp.ProgramLogic.propInd, hx] using
        (OracleComp.ProgramLogic.triple_zero
          (oa := do
            let (c, e) ← σ.commit pk sk
            let r ← $ᵗ Chal
            let s ← σ.respond pk sk e r
            pure (σ.verify pk c r s))
          (post := fun y => if y = true then 1 else 0))

/-- Trace used by the Fiat-Shamir forking reduction for managed-RO NMA adversaries. -/
structure ManagedRoNmaForkTrace where
  forgery : M × (Commit × Resp)
  advCache : (unifSpec + (M × Commit →ₒ Chal)).QueryCache
  roCache : (M × Commit →ₒ Chal).QueryCache
  queryLog : List (M × Commit)
  verified : Bool

/-- The hash point corresponding to the final forgery recorded in a fork trace. -/
def ManagedRoNmaForkTrace.target
    (trace : ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :
    M × Commit :=
  (trace.forgery.1, trace.forgery.2.1)

/-- Rewinding point extracted from a managed-RO fork trace. The fork is usable exactly when
the final forgery verifies and its hash point appears in the live query log. -/
def managedRoNmaForkPoint
    [DecidableEq M] [DecidableEq Commit]
    (qH : ℕ)
    (trace : ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :
    Option (Fin (qH + 1)) := by
  if hverified : trace.verified then
    let target := trace.target
    if hmem : target ∈ trace.queryLog then
      let idx := trace.queryLog.findIdx (· == target)
      if hidx : idx < qH + 1 then
        exact some ⟨idx, hidx⟩
      else
        exact none
    else
      exact none
  else
    exact none

lemma managedRoNmaForkPoint_some_imp_verified
    [DecidableEq M] [DecidableEq Commit]
    {qH : ℕ}
    {trace : ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {s : Fin (qH + 1)}
    (hs : managedRoNmaForkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH trace = some s) :
    trace.verified = true := by
  unfold managedRoNmaForkPoint at hs
  by_cases hverified : trace.verified
  · exact hverified
  · simp [hverified] at hs

lemma managedRoNmaForkPoint_some_imp_mem
    [DecidableEq M] [DecidableEq Commit]
    {qH : ℕ}
    {trace : ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {s : Fin (qH + 1)}
    (hs : managedRoNmaForkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH trace = some s) :
    trace.target ∈ trace.queryLog := by
  unfold managedRoNmaForkPoint at hs
  by_cases hverified : trace.verified
  · have hs' :
        trace.target ∈ trace.queryLog ∧
          ∃ h : trace.queryLog.findIdx (· == trace.target) ≤ qH,
            (⟨trace.queryLog.findIdx (· == trace.target), Nat.lt_succ_of_le h⟩ :
              Fin (qH + 1)) = s := by
        simpa [hverified, ManagedRoNmaForkTrace.target] using hs
    exact hs'.1
  · simp [hverified] at hs

lemma managedRoNmaForkPoint_getElem?_eq_some_target
    [DecidableEq M] [DecidableEq Commit]
    {qH : ℕ}
    {trace : ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {s : Fin (qH + 1)}
    (hs : managedRoNmaForkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      qH trace = some s) :
    trace.queryLog[↑s]? = some trace.target := by
  unfold managedRoNmaForkPoint at hs
  by_cases hverified : trace.verified
  · have hs' :
        trace.target ∈ trace.queryLog ∧
          ∃ h : trace.queryLog.findIdx (· == trace.target) ≤ qH,
            (⟨trace.queryLog.findIdx (· == trace.target), Nat.lt_succ_of_le h⟩ :
              Fin (qH + 1)) = s := by
        simpa [hverified, ManagedRoNmaForkTrace.target] using hs
    rcases hs' with ⟨hmem, ⟨hidx, hs'⟩⟩
    have hlt : trace.queryLog.findIdx (· == trace.target) < trace.queryLog.length := by
      exact List.findIdx_lt_length_of_exists ⟨trace.target, hmem, by simp⟩
    subst s
    exact (List.getElem_eq_iff
      (l := trace.queryLog)
      (i := trace.queryLog.findIdx (· == trace.target))
      (x := trace.target)
      hlt).mp <|
      by
        simpa [ManagedRoNmaForkTrace.target] using
          (List.findIdx_getElem (xs := trace.queryLog) (p := fun x => x == trace.target)
            (w := hlt))
  · simp [hverified] at hs

/-- Replay a managed-RO NMA adversary against a single counted challenge oracle, keeping both
the adversary-returned cache and the live query log that the forking lemma can rewind.

The `verified` flag is computed only from challenge values already present in one of those
two caches. In particular, this trace does not perform a fresh post-hoc verification query;
it records exactly the executions whose forgery is already determined by the adversary's
managed view of the random oracle. -/
noncomputable def managedRoNmaForkTraceComp
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (pk : Stmt) :
    OracleComp (unifSpec + (Unit →ₒ Chal))
      (ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) := by
  let origSpec := unifSpec + (M × Commit →ₒ Chal)
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  let wrappedSpec := unifSpec + chalSpec
  let simSt := (M × Commit →ₒ Chal).QueryCache × List (M × Commit)
  let unifFwd : QueryImpl unifSpec
      (StateT simSt (OracleComp wrappedSpec)) :=
    fun n => monadLift
      (liftM (query (spec := wrappedSpec) (Sum.inl n)) :
        OracleComp wrappedSpec _)
  let roImpl : QueryImpl (M × Commit →ₒ Chal)
      (StateT simSt (OracleComp wrappedSpec)) :=
    fun mc => do
      let (cache, log) ← get
      match cache mc with
      | some v => pure v
      | none =>
          let v : Chal ← monadLift
            (liftM (query (spec := wrappedSpec) (Sum.inr ())) :
              OracleComp wrappedSpec Chal)
          set ((cache.cacheQuery mc v : (M × Commit →ₒ Chal).QueryCache),
            log ++ [mc])
          pure v
  exact do
    let ((forgery, advCache), st) ←
      StateT.run (simulateQ (unifFwd + roImpl) (nmaAdv.main pk)) (∅, [])
    let verified :=
      match forgery with
      | (msg, (c, s)) =>
          match advCache (Sum.inr (msg, c)) with
          | some ω => σ.verify pk c ω s
          | none =>
              match st.1 (msg, c) with
              | some ω => σ.verify pk c ω s
              | none => false
    let (roCache, queryLog) := st
    pure {
      forgery := forgery
      advCache := advCache
      roCache := roCache
      queryLog := queryLog
      verified := verified
    }

/-- Forkable managed-RO NMA experiment. Success means the final forged transcript verifies and
the corresponding hash point appears in the live query log, so the forking lemma can rewind it. -/
noncomputable def managedRoNmaForkExp
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : ProbComp Bool :=
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := chalSpec))) (do
      let (pk, _) ←
        OracleComp.liftComp hr.gen (unifSpec + chalSpec)
      let trace ← managedRoNmaForkTraceComp σ hr M nmaAdv pk
      pure (managedRoNmaForkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
        qH trace).isSome)

/-- The forkable success probability of a managed-RO NMA adversary. -/
noncomputable def managedRoNmaForkAdvantage
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) : ENNReal :=
  Pr[= true | managedRoNmaForkExp σ hr M nmaAdv qH]

/-- Managed-RO replay-fork convenience theorem at a fixed public key, stated at the
`OracleComp (unifSpec + (Unit →ₒ Chal))` level.

This is the Fiat-Shamir-specific analogue of Firsov-Janku's `forking_lemma_ro` at
[fsec/proof/ForkingRO.ec:443](../../../fsec/proof/ForkingRO.ec). It packages the replay
quantitative bound with the distinct-answer and postcondition-transfer facts for the wrapped
managed random-oracle trace experiment, composing `le_probEvent_isSome_forkReplay`
(quantitative bound) and `forkReplay_propertyTransfer` (postcondition transfer).

**On the level of the statement.** We state the bound at the `OracleComp` level rather than
lifting through `simulateQ` to `ProbComp`. Each caller (e.g. `euf_nma_bound`) can bridge to
`ProbComp` in one line using `uniformSampleImpl.probEvent_simulateQ` when needed, keeping this
lemma focused on the forking-lemma content.

**On the target-equality conjunct.** A maximally-informative version would also conclude
`x₁.target = x₂.target` (i.e. message-commit pair coincidence at the fork point), matching
Firsov-Janku's `forking_lemma_ro`. In the Lean formalization this conjunct is consumed by the
downstream reduction `euf_nma_bound` to align the cached challenges `ω_i = x_i.roCache target`.
Since it relies on a value-level log-prefix invariant across `replayRunWithTraceValue` plus a
correspondence between the adversary's internal `queryLog` and the outer `QueryLog`, it is
extracted through the caller-provided `P_out` transfer predicate: the caller may choose `P_out`
so that `P_out x log` pins `x.target` to a deterministic function of `(log, cf x)`, and then
derive target-equality from the distinct-answer disagreement on the outer log. -/
theorem managedRoNmaForkingLemmaReplay
    [DecidableEq M] [DecidableEq Commit]
    [DecidableEq Chal] [SampleableType Chal] [Fintype Chal] [Inhabited Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ) (pk : Stmt)
    (P_out : ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) →
      QueryLog (unifSpec + (Unit →ₒ Chal)) → Prop)
    (hP : ∀ {x log},
      (x, log) ∈ support (replayFirstRun (managedRoNmaForkTraceComp σ hr M nmaAdv pk)) →
      P_out x log) :
    let wrappedMain := managedRoNmaForkTraceComp σ hr M nmaAdv pk
    let cf := managedRoNmaForkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
    let qb : ℕ ⊕ Unit → ℕ := fun j => match j with | .inl _ => 0 | .inr () => qH
    let acc := Pr[ fun x => (cf x).isSome | wrappedMain]
    acc * (acc / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
      Pr[
        fun r : Option
            (ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
          ∃ (x₁ x₂ :
              ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
            (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
            r = some (x₁, x₂) ∧
            cf x₁ = some s ∧
            cf x₂ = some s ∧
            QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
              QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
            P_out x₁ log₁ ∧
            P_out x₂ log₂
        | forkReplay wrappedMain qb (Sum.inr ()) cf] := by
  intro wrappedMain cf qb acc
  -- Step 1: Rewrite `acc` as `∑ s, Pr[= some s | cf <$> wrappedMain]`, matching the LHS of
  -- `le_probEvent_isSome_forkReplay`.
  classical
  have hAcc_sum :
      acc = ∑ s, Pr[= some s | cf <$> wrappedMain] := by
    simp only [acc]
    rw [show (fun x => (cf x).isSome = true) =
        (fun x : _ => (Option.isSome x = true)) ∘ cf from rfl,
      ← probEvent_map (q := fun r => Option.isSome r = true)]
    rw [probEvent_eq_tsum_ite]
    rw [tsum_option _ ENNReal.summable]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.isSome_some,
      ↓reduceIte, zero_add]
    rw [tsum_fintype]
  rw [hAcc_sum]
  -- Step 2: Apply the forking lemma lower bound `le_probEvent_isSome_forkReplay`,
  -- then upgrade the RHS event from `isSome` to the structural postcondition using
  -- `forkReplay_propertyTransfer` through `probEvent_mono`.
  have hH_inv : (Fintype.card ((unifSpec + (Unit →ₒ Chal)).Range (Sum.inr ())) : ENNReal)⁻¹ =
      challengeSpaceInv Chal := rfl
  have hqb_eq : qb (Sum.inr ()) = qH := rfl
  calc (∑ s, Pr[= some s | cf <$> wrappedMain]) *
        ((∑ s, Pr[= some s | cf <$> wrappedMain]) / (↑qH + 1) - challengeSpaceInv Chal)
      = (∑ s, Pr[= some s | cf <$> wrappedMain]) *
        ((∑ s, Pr[= some s | cf <$> wrappedMain]) / ↑(qb (Sum.inr ()) + 1)
          - challengeSpaceInv Chal) := by rw [hqb_eq]; push_cast; ring_nf
    _ ≤ Pr[ fun r : Option
            (ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
              r.isSome | forkReplay wrappedMain qb (Sum.inr ()) cf] := by
        have hbound := le_probEvent_isSome_forkReplay
          (main := wrappedMain) (qb := qb) (i := Sum.inr ()) (cf := cf)
        simp only at hbound
        rw [hH_inv] at hbound
        exact hbound
    _ ≤ _ := by
        apply probEvent_mono
        intro r hr hisSome
        rcases r with _ | ⟨x₁, x₂⟩
        · simp at hisSome
        obtain ⟨log₁, log₂, s, hcf₁, hcf₂, hP₁, hP₂, hneq⟩ :=
          forkReplay_propertyTransfer
            (main := wrappedMain) (qb := qb) (i := Sum.inr ()) (cf := cf)
            (P_out := P_out) (hP := hP) hr
        exact ⟨x₁, x₂, s, log₁, log₂, rfl, hcf₁, hcf₂, hneq, hP₁, hP₂⟩

/-- **CMA-to-NMA reduction via HVZK simulation.**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists a managed-RO NMA adversary `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{fork-NMA}_{qH}(B) + qS · ζ_zk + ζ_col`

The NMA adversary `B` is constructed by:
- Forwarding `A`'s hash queries to the external oracle (visible to `Fork.fork`)
- Simulating `A`'s signing queries using the HVZK simulator, programming the
  simulated challenge into the cache
- Returning `A`'s forgery together with the accumulated `QueryCache`

Each of the `qS` signing simulations introduces at most `ζ_zk` total-variation distance.
The `ζ_col` term accounts for collisions where `A` queries a hash that `B` later programs.

This step is independent of special soundness and the forking lemma; those are handled
by `euf_nma_bound`.

The Lean bound matches Firsov-Janku's `pr_koa_cma` at
[fsec/proof/Schnorr.ec:943](../../../fsec/proof/Schnorr.ec): the CMA-to-KOA reduction uses
`eq_except (signed qs) LRO.m{1} LRO.m{2}` as the RO-cache invariant, swaps real signing with
`simulator_equiv` (per-query HVZK cost), handles RO reprogramming via `lro_redo_inv` +
`ro_get_eq_except`, and absorbs the late-programming collision event through the `bad` flag,
bounded by `pr_bad_game` at [fsec/proof/Schnorr.ec:793](../../../fsec/proof/Schnorr.ec) as
`QS · (QS+QR) / |Ω|`, matching our `ζ_col`. -/
theorem euf_cma_to_nma
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk ζ_col : ℝ) (_hζ_zk : 0 ≤ ζ_zk) (_hζ_col : 0 ≤ ζ_col)
    (_hhvzk : σ.HVZK simTranscript ζ_zk)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (_hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ nmaAdv : SignatureAlg.managedRoNmaAdv
        (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M),
      (∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := nmaAdv.main pk) qH) ∧
      adv.advantage (runtime M) ≤
        managedRoNmaForkAdvantage σ hr M nmaAdv qH +
          ENNReal.ofReal (qS * ζ_zk + ζ_col) := by
  let spec := unifSpec + (M × Commit →ₒ Chal)
  let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
    fun n => fwd (.inl n)
  let roSim : QueryImpl (M × Commit →ₒ Chal)
      (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none =>
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  let baseSim : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    unifSim + roSim
  let sigSim : Stmt → QueryImpl (M →ₒ (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun pk msg => do
    let (c, ω, s) ← simulateQ unifSim (simTranscript pk)
    modifyGet fun cache =>
      match cache (.inr (msg, c)) with
      | some _ => ((c, s), cache)
      | none => ((c, s), cache.cacheQuery (.inr (msg, c)) ω)
  refine ⟨⟨fun pk => (simulateQ (baseSim + sigSim pk) (adv.main pk)).run ∅⟩, ?_, ?_⟩
  · -- Query bound: show the NMA adversary makes at most `qH` hash queries.
    -- `fwd` forwards each hash query as-is (1 hash query per CMA hash query).
    -- `sigSim` handles signing queries via `simTranscript` + cache programming,
    -- generating zero hash queries (only uniform queries from `simTranscript`).
    -- Requires a general `IsQueryBound` transfer lemma for `simulateQ` + `StateT.run`.
    intro pk
    let stepBudget :
        (spec + (M →ₒ (Commit × Resp))).Domain → ℕ × ℕ → ℕ := fun t _ =>
      match t with
      | .inl (.inl _) => 0
      | .inl (.inr _) => 1
      | .inr _ => 0
    have hbind :
        ∀ {α β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β} {Q₁ Q₂ : ℕ},
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa := oa) Q₁ →
          (∀ x, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := ob x) Q₂) →
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := oa >>= ob) (Q₁ + Q₂) := by
      intro α β oa ob Q₁ Q₂ h1 h2
      exact nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal) h1 h2
    have hfwd :
        ∀ (t : spec.Domain) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (fwd t).run s) (match t with
              | .inl _ => 0
              | .inr _ => 1) := by
      intro t s
      cases t with
      | inl n =>
          simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
            OracleComp.liftM_run_StateT] using
            (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
              (show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := liftM (query (spec := spec) (.inl n))) 0 by
                  exact
                    (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
                      (.inl n) 0).2 trivial)
              (fun u =>
                show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := pure (u, s)) 0 by
                    trivial))
      | inr mc =>
          simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
            OracleComp.liftM_run_StateT] using
            (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
              (show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := liftM (query (spec := spec) (.inr mc))) 1 by
                  exact
                    (nmaHashQueryBound_query_iff (M := M) (Commit := Commit) (Chal := Chal)
                      (.inr mc) 1).2 (Nat.succ_pos 0))
              (fun u =>
                show nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := pure (u, s)) 0 by
                    trivial))
    have hro :
        ∀ (mc : M × Commit) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (roSim mc).run s) 1 := by
      intro mc s
      cases hs : s (.inr mc) with
      | some v =>
          simp [roSim, hs, nmaHashQueryBound]
      | none =>
          simpa [roSim, hs] using
            ((OracleComp.isQueryBound_map_iff
                (oa := (fwd (.inr mc)).run s)
                (f := fun a : Chal × spec.QueryCache =>
                  (a.1, a.2.cacheQuery (.inr mc) a.1))
                (b := 1)
                (canQuery := fun t b => match t with
                  | .inl _ => True
                  | .inr _ => 0 < b)
                (cost := fun t b => match t with
                  | .inl _ => b
                  | .inr _ => b - 1)).2
              (hfwd (.inr mc) s))
    have hsig :
        ∀ (msg : M) (s : spec.QueryCache),
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (sigSim pk msg).run s) 0 := by
      intro msg s
      have hsource : OracleComp.IsQueryBound
          (simTranscript pk) () (fun _ _ => True) (fun _ _ => ()) := by
        induction simTranscript pk using OracleComp.inductionOn with
        | pure x =>
            trivial
        | query_bind t mx ih =>
            simp [OracleComp.isQueryBound_query_bind_iff, ih]
      have htranscript :
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := (simulateQ unifSim (simTranscript pk)).run s) 0 := by
        simpa [nmaHashQueryBound] using
          (OracleComp.IsQueryBound.simulateQ_run_of_step
            (h := hsource) (combine := Nat.add) (mapBudget := fun _ => 0)
            (stepBudget := fun _ _ => 0) (impl := unifSim)
            (hbind := by
              intro γ δ oa' ob b₁ b₂ h1 h2
              have h1' :
                  nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                    (oa := oa') b₁ := by
                simpa [nmaHashQueryBound] using h1
              have h2' : ∀ x,
                  nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                    (oa := ob x) b₂ := by
                intro x
                simpa [nmaHashQueryBound] using h2 x
              simpa [nmaHashQueryBound] using
                (nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
                  (oa := oa') (ob := ob) (Q₁ := b₁) (Q₂ := b₂) h1' h2')
            )
            (hstep := by
              intro t b s' ht
              simpa [unifSim] using hfwd (.inl t) s')
            (hcombine := by
              intro t b ht
              simp)
            (s := s))
      simpa [sigSim, nmaHashQueryBound] using
        ((OracleComp.isQueryBound_map_iff
            (oa := (simulateQ unifSim (simTranscript pk)).run s)
            (f := fun a : (Commit × Chal × Resp) × spec.QueryCache =>
              match a.2 (.inr (msg, a.1.1)) with
              | some _ => ((a.1.1, a.1.2.2), a.2)
              | none =>
                  ((a.1.1, a.1.2.2),
                    QueryCache.cacheQuery a.2 (.inr (msg, a.1.1)) a.1.2.1))
            (b := 0)
            (canQuery := fun t b => match t with
              | .inl _ => True
              | .inr _ => 0 < b)
            (cost := fun t b => match t with
              | .inl _ => b
              | .inr _ => b - 1)).2 htranscript)
    have hstep :
        ∀ t b s,
          (match t, b with
            | .inl (.inl _), _ => True
            | .inl (.inr _), (_, qH') => 0 < qH'
            | .inr _, (qS', _) => 0 < qS') →
          nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
            (oa := ((baseSim + sigSim pk) t).run s) (stepBudget t b) := by
      intro t b s ht
      rcases b with ⟨qS', qH'⟩
      cases t with
      | inl t =>
          cases t with
          | inl n =>
              simpa [baseSim, stepBudget] using hfwd (.inl n) s
          | inr mc =>
              simpa [baseSim, stepBudget] using hro mc s
      | inr msg =>
          simpa [stepBudget] using hsig msg s
    have hcombine :
        ∀ t b,
          (match t, b with
            | .inl (.inl _), _ => True
            | .inl (.inr _), (_, qH') => 0 < qH'
            | .inr _, (qS', _) => 0 < qS') →
          Nat.add (stepBudget t b)
            (Prod.snd (match t, b with
              | .inl (.inl _), b' => b'
              | .inl (.inr _), (qS', qH') => (qS', qH' - 1)
              | .inr _, (qS', qH') => (qS' - 1, qH'))) =
            Prod.snd b := by
      intro t b ht
      rcases b with ⟨qS', qH'⟩
      cases t with
      | inl t =>
          cases t with
          | inl n =>
              simp [stepBudget]
          | inr mc =>
              simp [stepBudget] at ht ⊢
              omega
      | inr msg =>
          simp [stepBudget]
    simpa [nmaHashQueryBound, signHashQueryBound] using
      (OracleComp.IsQueryBound.simulateQ_run_of_step
        (h := _hQ pk) (combine := Nat.add) (mapBudget := Prod.snd)
        (stepBudget := stepBudget) (impl := baseSim + sigSim pk)
        (hbind := by
          intro γ δ oa' ob b₁ b₂ h1 h2
          have h1' :
              nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := oa') b₁ := by
            simpa [nmaHashQueryBound] using h1
          have h2' : ∀ x,
              nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := ob x) b₂ := by
            intro x
            simpa [nmaHashQueryBound] using h2 x
          simpa [nmaHashQueryBound] using
            (hbind (oa := oa') (ob := ob) (Q₁ := b₁) (Q₂ := b₂) h1' h2')
        )
        (hstep := by
          intro t b s ht
          rcases b with ⟨qS', qH'⟩
          cases t with
          | inl t =>
              cases t with
              | inl n =>
                  simpa [nmaHashQueryBound, baseSim, stepBudget] using hfwd (.inl n) s
              | inr mc =>
                  simpa [nmaHashQueryBound, baseSim, stepBudget] using hro mc s
          | inr msg =>
              simpa [nmaHashQueryBound, stepBudget] using hsig msg s)
        (hcombine := by
          intro t b ht
          rcases b with ⟨qS', qH'⟩
          cases t with
          | inl t =>
              cases t with
              | inl n =>
                  simp [stepBudget]
              | inr mc =>
                  simp [stepBudget] at ht ⊢
                  omega
          | inr msg =>
              simp [stepBudget])
        (s := ∅))
  · -- Advantage bound: `adv.advantage ≤ Adv^{fork-NMA}_{qH}(nmaAdv) + qS * ζ_zk + ζ_col`.
    --
    -- Proof plan:
    --
    -- (1) Drop freshness: `!log.wasQueried msg && verified ≤ verified`, so
    --     `adv.advantage ≤ Pr[verified | CMA signing, real RO verification]`.
    --     Use `probEvent_mono` or `probOutput_map_le` after unfolding `unforgeableExp`.
    --
    -- (2) Intermediate game: define `CMA-no-freshness` that uses the real signing
    --     oracle but returns only the verification bit. Both the CMA-no-freshness
    --     and NMA experiments can be expressed as
    --       `(runtime M).evalDist (keygen >>= fun (pk, sk) => game_X pk sk)`
    --     where `game_X` runs `adv.main pk` with oracle `impl_X` and then verifies.
    --
    -- (3) TV distance decomposition (triangle inequality):
    --     `tvDist(CMA-no-fresh, NMA) ≤ tvDist(CMA-no-fresh, hybrid) + tvDist(hybrid, NMA)`
    --     where `hybrid` uses the simulated signing oracle but verifies with the real RO
    --     (no cache overlay).
    --
    --     (3a) CMA-no-fresh → hybrid: signing oracle replacement.
    --          Each of `qS` signing queries changes from real signing (commit, hash, respond)
    --          to simulated signing (simTranscript, cache program). Per query, HVZK gives
    --          `ζ_zk` TV distance. Total: `qS * ζ_zk`.
    --          Needs `tvDist_bind_left_le` and per-query HVZK bounds.
    --
    --     (3b) hybrid → fork-NMA: relate successful fresh forgeries to the forkable
    --          experiment `managedRoNmaForkExp`. The reduction now serves `A`'s live
    --          hash queries through the same managed cache it eventually returns, and
    --          `sigSim` preserves any pre-existing cache entry instead of overwriting it.
    --          The remaining discrepancy is exactly the late-programming collision event
    --          absorbed by the slack term `ζ_col`.
    --
    -- (4) Conclude:
    --       `adv.advantage ≤ Adv^{fork-NMA}_{qH}(nmaAdv)
    --          + ENNReal.ofReal (qS * ζ_zk + ζ_col)`.
    --     Use `abs_probOutput_toReal_sub_le_tvDist` to convert TV distance to ENNReal bound.
    sorry

section evalDistBridge

variable [Fintype Chal] [Inhabited Chal] [SampleableType Chal]

/-- The `ofLift + uniformSampleImpl` simulation on `unifSpec + (Unit →ₒ Chal)` preserves
`evalDist`. Both oracle components sample uniformly from their range (the `unifSpec`
side via `liftM (query n) : ProbComp (Fin (n+1))`, the challenge side via `$ᵗ Chal`),
so the simulated computation has the same distribution as the source. -/
private lemma evalDist_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) :
    evalDist (simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa) = evalDist oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    rcases t with n | u
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        id_map, evalDist_bind, ih]
      apply bind_congr
      simp [evalDist_query]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, QueryImpl.add_apply_inr, uniformSampleImpl,
        id_map, evalDist_bind, ih]
      have heq : (evalDist ($ᵗ ((ofFn fun _ : Unit => Chal).Range u)) :
            SPMF ((ofFn fun _ : Unit => Chal).Range u)) =
          (evalDist (liftM (query (Sum.inr u)) :
            OracleComp (unifSpec + (Unit →ₒ Chal)) _) :
            SPMF ((unifSpec + (Unit →ₒ Chal)).Range (Sum.inr u))) := by
        rw [evalDist_uniformSample, evalDist_query]; rfl
      exact heq ▸ rfl

/-- Corollary: `probEvent` is preserved by the `ofLift + uniformSampleImpl` simulation. -/
private lemma probEvent_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) (p : α → Prop) :
    Pr[ p | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa] = Pr[ p | oa] := by
  simp only [probEvent_eq_tsum_indicator]
  refine tsum_congr fun x => ?_
  unfold Set.indicator
  split_ifs with hpx
  · exact congrFun (congrArg DFunLike.coe (evalDist_simulateQ_unifChalImpl oa)) x
  · rfl

/-- Corollary: `probOutput` is preserved by the `ofLift + uniformSampleImpl` simulation. -/
private lemma probOutput_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (Unit →ₒ Chal)) α) (x : α) :
    Pr[= x | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (Unit →ₒ Chal)))) oa] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ_unifChalImpl oa)) x

end evalDistBridge

section jensenIntegration

/-- **Keygen-indexed Cauchy-Schwarz / Jensen step for the forking lemma.**

Given a per-element bound `acc x · (acc x / q - hinv) ≤ B x`, integrating over a
probabilistic key-generator `gen : ProbComp X` yields the "lifted" bound:

  `μ · (μ / q - hinv) ≤ 𝔼[B]`

where `μ = 𝔼[acc] = ∑' x, Pr[= x | gen] · acc x`.

The proof goes through the convexity identity `μ² ≤ 𝔼[acc²]` (Cauchy-Schwarz on the
probability distribution `Pr[= · | gen]`), together with `ENNReal.mul_sub` to handle the
truncated subtraction. -/
private lemma jensen_keygen_forking_bound
    {X : Type} (gen : ProbComp X)
    (acc B : X → ENNReal) (q hinv : ENNReal)
    (hinv_ne_top : hinv ≠ ⊤)
    (hacc_le : ∀ x, acc x ≤ 1)
    (hper : ∀ x, acc x * (acc x / q - hinv) ≤ B x) :
    (∑' x, Pr[= x | gen] * acc x) *
        ((∑' x, Pr[= x | gen] * acc x) / q - hinv) ≤
      ∑' x, Pr[= x | gen] * B x := by
  classical
  set w : X → ENNReal := fun x => Pr[= x | gen] with hw_def
  set μ : ENNReal := ∑' x, w x * acc x with hμ_def
  have hw_tsum_le_one : ∑' x, w x ≤ 1 := tsum_probOutput_le_one
  have hμ_le_one : μ ≤ 1 := by
    calc μ = ∑' x, w x * acc x := rfl
      _ ≤ ∑' x, w x * 1 := by gcongr with x; exact hacc_le x
      _ = ∑' x, w x := by simp
      _ ≤ 1 := hw_tsum_le_one
  have hμ_ne_top : μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hμ_le_one
  -- The integrand `w x * acc x * hinv`, with total sum `μ * hinv`.
  have hμ_hinv_ne_top : μ * hinv ≠ ⊤ := ENNReal.mul_ne_top hμ_ne_top hinv_ne_top
  -- Cauchy-Schwarz: `μ² ≤ ∑' w * acc²`.
  have hCS : μ ^ 2 ≤ ∑' x, w x * acc x ^ 2 :=
    ENNReal.sq_tsum_le_tsum_sq w acc hw_tsum_le_one
  -- Split off the key reverse-Jensen inequality as an intermediate calc.
  -- Integrate the per-element bound.
  calc μ * (μ / q - hinv)
      = μ * (μ / q) - μ * hinv :=
        ENNReal.mul_sub (fun _ _ => hμ_ne_top)
    _ = μ ^ 2 / q - μ * hinv := by
        rw [sq, mul_div_assoc]
    _ ≤ (∑' x, w x * acc x ^ 2) / q - μ * hinv := by
        gcongr
    _ = (∑' x, w x * acc x ^ 2 / q) - ∑' x, w x * acc x * hinv := by
        congr 1
        · simp only [div_eq_mul_inv]
          rw [ENNReal.tsum_mul_right]
        · rw [hμ_def, ENNReal.tsum_mul_right]
    _ ≤ ∑' x, (w x * acc x ^ 2 / q - w x * acc x * hinv) := by
        -- Reverse-Jensen: `∑' f - ∑' g ≤ ∑' (f - g)` in ENNReal when `∑' g ≠ ⊤`.
        set f : X → ENNReal := fun x => w x * acc x ^ 2 / q with hf_def
        set g : X → ENNReal := fun x => w x * acc x * hinv with hg_def
        have hg_sum_ne_top : ∑' x, g x ≠ ⊤ := by
          show ∑' x, w x * acc x * hinv ≠ ⊤
          rw [ENNReal.tsum_mul_right]; exact hμ_hinv_ne_top
        have hfg : ∑' x, f x ≤ ∑' x, (f x - g x) + ∑' x, g x := by
          calc ∑' x, f x ≤ ∑' x, ((f x - g x) + g x) := by
                exact ENNReal.tsum_le_tsum fun x => le_tsub_add
            _ = ∑' x, (f x - g x) + ∑' x, g x := ENNReal.tsum_add
        exact tsub_le_iff_right.2 hfg
    _ = ∑' x, w x * (acc x ^ 2 / q - acc x * hinv) := by
        refine tsum_congr fun x => ?_
        have hwx_ne_top : w x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
        rw [ENNReal.mul_sub (fun _ _ => hwx_ne_top), mul_div_assoc, mul_assoc]
    _ = ∑' x, w x * (acc x * (acc x / q - hinv)) := by
        refine tsum_congr fun x => ?_
        have hax_ne_top : acc x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top (hacc_le x)
        congr 1
        rw [ENNReal.mul_sub (fun _ _ => hax_ne_top), sq, mul_div_assoc]
    _ ≤ ∑' x, w x * B x := by
        gcongr with x
        exact hper x

end jensenIntegration

/-- **NMA-to-extraction via the forking lemma and special soundness.**

For any managed-RO NMA adversary `B` making at most `qH` random-oracle queries, there
exists a witness-extraction reduction such that:

  `Adv^{fork-NMA}_{qH}(B) · (Adv^{fork-NMA}_{qH}(B) / (qH + 1) - 1/|Ω|)
      ≤ Pr[extraction succeeds]`

Runs `B.main pk` twice with shared randomness up to a randomly chosen fork point, then
re-samples the oracle answer. Programmed cache entries are part of `B`'s deterministic
computation given the seed, so they are identical across both fork runs. The reduction
extracts only from fork outputs whose two forged transcripts share a commitment and whose
cached challenges are distinct. The remaining proof obligation is to show that successful
forks satisfy exactly those compatibility checks, after which special soundness applies.

Here `Adv^{fork-NMA}_{qH}(B)` is `managedRoNmaForkAdvantage`: it counts exactly the
managed-RO executions whose forgery already verifies from challenge values present in the
adversary's managed cache or in the live hash-query log recorded by
`managedRoNmaForkTraceComp`. This is the precise success event that the forking lemma can
rewind.

This matches Firsov-Janku's `schnorr_koa_secure` at
[fsec/proof/Schnorr.ec:448](../../../fsec/proof/Schnorr.ec), which applies `forking_lemma_ro`
with the single-run postcondition `verify` plus the extractor correctness lemma
`extractor_corr` at [fsec/proof/Schnorr.ec:87](../../../fsec/proof/Schnorr.ec). Our version
uses `managedRoNmaForkingLemmaReplay` for the RO-level packaging and `_hss` for special
soundness, with `σ.extract` playing the role of EC's `extractor`. -/
theorem euf_nma_bound
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ)
    (_hQ : ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := nmaAdv.main pk) qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      (managedRoNmaForkAdvantage σ hr M nmaAdv qH *
          (managedRoNmaForkAdvantage σ hr M nmaAdv qH / (qH + 1 : ENNReal) -
            challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  classical
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  -- Replay `nmaAdv` into a single-counted challenge oracle and record the rewindable trace.
  let wrappedMain : Stmt → OracleComp (unifSpec + (Unit →ₒ Chal))
      (ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) :=
    managedRoNmaForkTraceComp σ hr M nmaAdv
  let cf : ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) →
      Option (Fin (qH + 1)) :=
    managedRoNmaForkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
  -- ─── Replay-fork query budget ───
  -- Only the single counted challenge oracle is forked.
  let qb : ℕ ⊕ Unit → ℕ := fun | .inl _ => 0 | .inr () => qH
  -- ─── Replay-fork and extract ───
  -- Phase 1: replay-fork the wrapped adversary at the single challenge oracle,
  -- then extract a witness via special soundness.
  let forkExtract : Stmt → OracleComp (unifSpec + (Unit →ₒ Chal)) Wit := fun pk => do
    let result ← forkReplay (wrappedMain pk) qb (Sum.inr ()) cf
    match result with
    | none => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
    | some (x₁, x₂) =>
      let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
      let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
      if hc : c₁ = c₂ then
        match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
        | some ω₁, some ω₂ =>
            if hω : ω₁ ≠ ω₂ then
              liftComp (σ.extract ω₁ s₁ ω₂ s₂) (unifSpec + chalSpec)
            else
              liftComp ($ᵗ Wit) (unifSpec + chalSpec)
        | _, _ => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      else
        liftComp ($ᵗ Wit) (unifSpec + chalSpec)
  -- Phase 2: Convert to ProbComp by simulating the single challenge oracle
  -- with $ᵗ Chal (uniform challenge sampling).
  let reduction : Stmt → ProbComp Wit := fun pk =>
    simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := chalSpec))) (forkExtract pk)
  refine ⟨reduction, ?_⟩
  -- Phase 3: The probability bound, decomposed into four named steps (a)-(d).
  --
  -- Define the per-public-key acceptance probability used throughout.
  let acc : Stmt → ENNReal := fun pk => Pr[ fun x => (cf x).isSome | wrappedMain pk]
  -- ── Step (a): rewrite `managedRoNmaForkAdvantage` as the expected per-pk
  -- acceptance `Pr[isSome ∘ cf | keygen >>= wrappedMain]`. This unfolds the
  -- `simulateQ` wrapping around the sum spec via `uniformSampleImpl.probEvent_simulateQ`
  -- and applies `probEvent_map` for the final `(·.isSome)` event.
  have hAdv_eq : managedRoNmaForkAdvantage σ hr M nmaAdv qH =
      Pr[ fun (pt : Stmt × ManagedRoNmaForkTrace
          (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
            (cf pt.2).isSome | do
          let (pk, _) ← OracleComp.liftComp hr.gen (unifSpec + chalSpec)
          let trace ← wrappedMain pk
          pure (pk, trace)] := by
    show Pr[= true | managedRoNmaForkExp σ hr M nmaAdv qH] = _
    unfold managedRoNmaForkExp
    rw [← probEvent_eq_eq_probOutput, probEvent_simulateQ_unifChalImpl]
    simp only [bind_pure_comp, probEvent_map, probEvent_bind_eq_tsum,
      Function.comp_def]
    rfl
  -- The strengthened per-run invariant `P_out pk x log`: when `cf x = some s`, the
  -- cached RO value at the forgery target agrees with the logged challenge at index `s`,
  -- and the forgery verifies under that challenge relative to `pk`. Pairing this across
  -- both runs gives two accepting transcripts with the same commitment and distinct
  -- challenges — exactly what special soundness needs.
  let P_out : Stmt →
      ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) →
        QueryLog (unifSpec + (Unit →ₒ Chal)) → Prop :=
    fun pk x log => ∀ s : Fin (qH + 1), cf x = some s →
      ∃ ω : Chal,
        QueryLog.getQueryValue? log (Sum.inr ()) (↑s : ℕ) = some ω ∧
        x.roCache x.target = some ω ∧
        σ.verify pk x.target.2 ω x.forgery.2.2 = true
  -- Support invariant: `P_out pk` holds for every `(x, log)` in the support of the first
  -- run at public key `pk`. This follows from the definition of `managedRoNmaForkTraceComp`:
  -- whenever `cf x = some s` pins `x.target` to `x.queryLog[s]?` via
  -- `managedRoNmaForkPoint_getElem?_eq_some_target`, the trace's internal RO simulation
  -- guarantees `x.roCache x.target` matches the external `Sum.inr ()` oracle response at
  -- index `s`, and the `verified` flag verifies that response against `pk`.
  have hPinv : ∀ pk x log,
      (x, log) ∈ support (replayFirstRun (wrappedMain pk)) → P_out pk x log := by
    -- TODO(p6-support-invariant): prove the support invariant by induction on
    -- `managedRoNmaForkTraceComp` — each counted-oracle query updates `roCache` and the
    -- external log in lockstep, so their corresponding entries match, and `verified`
    -- guarantees `σ.verify pk` succeeds at the cached challenge.
    sorry
  -- ── Step (b): per-pk forking bound via `managedRoNmaForkingLemmaReplay`, using the
  -- strengthened `P_out pk` to pin each run's cached challenge to its outer log entry.
  have hPerPk : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun r : Option
            (ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
            ∃ (x₁ x₂ :
                ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
              (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
              r = some (x₁, x₂) ∧
              cf x₁ = some s ∧
              cf x₂ = some s ∧
              QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
                QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
              P_out pk x₁ log₁ ∧
              P_out pk x₂ log₂
            | forkReplay (wrappedMain pk) qb (Sum.inr ()) cf] := by
    intro pk
    exact managedRoNmaForkingLemmaReplay (σ := σ) (hr := hr) (M := M) nmaAdv qH pk
      (P_out := P_out pk) (hP := fun h => hPinv pk _ _ h)
  -- ── Step (c): per-pk extraction bound. The structural fork event plus target equality
  -- (established by `hTargetEq` below) plus special soundness give witness extraction.
  -- Target equality across the two fork runs: this holds because both runs share the
  -- oracle responses up to the fork index, so the adversary's internal query-log prefix up
  -- to index `s` is identical, and `managedRoNmaForkPoint_getElem?_eq_some_target` then
  -- forces the targets to agree.
  have hTargetEq : ∀ pk (x₁ x₂ :
      ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
      (s : Fin (qH + 1)),
      some (x₁, x₂) ∈ support (forkReplay (wrappedMain pk) qb (Sum.inr ()) cf) →
      cf x₁ = some s → cf x₂ = some s →
      x₁.target = x₂.target := by
    -- TODO(p6-target-equality): derive from `forkReplay_success_log_props` (shared prefix of
    -- `Sum.inr ()` responses up to index `s`) plus the managedRoNmaForkTraceComp invariant
    -- that `queryLog[n]` is determined by the first `n` counted-oracle responses.
    sorry
  have hExtract : ∀ pk : Stmt,
      Pr[ fun r : Option
          (ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
            ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
          ∃ (x₁ x₂ :
              ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
            (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
            r = some (x₁, x₂) ∧
            cf x₁ = some s ∧
            cf x₂ = some s ∧
            QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
              QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
            P_out pk x₁ log₁ ∧
            P_out pk x₂ log₂
          | forkReplay (wrappedMain pk) qb (Sum.inr ()) cf] ≤
        Pr[ fun w : Wit => rel pk w = true | reduction pk] := by
    intro pk
    classical
    -- Strip the simulator from `reduction pk = simulateQ _ (forkExtract pk)`.
    rw [show Pr[fun w : Wit => rel pk w = true | reduction pk] =
          Pr[fun w : Wit => rel pk w = true | forkExtract pk] from
        probEvent_simulateQ_unifChalImpl (forkExtract pk) _]
    -- Expand `forkExtract pk` as a bind over `forkReplay` followed by the case-match
    -- extractor `branchFn`.
    set branchFn : Option
        (ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
          ManagedRoNmaForkTrace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) →
        OracleComp (unifSpec + (Unit →ₒ Chal)) Wit :=
      fun result => match result with
      | none => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      | some (x₁, x₂) =>
        let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
        let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
        if _hc : c₁ = c₂ then
          match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
          | some ω₁, some ω₂ =>
              if _hω : ω₁ ≠ ω₂ then
                liftComp (σ.extract ω₁ s₁ ω₂ s₂) (unifSpec + chalSpec)
              else
                liftComp ($ᵗ Wit) (unifSpec + chalSpec)
          | _, _ => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
        else
          liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      with hbranchFn_def
    have hforkExtract_eq :
        forkExtract pk = forkReplay (wrappedMain pk) qb (Sum.inr ()) cf >>= branchFn := rfl
    rw [hforkExtract_eq, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    refine ENNReal.tsum_le_tsum fun r => ?_
    -- Pointwise comparison: `(if E r then Pr[= r | mx] else 0) ≤ Pr[= r | mx] * Pr[rel | branchFn r]`.
    by_cases hE :
        ∃ (x₁ x₂ : ManagedRoNmaForkTrace
            (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
          (s : Fin (qH + 1)) (log₁ log₂ : QueryLog (unifSpec + (Unit →ₒ Chal))),
          r = some (x₁, x₂) ∧
          cf x₁ = some s ∧
          cf x₂ = some s ∧
          QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
            QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
          P_out pk x₁ log₁ ∧
          P_out pk x₂ log₂
    swap
    · rw [if_neg hE]; exact zero_le _
    rw [if_pos hE]
    by_cases hsupp : r ∈ support (forkReplay (wrappedMain pk) qb (Sum.inr ()) cf)
    swap
    · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]
    obtain ⟨x₁, x₂, s, log₁, log₂, hreq, hcf₁, hcf₂, hneq, hP₁, hP₂⟩ := hE
    obtain ⟨ω₁, hlog₁, hcache₁, hverify₁⟩ := hP₁ s hcf₁
    obtain ⟨ω₂, hlog₂, hcache₂, hverify₂⟩ := hP₂ s hcf₂
    -- The two cached challenges are distinct because the outer-log entries are.
    have hω_ne : ω₁ ≠ ω₂ := by
      intro heq
      apply hneq
      rw [hlog₁, hlog₂, heq]
    -- Targets coincide by the shared-prefix property of `forkReplay`.
    have htarget : x₁.target = x₂.target :=
      hTargetEq pk x₁ x₂ s (hreq ▸ hsupp) hcf₁ hcf₂
    -- Name the projections of the forgery directly (no rcases).
    set m₁ := x₁.forgery.1 with hm₁_def
    set c₁ := x₁.forgery.2.1 with hc₁_def
    set sr₁ := x₁.forgery.2.2 with hsr₁_def
    set m₂ := x₂.forgery.1 with hm₂_def
    set c₂ := x₂.forgery.2.1 with hc₂_def
    set sr₂ := x₂.forgery.2.2 with hsr₂_def
    -- `target = (forgery.1, forgery.2.1)`, so target equality forces `m`s and `c`s.
    have htgt₁ : x₁.target = (m₁, c₁) := rfl
    have htgt₂ : x₂.target = (m₂, c₂) := rfl
    have htarget_eq : (m₁, c₁) = (m₂, c₂) := by rw [← htgt₁, ← htgt₂]; exact htarget
    have hc_eq : c₁ = c₂ := (Prod.mk.inj htarget_eq).2
    -- Specialize cache / verify to the projected form.
    have hcache₁' : x₁.roCache (m₁, c₁) = some ω₁ := hcache₁
    have hcache₂' : x₂.roCache (m₂, c₂) = some ω₂ := hcache₂
    have hverify₁' : σ.verify pk c₁ ω₁ sr₁ = true := hverify₁
    have hverify₂' : σ.verify pk c₂ ω₂ sr₂ = true := hverify₂
    have hverify₂'' : σ.verify pk c₁ ω₂ sr₂ = true := by rw [hc_eq]; exact hverify₂'
    -- Evaluate `branchFn r = liftComp (σ.extract ω₁ sr₁ ω₂ sr₂) _`.
    have hbranch :
        branchFn r = liftComp (σ.extract ω₁ sr₁ ω₂ sr₂) (unifSpec + chalSpec) := by
      rw [hbranchFn_def, hreq]
      change (if _hc : c₁ = c₂ then
        match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
        | some ω₁, some ω₂ =>
            if _hω : ω₁ ≠ ω₂ then
              liftComp (σ.extract ω₁ sr₁ ω₂ sr₂) (unifSpec + chalSpec)
            else
              liftComp ($ᵗ Wit) (unifSpec + chalSpec)
        | _, _ => liftComp ($ᵗ Wit) (unifSpec + chalSpec)
      else
        liftComp ($ᵗ Wit) (unifSpec + chalSpec)) = _
      rw [dif_pos hc_eq, hcache₁', hcache₂']
      simp only [dif_pos hω_ne]
    rw [hbranch, probEvent_liftComp]
    -- Probability on the extracted branch: 1 via special soundness + no-failure.
    have hrel_one :
        Pr[fun w : Wit => rel pk w = true | σ.extract ω₁ sr₁ ω₂ sr₂] = 1 := by
      rw [probEvent_eq_one_iff]
      refine ⟨hss_nf ω₁ sr₁ ω₂ sr₂, fun w hw => ?_⟩
      exact SigmaProtocol.extract_sound_of_speciallySoundAt σ (hss pk)
        hω_ne hverify₁' hverify₂'' hw
    rw [hrel_one, mul_one]
  -- ── Step (d): integrate (b)∘(c) over keygen using Cauchy-Schwarz / Jensen.
  -- Combining (b) and (c) gives the per-pk forking bound; integrating via
  -- `jensen_keygen_forking_bound` lifts it to the expected bound.
  have hPerPkFinal : ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        Pr[ fun w : Wit => rel pk w = true | reduction pk] := fun pk =>
    (hPerPk pk).trans (hExtract pk)
  -- Rewrite the advantage as the expected acceptance over keygen (marginalized to `pk`).
  have hAdv_eq_tsum :
      managedRoNmaForkAdvantage σ hr M nmaAdv qH =
        ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] * acc pkw.1 := by
    rw [hAdv_eq]
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun pkw => ?_
    rw [probOutput_liftComp]
    congr 1
    rcases pkw with ⟨pk, sk⟩
    simp only [bind_pure_comp, probEvent_map, Function.comp_def, acc]
  -- Rewrite the RHS (`Pr[= true | hardRelationExp]`) as a keygen-marginalized sum.
  have hRHS_eq_tsum : Pr[= true | hardRelationExp hr reduction] =
      ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] *
        Pr[ fun w : Wit => rel pkw.1 w = true | reduction pkw.1] := by
    unfold hardRelationExp
    rw [← probEvent_eq_eq_probOutput]
    simp only [bind_pure_comp, probEvent_bind_eq_tsum]
    refine tsum_congr fun pkw => ?_
    rcases pkw with ⟨pk, sk⟩
    congr 1
    rw [probEvent_map]
    rfl
  rw [hAdv_eq_tsum, hRHS_eq_tsum]
  -- Instantiate `jensen_keygen_forking_bound` with the keygen distribution.
  have hinv_le : challengeSpaceInv Chal ≤ 1 := by
    unfold challengeSpaceInv
    have hcard : (1 : ENNReal) ≤ (Fintype.card Chal : ENNReal) := by
      exact_mod_cast Fintype.card_pos
    exact ENNReal.inv_le_one.2 hcard
  have hinv_ne_top : challengeSpaceInv Chal ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hinv_le
  have hacc_le : ∀ pkw : Stmt × Wit, acc pkw.1 ≤ 1 := fun _ =>
    probEvent_le_one
  exact jensen_keygen_forking_bound (gen := hr.gen)
    (acc := fun pkw => acc pkw.1)
    (B := fun pkw => Pr[ fun w : Wit => rel pkw.1 w = true | reduction pkw.1])
    (q := (qH : ENNReal) + 1) (hinv := challengeSpaceInv Chal)
    hinv_ne_top hacc_le
    (fun pkw => hPerPkFinal pkw.1)

/-- **Combined EUF-CMA bound (Pointcheval-Stern with quantitative HVZK).**

Composes `euf_cma_to_nma` and `euf_nma_bound`:

1. Replace the signing oracle with the HVZK simulator, losing `qS · ζ_zk + ζ_col`.
2. Apply the forking lemma to the resulting forkable managed-RO NMA experiment.

The combined bound is:

  `(ε - qS·ζ_zk - ζ_col) · ((ε - qS·ζ_zk - ζ_col) / (qH+1) - 1/|Ω|)
      ≤ Pr[extraction succeeds]`

where `ε = Adv^{EUF-CMA}(A)`. The ENNReal subtraction truncates at zero, so
the bound is trivially satisfied when the simulation loss exceeds the advantage. -/
theorem euf_cma_bound
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, Pr[⊥ | σ.extract ω₁ p₁ ω₂ p₂] = 0)
    [Fintype Chal] [Inhabited Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk ζ_col : ℝ) (hζ_zk : 0 ≤ ζ_zk) (hζ_col : 0 ≤ ζ_col)
    (hhvzk : σ.HVZK simTranscript ζ_zk)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      let eps := adv.advantage (runtime M) -
        ENNReal.ofReal (qS * ζ_zk + ζ_col)
      (eps * (eps / (qH + 1 : ENNReal) - challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp hr reduction] := by
  haveI : DecidableEq M := Classical.decEq M
  haveI : DecidableEq Commit := Classical.decEq Commit
  obtain ⟨nmaAdv, hBound, hAdv⟩ := euf_cma_to_nma σ hr M simTranscript
    ζ_zk ζ_col hζ_zk hζ_col hhvzk adv qS qH hQ
  obtain ⟨reduction, hRed⟩ := euf_nma_bound σ hr M hss hss_nf nmaAdv qH hBound
  refine ⟨reduction, le_trans ?_ hRed⟩
  have hle : adv.advantage (runtime M) - ENNReal.ofReal (qS * ζ_zk + ζ_col) ≤
      managedRoNmaForkAdvantage σ hr M nmaAdv qH :=
    tsub_le_iff_left.mpr (by rwa [add_comm])
  exact mul_le_mul' hle (tsub_le_tsub_right (ENNReal.div_le_div_right hle _) _)

end security

end FiatShamir
