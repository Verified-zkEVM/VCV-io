/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.CryptoFoundations.Fork
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

/-- **CMA-to-NMA reduction via HVZK simulation.**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, there exists a managed-RO NMA adversary `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{managed-NMA}(B) + qS · ζ_zk + ζ_col`

The NMA adversary `B` is constructed by:
- Forwarding `A`'s hash queries to the external oracle (visible to `Fork.fork`)
- Simulating `A`'s signing queries using the HVZK simulator, programming the
  simulated challenge into the cache
- Returning `A`'s forgery together with the accumulated `QueryCache`

Each of the `qS` signing simulations introduces at most `ζ_zk` total-variation distance.
The `ζ_col` term accounts for collisions where `A` queries a hash that `B` later programs.

This step is independent of special soundness and the forking lemma; those are handled
by `euf_nma_bound`. -/
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
        nmaAdv.advantage (runtime M) +
          ENNReal.ofReal (qS * ζ_zk + ζ_col) := by
  let spec := unifSpec + (M × Commit →ₒ Chal)
  let sigSim : Stmt → QueryImpl (M →ₒ (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun pk msg => do
    let (c, ω, s) ← (monadLift (simTranscript pk) :
      StateT spec.QueryCache (OracleComp spec) (Commit × Chal × Resp))
    modify fun cache => cache.cacheQuery (.inr (msg, c)) ω
    pure (c, s)
  let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  refine ⟨⟨fun pk => (simulateQ (fwd + sigSim pk) (adv.main pk)).run ∅⟩, ?_, ?_⟩
  · sorry
  · sorry

/-- **NMA-to-extraction via the forking lemma and special soundness.**

For any managed-RO NMA adversary `B` making at most `qH` random-oracle queries, there
exists a witness-extraction reduction such that:

  `Adv^{managed-NMA}(B) · (Adv^{managed-NMA}(B) / (qH + 1) - 1/|Ω|)
      ≤ Pr[extraction succeeds]`

Runs `B.main pk` twice with shared randomness up to a randomly chosen fork point, then
re-samples the oracle answer. Programmed cache entries are part of `B`'s deterministic
computation given the seed, so they are identical across both fork runs. When the fork
changes one hash oracle answer, two forgeries with distinct challenges at the same
commitment are produced, and special soundness extracts a valid witness. -/
theorem euf_nma_bound
    [DecidableEq M] [DecidableEq Commit]
    [SampleableType Chal]
    (_hss : σ.SpeciallySound)
    [Fintype Chal]
    (nmaAdv : SignatureAlg.managedRoNmaAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qH : ℕ)
    (_hQ : ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := nmaAdv.main pk) qH) :
    ∃ reduction : Stmt → ProbComp Wit,
      (nmaAdv.advantage (runtime M) *
          (nmaAdv.advantage (runtime M) / (qH + 1 : ENNReal) -
            challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp (r := rel) reduction] := by
  classical
  let origSpec := unifSpec + (M × Commit →ₒ Chal)
  -- ─── Wrapped oracle spec ───
  -- Route all (M × Commit →ₒ Chal) queries through a single counted oracle,
  -- so Fork.fork can target one index with budget qH.
  let chalSpec : OracleSpec Unit := Unit →ₒ Chal
  let wrappedSpec := unifSpec + chalSpec
  -- Simulation state: RO cache + ordered query log
  let simSt := (M × Commit →ₒ Chal).QueryCache × List (M × Commit)
  -- ─── Query implementations ───
  -- Hash queries: cache lookup, then fresh query to the single challenge oracle
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
  -- Uniform queries: forward to the left summand
  let unifFwd : QueryImpl unifSpec
      (StateT simSt (OracleComp wrappedSpec)) :=
    fun n => monadLift
      (liftM (query (spec := wrappedSpec) (Sum.inl n)) :
        OracleComp wrappedSpec _)
  -- ─── Wrapped adversary ───
  let wrappedMain : Stmt → OracleComp wrappedSpec
      (((M × (Commit × Resp)) × origSpec.QueryCache) × simSt) :=
    fun pk => StateT.run
      (simulateQ (unifFwd + roImpl) (nmaAdv.main pk)) (∅, [])
  -- ─── Fork-point selector ───
  -- Returns the position of the forgery's hash query in the sequential log.
  -- Returns none when the managed cache programmed the forgery's challenge
  -- (since the fork cannot change a programmed entry).
  let cf : ((M × (Commit × Resp)) × origSpec.QueryCache) × simSt →
      Option (Fin (qH + 1)) :=
    fun ⟨⟨(m, (c, _)), advCache⟩, (_, queryLog)⟩ =>
      match advCache (Sum.inr (m, c)) with
      | some _ => none
      | none =>
        let idx := queryLog.findIdx (· == (m, c))
        if h : idx < qH + 1 then some ⟨idx, h⟩ else none
  -- ─── Query bound + seed list ───
  -- The budget and seed list for the wrapped spec.
  -- unifSpec indices get a budget derived from _hQ; the single challenge
  -- oracle gets qH. Converting the IsQueryBound on origSpec to
  -- IsPerIndexQueryBound on wrappedSpec requires additional infrastructure.
  let qb : ℕ ⊕ Unit → ℕ := fun | .inl _ => sorry | .inr () => qH
  let js : List (ℕ ⊕ Unit) := sorry
  -- Required instances for the wrapped spec
  haveI : ∀ i, SampleableType (wrappedSpec.Range i) := fun i =>
    match i with
    | .inl n => SampleableType.Fin n
    | .inr () => ‹SampleableType Chal›
  -- ─── Fork and extract ───
  -- Phase 1: Fork the wrapped adversary at the single challenge oracle,
  -- then extract a witness via special soundness.
  let forkExtract : Stmt → OracleComp wrappedSpec Wit := fun pk => do
    let result ← fork (wrappedMain pk) qb js (Sum.inr ()) cf
    match result with
    | none => liftComp ($ᵗ Wit) wrappedSpec
    | some (x₁, x₂) =>
      let ⟨⟨(m₁, (c₁, s₁)), _⟩, (roCache₁, _)⟩ := x₁
      let ⟨⟨(m₂, (c₂, s₂)), _⟩, (roCache₂, _)⟩ := x₂
      match roCache₁ (m₁, c₁), roCache₂ (m₂, c₂) with
      | some ω₁, some ω₂ =>
        liftComp (σ.extract ω₁ s₁ ω₂ s₂) wrappedSpec
      | _, _ => liftComp ($ᵗ Wit) wrappedSpec
  -- Phase 2: Convert to ProbComp by simulating the single challenge oracle
  -- with $ᵗ Chal (uniform challenge sampling).
  let reduction : Stmt → ProbComp Wit := fun pk =>
    simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := chalSpec))) (forkExtract pk)
  refine ⟨reduction, ?_⟩
  -- Phase 3: The probability bound.
  --
  -- The proof connects the success probability of `hardRelationExp reduction`
  -- to the forking lemma bound `le_probEvent_isSome_fork`:
  --
  --   acc * (acc / q - h⁻¹) ≤ Pr[isSome | fork ...]
  --
  -- where:
  --   • acc = ∑ s, Pr[= some s | cf <$> wrappedMain stmt]
  --           relates to `nmaAdv.advantage (runtime M)` via the managed-RO
  --           NMA experiment (the wrapping preserves the output distribution).
  --   • q = qH + 1 (total hash query budget plus one).
  --   • h = Fintype.card Chal (challenge space size).
  --
  -- When the fork succeeds with `some (x₁, x₂)`:
  --   • cf x₁ = cf x₂ = some s, so both forgeries use the s-th hash query.
  --   • The collision guard in `fork` ensures the resampled challenge differs.
  --   • Both transcripts share the same commitment (identical up to fork point).
  --   • Special soundness (`_hss`) extracts a valid witness from two accepting
  --     transcripts with the same commitment and distinct challenges.
  sorry

/-- **Combined EUF-CMA bound (Pointcheval-Stern with quantitative HVZK).**

Composes `euf_cma_to_nma` and `euf_nma_bound`:

1. Replace the signing oracle with the HVZK simulator, losing `qS · ζ_zk + ζ_col`.
2. Apply the forking lemma to the resulting managed-RO NMA adversary.

The combined bound is:

  `(ε - qS·ζ_zk - ζ_col) · ((ε - qS·ζ_zk - ζ_col) / (qH+1) - 1/|Ω|)
      ≤ Pr[extraction succeeds]`

where `ε = Adv^{EUF-CMA}(A)`. The ENNReal subtraction truncates at zero, so
the bound is trivially satisfied when the simulation loss exceeds the advantage. -/
theorem euf_cma_bound
    [SampleableType Chal]
    (hss : σ.SpeciallySound)
    [Fintype Chal]
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
        Pr[= true | hardRelationExp (r := rel) reduction] := by
  haveI : DecidableEq M := Classical.decEq M
  haveI : DecidableEq Commit := Classical.decEq Commit
  obtain ⟨nmaAdv, hBound, hAdv⟩ := euf_cma_to_nma σ hr M simTranscript
    ζ_zk ζ_col hζ_zk hζ_col hhvzk adv qS qH hQ
  obtain ⟨reduction, hRed⟩ := euf_nma_bound σ hr M hss nmaAdv qH hBound
  refine ⟨reduction, le_trans ?_ hRed⟩
  have hle : adv.advantage (runtime M) - ENNReal.ofReal (qS * ζ_zk + ζ_col) ≤
      nmaAdv.advantage (runtime M) :=
    tsub_le_iff_left.mpr (by rwa [add_comm])
  exact mul_le_mul' hle (tsub_le_tsub_right (ENNReal.div_le_div_right hle _) _)

end security

end FiatShamir
