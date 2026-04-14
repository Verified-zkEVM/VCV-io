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
variable [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]

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
            runtime costFn)] * val (costFn (msg, sig.1)) := by
          exact HasQuery.expectedQueryCost_eq_tsum_outputs_of_usesCostAs
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
    ] = val (costFn (msg, sig.1)) := by
  exact HasQuery.expectedQueryCost_eq_of_usesCostExactly
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

/-- Reciprocal of the finite challenge-space size. -/
noncomputable def challengeSpaceInv (challenge : Type) [Fintype challenge] : ENNReal :=
  (Fintype.card challenge : ENNReal)⁻¹

end bounds

section security

variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

/-- Completeness of the Fiat-Shamir signature scheme follows from completeness of the
underlying Σ-protocol. -/
theorem perfectlyCorrect [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
    (hc : σ.PerfectlyComplete) :
    SignatureAlg.PerfectlyComplete
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)
      (runtime M) := by
  intro msg
  classical
  let ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := randomOracle
  let idImpl := (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)
  have hleft :
      ∀ {α : Type} (oa : ProbComp α),
        simulateQ (idImpl + ro) (OracleComp.liftComp oa (unifSpec + (M × Commit →ₒ Chal))) =
          simulateQ idImpl oa := by
    intro α oa
    simpa using
      (QueryImpl.simulateQ_add_liftComp_left (impl₁' := idImpl) (impl₂' := ro) oa)
  have hrun :
      ∀ {α : Type} (oa : ProbComp α) (s : (M × Commit →ₒ Chal).QueryCache),
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
      ∀ {α : Type} (oa : ProbComp α) (s : (M × Commit →ₒ Chal).QueryCache),
        (simulateQ (idImpl + ro) (liftM oa)).run s = (fun x => (x, s)) <$> oa := by
    intro α oa s
    rw [show simulateQ (idImpl + ro) (liftM oa) = simulateQ idImpl oa by
      simpa using hleft oa]
    simpa using hrun oa s
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
    change evalDist (StateT.run' (simulateQ (idImpl + ro) (do
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
    have hquery :
        ∀ q : M × Commit,
          HasQuery.query
              (spec := (M × Commit →ₒ Chal))
              (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) q =
            (query (spec := unifSpec + (M × Commit →ₒ Chal)) (Sum.inr q) :
              OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal) := by
      intro q
      exact congrArg
        (fun z => (liftM z : OracleComp (unifSpec + (M × Commit →ₒ Chal)) Chal))
        (OracleQuery.liftM_add_right_query
          (spec₁ := unifSpec) (spec₂ := (M × Commit →ₒ Chal)) q)
    simp_rw [hquery]
    simp only [simulateQ_bind, simulateQ_pure, simulateQ_query,
      QueryImpl.add_apply_inr,
      OracleQuery.cont_query, OracleQuery.input_query, id_map]
    have hpeel : ∀ {α β : Type} (oa : ProbComp α)
        (rest : α → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp β)
        (s : (M × Commit →ₒ Chal).QueryCache),
        (simulateQ (idImpl + ro) (liftM oa) >>= rest).run' s =
          oa >>= fun x => (rest x).run' s := by
      intro α β oa rest s
      change Prod.fst <$> ((simulateQ (idImpl + ro) (liftM oa) >>= rest).run s) =
        oa >>= fun x => Prod.fst <$> (rest x).run s
      rw [StateT.run_bind, hrunLift]
      simp [map_bind]
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

set_option linter.unusedDecidableInType false
/-- Pointcheval-Stern style Fiat-Shamir reduction statement.

To obtain a meaningful EUF-CMA theorem we need:
* special soundness, to extract a witness from a successful fork;
* a perfect HVZK simulator for the underlying Σ-protocol, to model signing without the witness;
* a structural bound on hash-oracle queries.

The intended conclusion is stated as the existence of a witness-finding
reduction. The concrete Pointcheval-Stern reduction is not yet implemented in
this file, so the proof below remains a placeholder.

THIS THEOREM STATEMENT NEEDS TO BE UPDATED ONCE WE FIGURE OUT THE CORRECT LOSS TERM
FOR QUANTITATIVE HVZK. -/
theorem euf_cma_bound
    [DecidableEq M] [DecidableEq Commit] [DecidableEq Resp] [SampleableType Chal]
    (_hss : σ.SpeciallySound)
    [Fintype Chal]
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (_hhvzk : σ.PerfectHVZK simTranscript)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M))
    (qBound : ℕ)
    (_hQ : ∀ pk, hashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qBound) :
    ∃ reduction : Stmt → ProbComp Wit,
      (adv.advantage (runtime M) *
          (adv.advantage (runtime M) / (qBound + 1 : ENNReal) - challengeSpaceInv Chal)) ≤
        Pr[= true | hardRelationExp (r := rel) reduction] := by
  -- TODO: implement the explicit Pointcheval-Stern reduction.
  sorry

end security

end FiatShamir
