/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.CryptoFoundations.SigmaProtocol
public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
public import VCVio.OracleComp.HasQuery.Morphism
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.QueryCost
public import VCVio.OracleComp.Coercions.Add
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
public import VCVio.ProgramLogic.NotationCore
public import VCVio.ProgramLogic.Tactics.Unary

/-!
# Fiat-Shamir transform for Σ-protocols

The classical (non-aborting) Fiat-Shamir transform: given a 3-round Σ-protocol
and a generable relation, produce a signature scheme in the random-oracle
model. The signing algorithm commits, queries the random oracle on
`(message, commitment)`, and responds to the resulting challenge.

This file contains the scheme definition, the random-oracle runtime bundle,
the naturality theorem, cost accounting, and completeness. The forking-lemma
bridge lives in `FiatShamir.Sigma.Fork` and the EUF-CMA reduction in
`FiatShamir.Sigma.Security`.
-/

@[expose] public section

universe u v

open OracleComp OracleSpec

variable {Stmt Wit Commit PrvState Chal Resp : Type}
    {rel : Stmt → Wit → Bool}

/-- Given a Σ-protocol and a generable relation, the Fiat-Shamir transform produces a
signature scheme. The signing algorithm commits, queries the random oracle on (message,
commitment), and then responds to the challenge.

The Σ-protocol's own monad `mσ` is separate from the signature scheme's monad `m`, and is
required only to lift into it: the transform never samples a challenge from the Σ-protocol, so
a prover that queries oracles of its own (as the Kilian transform's does) is admissible here.
Every result below is stated at `mσ := ProbComp`. -/
def FiatShamir
    {m : Type → Type v} [Monad m]
    {mσ : Type → Type} [Monad mσ]
    (sigmaAlg : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel mσ)
    (hr : GenerableRelation Stmt Wit rel) (M : Type)
    [MonadLiftT ProbComp m] [MonadLiftT mσ m] [HasQuery (M × Commit →ₒ Chal) m] :
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
/-- Runtime bundle for the Fiat-Shamir random-oracle world starting from a fixed initial cache.

This is the cache-parametric form of `runtime`: the random oracle is preloaded with `cache`, so
queries that hit return the cached value and misses fall through to fresh uniform sampling and
get cached for later. Specializing `cache := ∅` recovers the standard fresh-RO runtime
(`runtime`).

The `cache` parameter is the universal hook for **programming** the random oracle: any caller
that wants to inject pre-decided answers at chosen points runs its experiment under
`runtimeWithCache cache` instead of `runtime`. -/
noncomputable def runtimeWithCache
    (cache : (M × Commit →ₒ Chal).QueryCache) :
    ProbCompRuntime (OracleComp (unifSpec + (M × Commit →ₒ Chal))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (M × Commit →ₒ Chal) (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
    cache
  toProbCompLift := ProbCompLift.ofMonadLift _

open scoped Classical in
/-- Runtime bundle for the Fiat-Shamir random-oracle world.

Definitionally equal to `runtimeWithCache ∅`: the standard runtime is the cache-parametric one
preloaded with the empty cache. -/
noncomputable def runtime :
    ProbCompRuntime (OracleComp (unifSpec + (M × Commit →ₒ Chal))) :=
  runtimeWithCache M ∅

@[simp] lemma runtime_eq_runtimeWithCache_empty :
    (runtime M : ProbCompRuntime (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) =
      runtimeWithCache M ∅ := rfl

/-- The cache-parametric Fiat-Shamir runtime commutes with `<$>`: mapping a function over the
surface computation is the same as mapping it over the observed `SPMF`. A direct corollary of
`SPMFSemantics.withStateOracle_evalSPMF_map`. -/
lemma runtimeWithCache_evalSPMF_map
    (cache : (M × Commit →ₒ Chal).QueryCache)
    {α β : Type} (f : α → β)
    (mx : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α) :
    (runtimeWithCache M cache).evalSPMF (f <$> mx) =
      f <$> (runtimeWithCache M cache).evalSPMF mx :=
  SPMFSemantics.withStateOracle_evalSPMF_map ..

/-- The cache-parametric Fiat-Shamir runtime commutes with `>>= pure ∘ f`. A direct corollary of
`runtimeWithCache_evalSPMF_map`. -/
lemma runtimeWithCache_evalSPMF_bind_pure
    (cache : (M × Commit →ₒ Chal).QueryCache)
    {α β : Type} (mx : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α) (f : α → β) :
    (runtimeWithCache M cache).evalSPMF (mx >>= fun x => pure (f x)) =
      f <$> (runtimeWithCache M cache).evalSPMF mx := by
  rw [show (mx >>= fun x => pure (f x)) = f <$> mx from (map_eq_bind_pure_comp _ f mx).symm,
    runtimeWithCache_evalSPMF_map]

/-- The Fiat-Shamir runtime commutes with binding a lifted `ProbComp` prefix:
evaluating `liftM oa >>= rest` under the runtime is the same as first sampling
`oa` in `SPMF` and then evaluating `rest x` under the runtime. -/
lemma runtimeWithCache_evalSPMF_bind_liftComp
    (cache : (M × Commit →ₒ Chal).QueryCache)
    {α β : Type} (oa : ProbComp α)
    (rest : α → OracleComp (unifSpec + (M × Commit →ₒ Chal)) β) :
    (runtimeWithCache M cache).evalSPMF (liftM oa >>= rest) =
      𝒮[oa] >>= fun x => (runtimeWithCache M cache).evalSPMF (rest x) := by
  classical
  let impl := unifFwdImpl (M × Commit →ₒ Chal) + (randomOracle :
    QueryImpl (M × Commit →ₒ Chal) (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))
  unfold runtimeWithCache ProbCompRuntime.evalSPMF SPMFSemantics.evalSPMF SemanticsVia.denote
  change 𝒮[(simulateQ impl (liftM oa >>= rest)).run' cache] =
      𝒮[oa] >>= fun x => 𝒮[(simulateQ impl (rest x)).run' cache]
  rw [simulateQ_bind, roSim.run'_liftM_bind, evalSPMF_bind]

/-- The Fiat-Shamir runtime commutes with `<$>`: `cache := ∅` instance of
`runtimeWithCache_evalSPMF_map`. -/
lemma runtime_evalSPMF_map
    {α β : Type} (f : α → β)
    (mx : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α) :
    (runtime M).evalSPMF (f <$> mx) = f <$> (runtime M).evalSPMF mx :=
  runtimeWithCache_evalSPMF_map M ∅ f mx

/-- The Fiat-Shamir runtime commutes with `>>= pure ∘ f`: `cache := ∅` instance of
`runtimeWithCache_evalSPMF_bind_pure`. -/
lemma runtime_evalSPMF_bind_pure
    {α β : Type} (mx : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α) (f : α → β) :
    (runtime M).evalSPMF (mx >>= fun x => pure (f x)) =
      f <$> (runtime M).evalSPMF mx :=
  runtimeWithCache_evalSPMF_bind_pure M ∅ mx f

/-- `cache := ∅` instance of `runtimeWithCache_evalSPMF_bind_liftComp`. -/
lemma runtime_evalSPMF_bind_liftComp
    {α β : Type} (oa : ProbComp α)
    (rest : α → OracleComp (unifSpec + (M × Commit →ₒ Chal)) β) :
    (runtime M).evalSPMF (liftM oa >>= rest) =
      𝒮[oa] >>= fun x => (runtime M).evalSPMF (rest x) :=
  runtimeWithCache_evalSPMF_bind_liftComp M ∅ oa rest

end semantics

section naturality

variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable {m : Type → Type u} [Monad m]
  {n : Type → Type v} [Monad n]
  [MonadLiftT ProbComp m] [MonadLiftT ProbComp n]
  [HasQuery (M × Commit →ₒ Chal) m] [HasQuery (M × Commit →ₒ Chal) n]

omit [SampleableType Stmt] [SampleableType Wit] in
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
  · simpa [FiatShamir, liftM, MonadLiftT.monadLift, -QueryImpl.toHasQuery_query]
      using hLift hr.gen
  · funext pk sk msg
    simp [FiatShamir, hLift (σ.commit pk sk), fun e r => hLift (σ.respond pk sk e r),
      HasQuery.map_query, -QueryImpl.toHasQuery_query]
  · funext pk msg sig
    cases sig
    simp [FiatShamir, HasQuery.map_query, -QueryImpl.toHasQuery_query]

end naturality

section costAccounting

variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma sign_outputs_withAddCost_eq_eval {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) :
    AddWriterT.outputs
        (HasQuery.Program.withAddCost
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
            (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
          runtime costFn) =
      HasQuery.Program.eval
        (fun [HasQuery (M × Commit →ₒ Chal) m] =>
          (FiatShamir (m := m) σ hr M).sign pk sk msg)
        runtime := by
  suffices h :
      (do
        let a ← WriterT.run (monadLift (σ.commit pk sk) : AddWriterT ω m (Commit × PrvState))
        let r ← runtime (msg, a.1.1)
        (fun z : Resp × Multiplicative ω ↦ (a.1.1, z.1)) <$>
          WriterT.run (monadLift (σ.respond pk sk a.1.2 r) : AddWriterT ω m Resp)) =
      (do
        let a ← (monadLift (σ.commit pk sk) : m (Commit × PrvState))
        let r ← runtime (msg, a.1)
        Prod.mk a.1 <$> (monadLift (σ.respond pk sk a.2 r) : m Resp)) by
    simpa [HasQuery.Program.eval, HasQuery.Program.withAddCost, AddWriterT.outputs, FiatShamir,
      QueryImpl.withAddCost_apply, AddWriterT.addTell] using h
  change (do
      let a ← WriterT.run (monadLift ((monadLift (σ.commit pk sk) : m (Commit × PrvState))) :
        AddWriterT ω m (Commit × PrvState))
      let r ← runtime (msg, a.1.1)
      (fun z : Resp × Multiplicative ω ↦ (a.1.1, z.1)) <$>
        WriterT.run (monadLift ((monadLift (σ.respond pk sk a.1.2 r) : m Resp)) :
          AddWriterT ω m Resp)) = _
  simp [bind_map_left]

omit [SampleableType Stmt] [SampleableType Wit] in
private lemma sign_costs_withAddCost_eq {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) :
    AddWriterT.costs
        (HasQuery.Program.withAddCost
          (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
            (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
          runtime costFn) =
      (fun sig ↦ costFn (msg, sig.1)) <$>
        HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            (FiatShamir (m := m) σ hr M).sign pk sk msg)
          runtime := by
  suffices h :
      (do
        let a ← WriterT.run (monadLift (σ.commit pk sk) : AddWriterT ω m (Commit × PrvState))
        let r ← runtime (msg, a.1.1)
        (fun z : Resp × Multiplicative ω ↦
          Multiplicative.toAdd a.2 +
            (costFn (msg, a.1.1) + Multiplicative.toAdd z.2)) <$>
          WriterT.run (monadLift (σ.respond pk sk a.1.2 r) : AddWriterT ω m Resp)) =
      (do
        let a ← (monadLift (σ.commit pk sk) : m (Commit × PrvState))
        let r ← runtime (msg, a.1)
        (fun _ ↦ costFn (msg, a.1)) <$>
          (monadLift (σ.respond pk sk a.2 r) : m Resp)) by
    simpa [HasQuery.Program.eval, HasQuery.Program.withAddCost, AddWriterT.costs, FiatShamir,
      QueryImpl.withAddCost_apply, AddWriterT.addTell] using h
  change (do
      let a ← WriterT.run (monadLift ((monadLift (σ.commit pk sk) : m (Commit × PrvState))) :
        AddWriterT ω m (Commit × PrvState))
      let r ← runtime (msg, a.1.1)
      (fun z : Resp × Multiplicative ω ↦
        Multiplicative.toAdd a.2 +
          (costFn (msg, a.1.1) + Multiplicative.toAdd z.2)) <$>
        WriterT.run (monadLift ((monadLift (σ.respond pk sk a.1.2 r) : m Resp)) :
          AddWriterT ω m Resp)) = _
  simp [bind_map_left]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Fiat-Shamir signing has query cost determined by its output: the signature `(c, s)` records
the unique queried commitment `c`, so the total weighted query cost is exactly
`costFn (msg, c)`. -/
theorem sign_usesCostAsQueryCost {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) :
    HasQuery.UsesCostAs
      (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
        (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
      runtime costFn (fun sig ↦ costFn (msg, sig.1)) := by
  rw [HasQuery.UsesCostAs, AddWriterT.costsAs_iff, sign_outputs_withAddCost_eq_eval]
  exact sign_costs_withAddCost_eq σ hr M runtime pk sk msg costFn

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Fiat-Shamir signing has expected weighted query cost equal to the expectation of the queried
commitment cost over the output signature distribution. -/
theorem sign_expectedQueryCost_eq_outputExpectation {ω : Type} [AddMonoid ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M)
    (costFn : M × Commit → ω) (val : ω → ENNReal) :
    ExpectedQueryCost[
      (FiatShamir σ hr M).sign pk sk msg in runtime by costFn via val
    ] =
      ∑' sig : Commit × Resp,
        Pr[= sig | HasQuery.Program.eval
          (fun [HasQuery (M × Commit →ₒ Chal) m] =>
            (FiatShamir (m := m) σ hr M).sign pk sk msg)
          runtime] * val (costFn (msg, sig.1)) := by
  calc
    ExpectedQueryCost[
      (FiatShamir σ hr M).sign pk sk msg in runtime by costFn via val
    ] =
      ∑' sig : Commit × Resp,
        Pr[= sig | AddWriterT.outputs
          (HasQuery.Program.withAddCost
            (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ω m)] =>
              (FiatShamir (m := AddWriterT ω m) σ hr M).sign pk sk msg)
            runtime costFn)] * val (costFn (msg, sig.1)) :=
          HasQuery.expectedQueryCost_eq_tsum_outputs_of_usesCostAs
            (sign_usesCostAsQueryCost σ hr M runtime pk sk msg costFn)
    _ = ∑' sig : Commit × Resp,
          Pr[= sig | HasQuery.Program.eval
            (fun [HasQuery (M × Commit →ₒ Chal) m] =>
              (FiatShamir (m := m) σ hr M).sign pk sk msg)
            runtime] * val (costFn (msg, sig.1)) := by
          rw [sign_outputs_withAddCost_eq_eval]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Fiat-Shamir signing makes exactly one random-oracle query under unit-cost instrumentation. -/
theorem sign_usesExactlyOneQuery
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (sk : Wit) (msg : M) :
    Queries[ (FiatShamir σ hr M).sign pk sk msg in runtime ] = 1 := by
  change HasQuery.UsesCostAs
    (fun [HasQuery (M × Commit →ₒ Chal) (AddWriterT ℕ m)] =>
      (FiatShamir (m := AddWriterT ℕ m) σ hr M).sign pk sk msg)
    runtime (fun _ ↦ 1) (fun _ ↦ 1)
  exact sign_usesCostAsQueryCost σ hr M runtime pk sk msg fun _ ↦ (1 : ℕ)

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Fiat-Shamir verification incurs exactly the weighted cost assigned to the single
random-oracle query on `(msg, sig.1)`. -/
theorem verify_usesExactQueryCost {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (msg : M) (sig : Commit × Resp)
    (costFn : M × Commit → ω) :
    QueryCost[ (FiatShamir σ hr M).verify pk msg sig in runtime by costFn ] =
      costFn (msg, sig.1) := by
  rcases sig with ⟨c, s⟩
  simp [HasQuery.UsesCostExactly, AddWriterT.hasCost_iff, HasQuery.Program.withAddCost,
    FiatShamir, QueryImpl.withAddCost_apply, AddWriterT.outputs, AddWriterT.costs,
    AddWriterT.addTell]

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Fiat-Shamir verification has expected weighted query cost equal to the weight of its single
random-oracle query. -/
theorem verify_expectedQueryCost_eq {ω : Type} [AddMonoid ω] [Preorder ω] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (msg : M)
    (sig : Commit × Resp) (costFn : M × Commit → ω) (val : ω → ENNReal) (hval : Monotone val) :
    ExpectedQueryCost[
      (FiatShamir σ hr M).verify pk msg sig in runtime by costFn via val
    ] = val (costFn (msg, sig.1)) :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (verify_usesExactQueryCost σ hr M runtime pk msg sig costFn) hval

omit [SampleableType Stmt] [SampleableType Wit] in
/-- Fiat-Shamir verification makes exactly one random-oracle query under unit-cost
instrumentation. -/
theorem verify_usesExactlyOneQuery
    (runtime : QueryImpl (M × Commit →ₒ Chal) m) (pk : Stmt) (msg : M)
    (sig : Commit × Resp) :
    Queries[ (FiatShamir σ hr M).verify pk msg sig in runtime ] = 1 := by
  simpa [HasQuery.UsesExactlyQueries] using
    verify_usesExactQueryCost σ hr M runtime pk msg sig fun _ ↦ (1 : ℕ)

attribute [simp] sign_usesExactlyOneQuery verify_usesExactlyOneQuery

end costAccounting

section correctness

variable [SampleableType Stmt] [SampleableType Wit]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel ProbComp)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)

open scoped Classical in
omit [SampleableType Stmt] [SampleableType Wit] in
private lemma perfectlyCorrect_evalSPMF_eq [SampleableType Chal] (msg : M) :
    (runtime M).evalSPMF (do
      let (pk, sk) ←
        (FiatShamir
          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).keygen
      let sig ←
        (FiatShamir
          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).sign pk sk msg
      (FiatShamir
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify pk msg sig) =
      𝒮[do
        let (pk, sk) ← hr.gen
        let (c, e) ← σ.commit pk sk
        let r ← $ᵗ Chal
        let s ← σ.respond pk sk e r
        pure (σ.verify pk c r s)] := by
  let ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := randomOracle
  let impl := unifFwdImpl (M × Commit →ₒ Chal) + ro
  have hSimQuery : ∀ (q : M × Commit),
      simulateQ impl (HasQuery.query q) = ro q :=
    roSim.simulateQ_HasQuery_query ro
  change 𝒮[StateT.run' (simulateQ impl (do
      let (pk, sk) ←
        (FiatShamir
          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).keygen
      let sig ←
        (FiatShamir
          (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).sign pk sk msg
      (FiatShamir
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M).verify
          pk msg sig)) ∅] = _
  dsimp only [FiatShamir]
  simp only [simulateQ_bind, simulateQ_pure, hSimQuery]
  have hpeel : ∀ {α β : Type} (oa : ProbComp α)
      (rest : α → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp β)
      (s : (M × Commit →ₒ Chal).QueryCache),
      (simulateQ impl (liftM oa) >>= rest).run' s =
        oa >>= fun x => (rest x).run' s :=
    fun oa rest s => roSim.run'_liftM_bind ro oa rest s
  simp_rw [hpeel]
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
      MonadLift.monadLift, QueryCache.empty_apply]
    simp only [StateT.run_lift, StateT.run_modifyGet]
    rw [bind_assoc]
    simp only [pure_bind]
  simp only [monad_norm]
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
  simp_rw [hro_hit, StateT.run'_pure']

open scoped Classical in
omit [SampleableType Stmt] [SampleableType Wit] in
/-- Completeness of the Fiat-Shamir signature scheme follows from completeness of the
underlying Σ-protocol. -/
theorem perfectlyCorrect [SampleableType Chal]
    (hc : σ.PerfectlyComplete) :
    SignatureAlg.PerfectlyComplete
      (FiatShamir (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) σ hr M)
      (runtime M) := by
  intro msg
  rw [perfectlyCorrect_evalSPMF_eq σ hr M msg]
  rw [probOutput_evalSPMF]
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
          (x := true) (h := by simpa using hc.probOutput_uniform_challenge_eq_one hrel))
    · simpa [OracleComp.ProgramLogic.propInd, hx] using
        (OracleComp.ProgramLogic.triple_zero
          (oa := do
            let (c, e) ← σ.commit pk sk
            let r ← $ᵗ Chal
            let s ← σ.respond pk sk e r
            pure (σ.verify pk c r s))
          (post := fun y => if y = true then 1 else 0))

end correctness

end FiatShamir
