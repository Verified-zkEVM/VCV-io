/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.HasQuery
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.EvalDist.Monad.Map
import ToMathlib.General

/-!
# Bundled Query Runtimes

This file packages concrete query implementations as explicit runtime objects.

`HasQuery spec m` is the right *capability* interface for constructions that only need to issue
queries. When we want to instrument, transport, or otherwise analyze that capability, we also need
an explicit `QueryImpl spec m` to work with. `QueryRuntime spec m` is the thin bundle that stores
that implementation without changing the capability layer.

The main use cases are:

- reifying an existing `HasQuery` capability as a `QueryRuntime`;
- adding cost, counting, or logging layers to a runtime;
- instantiating a generic `HasQuery` construction directly in an analysis monad.
-/

open OracleSpec

/-- Bundled implementation of the oracle family `spec` in the ambient monad `m`. -/
structure QueryRuntime {ι : Type} (spec : OracleSpec ι) (m : Type → Type*) where
  /-- Concrete implementation of each query in the family `spec`. -/
  impl : QueryImpl spec m

namespace QueryRuntime

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*}

/-- View a bundled query runtime as the corresponding `HasQuery` capability. -/
def toHasQuery (runtime : QueryRuntime spec m) : HasQuery spec m :=
  runtime.impl.toHasQuery

@[simp]
lemma toHasQuery_query (runtime : QueryRuntime spec m) (t : spec.Domain) :
    (runtime.toHasQuery).query t = runtime.impl t := rfl

/-- Repackage an existing `HasQuery` capability as an explicit query runtime. -/
def ofHasQuery [HasQuery spec m] : QueryRuntime spec m where
  impl := HasQuery.toQueryImpl

@[simp]
lemma ofHasQuery_impl [HasQuery spec m] (t : spec.Domain) :
    (ofHasQuery (spec := spec) (m := m)).impl t =
      HasQuery.query (spec := spec) (m := m) t := rfl

section instrumentation

variable [Monad m]

/-- Instrument a query runtime with multiplicative/monoidal cost accumulation in a `WriterT`
layer. -/
def withCost {ω : Type} [Monoid ω]
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) :
    QueryRuntime spec (WriterT ω m) where
  impl := QueryImpl.withCost (spec := spec) (m := m) runtime.impl costFn

@[simp]
lemma withCost_impl {ω : Type} [Monoid ω]
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) (t : spec.Domain) :
    (runtime.withCost costFn).impl t = (do tell (costFn t); liftM (runtime.impl t)) := by
  simp [withCost]

/-- Instrument a query runtime with additive cost accumulation in an `AddWriterT` layer. -/
def withAddCost {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) :
    QueryRuntime spec (AddWriterT ω m) where
  impl := QueryImpl.withCost (spec := spec) (m := m) runtime.impl
    (fun t => Multiplicative.ofAdd (costFn t))

@[simp]
lemma withAddCost_impl {ω : Type} [AddMonoid ω]
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) (t : spec.Domain) :
    (runtime.withAddCost costFn).impl t =
      (do AddWriterT.addTell (M := m) (costFn t); liftM (runtime.impl t)) := by
  simp [withAddCost, AddWriterT.addTell, QueryImpl.withCost]

/-- Instrument a query runtime with unit additive cost for every query. -/
def withUnitCost (runtime : QueryRuntime spec m) :
    QueryRuntime spec (AddWriterT ℕ m) :=
  runtime.withAddCost (fun _ ↦ 1)

@[simp]
lemma withUnitCost_impl (runtime : QueryRuntime spec m) (t : spec.Domain) :
    runtime.withUnitCost.impl t =
      (do AddWriterT.addTell (M := m) 1; liftM (runtime.impl t)) := by
  simp [withUnitCost]

end instrumentation

end QueryRuntime

namespace AddWriterT

section unitCostBounds

variable {m : Type → Type*} [Monad m] [HasEvalSet m]
variable {α β : Type}

/-- Pathwise upper bound for a unit-cost `AddWriterT` computation: every value in the support of
`oa.run` carries additive cost at most `n`. -/
def QueryBoundedBy (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  ∀ z ∈ support oa.run, Multiplicative.toAdd z.2 ≤ n

/-- Pathwise lower bound for a unit-cost `AddWriterT` computation. -/
def QueryBoundedBelowBy (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  ∀ z ∈ support oa.run, n ≤ Multiplicative.toAdd z.2

lemma queryBoundedBy_pure [LawfulMonad m] (x : α) :
    QueryBoundedBy (pure x : AddWriterT ℕ m α) 0 := by
  intro z hz
  rw [WriterT.run_pure, support_pure] at hz
  rcases hz with rfl
  simp

lemma queryBoundedBelowBy_pure [LawfulMonad m] (x : α) :
    QueryBoundedBelowBy (pure x : AddWriterT ℕ m α) 0 := by
  intro z hz
  rw [WriterT.run_pure, support_pure] at hz
  rcases hz with rfl
  simp

lemma queryBoundedBy_monadLift [LawfulMonad m] (x : m α) :
    QueryBoundedBy (monadLift x : AddWriterT ℕ m α) 0 := by
  intro z hz
  rw [WriterT.run_monadLift, support_map] at hz
  rcases hz with ⟨a, _, rfl⟩
  simp

lemma queryBoundedBelowBy_monadLift [LawfulMonad m] (x : m α) :
    QueryBoundedBelowBy (monadLift x : AddWriterT ℕ m α) 0 := by
  intro z hz
  rw [WriterT.run_monadLift, support_map] at hz
  rcases hz with ⟨a, _, rfl⟩
  simp

lemma queryBoundedBy_mono {oa : AddWriterT ℕ m α} {n₁ n₂ : ℕ}
    (h : QueryBoundedBy oa n₁) (hn : n₁ ≤ n₂) :
    QueryBoundedBy oa n₂ := by
  intro z hz
  exact le_trans (h z hz) hn

lemma queryBoundedBelowBy_mono {oa : AddWriterT ℕ m α} {n₁ n₂ : ℕ}
    (h : QueryBoundedBelowBy oa n₂) (hn : n₁ ≤ n₂) :
    QueryBoundedBelowBy oa n₁ := by
  intro z hz
  exact le_trans hn (h z hz)

lemma queryBoundedBy_addTell [LawfulMonad m] (w : ℕ) :
    QueryBoundedBy (AddWriterT.addTell (M := m) w) w := by
  intro z hz
  rw [AddWriterT.run_addTell, support_pure] at hz
  rcases hz with rfl
  simp

lemma queryBoundedBelowBy_addTell [LawfulMonad m] (w : ℕ) :
    QueryBoundedBelowBy (AddWriterT.addTell (M := m) w) w := by
  intro z hz
  rw [AddWriterT.run_addTell, support_pure] at hz
  rcases hz with rfl
  simp

lemma queryBoundedBy_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ} (f : α → β)
    (h : QueryBoundedBy oa n) :
    QueryBoundedBy (f <$> oa) n := by
  intro z hz
  rw [WriterT.run_map, support_map] at hz
  rcases hz with ⟨z', hz', rfl⟩
  exact h z' hz'

lemma queryBoundedBelowBy_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ} (f : α → β)
    (h : QueryBoundedBelowBy oa n) :
    QueryBoundedBelowBy (f <$> oa) n := by
  intro z hz
  rw [WriterT.run_map, support_map] at hz
  rcases hz with ⟨z', hz', rfl⟩
  exact h z' hz'

lemma queryBoundedBy_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryBoundedBy oa n₁) (h₂ : ∀ a, QueryBoundedBy (f a) n₂) :
    QueryBoundedBy (oa >>= f) (n₁ + n₂) := by
  intro z hz
  rw [WriterT.run_bind] at hz
  rcases (mem_support_bind_iff _ _ _).1 hz with ⟨aw, haw, hz⟩
  rcases aw with ⟨a, wa⟩
  rw [support_map] at hz
  rcases hz with ⟨bw, hbw, rfl⟩
  rcases bw with ⟨b, wb⟩
  simpa using Nat.add_le_add (h₁ (a, wa) haw) (h₂ a (b, wb) hbw)

lemma queryBoundedBelowBy_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryBoundedBelowBy oa n₁) (h₂ : ∀ a, QueryBoundedBelowBy (f a) n₂) :
    QueryBoundedBelowBy (oa >>= f) (n₁ + n₂) := by
  intro z hz
  rw [WriterT.run_bind] at hz
  rcases (mem_support_bind_iff _ _ _).1 hz with ⟨aw, haw, hz⟩
  rcases aw with ⟨a, wa⟩
  rw [support_map] at hz
  rcases hz with ⟨bw, hbw, rfl⟩
  rcases bw with ⟨b, wb⟩
  simpa using Nat.add_le_add (h₁ (a, wa) haw) (h₂ a (b, wb) hbw)

lemma queryBoundedBy_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryBoundedBy (f i) k) :
    QueryBoundedBy (Fin.mOfFn n f) (n * k) := by
  induction n with
  | zero =>
      simp [Fin.mOfFn, queryBoundedBy_pure]
  | succ n ih =>
      simp only [Fin.mOfFn, Nat.succ_mul]
      simpa [Nat.add_comm] using
        (queryBoundedBy_bind (n₁ := k) (n₂ := n * k)
          (by simpa using h 0)
          (fun a ↦
            queryBoundedBy_map (fun rest ↦ Fin.cons a rest)
              (ih (fun i ↦ h i.succ))))

lemma queryBoundedBelowBy_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryBoundedBelowBy (f i) k) :
    QueryBoundedBelowBy (Fin.mOfFn n f) (n * k) := by
  induction n with
  | zero =>
      simp [Fin.mOfFn, queryBoundedBelowBy_pure]
  | succ n ih =>
      simp only [Fin.mOfFn, Nat.succ_mul]
      simpa [Nat.add_comm] using
        (queryBoundedBelowBy_bind (n₁ := k) (n₂ := n * k)
          (by simpa using h 0)
          (fun a ↦
            queryBoundedBelowBy_map (fun rest ↦ Fin.cons a rest)
              (ih (fun i ↦ h i.succ))))

end unitCostBounds
end AddWriterT

namespace HasQuery

section runtimeInstantiation

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} {α : Type}

/-- Instantiate a generic `HasQuery` computation in the concrete runtime `runtime`. -/
def inRuntime (oa : [HasQuery spec m] → m α) (runtime : QueryRuntime spec m) : m α := by
  letI := runtime.toHasQuery
  exact oa

section instrumentation

variable [Monad m]

/-- Instantiate a generic `HasQuery` computation in the additive-cost instrumented runtime
obtained from `runtime`. -/
def withAddCost {ω : Type} [AddMonoid ω]
    (oa : [HasQuery spec (AddWriterT ω m)] → AddWriterT ω m α)
    (runtime : QueryRuntime spec m) (costFn : spec.Domain → ω) : AddWriterT ω m α := by
  letI := (runtime.withAddCost costFn).toHasQuery
  exact oa

/-- Instantiate a generic `HasQuery` computation in the unit-cost instrumented runtime obtained
from `runtime`. -/
def withUnitCost (oa : [HasQuery spec (AddWriterT ℕ m)] → AddWriterT ℕ m α)
    (runtime : QueryRuntime spec m) : AddWriterT ℕ m α := by
  letI := runtime.withUnitCost.toHasQuery
  exact oa

end instrumentation
end runtimeInstantiation

section queryBounds

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*}
variable [Monad m] [LawfulMonad m] [HasEvalSet m]

lemma queryBoundedBy_withUnitCost_query
    (runtime : QueryRuntime spec m) (t : spec.Domain) :
    AddWriterT.QueryBoundedBy
      (HasQuery.withUnitCost
        (fun [HasQuery spec (AddWriterT ℕ m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ℕ m) t)
        runtime)
      1 := by
  change AddWriterT.QueryBoundedBy ((runtime.withUnitCost).impl t) 1
  rw [QueryRuntime.withUnitCost_impl]
  apply AddWriterT.queryBoundedBy_bind (n₁ := 1) (n₂ := 0)
  · exact AddWriterT.queryBoundedBy_addTell 1
  · intro _
    exact AddWriterT.queryBoundedBy_monadLift (runtime.impl t)

lemma queryBoundedBelowBy_withUnitCost_query
    (runtime : QueryRuntime spec m) (t : spec.Domain) :
    AddWriterT.QueryBoundedBelowBy
      (HasQuery.withUnitCost
        (fun [HasQuery spec (AddWriterT ℕ m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ℕ m) t)
        runtime)
      1 := by
  change AddWriterT.QueryBoundedBelowBy ((runtime.withUnitCost).impl t) 1
  rw [QueryRuntime.withUnitCost_impl]
  apply AddWriterT.queryBoundedBelowBy_bind (n₁ := 1) (n₂ := 0)
  · exact AddWriterT.queryBoundedBelowBy_addTell 1
  · intro _
    exact AddWriterT.queryBoundedBelowBy_monadLift (runtime.impl t)

end queryBounds

section costAccounting

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} {α : Type}

/-- A computation generic over a `HasQuery spec m` capability. -/
abbrev Computation (spec : OracleSpec ι) (m : Type → Type*) (α : Type) :=
  [HasQuery spec m] → m α

section genericCost

variable [Monad m]

/-- Running `oa` in the additive-cost instrumentation of `runtime` yields an output-dependent
cost described by `f`. -/
def UsesCostAs {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (f : α → ω) : Prop :=
  AddWriterT.CostsAs (HasQuery.withAddCost oa runtime costFn) f

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs constant cost `w`. -/
def UsesCostExactly {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  Cost[ HasQuery.withAddCost oa runtime costFn ] = w

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs cost at most `w` on
every execution path. This is a semantic support bound, not merely an output-indexed cost
description. -/
def UsesCostAtMost {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m] [HasEvalSet m]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  ∀ z ∈ support (HasQuery.withAddCost oa runtime costFn).run, Multiplicative.toAdd z.2 ≤ w

/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs cost at least `w` on
every execution path. -/
def UsesCostAtLeast {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m] [HasEvalSet m]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  ∀ z ∈ support (HasQuery.withAddCost oa runtime costFn).run, w ≤ Multiplicative.toAdd z.2

lemma usesCostAtMost_of_usesCostExactly {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryRuntime spec m}
    {costFn : spec.Domain → ω} {w b : ω}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hwb : w ≤ b) :
    HasQuery.UsesCostAtMost oa runtime costFn b := by
  intro z hz
  have hzCost : Multiplicative.toAdd z.2 ∈
      support (HasQuery.withAddCost oa runtime costFn).costs := by
    rw [AddWriterT.costs_def, support_map]
    exact ⟨z, hz, rfl⟩
  rw [h] at hzCost
  rw [support_map] at hzCost
  rcases hzCost with ⟨a, _, hzCost⟩
  simpa [hzCost] using hwb

lemma usesCostAtLeast_of_usesCostExactly {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryRuntime spec m}
    {costFn : spec.Domain → ω} {w b : ω}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hbw : b ≤ w) :
    HasQuery.UsesCostAtLeast oa runtime costFn b := by
  intro z hz
  have hzCost : Multiplicative.toAdd z.2 ∈
      support (HasQuery.withAddCost oa runtime costFn).costs := by
    rw [AddWriterT.costs_def, support_map]
    exact ⟨z, hz, rfl⟩
  rw [h] at hzCost
  rw [support_map] at hzCost
  rcases hzCost with ⟨a, _, hzCost⟩
  simpa [hzCost] using hbw

/-- Unit-cost specialization: every query contributes cost `1`. -/
def UsesExactlyQueries (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryRuntime spec m) (n : ℕ) : Prop :=
  HasQuery.UsesCostExactly oa runtime (fun _ ↦ 1) n

/-- Unit-cost specialization: every query contributes cost `1`, with an upper bound. -/
def UsesAtMostQueries [LawfulMonad m] [HasEvalSet m]
    (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryRuntime spec m) (n : ℕ) : Prop :=
  AddWriterT.QueryBoundedBy (HasQuery.withUnitCost oa runtime) n

/-- Unit-cost specialization: every query contributes cost `1`, with a lower bound. -/
def UsesAtLeastQueries [LawfulMonad m] [HasEvalSet m]
    (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryRuntime spec m) (n : ℕ) : Prop :=
  AddWriterT.QueryBoundedBelowBy (HasQuery.withUnitCost oa runtime) n

lemma usesAtMostQueries_of_usesExactlyQueries
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m}
    {n b : ℕ} (h : HasQuery.UsesExactlyQueries oa runtime n) (hnb : n ≤ b) :
    HasQuery.UsesAtMostQueries oa runtime b :=
  usesCostAtMost_of_usesCostExactly h hnb

lemma usesAtLeastQueries_of_usesExactlyQueries
    [LawfulMonad m] [HasEvalSet m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryRuntime spec m}
    {n b : ℕ} (h : HasQuery.UsesExactlyQueries oa runtime n) (hbn : b ≤ n) :
    HasQuery.UsesAtLeastQueries oa runtime b :=
  usesCostAtLeast_of_usesCostExactly h hbn

end genericCost

/-- `Queries[ oa in runtime ] = n` means that the generic `HasQuery` computation `oa` makes
exactly `n` oracle queries when instantiated in `runtime` and instrumented with unit additive
cost per query.

The computation `oa` is written in direct `HasQuery` style. The notation elaborates it against
the unit-cost analysis monad induced by `runtime`, so statements can usually be written without
explicit monad annotations such as `m := AddWriterT ℕ m`. -/
syntax:max "Queries[ " term " in " term " ]" " = " term:50 : term

macro_rules
  | `(Queries[ $oa in $runtime ] = $n) =>
      `(HasQuery.UsesExactlyQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $n)

/-- `Queries[ oa in runtime ] ≤ n` means that every execution path of `oa` makes at most `n`
oracle queries when run in the unit-cost instrumentation of `runtime`.

This packages the common cryptographic statement “the construction uses at most `n` queries” on
top of [`HasQuery.UsesAtMostQueries`]. -/
syntax:max "Queries[ " term " in " term " ]" " ≤ " term:50 : term

macro_rules
  | `(Queries[ $oa in $runtime ] ≤ $n) =>
      `(HasQuery.UsesAtMostQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $n)

/-- `Queries[ oa in runtime ] ≥ n` means that every execution of `oa` in the unit-cost
instrumentation of `runtime` incurs at least `n` query-cost units.

This is less common than the exact and upper-bound forms, but it is useful for statements saying
that a construction must query the oracle at least a certain number of times. -/
syntax:max "Queries[ " term " in " term " ]" " ≥ " term:50 : term

macro_rules
  | `(Queries[ $oa in $runtime ] ≥ $n) =>
      `(HasQuery.UsesAtLeastQueries
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          $runtime $n)

/-- `QueryCost[ oa in runtime by costFn ] = w` means that `oa`, instantiated in `runtime` and
instrumented so that each query `t` contributes cost `costFn t`, has constant total query cost
`w`.

Use this when the cost model is not unit cost, for example when different query families or
different query shapes carry different weights. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " = " term:50 : term

macro_rules
  | `(QueryCost[ $oa in $runtime by $costFn ] = $w) =>
      `(HasQuery.UsesCostExactly
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
          $runtime $costFn $w)

/-- `QueryCost[ oa in runtime by costFn ] ≤ w` means that every execution path of `oa` has total
query cost bounded above by `w` under the weighting function `costFn`.

This is the weighted analogue of [`Queries[ oa in runtime ] ≤ n`]. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " ≤ " term:50 : term

macro_rules
  | `(QueryCost[ $oa in $runtime by $costFn ] ≤ $w) =>
      `(HasQuery.UsesCostAtMost
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
          $runtime $costFn $w)

/-- `QueryCost[ oa in runtime by costFn ] ≥ w` means that every execution path of `oa` has total
query cost bounded below by `w` under the weighting function `costFn`.

This is the weighted analogue of [`Queries[ oa in runtime ] ≥ n`]. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " ≥ " term:50 : term

macro_rules
  | `(QueryCost[ $oa in $runtime by $costFn ] ≥ $w) =>
      `(HasQuery.UsesCostAtLeast
          (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
          $runtime $costFn $w)

end costAccounting

end HasQuery
