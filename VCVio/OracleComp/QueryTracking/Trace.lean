/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.OracleComp.Coinductive.DynSystem
import PolyFun.PFunctor.Trace

/-!
# Query logs and counts as polynomial-functor traces

VCVio's query-tracking carriers are *already* the generic PFunctor trace types of
`PolyFun.PFunctor.Trace`, up to definitional unfolding — this file makes that identification
explicit so the abstract trace algebra (`Control.Trace`, `PFunctor.TraceList`, the free-monoid
universal property `FreeMonoid.lift`) applies to oracle logs and counts.

* `QueryLog spec` is the free monoid on query/answer events `PFunctor.Idx spec.toPFunctor`, i.e.
  `PFunctor.TraceList spec.toPFunctor` (`queryLog_eq_traceList`). The empty log is `1`, a single
  entry is `FreeMonoid.of`, and `withLogging`'s instrumentation is exactly `FreeMonoid.of`.
* `QueryCount ι` is `Control.Trace ℕ ι` (`queryCount_eq_controlTrace`) — but with the bespoke
  *additive* monoid, **not** `Control.Trace`'s default pointwise-multiplicative one.
* Every monoid-valued readout of a run factors through the log by the free-monoid universal
  property: `FreeMonoid.lift φ` post-composes a log with a valuation `φ : Idx → ω`. The coalgebraic
  `OracleComp.transcript` (in `Coinductive.DynSystem`) is such a free-monoid word.

These are identities (`rfl`) — the unification is latent in the definitions; we only name it.
-/

universe u v

open OracleSpec OracleComp

namespace OracleSpec.QueryLog

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}

/-! ### `QueryLog` is the free monoid on query events -/

/-- A query log is the free monoid on query/answer events `PFunctor.Idx spec.toPFunctor`. -/
theorem eq_traceList : QueryLog spec = PFunctor.TraceList spec.toPFunctor := rfl

/-- The empty log is the free-monoid identity. -/
theorem nil_eq_one : ([] : QueryLog spec) = (1 : PFunctor.TraceList spec.toPFunctor) := rfl

/-- A single-entry log is a free-monoid generator. -/
theorem singleton_eq_of (t : spec.Domain) (u : spec.Range t) :
    QueryLog.singleton t u = FreeMonoid.of (⟨t, u⟩ : PFunctor.Idx spec.toPFunctor) := rfl

/-- The `withLogging` instrumentation `fun t u => [⟨t, u⟩]`, read as a valuation
`PFunctor.Idx spec.toPFunctor → QueryLog spec`, is exactly the free-monoid generator map. -/
theorem withLogging_traceFn_eq_of :
    (fun i : PFunctor.Idx spec.toPFunctor => ([⟨i.1, i.2⟩] : QueryLog spec)) =
      fun i => FreeMonoid.of i := rfl

/-- The free-monoid universal property at a generator: a valuation `φ : Idx → ω` reads a
single-entry log as `φ ⟨t, u⟩`. The base case of "every monoid readout factors through the log". -/
@[simp] theorem lift_singleton {ω : Type*} [Monoid ω] (φ : PFunctor.Idx spec.toPFunctor → ω)
    (t : spec.Domain) (u : spec.Range t) :
    FreeMonoid.lift φ (QueryLog.singleton t u) = φ ⟨t, u⟩ := rfl

end OracleSpec.QueryLog

namespace OracleSpec.QueryCount

variable {ι : Type u}

/-- A per-oracle query count is an `ℕ`-valued `Control.Trace`. **Caveat:** the load-bearing monoid
on `QueryCount` is the bespoke *additive* one (`Structures.lean`); it is **not** `Control.Trace`'s
default pointwise-multiplicative `Pi.monoid`, so do not infer the monoid through this equality. -/
theorem eq_controlTrace : QueryCount ι = Control.Trace ℕ ι := rfl

end OracleSpec.QueryCount

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α : Type v}

/-- The coalgebraic `transcript` is a free-monoid word, so any valuation `φ` of query events reads
it off by `FreeMonoid.lift φ` — the monoid-trace view of a deterministic run. -/
theorem lift_transcript_pure {ω : Type*} [Monoid ω] (φ : PFunctor.Idx spec.toPFunctor → ω)
    (h : OracleHandler spec) (x : α) :
    FreeMonoid.lift φ (transcript h (pure x : OracleComp spec α)) = 1 :=
  map_one (FreeMonoid.lift φ)

theorem lift_transcript_queryBind {ω : Type*} [Monoid ω] (φ : PFunctor.Idx spec.toPFunctor → ω)
    (h : OracleHandler spec) (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    FreeMonoid.lift φ (transcript h (queryBind t k)) =
      φ ⟨t, h t⟩ * FreeMonoid.lift φ (transcript h (k (h t))) := by
  rw [transcript_queryBind]
  simp only [FreeMonoid.lift_apply]
  rfl

end OracleComp
