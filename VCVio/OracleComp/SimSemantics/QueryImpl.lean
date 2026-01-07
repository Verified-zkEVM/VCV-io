/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.OracleComp
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Implementing Oracle Queries in Other Monads

This file defines a type `QueryImpl spec m` to represent implementations
of queries to `spec` in terms of the monad `m`.
-/

open OracleSpec OracleComp

universe u v w

/-- Specifies a way to implement queries to oracles in `spec` using the monad `m`.
This is defined in terms of a mapping of input elements to oracle outputs,
which extends to a mapping on `OracleQuery spec` by copying over the continuation,
and then further to `OracleComp spec` by preserving the pure and bind operations.
See `QueryImpl.map_query` and `HasSimulateQ` for these two operations. -/
@[reducible] def QueryImpl {ι} (spec : OracleSpec ι) (m : Type u → Type v) :=
  (x : spec.Domain) → m (spec.Range x)

namespace QueryImpl

variable {ι} {spec : OracleSpec ι} {m : Type u → Type v} {n : Type u → Type w}

instance [spec.Inhabited] [Pure m] : Inhabited (QueryImpl spec m) where
  default _ := pure default

/-- Two query implementations are the same if they are the same on all query inputs. -/
@[ext] lemma ext {so so' : QueryImpl spec m}
    (h : ∀ x : spec.Domain, so x = so' x) : so = so' := funext h

/-- Embed an oracle query into a new functor by applying the implementation to the input value
before applying the continuation of the element. -/
def mapQuery {α} [Functor m] (impl : QueryImpl spec m)
    (q : OracleQuery spec α) : m α := q.cont <$> impl q.input

@[simp] lemma mapQuery_query [Functor m] [LawfulFunctor m] (impl : QueryImpl spec m)
    (t : spec.Domain) : impl.mapQuery (query t) = impl t := by
  simp [mapQuery]

section liftTarget

/-- Gadget for auto-adding a lift to the end of a query implementation. -/
def liftTarget (n : Type u → Type*) [MonadLiftT m n]
    (impl : QueryImpl spec m) : QueryImpl spec n :=
  fun t : spec.Domain => liftM (impl t)

@[simp] lemma liftTarget_apply (n : Type u → Type*) [MonadLiftT m n]
    (impl : QueryImpl spec m) (t : spec.Domain) : impl.liftTarget n t = liftM (impl t) := rfl

/-- Lifting an implementation to the original monad has no effect. -/
@[simp] lemma liftTarget_self (impl : QueryImpl spec m) :
    impl.liftTarget m = impl := rfl

@[simp] lemma mapQuery_liftTarget {α} (n : Type u → Type w)
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [MonadLiftT m n]
    [LawfulMonadLiftT m n] (impl : QueryImpl spec m) (q : OracleQuery spec α) :
    (impl.liftTarget n).mapQuery q = liftM (impl.mapQuery q) := by
  simp [mapQuery]

end liftTarget

section id

/-- Identity implementation for queries, sending `q : OracleQuery spec α` to itself. -/
protected def id (spec : OracleSpec ι) :
    QueryImpl spec (OracleQuery spec) := query

@[simp] lemma id_apply {spec : OracleSpec ι} (t : spec.Domain) :
    QueryImpl.id spec t = query t := rfl

@[simp] lemma mapQuery_id {α} {spec : OracleSpec ι} (q : OracleQuery spec α) :
    (QueryImpl.id spec).mapQuery q = q := rfl

/-- Version of `QueryImpl.id` that automatically lifts into `OracleComp spec` rather than
just implementing queries in the lower level `OracleQuery spec` monad -/
protected def id' {ι} (spec : OracleSpec ι) :
    QueryImpl spec (OracleComp spec) := QueryImpl.liftTarget _ (QueryImpl.id spec)

@[simp] lemma id'_apply {spec : OracleSpec ι} (t : spec.Domain) :
    QueryImpl.id' spec t = liftM (query t) := rfl

@[simp] lemma mapQuery_id' {α} {spec : OracleSpec ι} (q : OracleQuery spec α) :
    (QueryImpl.id' spec).mapQuery q = q := rfl

end id

section ofLift

/-- Given that queries in `spec` lift to the monad `m` we get an implementation via lifting. -/
def ofLift (spec : OracleSpec ι) (m : Type u → Type v)
    [MonadLiftT (OracleQuery spec) m] : QueryImpl spec m :=
  fun t : spec.Domain => liftM (query t)

@[simp] lemma ofLift_apply (spec : OracleSpec ι) (m : Type u → Type v)
    [MonadLiftT (OracleQuery spec) m] (t : spec.Domain) : ofLift spec m t = liftM (query t) := rfl

@[simp] lemma mapQuery_ofLift {α} (spec : OracleSpec ι) (m : Type u → Type v)
    [Functor m] [MonadLiftT (OracleQuery spec) m] (q : OracleQuery spec α) :
    (ofLift spec m).mapQuery q = q.cont <$> liftM (query q.input) := by
  simp [mapQuery]

@[simp] lemma ofLift_eq_id : ofLift spec (OracleQuery spec) = QueryImpl.id spec := rfl

@[simp] lemma ofLift_eq_id' : ofLift spec (OracleComp spec) = QueryImpl.id' spec := rfl

end ofLift

section ofFn

/-- View a function from oracle inputs to outputs as an implementation in the `Id` monad.
Can be used to run a computation to get a specific value. -/
def ofFn (f : (t : spec.Domain) → spec.Range t) :
    QueryImpl spec Id := f

@[simp] lemma ofFn_apply (f : (t : spec.Domain) → spec.Range t)
    (t : spec.Domain) : ofFn f t = f t := rfl

@[simp] lemma mapQuery_ofFn {α} (f : (t : spec.Domain) → spec.Range t)
    (q : OracleQuery spec α) : (ofFn f).mapQuery q = q.cont (f q.input) := rfl

end ofFn

section ofFn?

/-- Version of `ofFn` that allows queries to fail to return a value. -/
def ofFn? (f : (t : spec.Domain) → Option (spec.Range t)) :
    QueryImpl spec Option := f

@[simp] lemma ofFn?_apply (f : (t : spec.Domain) → Option (spec.Range t))
    (t : spec.Domain) : ofFn? f t = f t := rfl

@[simp] lemma mapQuery_ofFn? {α} (f : (t : spec.Domain) → Option (spec.Range t))
    (q : OracleQuery spec α) : (ofFn? f).mapQuery q = (f q.input).map q.cont := rfl

end ofFn?

/-- Implement a single oracle as evaluation of a `Polynomial`. -/
@[reducible] def ofPolynomial {R} [Semiring R] (p : Polynomial R) :
    QueryImpl (R →ₒ R) Id :=
  .ofFn fun t : R => p.eval t

/-- Implement a single oracle as the evaluation of an `MvPolynomial. -/
@[reducible] def ofMvPolynomial {R σ} [CommSemiring R] (p : MvPolynomial σ R) :
    QueryImpl ((σ → R) →ₒ R) Id :=
  .ofFn fun t : σ → R => p.eval t

/-- Implement a single oracle as indexing into a `Vector`. -/
@[reducible] def ofVector {α n} (v : Vector α n) :
    QueryImpl (Fin n →ₒ α) Id :=
  .ofFn fun t : Fin n => v[t]

/-- Oracle context for ability to query elements of a vector `v`. -/
@[reducible] def ofListVector {α n} (v : List.Vector α n) :
    QueryImpl (Fin n →ₒ α) Id :=
  .ofFn fun t : Fin n => v[t]

end QueryImpl
