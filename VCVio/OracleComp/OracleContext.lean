/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Append

/-!
# Bundled Oracle Specs and Implementations

This file defines a type `OracleContext m` that provides an ambient set of oracles,
along with an implementation of those oracles in the monad `m`.

-/

universe u v w z

open OracleSpec OracleComp Polynomial MvPolynomial

/-- An `OracleContext m` bundles an ambient `OracleSpec` with an implementation of
itself in terms of the monad `m`. This is useful for defining a shared interface
in protocols where the execution method in protocol-dependent.
A signature scheme for example could either include a random oracle or not,
and set the appropriate behavior for the oracles in `OracleContext.impl`.-/
structure OracleContext (m : Type v → Type w) :
      Type (max u v w + 1) extends OracleSpec.{u,v}
  where impl : QueryImpl toOracleSpec m

namespace OracleContext

variable {spec : OracleSpec} {m : Type u → Type v}

instance {m : Type u → Type v} : Inhabited (OracleContext m) :=
  ⟨{ toOracleSpec := []ₒ, impl t := PEmpty.elim t }⟩

/-- Simple `OracleContext` that implements the queries in the same original `spec`.  -/
def defaultContext (spec : OracleSpec.{u,v}) :
    OracleContext (OracleComp spec) where
  toOracleSpec := spec
  impl := QueryImpl.id' spec

/-- Convert a `QueryImpl` of `spec` in monad `m` to an oracle context by
taking the ambient  -/
@[reducible] def ofImpl {spec : OracleSpec} (impl : QueryImpl spec m) :
    OracleContext m where
  toOracleSpec := spec
  impl := impl

/-- Oracle context corresponding to black-box evaluation of `f` at an input. -/
@[reducible] def ofFn {α : Type u} {β : α → Type v} (f : (t : α) → β t) :
    OracleContext Id where
  toOracleSpec := singletonSpec α β
  impl t := do return f t

/-- Oracle context corresponding to black-box evaluation of a polynomial at points. -/
@[reducible] def ofPolynomial {R} [Semiring R] (p : R[X]) : OracleContext Id :=
  ofFn fun t : R => p.eval t

/-- Oracle context corresponding to black-box evaluation of a mv polynomial at points. -/
@[reducible] def ofMvPolynomial {R σ} [CommSemiring R] (p : MvPolynomial σ R) : OracleContext Id :=
  ofFn fun t : σ → R => p.eval t

/-- Oracle context for ability to query elements of a vector `v`. -/
@[reducible] def ofVector {α n} (v : Vector α n) : OracleContext Id :=
  ofFn fun t : Fin n => v[t]

/-- Oracle context for ability to query elements of a vector `v`. -/
@[reducible] def ofListVector {α n} (v : List.Vector α n) : OracleContext Id :=
  ofFn fun t : Fin n => v[t]

/-- Combine two oracle contexts with the same target monad, giving access to both ambient
oracles and implementing queries to each independently. -/
@[reducible] protected def add {m : Type u → Type v}
    (O O' : OracleContext m) : OracleContext m where
  toOracleSpec := O.toOracleSpec + O'.toOracleSpec
  impl := O.impl + O'.impl

instance : Add (OracleContext m) where add := OracleContext.add

end OracleContext
