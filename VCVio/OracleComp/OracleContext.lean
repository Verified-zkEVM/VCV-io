/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Append

/-!
# Bundled Oracle Specs and Implementations

This file defines a type `OracleContext ι m` that provides an ambient set of oracles,
along with an implementation of those oracles in the monad `m`.

-/

universe u v w z

open OracleSpec OracleComp Polynomial MvPolynomial

/-- An `OracleContext ι m` bundles a specification `spec` of oracles with input set `ι`
and an implementation of the oracles in terms of the monad `m`.
Structures can extend this to get  -/
structure OracleContext (ι : Type u) (m : Type v → Type w) :
      Type (max u v w + 1) where
  spec : OracleSpec.{u,v} ι
  impl : QueryImpl spec m

/-- Convert an `OracleSpec` into an `OracleContext` with `OracleComp` as the implementation monad,
using the identity implementation for queries. -/
@[reducible]
def OracleSpec.defaultContext {ι : Type u} (spec : OracleSpec ι) :
    OracleContext spec.Domain (OracleComp spec) where
  spec := spec
  impl := QueryImpl.id' spec

namespace OracleContext

instance {ι} {m : Type u → Type v} [Pure m] : Inhabited (OracleContext ι m) :=
  ⟨{ spec := ι →ₒ PUnit, impl _ := pure PUnit.unit }⟩

variable {ι ι'} {spec : OracleSpec ι} {m : Type u → Type v}

/-- Convert a `QueryImpl` into an `OracleContext` by bundling the `OracleSpec` corresponding
to the particular implementation. -/
@[reducible] def ofImpl (impl : QueryImpl spec m) : OracleContext ι m where
  spec := spec
  impl := impl

/-- Combine two oracle contexts with the same target monad, giving access to both ambient
oracles and implementing queries to each independently. -/
@[reducible] protected def add (O : OracleContext ι m) (O' : OracleContext ι' m) :
    OracleContext (ι ⊕ ι') m where
  spec := O.spec + O'.spec
  impl := O.impl + O'.impl

instance : HAdd (OracleContext ι m) (OracleContext ι' m)
    (OracleContext (ι ⊕ ι') m) where
  hAdd := OracleContext.add

@[simp] lemma add_def (O : OracleContext ι m) (O' : OracleContext ι' m) :
    O + O' = O.add O' := rfl

lemma spec_add (O : OracleContext ι m) (O' : OracleContext ι' m) :
    (O + O').spec = O.spec + O'.spec := by simp

lemma impl_add (O : OracleContext ι m) (O' : OracleContext ι' m) :
    (O + O').impl = O.impl + O'.impl := by simp

end OracleContext
