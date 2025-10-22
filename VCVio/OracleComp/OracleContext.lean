/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Bundled Oracle Specs and Implementations

-/

universe u v w z

open OracleSpec OracleComp

/-- An `OracleContext m` bundles an `OracleSpec` with an implementation of
itself in terms of the monad `m`. This is useful for defining a shared interface
in protocols where the execution method in protocol-dependent.

A signature scheme for example could either include a random oracle or not,
and set the appropriate behavior for the oracles in `OracleContext.impl`.-/
structure OracleContext (m : Type v → Type w) :
      Type (max u v w + 1) extends OracleSpec.{u,v}
  where impl : QueryImpl toOracleSpec m

namespace OracleContext

/-- Simple `OracleContext` that implements the queries in the same
overall `OracleComp spec` monad. -/
def defaultContext (spec : OracleSpec.{u,v}) :
    OracleContext (OracleComp spec) where
  toOracleSpec := spec
  impl := QueryImpl.id' spec

end OracleContext
