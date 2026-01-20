/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Query Implementations with State Monads

This file gives lemmas about `QueryImpl spec m` when `m` is something like `StateT σ n`.

TODO: should generalize things to `MonadState` once laws for it exist.
-/

universe u v w

open OracleSpec

namespace QueryImpl

/-- Given implementations for oracles in `spec₁` and `spec₂` in terms of reader monads for
two different contexts `ρ₁` and `ρ₂`, implement the combined set `spec₁ + spec₂` in terms
of a combined `ρ₁ × ρ₂` state.
dtumad: should we call this an addition or multiplication operation? -/
def addReaderT {ι₁ ι₂ : Type _}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type _ → Type _} {ρ₁ ρ₂ : Type _}
    (impl₁ : QueryImpl spec₁ (ReaderT ρ₁ m))
    (impl₂ : QueryImpl spec₂ (ReaderT ρ₂ m)) :
    QueryImpl (spec₁ + spec₂) (ReaderT (ρ₁ × ρ₂) m)
  | .inl t => ReaderT.mk fun s => (impl₁ t).run s.1
  | .inr t => ReaderT.mk fun s => (impl₂ t).run s.2

/-- Indexed version of `QueryImpl.prodReader`. Note that `m` cannot vary with `t`. -/
def sigmaReaderT {τ : Type} {ι : τ → Type _}
    {spec : (t : τ) → OracleSpec (ι t)}
    {m : Type _ → Type _} {ρ : τ → Type _}
    (impl : (t : τ) → QueryImpl (spec t) (ReaderT (ρ t) m)) :
    QueryImpl (OracleSpec.sigma spec) (ReaderT ((t : τ) → ρ t) m)
  | ⟨t, q⟩ => ReaderT.mk fun s => (impl t q).run (s t)


end QueryImpl
