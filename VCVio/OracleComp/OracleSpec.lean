/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Fintype.Card

/-!
# Specifications of Available Oracles

This file defines a type `OracleSpec` to represent a set of available oracles.
The available oracles are all indexed by some (potentially infinite) indexing set `ι`,
and for each index `i` a pair of types `domain i` and `range i`.

We also define a number of basic oracle constructions:
* `∅`: Access to no oracles
* `T →ₒ U`: Access to a single oracle with given input and output
* `coinSpec`: A single oracle for flipping a coin
* `unifSpec`: A family of oracles for selecting from `[0..n]` for any `n`
-/

universe u u' v w

/-- A structure to represents a specification of oracles available to a computation.
The available oracles are all indexed by some (potentially infinite) indexing set `ι`.
Represented as a map from indices `i` to the domain and codomain of the corresponding oracle. -/
def OracleSpec (ι : Type u) : Type (max u (v + 1)) :=
  (i : ι) → Type v × Type v

namespace OracleSpec

variable {ι : Type u} {τ : Type u'} {spec : OracleSpec ι} (i : ι)

instance : Inhabited (OracleSpec ι) := ⟨λ _ ↦ (PUnit, PUnit)⟩

/-- Type of the domain for calls to the oracle corresponding to `i`. -/
@[inline, reducible]
protected def domain (spec : OracleSpec ι) (i : ι) : Type v := (spec i).1

/-- Type of the range for calls to the oracle corresponding to `i`. -/
@[inline, reducible]
protected def range (spec : OracleSpec ι) (i : ι) : Type w := (spec i).2

/-- Typeclass to capture decidable equality of the oracle input and outputs.
Needed for things like `finSupport` to be well defined. -/
protected class DecidableEq (spec : OracleSpec ι) where
  domain_decidableEq' (i : ι) : DecidableEq (spec.domain i)
  range_decidableEq' (i : ι) : DecidableEq (spec.range i)

instance domain_decidableEq {i : ι} [h : spec.DecidableEq] :
    DecidableEq (spec.domain i) := h.domain_decidableEq' i

instance range_decidableEq {i : ι} [h : spec.DecidableEq] :
    DecidableEq (spec.range i) := h.range_decidableEq' i

/-- Typeclass for specs where each oracle has a finite and non-empty output type.
Needed for things like `evalDist` and `probOutput`. -/
class FiniteRange (spec : OracleSpec ι) where
    range_inhabited' (i : ι) : Inhabited (spec.range i)
    range_fintype' (i : ι) : Fintype (spec.range i)

instance range_inhabited {i : ι} [h : FiniteRange spec] :
    Inhabited (spec.range i) := h.range_inhabited' i

instance range_fintype {i : ι} [h : FiniteRange spec] :
    Fintype (spec.range i) := h.range_fintype' i

section append

/-- `spec₁ ++ spec₂` combines the two sets of oracles disjointly using `Sum` for the indexing set.
`inl i` is a query to oracle `i` of `spec`, and `inr i` for oracle `i` of `spec'`. -/
def append {ι₁ : Type u} {ι₂ : Type u'} (spec₁ : OracleSpec ι₁) (spec₂ : OracleSpec ι₂) :
    OracleSpec (ι₁ ⊕ ι₂) := 
  fun | .inl i => spec₁ i | .inr i => spec₂ i
    
    -- Sum.elim spec₁ spec₂



infixl : 65 " ++ₒ " => OracleSpec.append

variable {ι₁ : Type u} {ι₂ : Type u'} (spec₁ : OracleSpec ι₁) (spec₂ : OracleSpec ι₂)

instance [h₁ : spec₁.DecidableEq] [h₂ : spec₂.DecidableEq] :
    (spec₁ ++ₒ spec₂).DecidableEq where
  domain_decidableEq' := Sum.rec h₁.domain_decidableEq' h₂.domain_decidableEq'
  range_decidableEq' := Sum.rec h₁.range_decidableEq' h₂.range_decidableEq'

instance [h₁ : spec₁.FiniteRange] [h₂ : spec₂.FiniteRange] :
    (spec₁ ++ₒ spec₂).FiniteRange where
  range_inhabited' := λ i ↦ Sum.recOn i h₁.range_inhabited' h₂.range_inhabited'
  range_fintype' := λ i ↦ Sum.recOn i h₁.range_fintype' h₂.range_fintype'

end append

/-- Reduce the indexing set by pulling back along some map `f`. -/
@[inline, reducible]
def rename (spec : OracleSpec ι) (f : τ → ι) : OracleSpec τ := spec ∘ f

end OracleSpec

open OracleSpec

/-- Access to no oracles, represented by an empty indexing set.
We take the domain and range to be `PUnit` (rather than e.g. `empty.elim i`),
which often gives better behavior for proofs even though the oracle is never called. -/
@[inline, reducible]
def emptySpec : OracleSpec PEmpty := λ _ ↦ (PUnit, PUnit)

notation "[]ₒ" => emptySpec

instance (i : PEmpty) : Unique ([]ₒ.domain i) := PUnit.instUnique
instance (i : PEmpty) : Unique ([]ₒ.range i) := PUnit.instUnique

instance : OracleSpec.DecidableEq []ₒ where
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance

instance : FiniteRange []ₒ where
  range_inhabited' := inferInstance
  range_fintype' := inferInstance

/-- `T →ₒ U` represents a single oracle, with domain `T` and range `U`.
Uses the singleton type `PUnit` as the indexing set. -/
@[inline, reducible]
def singletonSpec (T U : Type v) : OracleSpec.{u,v} PUnit :=
  λ _ ↦ (T, U)

infixl : 25 " →ₒ " => singletonSpec

instance {T U : Type v} [DecidableEq T] [DecidableEq U] : (T →ₒ U).DecidableEq where
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance

instance {T U : Type v} [Inhabited U] [Fintype U] : (T →ₒ U).FiniteRange where
  range_inhabited' := inferInstance
  range_fintype' := inferInstance

/-- A coin flipping oracle produces a random `Bool` with no meaningful input. -/
@[inline, reducible] def coinSpec : OracleSpec.{0,0} Unit := Unit →ₒ Bool

instance : coinSpec.DecidableEq where
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance

instance : coinSpec.FiniteRange where
  range_inhabited' := inferInstance
  range_fintype' := inferInstance

-- Nicer than uniform selection but worse computability.
-- Could just throw errors running if no selectable type exists.
def unifSpec' : OracleSpec.{u+1,u} (Type u) :=
  λ α : Type u ↦ (PUnit, α)

/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`.
By adding `1` to the index we avoid selection from the empty type `Fin 0 ≃ empty`.-/
@[inline, reducible] def unifSpec : OracleSpec.{0,0} ℕ :=
  λ n ↦ (Unit, Fin (n + 1))

def probSpec : OracleSpec.{0,0} ℕ :=
  fun n => (ℕ, Fin (n + 1))

instance : unifSpec.DecidableEq where
  domain_decidableEq' := inferInstance
  range_decidableEq' := inferInstance

instance : unifSpec.FiniteRange where
  range_inhabited' := inferInstance
  range_fintype' := inferInstance
