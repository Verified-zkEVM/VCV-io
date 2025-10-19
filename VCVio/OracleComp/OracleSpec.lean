/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Data.Fintype.Card
import ToMathlib.PFunctor.Basic

/-!
# Specifications of Available Oracles

This file defines a type `OracleSpec` to represent a set of available oracles.
The available oracles are all indexed by some (potentially infinite) indexing set `ι`,
and for each index `i` a pair of types `domain i` and `range i`.

TODO: update documentation (now there is a single dependent oracle)

We also define a number of basic oracle constructions:
* `T →ₒ U`: Access to a single oracle with given input and output
* `coinSpec`: A single oracle for flipping a coin
* `unifSpec`: A family of oracles for selecting from `[0..n]` for any `n`
-/

universe u u' v w

/-- Oracles are specified by a polynomial functor, where `domain` is the index/input of the oracle,
and `range` gives the output type of the oracle for a given index.
This type is essentially a copy of `PFunctor` used to hide certain abstractions
in a form that is more familiar to an average user. -/
structure OracleSpec where
  Domain : Type u
  Range : Domain → Type v
  deriving Inhabited

namespace OracleSpec

variable {spec : OracleSpec}

instance : Coe OracleSpec PFunctor where
  coe spec := { A := spec.Domain, B := spec.Range }

@[simp] lemma coe_def (spec : OracleSpec) :
    (↑spec : PFunctor) = { A := spec.Domain, B := spec.Range } := rfl

@[reducible, simp] def ofPFunctor (P : PFunctor) : OracleSpec :=
  { Domain := P.A, Range := P.B }

/-- An oracle spec has indexing in a type `ι` if the `range` function factors through `ι`.
dt: not sure if this is really the right approach for e.g. `pregen`. -/
class HasIndexing (spec : OracleSpec) (ι : Type w) where
  idx : spec.Domain → ι
  xdi : ι → Type _
  range_idx (t : spec.Domain) : spec.Range t = xdi (idx t)

protected class Fintype (spec : OracleSpec) extends PFunctor.Fintype ↑spec
protected class Inhabited (spec : OracleSpec) extends PFunctor.Inhabited ↑spec
protected class DecidableEq (spec : OracleSpec) extends PFunctor.DecidableEq ↑spec

instance [h : spec.Fintype] (t : spec.Domain) : Fintype (spec.Range t) := h.fintype_B t
instance [h : spec.Inhabited] (t : spec.Domain) : Inhabited (spec.Range t) := h.inhabited_B t
instance [h : spec.DecidableEq] : DecidableEq spec.Domain := h.decidableEq_A
instance [h : spec.DecidableEq] (t : spec.Domain) : DecidableEq (spec.Range t) := h.decidableEq_B t

instance : Add OracleSpec where add spec spec' := ofPFunctor (spec + spec')

@[simp] lemma domain_add (spec spec' : OracleSpec) :
    (spec + spec').Domain = (spec.Domain ⊕ spec'.Domain) := rfl
@[simp] lemma range_add_inl (spec spec' : OracleSpec) (t : spec.Domain) :
    (spec + spec').Range (.inl t) = spec.Range t := rfl
@[simp] lemma range_add_inr (spec spec' : OracleSpec) (t : spec'.Domain) :
    (spec + spec').Range (.inr t) = spec'.Range t := rfl

end OracleSpec

def emptySpec : OracleSpec := .ofPFunctor 0
notation "[]ₒ" => emptySpec

def singletonSpec (A B : Type*) : OracleSpec := .ofPFunctor (PFunctor.ofConst A B)
infixl : 25 " →ₒ " => singletonSpec

/-- Access to a coin flipping oracle. Because of termination rules in Lean this is slightly
weaker than `unifSpec`, as we have only finitely many coin flips. -/
@[inline, reducible]
def coinSpec : OracleSpec.{0,0} := Unit →ₒ Bool

@[simp] lemma domain_coinSpec : coinSpec.Domain = Unit := rfl
@[simp] lemma range_coinSpec (t : coinSpec.Domain) : coinSpec.Range t = Bool := rfl

/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`.
By adding `1` to the index we avoid selection from the empty type `Fin 0 ≃ empty`.-/
@[inline, reducible] def unifSpec : OracleSpec.{0,0} where
  Domain := ℕ
  Range n := Fin (n + 1)

@[simp] lemma domain_unifSpec : unifSpec.Domain = ℕ := rfl
@[simp] lemma range_unifSpec (t : unifSpec.Domain) : unifSpec.Range t = Fin (t + 1) := rfl

instance : unifSpec.Fintype where fintype_B n := inferInstanceAs (Fintype (Fin (n + 1)))
instance : unifSpec.Inhabited where inhabited_B n := inferInstanceAs (Inhabited (Fin (n + 1)))

/-- dt: should or shouldn't we switch to this. Compare to `(· + m) <$> $[0..n]`.
One question is that we may have empty selection
Select uniformly from a range (not starting from zero).-/
@[inline, reducible] def probSpec : OracleSpec.{0,0} where
  Domain := ℕ × ℕ
  Range r := Fin (r.2 + 1)
