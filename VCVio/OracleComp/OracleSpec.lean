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
  domain : Type u
  range : domain → Type v
  deriving Inhabited

namespace OracleSpec

variable {spec : OracleSpec}

instance : Coe OracleSpec PFunctor where
  coe spec := { A := spec.domain, B := spec.range }

@[simp] lemma coe_def (spec : OracleSpec) :
    (↑spec : PFunctor) = { A := spec.domain, B := spec.range } := rfl

@[reducible, simp] def ofPFunctor (P : PFunctor) : OracleSpec :=
  { domain := P.A, range := P.B }

/-- An oracle spec has indexing in a type `ι` if the `range` function factors through `ι`.
dt: not sure if this is really the right approach for e.g. `pregen`. -/
class HasIndexing (spec : OracleSpec) (ι : Type w) where
  idx : spec.domain → ι
  xdi : ι → Type _
  range_idx (t : spec.domain) : spec.range t = xdi (idx t)

protected class Fintype (spec : OracleSpec) extends PFunctor.Fintype ↑spec
protected class Inhabited (spec : OracleSpec) extends PFunctor.Inhabited ↑spec
protected class DecidableEq (spec : OracleSpec) extends PFunctor.DecidableEq ↑spec

instance [h : spec.Fintype] (t : spec.domain) : Fintype (spec.range t) := h.fintype_B t
instance [h : spec.Inhabited] (t : spec.domain) : Inhabited (spec.range t) := h.inhabited_B t
instance [h : spec.DecidableEq] : DecidableEq spec.domain := h.decidableEq_A
instance [h : spec.DecidableEq] (t : spec.domain) : DecidableEq (spec.range t) := h.decidableEq_B t

instance : Add OracleSpec where add spec spec' := ofPFunctor (spec + spec')

@[simp] lemma domain_add (spec spec' : OracleSpec) :
    (spec + spec').domain = (spec.domain ⊕ spec'.domain) := rfl

@[simp] lemma range_add_inl (spec spec' : OracleSpec) (t : spec.domain) :
    (spec + spec').range (.inl t) = spec.range t := rfl

@[simp] lemma range_add_inr (spec spec' : OracleSpec) (t : spec'.domain) :
    (spec + spec').range (.inr t) = spec'.range t := rfl

end OracleSpec

def emptySpec : OracleSpec := .ofPFunctor 0
notation "[]ₒ" => emptySpec

def singletonSpec (A B : Type*) : OracleSpec := .ofPFunctor (PFunctor.ofConst A B)
infixl : 25 " →ₒ " => singletonSpec

/-- Access to a coin flipping oracle. Because of termination rules in Lean this is slightly
weaker than `unifSpec`, as we have only finitely many coin flips. -/
@[inline, reducible]
def coinSpec : OracleSpec.{0,0} := Unit →ₒ Bool

@[simp] lemma domain_coinSpec : coinSpec.domain = Unit := rfl
@[simp] lemma range_coinSpec (t : coinSpec.domain) : coinSpec.range t = Bool := rfl

/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`.
By adding `1` to the index we avoid selection from the empty type `Fin 0 ≃ empty`.-/
@[inline, reducible] def unifSpec : OracleSpec.{0,0} where
  domain := ℕ
  range n := Fin (n + 1)

@[simp] lemma domain_unifSpec : unifSpec.domain = ℕ := rfl
@[simp] lemma range_unifSpec (t : unifSpec.domain) : unifSpec.range t = Fin (t + 1) := rfl

instance : unifSpec.Fintype where fintype_B n := inferInstanceAs (Fintype (Fin (n + 1)))
instance : unifSpec.Inhabited where inhabited_B n := inferInstanceAs (Inhabited (Fin (n + 1)))

/-- dt: should or shouldn't we switch to this. Compare to `(· + m) <$> $[0..n]`.
One question is that we may have empty selection
Select uniformly from a range (not starting from zero).-/
@[inline, reducible] def probSpec : OracleSpec.{0,0} where
  domain := ℕ × ℕ
  range r := Fin (r.2 + 1)
