/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coercions.SubSpec

/-!
# Coercing Computations to Larger Oracle Sets

This file defines an append operation on `OracleSpec` to combine different sets of oracles.
We use `Sum` to combine the indexing sets, so this operation is "ordered"
in the sense that the two oracle sets correspond to `Sum.inl` and `Sum.inr`.
Note that this operation is never associative, as `Sum` is not associative

We also define a number of coercions involving append.
These instances allow an `OracleSpec` of the form `spec₁ + ... + spec₂`
to coerce to one of the form `spec'₁ + ... + spec'₂`, assuming that
the set of oracles in the first is a sub-sequence of the oracles in the second.
We also include associativity instances, so parenthisization of the sequence is irrelevant.

Note that this requires the ordering of oracles in each to match,
and so we generally adopt a standard ordering of `OracleSpec` for computations
in order to make this apply as often as possible. We specifically adopt the following convention:
  `{coin_oracle} + {unif_spec} + {random oracle} + {adversary oracles} + ...`,
where any of the individual parts may be ommited. The adversary oracles are for
things like a signing oracle in unforgeability experiments of a signature scheme.

TODO!: This is still not as powerful as what could be done in Lean3
** Maybe just manually add a ton of these, simp *should* mostly help that**

The typelcasses are applied in an order defined by specific priorities:
1. Try applying the associativity instance to remove parenthesization.
2. If both the subspec and superspec are an append, try to independently coerce both sides.
3. Try to coerce the subspec to the left side of the superspec append.
4. Try to coerce the subspec to the right side of the superspec append.
5. Try appending a single oracle to the left side of the subspec.
6. Try appending a single oracle to the right side of the subspec.
7. Try coercing the subspec to itself.
This ordering is chosen to both give a generally applicable instance tree,
and avoid an infinite typeclass search whether or not an instance exists.
-/

open Sum

namespace OracleSpec

universe u v w

variable (spec₁ spec₂ spec₃ spec₄ : OracleSpec) {α β γ : Type u}

section instances

/-- Add additional oracles to the right side of the existing ones. -/
instance subSpec_append_left : spec₁ ⊂ₒ (spec₁ + spec₂) where
  monadLift | q => ⟨.inl q.1, q.2⟩

@[simp] lemma liftM_append_left_eq (q : OracleQuery spec₁ α) :
    (liftM q : OracleQuery (spec₁ + spec₂) α) = ⟨.inl q.1, q.2⟩ := rfl

/-- Add additional oracles to the left side of the exiting ones-/
instance subSpec_append_right : spec₂ ⊂ₒ (spec₁ + spec₂) where
  monadLift | q => ⟨.inr q.1, q.2⟩

@[simp] lemma liftM_append_right_eq (q : OracleQuery spec₂ α) :
    (liftM q : OracleQuery (spec₁ + spec₂) α) = ⟨.inr q.1, q.2⟩ := rfl

instance subSpec_left_append_left_append_of_subSpec [h : spec₁ ⊂ₒ spec₃] :
    spec₁ + spec₂ ⊂ₒ spec₃ + spec₂ where
  monadLift
    | ⟨.inl q, f⟩ => h.monadLift ⟨q, f⟩
    | ⟨.inr q, f⟩ => ⟨.inr q, f⟩

@[simp]
lemma liftM_left_append_left_append_eq [h : spec₁ ⊂ₒ spec₃]
    (q : OracleQuery (spec₁ + spec₂) α) : (liftM q : OracleQuery (spec₃ + spec₂) α) =
    match q with
    | ⟨.inl q, f⟩ => h.monadLift ⟨q, f⟩
    | ⟨.inr q, f⟩ => ⟨.inr q, f⟩ := rfl

instance subSpec_right_append_right_append_of_subSpec [h : spec₂ ⊂ₒ spec₃] :
    spec₁ + spec₂ ⊂ₒ spec₁ + spec₃ where
  monadLift
    | ⟨.inl q, f⟩ => ⟨.inl q, f⟩
    | ⟨.inr q, f⟩ => h.monadLift ⟨q, f⟩

@[simp]
lemma liftM_right_append_right_append_eq [h : spec₂ ⊂ₒ spec₃]
    (q : OracleQuery (spec₁ + spec₂) α) : (liftM q : OracleQuery (spec₁ + spec₃) α) =
    match q with
    | ⟨.inl q, f⟩ => ⟨.inl q, f⟩
    | ⟨.inr q, f⟩ => h.monadLift ⟨q, f⟩ := rfl

instance subSpec_assoc : spec₁ + (spec₂ + spec₃) ⊂ₒ spec₁ + spec₂ + spec₃ where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl (.inl t), f⟩
    | ⟨.inr (.inl t), f⟩ => ⟨.inl (.inr t), f⟩
    | ⟨.inr (.inr t), f⟩ => ⟨.inr t, f⟩

end instances

end OracleSpec

section tests

set_option linter.unusedVariables false

-- This set of examples serves as sort of a "unit test" for the coercions above
variable (α : Type)
  (spec₁ spec₂ spec₃ spec₄ coeSpec coeSuperSpec : OracleSpec)
  [coeSpec ⊂ₒ coeSuperSpec]

-- coerce a single `coin_spec` and then append extra oracles
example (oa : OracleComp coeSpec α) :
  OracleComp (coeSuperSpec + spec₂ + spec₃) α := oa
example (oa : OracleComp coeSpec α) :
  OracleComp (spec₁ + coeSuperSpec + spec₂) α := oa
example (oa : OracleComp coeSpec α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec) α := oa

-- coerce left side of append and then append on additional oracles
example (oa : OracleComp (coeSpec + spec₁) α) :
  OracleComp (coeSuperSpec + spec₁ + spec₂) α := oa
example (oa : OracleComp (coeSpec + spec₁) α) :
  OracleComp (coeSuperSpec + spec₂ + spec₁) α := oa
example (oa : OracleComp (coeSpec + spec₁) α) :
  OracleComp (spec₂ + coeSuperSpec + spec₁) α := oa

-- coerce right side of append and then append on additional oracles
example (oa : OracleComp (spec₁ + coeSpec) α) :
  OracleComp (spec₁ + coeSuperSpec + spec₂) α := oa
example (oa : OracleComp (spec₁ + coeSpec) α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec) α := oa
example (oa : OracleComp (spec₁ + coeSpec) α) :
  OracleComp (spec₂ + spec₁ + coeSuperSpec) α := oa

-- coerce an inside part while also applying associativity
example (oa : OracleComp (spec₁ + (spec₂ + coeSpec)) α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec) α := oa
example (oa : OracleComp (spec₁ + (coeSpec + spec₂)) α) :
  OracleComp (spec₁ + coeSuperSpec + spec₂) α := oa
example (oa : OracleComp (coeSpec + (spec₁ + spec₂)) α) :
  OracleComp (coeSuperSpec + spec₁ + spec₂) α := oa

-- coerce two oracles up to four oracles
example (oa : OracleComp (spec₁ + spec₂) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₁ + spec₃) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₁ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₂ + spec₃) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₂ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₃ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- coerce threee oracles up to four oracles
example (oa : OracleComp (spec₁ + spec₂ + spec₃) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₁ + spec₂ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₁ + spec₃ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₂ + spec₃ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- four oracles with associativity and internal coercion
example (oa : OracleComp ((coeSpec + spec₂) + (spec₃ + spec₄)) α) :
  OracleComp (coeSuperSpec + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp ((spec₁ + spec₂) + (coeSpec + spec₄)) α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec + spec₄) α := oa
example (oa : OracleComp ((spec₁ + coeSpec) + (spec₃ + spec₄)) α) :
  OracleComp (spec₁ + coeSuperSpec + spec₃ + spec₄) α := oa
example (oa : OracleComp ((spec₁ + spec₂) + (spec₃ + coeSuperSpec)) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + coeSuperSpec) α := oa

/-- coercion makes it possible to mix computations on individual oracles -/
example : OracleComp (unifSpec + spec₁) Bool := do
  let n : Fin 315 ←$[0..314]; let m : Fin 315 ←$[0..314]
  if n = m then return true else $ᵗ Bool

end tests
