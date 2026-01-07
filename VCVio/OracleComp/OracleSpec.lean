/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import ToMathlib.PFunctor.Basic

/-!
# Specifications of Available Oracles

-/

universe u u' v w


/-- An `OracleSpec ι` is specieifes a set of oracles indexed by `ι`.
Defined as a map from each input to the type of the oracle's output. -/
def OracleSpec (ι : Type u) : Type (max u (v + 1)) :=
  ι → Type v

namespace OracleSpec

variable {ι : Type u}

def toPFunctor (spec : OracleSpec ι) : PFunctor := { A := ι, B := spec }

@[reducible, inline]
def ofPFunctor (P : PFunctor) : OracleSpec P.A := P.B

@[simp] lemma toPFunctor_ofPFunctor (P : PFunctor) :
    OracleSpec.toPFunctor (OracleSpec.ofPFunctor P) = P := rfl

@[simp] lemma ofPFunctor_toPFunctor (spec : OracleSpec ι) :
    OracleSpec.ofPFunctor (OracleSpec.toPFunctor spec) = spec := rfl

abbrev Domain (_spec : OracleSpec ι) : Type _ := ι
abbrev Range (spec : OracleSpec ι) (t : ι) : Type _ := spec t

protected class Fintype (spec : OracleSpec ι) extends PFunctor.Fintype spec.toPFunctor

instance {spec : OracleSpec ι} [h : spec.Fintype] (t : spec.Domain) :
  Fintype (spec.Range t) := h.fintype_B t

protected class Inhabited (spec : OracleSpec ι) extends PFunctor.Inhabited spec.toPFunctor

instance {spec : OracleSpec ι} [h : spec.Inhabited] (t : spec.Domain) :
  Inhabited (spec.Range t) := h.inhabited_B t

protected class DecidableEq (spec : OracleSpec ι) extends PFunctor.DecidableEq spec.toPFunctor

instance {spec : OracleSpec ι} [h : spec.DecidableEq] :
  DecidableEq spec.Domain := h.decidableEq_A
instance {spec : OracleSpec ι} [h : spec.DecidableEq] (t : spec.Domain) :
  DecidableEq (spec.Range t) := h.decidableEq_B t

/-- Type-class gadget to enable probability notation for computation over an `OracleSpec`.
Can be defined for any `spec` with `spec.Range` finite and inhabited, but generally should
only be instantied for things like `coinSpec` or `unifSpec`.
dtumad: we should examine if this should be used more strictly in `evalDist` stuff.
We could require computations without this tag to provide their own `PMF` embedding,
even if it can be inferred implicitly. -/
protected class IsProbSpec (spec : OracleSpec ι) [spec.Inhabited] [spec.Fintype]

section ofFn

@[reducible, always_inline] def ofFn {ι : Type u} (F : ι → Type v) : OracleSpec ι := F
notation:25 (name := singletonSpec) A:25 " →ₒ " B:26 =>
  OracleSpec.ofFn (ι := A) (fun _ => B)

instance {ι : Type u} (F : ι → Type v) [h : (i : ι) → Fintype (F i)] :
    (OracleSpec.ofFn F).Fintype where
  fintype_B := h

instance {ι : Type u} (F : ι → Type v) [h : DecidableEq ι] [h' : (i : ι) → DecidableEq (F i)] :
    (OracleSpec.ofFn F).DecidableEq where
  decidableEq_A := h
  decidableEq_B := h'

instance {ι : Type u} (F : ι → Type v) [h : (i : ι) → Inhabited (F i)] :
    (OracleSpec.ofFn F).Inhabited where
  inhabited_B := h

end ofFn

section add

/-- `spec₁ + spec₂` specifies access to oracles in both `spec₁` and `spec₂`.
The input is split as a sum type of the two original input sets.
This corresponds exactly to addition of the corresponding `PFunctor`. -/
instance {ι ι'} : HAdd (OracleSpec ι) (OracleSpec ι') (OracleSpec (ι ⊕ ι')) where
  hAdd spec spec' := Sum.elim spec spec'

lemma add_def {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι') :
    spec + spec' = Sum.elim spec spec' := rfl

@[simp] lemma add_apply_inl {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    (t : ι) : (spec + spec') (.inl t) = spec t := rfl

@[simp] lemma add_apply_inr {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    (t : ι') : (spec + spec') (.inr t) = spec' t := rfl

@[simp] lemma toPFunctor_add {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι') :
    (spec + spec').toPFunctor = spec.toPFunctor + spec'.toPFunctor := rfl

@[simp] lemma ofPFunctor_add (P P' : PFunctor) :
    OracleSpec.ofPFunctor (P + P') = OracleSpec.ofPFunctor P + OracleSpec.ofPFunctor P' := rfl

end add

section sigma

/-- Given an indexed set of `OracleSpec`, specifiy access to all of the oracles,
by requiring an index into the corresponding oracle in the input. -/
protected def sigma {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i)) :
    OracleSpec ((i : ι) × (specs i).Domain) :=
  fun t => specs t.1 t.2

@[simp] lemma sigma_apply {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i))
    (t : (i : ι) × (specs i).Domain) : OracleSpec.sigma specs t = specs t.1 t.2 := rfl

@[simp] lemma toPFunctor_sigma {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i)) :
    OracleSpec.toPFunctor (OracleSpec.sigma specs) =
      PFunctor.sigma fun i => (OracleSpec.toPFunctor (specs i)) := rfl

@[simp] lemma ofPFunctor_sigma {ι} (P : ι → PFunctor) :
    OracleSpec.ofPFunctor (PFunctor.sigma P) =
      OracleSpec.sigma fun i => OracleSpec.ofPFunctor (P i) := rfl

end sigma

section mul

/-- `spec₁ * spec₂` represents an oracle that takes in a pair of inputs for each set,
and returns an element in the output of one oracle or the other.
The corresponds exactly to multiplication in `PFunctor`. -/
instance {ι ι'} : HMul (OracleSpec ι) (OracleSpec ι') (OracleSpec (ι × ι'))
  where hMul spec spec' := fun t => spec.Range t.1 ⊕ spec'.Range t.2

@[simp] lemma mul_apply {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    (t : ι × ι') : (spec * spec').Range t = (spec.Range t.1 ⊕ spec'.Range t.2) := rfl

@[simp] lemma toPFunctor_mul {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι') :
    (spec * spec').toPFunctor = spec.toPFunctor * spec'.toPFunctor := rfl

@[simp] lemma ofPFunctor_mul (P P' : PFunctor) :
    OracleSpec.ofPFunctor (P * P') = OracleSpec.ofPFunctor P * OracleSpec.ofPFunctor P' := rfl

end mul

section pi

/-- Given an indexed set of `OracleSpec`, specifiy access to an oracle that given an input to
the oracle for each index returns an index and an ouptut for that index. -/
protected def pi {ι : Type _} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i)) :
    OracleSpec ((i : ι) → (specs i).Domain) :=
  fun t => (i : ι) × specs i (t i)

@[simp] lemma pi_apply {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i))
    (t : (i : ι) → (specs i).Domain) : OracleSpec.pi specs t = ((i : ι) × specs i (t i)) := rfl

@[simp] lemma toPFunctor_pi {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i)) :
    OracleSpec.toPFunctor (OracleSpec.pi specs) =
      PFunctor.pi fun i => (OracleSpec.toPFunctor (specs i)) := rfl

@[simp] lemma ofPFunctor_pi {ι} (P : ι → PFunctor) :
    OracleSpec.ofPFunctor (PFunctor.pi P) =
      OracleSpec.pi fun i => OracleSpec.ofPFunctor (P i) := rfl

end pi

-- /-- An oracle spec has indexing in a type `ι` if the `range` function factors through `ι`.
-- dt: not sure if this is really the right approach for e.g. `pregen`. -/
-- class HasIndexing (spec : OracleSpec) (ι : Type w) where
--   idx : spec.Domain → ι
--   xdi : ι → Type _
--   range_idx (t : spec.Domain) : spec.Range t = xdi (idx t)

section emptySpec

/-- Specifies access to no oracles, using the empty type as the indexing type. -/
@[reducible] def emptySpec : OracleSpec PEmpty := PEmpty →ₒ PEmpty
notation "[]ₒ" => emptySpec

@[simp] lemma toPFunctor_emptySpec : []ₒ.toPFunctor = 0 := rfl

@[simp] lemma ofPFunctor_zero : OracleSpec.ofPFunctor 0 = []ₒ := rfl

end emptySpec

end OracleSpec

/-- Access to a coin flipping oracle. Because of termination rules in Lean this is slightly
weaker than `unifSpec`, as we have only finitely many coin flips. -/
@[reducible] def coinSpec : OracleSpec.{0,0} Unit := Unit →ₒ Bool

section unifSpec

/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`.
By adding `1` to the index we avoid selection from the empty type `Fin 0 ≃ empty`.-/
@[inline, reducible] def unifSpec : OracleSpec ℕ :=
  OracleSpec.ofFn fun n => Fin (n + 1)

end unifSpec

section probSpec
/-- dt: should or shouldn't we switch to this. Compare to `(· + m) <$> $[0..n]`.
One question is that we may have empty selection
Select uniformly from a range (not starting from zero).-/
@[inline, reducible] def probSpec : OracleSpec (ℕ × ℕ) :=
  OracleSpec.ofFn fun (_n, m) => Fin (m + 1)

end probSpec
