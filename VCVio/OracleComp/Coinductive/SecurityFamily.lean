/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.OracleComp
public import PolyFun.PFunctor.Free.Sigma

/-!
# Security-parameter families as one syntactic interaction

Cryptographic definitions are commonly presented as a family of computations indexed by a
security parameter. Such a family is only a semantic presentation: allowing an unrelated
implementation at every index would make a purported polynomial-time witness nonuniform.

This module packages an indexed family into one `OracleComp` over the sigma of its interfaces.
The packed computation receives the security parameter as ordinary input, tags every query with
that parameter, and tags its result with the same parameter. A quantitative realization of the
packed program is therefore one implementation of the whole family.

The construction is entirely syntactic. It specializes PolyFun's generic `FreeM.sigmaInj` and
`FreeM.packFamily` operations to `Nat`-indexed `OracleComp` families, preserving the original
query tree and all typed answer paths. This file deliberately does not select an encoding of
`Nat`; a concrete complexity backend must pin one explicitly (normally unary for a cryptographic
security parameter).
-/

@[expose] public section

universe u v w w'

namespace OracleComp.SecurityFamily

/-- The input type of a security-parameter family, retaining the parameter with the value. -/
abbrev Input (α : Nat → Type w) := (n : Nat) × α n

/-- The result type of a security-parameter family, retaining the parameter with the value. -/
abbrev Output (β : Nat → Type w') := (n : Nat) × β n

/-- All interfaces in a security-parameter family, with every query tagged by its parameter. -/
abbrev Spec {ι : Nat → Type u} (spec : (n : Nat) → OracleSpec.{u, v} (ι n)) :
    OracleSpec ((n : Nat) × (spec n).Domain) :=
  OracleSpec.sigma spec

variable {ι : Nat → Type u} {spec : (n : Nat) → OracleSpec.{u, v} (ι n)}
  {α : Nat → Type w} {β : Nat → Type w'}

/-- Lift one member of an oracle family into the aggregate, parameter-tagged interface. -/
def packComp (n : Nat) (oa : OracleComp (spec n) (β n)) :
    OracleComp (Spec spec) (Output β) :=
  OracleComp.ofFreeM <| (OracleSpec.toPFunctor_sigma spec).symm ▸
    PFunctor.FreeM.sigmaInj (P := fun n ↦ (spec n).toPFunctor) (X := β) n oa.toFreeM

/-- Package a security-indexed program family as one program over the aggregate interface.

Uniform complexity is stated about a single realization of this function. Pointwise realizations
of `program n` do not by themselves give a realization of `packProgram program`. -/
def packProgram (program : (n : Nat) → α n → OracleComp (spec n) (β n)) :
    Input α → OracleComp (Spec spec) (Output β) :=
  fun input ↦ OracleComp.ofFreeM <|
    (OracleSpec.toPFunctor_sigma spec).symm ▸
      PFunctor.FreeM.packFamily (P := fun n ↦ (spec n).toPFunctor)
        (fun n value ↦ (program n value).toFreeM) input

@[simp]
theorem packProgram_apply (program : (n : Nat) → α n → OracleComp (spec n) (β n))
    (n : Nat) (input : α n) :
    packProgram program ⟨n, input⟩ = packComp n (program n input) :=
  rfl

@[simp]
theorem packComp_pure (n : Nat) (value : β n) :
    packComp (spec := spec) n (pure value) = pure ⟨n, value⟩ :=
  rfl

theorem packComp_queryBind (n : Nat) (query : (spec n).Domain)
    (next : (spec n).Range query → OracleComp (spec n) (β n)) :
    packComp n (OracleComp.queryBind query next) =
      OracleComp.queryBind (spec := Spec spec) ⟨n, query⟩
        (fun answer ↦ packComp n (next answer)) :=
  rfl

end OracleComp.SecurityFamily
