/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public import PolyFun.PFunctor.Free.WP

/-!
# Proof-bearing oracle handlers

An open resource contract describes which answers an oracle may return and how large those
answers may be. Closing an interface requires more than substituting a numeric bound: one uniform
handler program must implement all query positions, satisfy its own strict resource bound, and
prove that every result reached along a conforming inner interaction path is admitted by the outer
contract.

This module packages that non-circular proof boundary. `HandlerCertificate` currently proves the
semantic leaf-conformance needed for typed handler substitution. A future trace simulation and
resource-polynomial substitution theorem will consume the same certificate; a bare `QueryImpl` or
claimed cost function cannot justify that quantitative step.
-/

@[expose] public section

universe u v w x y

namespace OracleComp.Complexity

open PFunctor
open PFunctor.DynSystem.DynComputation

variable {p q : PFunctor.{u, u}} {α : Type u} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{u, v, w} C}

/-! ## Sequential strict-PPT closure seam -/

section Bind

variable [DecidableEq p.A] [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd]
  [Q.IsDistributive]
  {input middle output : Type u} {bd : Boundary C p input middle}
  {outRep : C.Str output} {label : Type x}
  {contract : OracleContract Q bd.interface label}
  {program : input → FreeM p middle} {next : middle → FreeM p output}

/-- The generic resource obligations needed to compose two strict-PPT witnesses.

Both fields are PolyFun certificates: `handoff` bounds every conformingly reachable second phase,
while `cost` bounds the concrete structural overhead of the assembled `seqComp` realization. -/
structure BindCertificate
    (first : StrictPPTWitness Q bd contract program)
    (second : StrictPPTWitness Q (bd.mid outRep) contract next) where
  handoff : PolynomialSeqCompHandoffBound first.realization second.realization contract
    second.runBound
  cost : PolynomialSeqCompCostCertificate first.realization second.realization contract

namespace BindCertificate

variable {first : StrictPPTWitness Q bd contract program}
  {second : StrictPPTWitness Q (bd.mid outRep) contract next}

/-- The generic composed run bound. -/
def runBound (certificate : BindCertificate first second) :
    PolynomialRunBound (first.realization.seqComp second.realization) contract :=
  first.runBound.seqComp second.runBound certificate.handoff certificate.cost

/-- Canonical resource polynomial for a certified bind.

The composed bound is the sum of the first-phase bound, the supplied handoff envelope for the
reachable second-phase initial states, and the supplied comparison bound for the assembled
machine's actual costs. -/
abbrev polynomial (certificate : BindCertificate first second) :=
  certificate.runBound.polynomial

/-- PolyFun's bounded sequential-composition theorem derives the complete exact bound. -/
theorem runsWithin (certificate : BindCertificate first second)
    (model : contract.Model) :
    (first.realization.seqComp second.realization).RunsWithinUnder
      model.resourceModel.allows fun value ↦
        certificate.polynomial.eval model.modulus (Q.size bd.input value) :=
  certificate.runBound.runsWithin model

/-- Assemble the complete strict-PPT witness for monadic sequencing. -/
def strictPPTWitness (certificate : BindCertificate first second) :
    StrictPPTWitness Q (bd.withOut outRep) contract fun value ↦
      FreeM.bind (program value) next :=
  PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.bind first second
    certificate.handoff certificate.cost

/-- A certified exact-resource bind establishes backend-relative strict oracle PPT. -/
theorem isOraclePPTBy (certificate : BindCertificate first second) :
    IsOraclePPTBy Q (bd.withOut outRep) contract fun value ↦
      FreeM.bind (program value) next :=
  ⟨certificate.strictPPTWitness⟩

end BindCertificate

/-- Strict PPT composes through bind once exact resource closure has been proved for the two
hidden executable witnesses.

The closure argument returns `Nonempty` because the component predicates are propositions. This
keeps executable evidence from being extracted from proof irrelevance while still supporting
compositional PPT proofs. -/
theorem IsOraclePPTBy.bind
    (first : IsOraclePPTBy Q bd contract program)
    (second : IsOraclePPTBy Q (bd.mid outRep) contract next)
    (resourceClosure : ∀ (firstWitness : StrictPPTWitness Q bd contract program)
      (secondWitness : StrictPPTWitness Q (bd.mid outRep) contract next),
      Nonempty (BindCertificate firstWitness secondWitness)) :
    IsOraclePPTBy Q (bd.withOut outRep) contract fun value ↦
      FreeM.bind (program value) next := by
  obtain ⟨firstWitness⟩ := first
  obtain ⟨secondWitness⟩ := second
  obtain ⟨certificate⟩ := resourceClosure firstWitness secondWitness
  exact certificate.isOraclePPTBy

end Bind

/-- Boundary used to certify one packed handler dispatcher.

The input and result representations are the outer interface's position and tagged-answer
representations. Its visible interactions use the inner interface. -/
def handlerBoundary (outer : InterfaceBoundary C p) (inner : InterfaceBoundary C q) :
    Boundary C q p.A p.Idx where
  input := outer.pos
  out := outer.idx
  pos := inner.pos
  idx := inner.idx

/-- Pack a dependent handler into one ordinary program family.

The returned sigma tag is fixed by construction, so one realization implements every outer query
position without a pointwise choice of code. -/
def packHandler (handler : ∀ position : p.A, FreeM q (p.B position)) :
    p.A → FreeM q p.Idx :=
  fun position ↦ (fun answer ↦ ⟨position, answer⟩) <$> handler position

/-- Interpret every outer query by a dependent handler, leaving the handler's inner queries open. -/
def closeHandler (handler : ∀ position : p.A, FreeM q (p.B position))
    (program : FreeM p α) : FreeM q α :=
  program.liftM handler

@[simp]
theorem closeHandler_pure (handler : ∀ position : p.A, FreeM q (p.B position))
    (result : α) : closeHandler handler (pure result : FreeM p α) = pure result :=
  rfl

theorem closeHandler_liftBind (handler : ∀ position : p.A, FreeM q (p.B position))
    (position : p.A) (next : p.B position → FreeM p α) :
    closeHandler handler (FreeM.liftBind position next) =
      handler position >>= fun direction ↦ closeHandler handler (next direction) :=
  rfl

/-- Closing an outer program through conforming handlers preserves its leaf contract.

The proof ranges over every answer admitted by the two contracts. It therefore composes the
semantic obligations needed by oracle substitution without appealing to probabilities or to a
particular machine backend. -/
theorem leavesSatisfyUnder_closeHandler
    (handler : ∀ position : p.A, FreeM q (p.B position))
    (outerAllows : ∀ position, p.B position → Prop)
    (innerAllows : ∀ position, q.B position → Prop)
    (accept : α → Prop)
    (hhandler : ∀ position,
      (handler position).LeavesSatisfyUnder innerAllows (outerAllows position))
    (program : FreeM p α)
    (hprogram : program.LeavesSatisfyUnder outerAllows accept) :
    (closeHandler handler program).LeavesSatisfyUnder innerAllows accept :=
  PFunctor.FreeM.leavesSatisfyUnder_liftM handler outerAllows innerAllows accept
    hhandler program hprogram

/-- Result conformance of a dependent handler is equivalent to conformance of its packed form. -/
theorem leavesSatisfyUnder_packHandler_iff
    (handler : ∀ position : p.A, FreeM q (p.B position))
    (allows : ∀ position, q.B position → Prop) (accept : p.Idx → Prop)
    (position : p.A) :
    (packHandler handler position).LeavesSatisfyUnder allows accept ↔
      (handler position).LeavesSatisfyUnder allows
        (fun answer ↦ accept ⟨position, answer⟩) := by
  change
    ((fun answer ↦ ⟨position, answer⟩) <$> handler position).LeavesSatisfyUnder allows accept ↔
      (handler position).LeavesSatisfyUnder allows
        (accept ∘ fun answer ↦ ⟨position, answer⟩)
  exact PFunctor.FreeM.leavesSatisfyUnder_map_iff allows accept
    (fun answer ↦ ⟨position, answer⟩) (handler position)

variable [DecidableEq q.A]

/-- One uniform, strict-PPT implementation of an outer interface using an inner interface.

`witness` supplies executable code and pathwise resource bounds for the single packed dispatcher.
`modelMap` identifies the outer resource environment implemented under each inner environment.
`returnsAllowed` then proves semantic compatibility: every handler result along an
inner-contract-conforming path is admitted by that selected outer model. This avoids requiring
unrelated outer and inner models to be compatible while keeping the relationship explicit. -/
structure HandlerCertificate
    (outer : InterfaceBoundary C p) (inner : InterfaceBoundary C q)
    {outerLabel : Type x} {innerLabel : Type y}
    (outerContract : OracleContract Q outer outerLabel)
    (innerContract : OracleContract Q inner innerLabel)
    (handler : ∀ position : p.A, FreeM q (p.B position)) where
  /-- One code and polynomial bound for the entire dependent dispatcher. -/
  witness : StrictPPTWitness Q (handlerBoundary outer inner) innerContract
    (packHandler handler)
  /-- Outer resource environment implemented under each inner environment. -/
  modelMap : innerContract.Model → outerContract.Model
  /-- Every result of the handler satisfies the selected outer environment. -/
  returnsAllowed : ∀ (innerModel : innerContract.Model) (position : p.A),
    (handler position).LeavesSatisfyUnder innerModel.resourceModel.allows
      ((modelMap innerModel).resourceModel.allows position)

namespace HandlerCertificate

variable {outer : InterfaceBoundary C p} {inner : InterfaceBoundary C q}
  {outerLabel : Type x} {innerLabel : Type y}
  {outerContract : OracleContract Q outer outerLabel}
  {innerContract : OracleContract Q inner innerLabel}
  {handler : ∀ position : p.A, FreeM q (p.B position)}

/-- Build propositional existence of a handler certificate from strict PPT of the packed
dispatcher and semantic compatibility of its returned leaves.

The result is `Nonempty` because `IsOraclePPTBy` deliberately hides its executable witness behind
a proposition. This theorem does not eliminate that proposition into computational data. -/
theorem nonempty_of_isOraclePPTBy
    (hppt : IsOraclePPTBy Q (handlerBoundary outer inner) innerContract
      (packHandler handler))
    (modelMap : innerContract.Model → outerContract.Model)
    (returnsAllowed : ∀ (innerModel : innerContract.Model) (position : p.A),
      (handler position).LeavesSatisfyUnder innerModel.resourceModel.allows
        ((modelMap innerModel).resourceModel.allows position)) :
    Nonempty (HandlerCertificate outer inner outerContract innerContract handler) := by
  obtain ⟨witness⟩ := hppt
  exact ⟨⟨witness, modelMap, returnsAllowed⟩⟩

/-- The packed dispatcher returns only correctly tagged answers admitted by the outer model. -/
theorem packedReturnsAllowed
    (certificate : HandlerCertificate outer inner outerContract innerContract handler)
    (innerModel : innerContract.Model) (position : p.A) :
    (packHandler handler position).LeavesSatisfyUnder innerModel.resourceModel.allows
      (fun answer ↦ answer.1 = position ∧
        (certificate.modelMap innerModel).resourceModel.allows answer.1 answer.2) := by
  rw [leavesSatisfyUnder_packHandler_iff]
  exact (certificate.returnsAllowed innerModel position).mono fun answer hanswer ↦
    ⟨rfl, hanswer⟩

/-- A certified handler transports any outer-model leaf invariant to the closed program under the
chosen inner model. This is the semantic half of oracle substitution; the quantitative machine
and bound substitution remain separate obligations. -/
theorem closeLeavesSatisfyUnder
    (certificate : HandlerCertificate outer inner outerContract innerContract handler)
    (innerModel : innerContract.Model) (accept : α → Prop) (program : FreeM p α)
    (hprogram : program.LeavesSatisfyUnder
      (certificate.modelMap innerModel).resourceModel.allows accept) :
    (closeHandler handler program).LeavesSatisfyUnder
      innerModel.resourceModel.allows accept :=
  leavesSatisfyUnder_closeHandler handler
    (certificate.modelMap innerModel).resourceModel.allows
    innerModel.resourceModel.allows accept
    (certificate.returnsAllowed innerModel) program hprogram

/-- Forget handler conformance while retaining strict PPT of its packed dispatcher. -/
theorem isOraclePPTBy
    (certificate : HandlerCertificate outer inner outerContract innerContract handler) :
    IsOraclePPTBy Q (handlerBoundary outer inner) innerContract (packHandler handler) :=
  ⟨certificate.witness⟩

end HandlerCertificate

end OracleComp.Complexity
