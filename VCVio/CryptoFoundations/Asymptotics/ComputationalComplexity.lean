/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.SecurityFamily
public import PolyFun.Realizability.Quantitative.Resource

/-!
# Strict polynomial time for syntactic oracle computations

This file gives VCVio's backend-relative, worst-case notion of polynomial time. It combines four
pieces which remain explicit in every statement:

1. one `DynComputation` implementing the whole input family;
2. Type-valued executable evidence for its `init`, `head`, and enabled `update?` maps;
3. exact resource accounting for every finite, typed query-answer prefix; and
4. second-order polynomial bounds in the encoded input size and oracle response-length functions.

The generic definition is deliberately named `IsOraclePPTBy`: a `QuantitativeStepClass` supplies an
operational backend, but only a backend-specific adequacy theorem can identify that cost with a
standard machine model. VCVio does not turn an arbitrary cost annotation into an unqualified
claim of PPT.

Random sampling is just another syntactic oracle interaction. Consequently the strict predicate
quantifies over every contract-conforming answer branch, including every coin outcome and branches
having probability zero under a later semantics. Expected polynomial time is a different
probabilistic notion and is not smuggled into this pathwise definition.
-/

@[expose] public section

universe u v w x y

namespace OracleComp.Complexity

open PFunctor
open PFunctor.DynSystem.DynComputation

/-! ## Generic quantitative-resource facade -/

/-- VCVio's crypto-facing name for PolyFun's generic execution-cost polynomial. -/
abbrev ResourcePolynomial (label : Type x) := PFunctor.ExecutionCostPolynomial label

namespace ResourcePolynomial

@[inherit_doc PFunctor.ExecutionCostPolynomial.ofFirstOrder]
abbrev ofFirstOrder := @PFunctor.ExecutionCostPolynomial.ofFirstOrder
@[inherit_doc PFunctor.ExecutionCostPolynomial.eval]
abbrev eval {label : Type x} (bound : ResourcePolynomial label)
    (length : label → ℕ → ℕ) (inputSize : ℕ) :=
  PFunctor.ExecutionCostPolynomial.eval bound length inputSize
@[inherit_doc PFunctor.ExecutionCostPolynomial.const]
abbrev const := @PFunctor.ExecutionCostPolynomial.const
@[inherit_doc PFunctor.ExecutionCostPolynomial.add]
abbrev add {label : Type x} (left right : ResourcePolynomial label) :=
  PFunctor.ExecutionCostPolynomial.add left right
@[inherit_doc PFunctor.ExecutionCostPolynomial.comp]
abbrev comp {label : Type x} (bound : ResourcePolynomial label)
    (inputBound : _root_.Complexity.SecondOrderPolynomial label) :=
  PFunctor.ExecutionCostPolynomial.comp bound inputBound
@[inherit_doc PFunctor.ExecutionCostPolynomial.reindex]
abbrev reindex {label : Type x} {target : Type y} (bound : ResourcePolynomial label)
    (map : label → target) :=
  PFunctor.ExecutionCostPolynomial.reindex bound map
@[inherit_doc PFunctor.ExecutionCostPolynomial.subst]
abbrev subst {label : Type x} {target : Type y} (bound : ResourcePolynomial label)
    (replacement : label → _root_.Complexity.SecondOrderPolynomial target) :=
  PFunctor.ExecutionCostPolynomial.subst bound replacement
@[inherit_doc PFunctor.ExecutionCostPolynomial.eval_ofFirstOrder]
alias eval_ofFirstOrder := PFunctor.ExecutionCostPolynomial.eval_ofFirstOrder
@[inherit_doc PFunctor.ExecutionCostPolynomial.eval_const]
alias eval_const := PFunctor.ExecutionCostPolynomial.eval_const
@[inherit_doc PFunctor.ExecutionCostPolynomial.eval_comp]
alias eval_comp := PFunctor.ExecutionCostPolynomial.eval_comp
@[inherit_doc PFunctor.ExecutionCostPolynomial.eval_reindex]
alias eval_reindex := PFunctor.ExecutionCostPolynomial.eval_reindex
@[inherit_doc PFunctor.ExecutionCostPolynomial.eval_subst]
alias eval_subst := PFunctor.ExecutionCostPolynomial.eval_subst
@[inherit_doc PFunctor.ExecutionCostPolynomial.add_eval_le_eval_add]
alias add_eval_le_eval_add := PFunctor.ExecutionCostPolynomial.add_eval_le_eval_add
@[inherit_doc PFunctor.ExecutionCostPolynomial.eval_mono_input]
alias eval_mono_input := PFunctor.ExecutionCostPolynomial.eval_mono_input
@[inherit_doc PFunctor.ExecutionCostPolynomial.eval_mono_lengths]
alias eval_mono_lengths := PFunctor.ExecutionCostPolynomial.eval_mono_lengths

end ResourcePolynomial

/-- VCVio's oracle-facing name for PolyFun's response-size modulus symbols. -/
abbrev OracleModulus (label : Type x) :=
  PFunctor.DynSystem.DynComputation.ResponseModulus label

/-- VCVio's oracle-facing view of PolyFun's admitted-response resource model. -/
abbrev OracleResourceModel {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
    {label : Type x} (Q : QuantitativeStepClass.{u, v, w} C)
    (interface : InterfaceBoundary C p) (labelOf : p.A → label) :=
  PFunctor.DynSystem.DynComputation.ResponseResourceModel Q interface labelOf

/-- VCVio's oracle-facing view of PolyFun's nonempty response-resource contract. -/
abbrev OracleContract {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
    (Q : QuantitativeStepClass.{u, v, w} C) (interface : InterfaceBoundary C p)
    (label : Type x) :=
  PFunctor.DynSystem.DynComputation.ResponseResourceContract Q interface label

namespace OracleResourceModel

@[inherit_doc PFunctor.DynSystem.DynComputation.ResponseResourceModel.modulus]
abbrev modulus := @PFunctor.DynSystem.DynComputation.ResponseResourceModel.modulus
@[inherit_doc PFunctor.DynSystem.DynComputation.ResponseResourceModel.modulus_monotone]
alias modulus_monotone := PFunctor.DynSystem.DynComputation.ResponseResourceModel.modulus_monotone

end OracleResourceModel

namespace OracleContract

@[inherit_doc PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model]
abbrev Model {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
    {Q : QuantitativeStepClass.{u, v, w} C} {interface : InterfaceBoundary C p}
    {label : Type x} (contract : OracleContract Q interface label) :=
  PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model contract

namespace Model

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  {Q : QuantitativeStepClass.{u, v, w} C} {interface : InterfaceBoundary C p}
  {label : Type x} {contract : OracleContract Q interface label}

@[inherit_doc PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model.resourceModel]
abbrev resourceModel (model : contract.Model) :=
  PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model.resourceModel model
@[inherit_doc PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model.modulus]
abbrev modulus (model : contract.Model) :=
  PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model.modulus model
theorem modulus_monotone (model : contract.Model) :
    _root_.Complexity.SecondOrderPolynomial.MonotoneLengths model.modulus :=
  PFunctor.DynSystem.DynComputation.ResponseResourceContract.Model.modulus_monotone model

end Model

end OracleContract

/-! ## Backend-relative strict PPT -/

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output} {label : Type x}

/-- VCVio's strict-PPT witness is PolyFun's generic polynomial program witness, interpreted as a
cryptographic open-oracle certificate. -/
abbrev StrictPPTWitness
    (Q : QuantitativeStepClass.{u, v, w} C) (bd : Boundary C p input output)
    (contract : OracleContract Q bd.interface label) (program : input → FreeM p output) :=
  PFunctor.DynSystem.DynComputation.PolynomialProgramWitness Q bd contract program

/-- VCVio's certified-pure facade over PolyFun's generic pure resource certificate. -/
abbrev PureCertificate
    (Q : QuantitativeStepClass.{u, v, w} C) (bd : Boundary C p input output)
    (function : input → output) :=
  PFunctor.DynSystem.DynComputation.PureResourceCertificate Q bd function

namespace PureCertificate

@[inherit_doc PFunctor.DynSystem.DynComputation.PureResourceCertificate.ofPolyRealizer]
abbrev ofPolyRealizer :=
  @PFunctor.DynSystem.DynComputation.PureResourceCertificate.ofPolyRealizer
@[inherit_doc PFunctor.DynSystem.DynComputation.PureResourceCertificate.realization]
abbrev realization :=
  @PFunctor.DynSystem.DynComputation.PureResourceCertificate.realization
@[inherit_doc PFunctor.DynSystem.DynComputation.PureResourceCertificate.polynomial]
abbrev polynomial :=
  @PFunctor.DynSystem.DynComputation.PureResourceCertificate.polynomial
@[inherit_doc PFunctor.DynSystem.DynComputation.PureResourceCertificate.implements]
abbrev implements :=
  @PFunctor.DynSystem.DynComputation.PureResourceCertificate.implements
@[inherit_doc PFunctor.DynSystem.DynComputation.PureResourceCertificate.runsWithin]
abbrev runsWithin :=
  @PFunctor.DynSystem.DynComputation.PureResourceCertificate.runsWithin

variable {function : input → output}

/-- Build the complete strict-PPT witness for an immediately returning program. -/
def strictPPTWitness (certificate : PureCertificate Q bd function)
    (contract : OracleContract Q bd.interface label) :
    StrictPPTWitness Q bd contract fun value ↦ FreeM.pure (function value) :=
  PFunctor.DynSystem.DynComputation.PureResourceCertificate.programWitness
    certificate contract

end PureCertificate

/-- Strict, worst-case oracle PPT relative to an explicit quantitative backend. -/
def IsOraclePPTBy (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C p input output) (contract : OracleContract Q bd.interface label)
    (program : input → FreeM p output) : Prop :=
  Nonempty (StrictPPTWitness Q bd contract program)

/-- An explicit synonym emphasizing that the generic oracle predicate is strict and pathwise. -/
abbrev IsStrictPPTBy := @IsOraclePPTBy

/-- An immediately returning function with explicit polynomial code is strict oracle PPT. -/
theorem PureCertificate.isOraclePPTBy {function : input → output}
    (certificate : PureCertificate Q bd function)
    (contract : OracleContract Q bd.interface label) :
    IsOraclePPTBy Q bd contract fun value ↦ FreeM.pure (function value) :=
  ⟨certificate.strictPPTWitness contract⟩

namespace StrictPPTWitness

variable {contract : OracleContract Q bd.interface label} {program : input → FreeM p output}

/-- Preserve VCVio's direct polynomial projection over PolyFun's factored run certificate. -/
abbrev polynomial (witness : StrictPPTWitness Q bd contract program) :=
  witness.runBound.polynomial

/-- Preserve VCVio's model-specialized pathwise bound accessor. -/
theorem runsWithin (witness : StrictPPTWitness Q bd contract program)
    (model : contract.Model) :
    witness.realization.RunsWithinUnder model.resourceModel.allows fun value ↦
      witness.polynomial.eval model.modulus (Q.size bd.input value) :=
  witness.runBound.runsWithin model

@[inherit_doc PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.outputSizePolynomial]
abbrev outputSizePolynomial :=
  @PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.outputSizePolynomial
@[inherit_doc PolynomialProgramWitness.eval_outputSizePolynomial]
alias eval_outputSizePolynomial := PolynomialProgramWitness.eval_outputSizePolynomial
@[inherit_doc PolynomialProgramWitness.returnedSize_le]
alias returnedSize_le := PolynomialProgramWitness.returnedSize_le
@[inherit_doc PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.congrProgram]
def congrProgram {program' : input → FreeM p output}
    (witness : StrictPPTWitness Q bd contract program) (hprogram : program = program') :
    StrictPPTWitness Q bd contract program' :=
  PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.congrProgram witness hprogram

theorem isQuantitativelyRealizableBy (witness : StrictPPTWitness Q bd contract program) :
    IsQuantitativelyRealizableBy Q bd program :=
  PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.isQuantitativelyRealizableBy witness

theorem isQuantitativelyRealizableWithinUnder
    (witness : StrictPPTWitness Q bd contract program) (model : contract.Model) :
    IsQuantitativelyRealizableWithinUnder Q bd model.resourceModel.allows program
      (fun value ↦ witness.polynomial.eval model.modulus (Q.size bd.input value)) :=
  ⟨witness.realization, witness.implements, witness.runsWithin model⟩

theorem isTotalRollBound (witness : StrictPPTWitness Q bd contract program)
    (model : contract.Model)
    (hAllows : ∀ position answer, model.resourceModel.allows position answer)
    (value : input) :
    (program value).IsTotalRollBound
      (witness.polynomial.eval model.modulus (Q.size bd.input value)).queries := by
  simpa only [PolynomialRunBound.bound_apply] using
    PFunctor.DynSystem.DynComputation.PolynomialProgramWitness.isTotalRollBound
      witness model hAllows value

end StrictPPTWitness

namespace IsOraclePPTBy

variable {contract : OracleContract Q bd.interface label} {program : input → FreeM p output}

/-- Strict oracle PPT is invariant under equality of whole program families. -/
theorem congrProgram {program' : input → FreeM p output}
    (h : IsOraclePPTBy Q bd contract program) (hprogram : program = program') :
    IsOraclePPTBy Q bd contract program' := by
  obtain ⟨witness⟩ := h
  exact ⟨witness.congrProgram hprogram⟩

/-- Strict PPT implies backend-relative quantitative realizability. -/
theorem isQuantitativelyRealizableBy (h : IsOraclePPTBy Q bd contract program) :
    IsQuantitativelyRealizableBy Q bd program := by
  obtain ⟨witness⟩ := h
  exact witness.isQuantitativelyRealizableBy

/-- Strict PPT erases to qualitative realizability. -/
theorem isRealizableBy (h : IsOraclePPTBy Q bd contract program) :
    IsRealizableBy C bd program :=
  h.isQuantitativelyRealizableBy.isRealizableBy

end IsOraclePPTBy
/-! ## OracleComp and uniform-family facades -/

/-- Strict oracle PPT for a VCVio `OracleComp` program, via its definitional `FreeM` syntax. -/
def OracleProgram.IsOraclePPTBy {index : Type u} {spec : OracleSpec.{u, u} index}
    {input output : Type u} {C : StepClass.{u, v}}
    [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq spec.Domain]
    (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C spec.toPFunctor input output)
    {label : Type x} (contract : OracleContract Q bd.interface label)
    (program : input → OracleComp spec output) : Prop :=
  OracleComp.Complexity.IsOraclePPTBy Q bd contract fun value ↦
    (program value).toFreeM

/-- Canonical finite resource model for the explicit fair-coin interface.

The response envelope is the larger encoded tagged-answer size of the two Boolean outcomes. This
contract concerns only the open computation's answer lengths; efficient fair-bit generation is a
separate sampler/handler certificate. -/
def fairCoinResourceModel {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor) :
    OracleResourceModel Q interface (fun _ ↦ PUnit.unit) where
  allows := fun _ _ ↦ True
  responseSize := fun _ _ ↦
    max (Q.size interface.idx ⟨PUnit.unit, false⟩)
      (Q.size interface.idx ⟨PUnit.unit, true⟩)
  responseSize_monotone := fun _ _ _ _ ↦ le_rfl
  responseSize_le := fun position answer _ ↦ by
    cases position
    cases answer
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _

/-- Both Boolean replies are admitted by the canonical fair-coin resource model. -/
@[simp]
theorem fairCoinResourceModel_allows {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor)
    (position : coinSpec.Domain) (answer : coinSpec.Range position) :
    (fairCoinResourceModel Q interface).allows position answer :=
  trivial

/-- Contract admitting exactly the canonical finite fair-coin resource model. -/
def fairCoinContract {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor) :
    OracleContract Q interface Unit where
  labelOf _ := PUnit.unit
  admissible model := model = fairCoinResourceModel Q interface
  model_nonempty := ⟨fairCoinResourceModel Q interface, rfl⟩

/-- A model compatible with `fairCoinContract` is the canonical fair-coin model. -/
@[simp]
theorem fairCoinContract_admissible_iff {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor)
    (model : OracleResourceModel Q interface (fairCoinContract Q interface).labelOf) :
    (fairCoinContract Q interface).admissible model ↔
      model = fairCoinResourceModel Q interface :=
  Iff.rfl

/-- The canonical resource model packaged with its fair-coin contract evidence. -/
def fairCoinModel {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor) :
    (fairCoinContract Q interface).Model :=
  ⟨fairCoinResourceModel Q interface, rfl⟩

/-- The fair-coin contract admits no resource model other than the canonical one. -/
theorem fairCoinModel_eq {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (interface : InterfaceBoundary C coinSpec.toPFunctor)
    (model : (fairCoinContract Q interface).Model) :
    model = fairCoinModel Q interface := by
  apply Subtype.ext
  exact model.2

/-- Strict probabilistic polynomial time, specialized to the explicit fair-coin interface.

The backend and every boundary representation remain explicit, while the oracle contract is fixed
to `fairCoinContract`. Fairness belongs to VCVio's probability interpretation of `coinSpec`;
strict cost still quantifies over both Boolean answers. -/
def IsPPTBy {input output : Type} {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    (Q : QuantitativeStepClass C)
    (bd : Boundary C coinSpec.toPFunctor input output)
    (program : input → OracleComp coinSpec output) : Prop :=
  OracleProgram.IsOraclePPTBy Q bd (fairCoinContract Q bd.interface) program

/-! ## Security-family resource contracts -/

namespace SecurityFamily

/-- The raw dependent sum of parameter-indexed resource labels.

This is only a carrier construction, not a way for one finite second-order-polynomial expression
to select its current security parameter dynamically. A polynomial can mention only finitely many
concrete inhabitants of this sum. Uniform families should therefore normally classify queries by
a fixed global port-label type; use this carrier only when those finitely mentioned sigma labels
have an independently justified meaning. -/
abbrev ParameterizedLabel (label : ℕ → Type x) := (n : ℕ) × label n

variable {index : ℕ → Type u} {spec : (n : ℕ) → OracleSpec.{u, u} (index n)}
  {C : StepClass.{u, v}} {Q : QuantitativeStepClass.{u, v, w} C}
  {interface : InterfaceBoundary C (OracleComp.SecurityFamily.Spec spec).toPFunctor}
  {label : Type x}

/-- Pack a member-wise query classification into the sigma interface used by
`SecurityFamily.packProgram`. The result type is one global resource-label space, so one uniform
second-order polynomial can refer to its symbols. -/
def packedLabelOf (labelOf : ∀ n, (spec n).Domain → label) :
    (OracleComp.SecurityFamily.Spec spec).Domain → label
  | ⟨n, position⟩ => labelOf n position

@[simp]
theorem packedLabelOf_apply (labelOf : ∀ n, (spec n).Domain → label)
    (n : ℕ) (position : (spec n).Domain) :
    packedLabelOf labelOf ⟨n, position⟩ = labelOf n position :=
  rfl

/-- A resource model presented member-by-member before packing a security family.

This is only an ergonomic view of `OracleResourceModel`: executable costs and encoded sizes still
come from the explicit quantitative backend `Q` and the pinned packed interface boundary. No
machine model, encoding, or complexity library is definitionally selected here. -/
structure ResourceModel
    (Q : QuantitativeStepClass.{u, v, w} C)
    (interface : InterfaceBoundary C (OracleComp.SecurityFamily.Spec spec).toPFunctor)
    (labelOf : ∀ n, (spec n).Domain → label) where
  /-- Replies admitted for each parameter and typed query position. -/
  allows : ∀ n (position : (spec n).Domain), (spec n).Range position → Prop
  /-- Tagged-response size envelope for each global interface label. -/
  responseSize : label → ℕ → ℕ
  /-- Every response-size envelope is monotone in encoded query size. -/
  responseSize_monotone : ∀ interface, Monotone (responseSize interface)
  /-- Every admitted typed reply fits its packed tagged-response envelope. -/
  responseSize_le : ∀ n (position : (spec n).Domain) (answer : (spec n).Range position),
    allows n position answer →
      Q.size interface.idx ⟨⟨n, position⟩, answer⟩ ≤
        responseSize (labelOf n position) (Q.size interface.pos ⟨n, position⟩)

namespace ResourceModel

variable {labelOf : ∀ n, (spec n).Domain → label}

/-- Pack a family resource model into the backend-neutral core contract layer. -/
def pack (model : ResourceModel Q interface labelOf) :
    OracleResourceModel Q interface (packedLabelOf labelOf) where
  allows := fun ⟨n, position⟩ answer ↦ model.allows n position answer
  responseSize := model.responseSize
  responseSize_monotone := model.responseSize_monotone
  responseSize_le := fun ⟨n, position⟩ answer hanswer ↦
    model.responseSize_le n position answer hanswer

/-- Present a packed resource model member-by-member. -/
def unpack (model : OracleResourceModel Q interface (packedLabelOf labelOf)) :
    ResourceModel Q interface labelOf where
  allows := fun n position answer ↦ model.allows ⟨n, position⟩ answer
  responseSize := model.responseSize
  responseSize_monotone := model.responseSize_monotone
  responseSize_le := fun n position answer hanswer ↦
    model.responseSize_le ⟨n, position⟩ answer hanswer

@[simp]
theorem unpack_pack (model : ResourceModel Q interface labelOf) :
    unpack model.pack = model := by
  cases model
  rfl

@[simp]
theorem pack_unpack (model : OracleResourceModel Q interface (packedLabelOf labelOf)) :
    pack (unpack model) = model := by
  cases model
  rfl

/-- Family and packed presentations of a resource model are equivalent data. -/
def equiv : ResourceModel Q interface labelOf ≃
    OracleResourceModel Q interface (packedLabelOf labelOf) where
  toFun := pack
  invFun := unpack
  left_inv := unpack_pack
  right_inv := pack_unpack

end ResourceModel

/-- A contract stated over the members of a security family.

Packing this structure produces an ordinary `OracleContract`, so all strict-PPT definitions remain
parametric in the quantitative backend and consume the same small core interface. -/
structure ResourceContract
    (Q : QuantitativeStepClass.{u, v, w} C)
    (interface : InterfaceBoundary C (OracleComp.SecurityFamily.Spec spec).toPFunctor)
    (label : Type x) where
  /-- Interface label of each member's query positions. -/
  labelOf : ∀ n, (spec n).Domain → label
  /-- Resource environments admitted by this family contract. -/
  admissible : ResourceModel Q interface labelOf → Prop
  /-- The family contract admits at least one global finite resource envelope. -/
  model_nonempty : ∃ model, admissible model

namespace ResourceContract

variable (contract : ResourceContract Q interface label)

/-- Pack a family contract into the core oracle-contract layer. -/
def pack : OracleContract Q interface label where
  labelOf := packedLabelOf contract.labelOf
  admissible model := contract.admissible (ResourceModel.unpack model)
  model_nonempty := by
    obtain ⟨model, hmodel⟩ := contract.model_nonempty
    exact ⟨model.pack, by simpa using hmodel⟩

/-- A resource environment compatible with a family contract. -/
abbrev Model := { model : ResourceModel Q interface contract.labelOf //
  contract.admissible model }

namespace Model

variable {contract : ResourceContract Q interface label}

/-- Forget that a family resource environment satisfies its contract. -/
abbrev resourceModel (model : contract.Model) :
    ResourceModel Q interface contract.labelOf :=
  model.1

/-- Pack a compatible family model for use by the core strict-PPT witness. -/
def pack (model : contract.Model) : contract.pack.Model :=
  ⟨model.resourceModel.pack, by
    change contract.admissible (ResourceModel.unpack model.resourceModel.pack)
    rw [ResourceModel.unpack_pack]
    exact model.2⟩

/-- Recover the family presentation of a compatible packed model. -/
def unpack (model : contract.pack.Model) : contract.Model :=
  ⟨ResourceModel.unpack model.1, model.2⟩

@[simp]
theorem unpack_pack (model : contract.Model) : unpack model.pack = model := by
  apply Subtype.ext
  exact ResourceModel.unpack_pack model.resourceModel

@[simp]
theorem pack_unpack (model : contract.pack.Model) : pack (unpack model) = model := by
  apply Subtype.ext
  exact ResourceModel.pack_unpack model.1

end Model

end ResourceContract

end SecurityFamily

/-- Strict PPT for a security-indexed family means strict PPT of its one packed program.

This requires one shared realization and one shared polynomial across all security parameters. It
is strictly stronger than choosing unrelated witnesses pointwise. -/
def SecurityFamily.IsOraclePPTBy
    {index : ℕ → Type u} {spec : (n : ℕ) → OracleSpec.{u, u} (index n)}
    {input output : ℕ → Type u} {C : StepClass.{u, v}}
    [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq (SecurityFamily.Spec spec).Domain]
    (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C (SecurityFamily.Spec spec).toPFunctor
      (SecurityFamily.Input input) (SecurityFamily.Output output))
    {label : Type x} (contract : OracleContract Q bd.interface label)
    (program : (n : ℕ) → input n → OracleComp (spec n) (output n)) : Prop :=
  OracleProgram.IsOraclePPTBy Q bd contract (SecurityFamily.packProgram program)

/-- Uniform strict oracle PPT using a member-by-member family resource contract.

This is an ergonomic adapter to `SecurityFamily.IsOraclePPTBy`; it does not change the trusted
complexity predicate or select a concrete backend. -/
def SecurityFamily.IsOraclePPTByContract
    {index : ℕ → Type u} {spec : (n : ℕ) → OracleSpec.{u, u} (index n)}
    {input output : ℕ → Type u} {C : StepClass.{u, v}}
    [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq (SecurityFamily.Spec spec).Domain]
    (Q : QuantitativeStepClass.{u, v, w} C)
    (bd : Boundary C (SecurityFamily.Spec spec).toPFunctor
      (SecurityFamily.Input input) (SecurityFamily.Output output))
    {label : Type x} (contract : SecurityFamily.ResourceContract Q bd.interface label)
    (program : (n : ℕ) → input n → OracleComp (spec n) (output n)) : Prop :=
  SecurityFamily.IsOraclePPTBy Q bd contract.pack program

/-- An explicit synonym emphasizing strict pathwise bounds for a packed oracle family. -/
abbrev SecurityFamily.IsStrictPPTBy := @SecurityFamily.IsOraclePPTBy

/-- Uniform strict oracle PPT for a packed security family whose only syntactic interaction is a
fair coin.

The explicit contract must additionally control how the packed security parameter contributes to
the boundary's encoded query and tagged-answer sizes. Deriving that contract requires a
quantitative encoding-growth certificate and cannot be done from an arbitrary `Boundary` alone. -/
def SecurityFamily.IsCoinPPTByUnder
    {input output : ℕ → Type} {C : StepClass}
    [C.HasProd] [C.HasSum] [C.HasOption]
    [DecidableEq (SecurityFamily.Spec (fun _ : ℕ ↦ coinSpec)).Domain]
    (Q : QuantitativeStepClass C)
    (bd : Boundary C (SecurityFamily.Spec (fun _ : ℕ ↦ coinSpec)).toPFunctor
      (SecurityFamily.Input input) (SecurityFamily.Output output))
    {label : Type x} (contract : OracleContract Q bd.interface label)
    (program : (n : ℕ) → input n → OracleComp coinSpec (output n)) : Prop :=
  SecurityFamily.IsOraclePPTBy Q bd contract program

end OracleComp.Complexity
