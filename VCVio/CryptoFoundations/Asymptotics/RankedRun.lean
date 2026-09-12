/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity

/-!
# Ranked resource certificates for finite oracle computations

This module gives VCVio's crypto-facing names to PolyFun's generic ranked resource certificates.
A certificate assigns each hidden state both a resource potential and a natural rank. The
potential pays for stopping at that state or for one enabled query followed by the next potential.
The rank strictly decreases along every allowed answer, while a separate progress field prevents
vacuous termination claims when a query admits no response.

The construction never assigns work to code. Every local cost is read directly from the
`QuantitativeStepClass` realizers already stored by the realization. Consequently it is useful for
small finite-state programs and bounded loops without weakening the backend-relative trust
boundary of `IsOraclePPTBy`.
-/

@[expose] public section

universe u v w x

namespace OracleComp.Complexity

open PFunctor
open PFunctor.DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output}

/-! ## Local resource-cost facade -/

namespace RankedRun

/-- Cost of observing a state as the final state of an execution prefix. -/
abbrev terminalCost :=
  @PFunctor.DynSystem.DynComputation.RankedResource.terminalCost

/-- Cost contributed by one enabled query-answer transition. -/
abbrev queryStepCost :=
  @PFunctor.DynSystem.DynComputation.RankedResource.queryStepCost

@[inherit_doc RankedResource.executionTrace_cost_query]
alias executionTrace_cost_query := RankedResource.executionTrace_cost_query

@[inherit_doc RankedResource.executionCost_eq_init_add_trace_add_terminal]
alias executionCost_eq_init_add_trace_add_terminal :=
  RankedResource.executionCost_eq_init_add_trace_add_terminal

/-- VCVio's historical name for PolyFun's generic ranked resource-potential certificate. -/
abbrev ResourcePotentialCertificate (R : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop) (bound : input → ExecutionCost) :=
  PFunctor.DynSystem.DynComputation.RankedResource.PotentialCertificate R allows bound

namespace ResourcePotentialCertificate

variable {R : QuantitativeRealization Q bd}
  {allows : ∀ position, p.B position → Prop} {bound : input → ExecutionCost}

theorem traceCost_add_terminal_le
    (certificate : ResourcePotentialCertificate R allows bound)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish)
    (htrace : trace.Conforms allows) :
    trace.cost + terminalCost R finish ≤ certificate.potential start :=
  PFunctor.DynSystem.DynComputation.RankedResource.PotentialCertificate.traceCost_add_terminal_le
    certificate trace htrace

theorem resolvesInUnder (certificate : ResourcePotentialCertificate R allows bound)
    (state : R.machine.State) :
    R.machine.ResolvesInUnder allows (certificate.toRankedRunCertificate.rank state) state :=
  PFunctor.DynSystem.DynComputation.RankedResource.PotentialCertificate.resolvesInUnder
    certificate state

theorem runsWithinUnder (certificate : ResourcePotentialCertificate R allows bound) :
    R.RunsWithinUnder allows bound :=
  PFunctor.DynSystem.DynComputation.RankedResource.PotentialCertificate.runsWithinUnder
    certificate

end ResourcePotentialCertificate

end RankedRun

/-! ## Strict-PPT packaging -/

/-- VCVio's crypto-facing name for PolyFun's ranked polynomial program certificate. -/
abbrev RankedPPTCertificate {label : Type x}
    (Q : QuantitativeStepClass.{u, v, w} C) (bd : Boundary C p input output)
    (contract : OracleContract Q bd.interface label) (program : input → FreeM p output) :=
  PFunctor.DynSystem.DynComputation.RankedResourceCertificate Q bd contract program

namespace RankedPPTCertificate

variable {label : Type x} {contract : OracleContract Q bd.interface label}
  {program : input → FreeM p output}

/-- Forget ranked local evidence to VCVio's strict-PPT witness. -/
def strictPPTWitness (certificate : RankedPPTCertificate Q bd contract program) :
    StrictPPTWitness Q bd contract program :=
  PFunctor.DynSystem.DynComputation.RankedResourceCertificate.programWitness certificate

/-- Ranked local evidence establishes backend-relative strict oracle PPT. -/
theorem isOraclePPTBy (certificate : RankedPPTCertificate Q bd contract program) :
    IsOraclePPTBy Q bd contract program :=
  ⟨certificate.strictPPTWitness⟩

end RankedPPTCertificate
end OracleComp.Complexity
