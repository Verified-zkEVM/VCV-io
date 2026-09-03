/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.PFunctor
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.QueryTracking.Tracing
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# PFunctor and OracleSpec Semantics Canaries

These examples exercise the generic polynomial-functor API directly and the
`OracleSpec` compatibility façade. They ensure that probability semantics and
handler instrumentation remain usable without unfolding VCVio internals.
-/

public section

namespace VCVioTest.PFunctorFacade

/-- A one-operation polynomial interface returning one of three directions. -/
@[expose, reducible] def triPFunctor : PFunctor := ⟨Unit, fun _ => Fin 3⟩

instance : triPFunctor.Fintype where
  fintypeB _ := by infer_instance

instance : triPFunctor.Inhabited where
  inhabitedB _ := by infer_instance

noncomputable instance : triPFunctor.IsUniformSpec :=
  PFunctor.IsUniformSpec.ofFintypeInhabited _

/-- The direct PFunctor program issuing the three-way operation once. -/
@[expose]
def directSample : PFunctor.FreeM triPFunctor (Fin 3) :=
  PFunctor.FreeM.lift ()

example : 𝒮[directSample] =
    (PFunctor.IsProbabilitySpec.toPMF (P := triPFunctor) () : SPMF (Fin 3)) := by
  simpa only [directSample] using
    (PFunctor.FreeM.evalSPMF_lift (P := triPFunctor) ())

example := PFunctor.FreeM.evalSPMF_lift_eq_uniform (P := triPFunctor) ()

example : support directSample = Set.univ := by
  simpa only [directSample] using
    (PFunctor.FreeM.support_lift_eq_univ (P := triPFunctor) ())

example : EvalDistCompatible (PFunctor.FreeM triPFunctor) := inferInstance

/-- A deterministic handler used to exercise generic instrumentation. -/
@[expose]
def zeroHandler : PFunctor.Handler Option triPFunctor :=
  fun _ => some 0

example : zeroHandler.preInsert (fun _ => some ()) () = some 0 := by
  simp [zeroHandler, seqRight_eq]

example : zeroHandler.postInsert (fun _ _ => some ()) () = some 0 := by
  simp [zeroHandler]

/-! ## OracleSpec compatibility -/

/-- The oracle presentation of the same Boolean interface. -/
@[expose, reducible] def boolOracleSpec : OracleSpec (Fin 1) := fun _ => Bool

noncomputable instance : IsUniformSpec boolOracleSpec :=
  OracleSpec.IsUniformSpec.ofFintypeInhabited _

noncomputable example : MonadLiftT (OracleComp boolOracleSpec) PMF := inferInstance

example : MonadLiftT (OracleComp boolOracleSpec) SetM := inferInstance

noncomputable example : PFunctor.IsProbabilitySpec boolOracleSpec.toPFunctor := inferInstance

noncomputable example : PFunctor.IsUniformSpec boolOracleSpec.toPFunctor :=
  OracleSpec.IsUniformSpec.toPFunctor

example (program : OracleComp boolOracleSpec Bool) :
    𝒮[program] = program.liftM PFunctor.IsProbabilitySpec.toPMF :=
  PFunctor.FreeM.evalSPMF_eq_liftM program

example (program : OracleComp boolOracleSpec Bool) :
    𝒮[program] = simulateQ OracleSpec.IsProbabilitySpec.toPMF program :=
  OracleComp.evalSPMF_eq_simulateQ program

/-! ## Nested coproduct transparency -/

section NestedCoproductTransparency

variable {ι₁ ι₂ ι₃ : Type}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃}

set_option linter.tacticCheckInstances true

example (impl : QueryImpl ((spec₁ + spec₂) + spec₃) Id) (t : spec₂.Domain)
    (consume : spec₂.Range t → Nat) :
    consume (impl (.inl (.inr t))) = consume (impl (.inl (.inr t))) := by
  rfl

example (impl : QueryImpl ((spec₁ + spec₂) + spec₃) Id) (t : spec₃.Domain)
    (consume : spec₃.Range t → Nat) :
    consume (impl (.inr t)) = consume (impl (.inr t)) := by
  rfl

example (impl : QueryImpl ((spec₁ + spec₂) + spec₃) Id) :
    QueryImpl spec₃ (StateT (List spec₃.Domain) Id) :=
  QueryImpl.appendInputLog (fun t => impl (.inr t))

example [IsProbabilitySpec ((spec₁ + spec₂) + spec₃)] (t : spec₂.Domain)
    (program : OracleComp ((spec₁ + spec₂) + spec₃)
      ((((spec₁ + spec₂) + spec₃).Range (.inl (.inr t))) × Bool)) :
    Pr[fun z : spec₂.Range t × Bool => z.2 = true | program] =
      Pr[fun z : spec₂.Range t × Bool => z.2 = true | program] := by
  rfl

example [IsProbabilitySpec ((spec₁ + spec₂) + spec₃)] (t : spec₃.Domain)
    (program : OracleComp ((spec₁ + spec₂) + spec₃)
      ((((spec₁ + spec₂) + spec₃).Range (.inr t)) × Bool)) :
    Pr[fun z : spec₃.Range t × Bool => z.2 = true | program] =
      Pr[fun z : spec₃.Range t × Bool => z.2 = true | program] := by
  rfl

end NestedCoproductTransparency

end VCVioTest.PFunctorFacade
