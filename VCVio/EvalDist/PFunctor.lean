/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.NeverFails
public import PolyFun.PFunctor.Free.Basic
public import PolyFun.PFunctor.Handler

/-!
# Probability Semantics for Polynomial Free Monads

This module equips an arbitrary polynomial functor with per-operation
probability semantics and interprets its free monad in `PMF`. It also provides
the syntax-only support interpretation in `SetM`. The API is independent of
`OracleSpec`; oracle computations inherit it through their underlying
polynomial functor.
-/

@[expose] public section

open ENNReal

universe u v uA

namespace PFunctor

/- Lean 4.33 compares the syntax-only `SetM = Set` handler at implicit
transparency when applying the generic `FreeM.liftM_lift` law. -/
attribute [local implicit_reducible] SetM

/-- Per-operation probability distributions for a polynomial interface. -/
class IsProbabilitySpec (P : PFunctor.{uA, u}) where
  /-- The distribution of directions available at an operation. -/
  toPMF : Handler PMF P

/-- A finitely branching polynomial interface whose operation responses use
the canonical uniform distribution. -/
class IsUniformSpec (P : PFunctor.{uA, u}) extends IsProbabilitySpec P where
  /-- Every direction type is finite. -/
  fintype : P.Fintype
  /-- Every direction type is inhabited. -/
  inhabited : P.Inhabited
  /-- Each operation uses the canonical uniform distribution on directions. -/
  toPMF_eq_uniform : ∀ operation,
    toPMF operation = PMF.uniformOfFintype (P.B operation)

attribute [reducible, instance] IsUniformSpec.fintype IsUniformSpec.inhabited

/-- Construct uniform probability semantics from finite, inhabited direction
types. This is deliberately not an instance: probability semantics remain an
explicit opt-in. -/
@[reducible]
noncomputable def IsUniformSpec.ofFintypeInhabited (P : PFunctor.{uA, u})
    [hF : P.Fintype] [hI : P.Inhabited] : IsUniformSpec P where
  toPMF operation := PMF.uniformOfFintype (P.B operation)
  fintype := hF
  inhabited := hI
  toPMF_eq_uniform _ := rfl

namespace FreeM

variable {P : PFunctor.{uA, u}} {α β : Type u}

/-- Interpret a polynomial free program using its per-operation probability
distributions. -/
noncomputable instance instMonadLiftTPMF [P.IsProbabilitySpec] :
    MonadLiftT (FreeM P) PMF where
  monadLift program := program.liftM IsProbabilitySpec.toPMF

noncomputable instance instLawfulMonadLiftTPMF [P.IsProbabilitySpec] :
    LawfulMonadLiftT (FreeM P) PMF where
  monadLift_pure := FreeM.liftM_pure _
  monadLift_bind := FreeM.liftM_bind _

/-- Interpret support syntactically by allowing every direction at every
operation. This does not require probability or finiteness assumptions. -/
instance instMonadLiftTSetM : MonadLiftT (FreeM P) SetM where
  monadLift program := program.liftM fun _ => Set.univ

instance instLawfulMonadLiftTSetM : LawfulMonadLiftT (FreeM P) SetM where
  monadLift_pure := FreeM.liftM_pure _
  monadLift_bind := FreeM.liftM_bind _

/-- The distribution semantics of a polynomial free program is its universal
fold into `PMF`. -/
theorem evalSPMF_eq_liftM [P.IsProbabilitySpec] (program : FreeM P α) :
    𝒮[program] = program.liftM IsProbabilitySpec.toPMF := rfl

/-- The support semantics of a polynomial free program is its universal fold
with every operation direction available. -/
theorem support_eq_liftM (program : FreeM P α) :
    support program = SetM.run (program.liftM fun _ => Set.univ) := rfl

/-- A single operation evaluates to its configured direction distribution. -/
@[simp]
theorem evalSPMF_lift [P.IsProbabilitySpec] (operation : P.A) :
    𝒮[(FreeM.lift operation : FreeM P (P.B operation))] =
      (IsProbabilitySpec.toPMF operation : SPMF (P.B operation)) := by
  rw [evalSPMF_eq_liftM, FreeM.liftM_lift]

/-- A single operation on a uniform polynomial interface evaluates to the
canonical uniform distribution on its directions. -/
@[simp]
theorem evalSPMF_lift_eq_uniform [h : P.IsUniformSpec] (operation : P.A) :
    𝒮[(FreeM.lift operation : FreeM P (P.B operation))] =
      (PMF.uniformOfFintype (P.B operation) : SPMF (P.B operation)) := by
  rw [evalSPMF_lift]
  exact congrArg (fun distribution : PMF (P.B operation) =>
    (distribution : SPMF (P.B operation))) (h.toPMF_eq_uniform operation)

/-- The support of an operation with a result continuation is the range of
that continuation. -/
@[simp]
theorem support_liftObj (object : P.Obj α) :
    support (FreeM.liftObj object : FreeM P α) = Set.range object.2 := by
  change SetM.run ((FreeM.liftObj object).liftM fun _ => Set.univ) =
    Set.range object.2
  rw [FreeM.liftM_liftObj]
  exact Set.image_univ

/-- Every direction of a single operation belongs to its `SetM`-fold support.

This name distinguishes VCVio's denotational `support` from PolyFun's structural
`MonadAttach.support_lift` theorem. -/
@[simp]
theorem support_lift_eq_univ (operation : P.A) :
    support (FreeM.lift operation : FreeM P (P.B operation)) = Set.univ := by
  change SetM.run ((FreeM.lift operation).liftM fun _ => Set.univ) = Set.univ
  rw [FreeM.liftM_lift]
  rfl

/-- Syntactic support and distribution support agree for a uniformly
interpreted polynomial free monad.

For an oracle spec this is reached explicitly, not by synthesis:
`OracleComp.instEvalDistCompatible` supplies the `IsUniformSpec` premise through
`OracleSpec.IsUniformSpec.toPFunctor`, which is deliberately a definition rather than an
instance so that nothing unifies against the reducible head `spec.toPFunctor`. Keep it that
way — promoting that conversion would make this instance and the oracle-level one both
applicable to the same goal. -/
instance (priority := 100) instEvalDistCompatible [uniform : P.IsUniformSpec] :
    EvalDistCompatible (FreeM P) where
  support_eq_SPMF_support program := by
    change support program = SPMF.support 𝒮[program]
    induction program with
    | pure result => simp
    | lift_bind operation next ih =>
        ext result
        simp [support_lift_eq_univ, uniform.toPMF_eq_uniform, ih]

end FreeM
end PFunctor
