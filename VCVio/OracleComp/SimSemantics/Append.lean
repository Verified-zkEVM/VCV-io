/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.Coercions.Add

/-!
# Append/Add Operation for Simulation Oracles
-/

universe u v w

namespace QueryImpl

variable {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {m n r : Type u → Type*}

/-- Simplest version of adding queries when all implementations are in the same monad.
The actual add notation for `QueryImpl` uses `QueryImpl.addLift` which adds monad lifting
to this definition for greater flexibility. -/
protected def add (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m) :
    QueryImpl (spec₁ + spec₂) m | .inl t => impl₁ t | .inr t => impl₂ t

/-- Add two `QueryImpl` to get an implementation on the sum of the two `OracleSpec`.-/
instance : HAdd (QueryImpl spec₁ m) (QueryImpl spec₂ m) (QueryImpl (spec₁ + spec₂) m) where
  hAdd := QueryImpl.add

lemma add_apply (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : OracleSpec.Domain (spec₁ + spec₂)) : (impl₁ + impl₂) t =
      match t with | .inl t => impl₁ t | .inr t => impl₂ t := rfl

@[simp] lemma add_apply_inl (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : spec₁.Domain) : (impl₁ + impl₂) (.inl t) = impl₁ t := rfl

@[simp] lemma add_apply_inr (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : spec₂.Domain) : (impl₁ + impl₂) (.inr t) = impl₂ t := rfl

/-- Version of `QueryImpl.add` that also lifts the two implementations to a shared lift monad. -/
def addLift {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m n r : Type u → Type*} [MonadLiftT m r] [MonadLiftT n r]
    (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ n) : QueryImpl (spec₁ + spec₂) r :=
  (impl₁.liftTarget r) + (impl₂.liftTarget r)

@[simp] lemma addLift_def {ι₁ ι₂} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m n r : Type u → Type*} [MonadLiftT m r] [MonadLiftT n r]
    (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ n) :
    (impl₁.addLift impl₂ : QueryImpl (spec₁ + spec₂) r) =
      (impl₁.liftTarget r) + (impl₂.liftTarget r) := rfl

section simulateQ_add_liftComp

variable {ι₁' : Type} {ι₂' : Type}
  {spec₁' : OracleSpec ι₁'} {spec₂' : OracleSpec ι₂'}
  {α : Type} {m' : Type → Type v} [Monad m'] [LawfulMonad m']
  (impl₁' : QueryImpl spec₁' m') (impl₂' : QueryImpl spec₂' m')

private lemma simulateQ_add_liftM_left (t : spec₁'.Domain) :
    simulateQ (impl₁' + impl₂')
      (liftM (OracleQuery.query (spec := spec₁') t) : OracleComp (spec₁' + spec₂') _) =
    impl₁' t := by
  show simulateQ (impl₁' + impl₂')
    (liftM (liftM (OracleQuery.query (spec := spec₁') t) : OracleQuery (spec₁' + spec₂') _)) = _
  simp [simulateQ_query]

private lemma simulateQ_add_liftM_right (t : spec₂'.Domain) :
    simulateQ (impl₁' + impl₂')
      (liftM (OracleQuery.query (spec := spec₂') t) : OracleComp (spec₁' + spec₂') _) =
    impl₂' t := by
  show simulateQ (impl₁' + impl₂')
    (liftM (liftM (OracleQuery.query (spec := spec₂') t) : OracleQuery (spec₁' + spec₂') _)) = _
  simp [simulateQ_query]

@[simp]
lemma simulateQ_add_liftComp_left (oa : OracleComp spec₁' α) :
    simulateQ (impl₁' + impl₂') (OracleComp.liftComp oa (spec₁' + spec₂')) =
      simulateQ impl₁' oa := by
  have h : (impl₁' + impl₂') ∘ₛ
      (fun t => liftM (OracleQuery.query (spec := spec₁') t) : QueryImpl spec₁' (OracleComp (spec₁' + spec₂'))) =
      impl₁' := by
    funext t; exact simulateQ_add_liftM_left impl₁' impl₂' t
  rw [OracleComp.liftComp_def, ← simulateQ_compose, h]

@[simp]
lemma simulateQ_add_liftComp_right (ob : OracleComp spec₂' α) :
    simulateQ (impl₁' + impl₂') (OracleComp.liftComp ob (spec₁' + spec₂')) =
      simulateQ impl₂' ob := by
  have h : (impl₁' + impl₂') ∘ₛ
      (fun t => liftM (OracleQuery.query (spec := spec₂') t) : QueryImpl spec₂' (OracleComp (spec₁' + spec₂'))) =
      impl₂' := by
    funext t; exact simulateQ_add_liftM_right impl₁' impl₂' t
  rw [OracleComp.liftComp_def, ← simulateQ_compose, h]

end simulateQ_add_liftComp

end QueryImpl
