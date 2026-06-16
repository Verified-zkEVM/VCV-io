/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions
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

/-- Add two `QueryImpl` to get an implementation on the sum of the two `OracleSpec`. -/
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

private lemma simulateQ_add_liftM_query_left (t : spec₁'.Domain) :
    simulateQ (impl₁' + impl₂')
      (liftM (spec₁'.query t) : OracleComp (spec₁' + spec₂') _) =
    impl₁' t := by
  change simulateQ (impl₁' + impl₂')
    (liftM (liftM (spec₁'.query t) : OracleQuery (spec₁' + spec₂') _)) = _
  simp [simulateQ_query]

private lemma simulateQ_add_liftM_query_right (t : spec₂'.Domain) :
    simulateQ (impl₁' + impl₂')
      (liftM (spec₂'.query t) : OracleComp (spec₁' + spec₂') _) =
    impl₂' t := by
  change simulateQ (impl₁' + impl₂')
    (liftM (liftM (spec₂'.query t) : OracleQuery (spec₁' + spec₂') _)) = _
  simp [simulateQ_query]

@[simp]
lemma simulateQ_add_liftComp_left (oa : OracleComp spec₁' α) :
    simulateQ (impl₁' + impl₂') (OracleComp.liftComp oa (spec₁' + spec₂')) =
      simulateQ impl₁' oa := by
  rw [OracleComp.liftComp_def, ← simulateQ_compose]
  congr 1
  funext t
  exact simulateQ_add_liftM_query_left impl₁' impl₂' t

@[simp]
lemma simulateQ_add_liftComp_right (ob : OracleComp spec₂' α) :
    simulateQ (impl₁' + impl₂') (OracleComp.liftComp ob (spec₁' + spec₂')) =
      simulateQ impl₂' ob := by
  rw [OracleComp.liftComp_def, ← simulateQ_compose]
  congr 1
  funext t
  exact simulateQ_add_liftM_query_right impl₁' impl₂' t

/-- `liftM`-normal-form companion of `simulateQ_add_liftComp_left`. Because `liftComp_eq_liftM`
normalizes `liftComp → liftM` under `simp`, the `liftComp`-keyed lemma never fires inside `simp`;
this `liftM`-keyed form is what `simp` actually needs.

Deliberately **not** `@[simp]`: as a global rule it shifts the normal form of `simulateQ` over an
added handler applied to a lifted-in computation, which pre-empts and breaks existing proofs that
manage that reduction themselves. Pass it explicitly, e.g.
`simp [myHandler, simulateQ_add_liftM_left, simulateQ_toQueryImpl]`. -/
lemma simulateQ_add_liftM_left (oa : OracleComp spec₁' α) :
    simulateQ (impl₁' + impl₂') (liftM oa : OracleComp (spec₁' + spec₂') α) =
      simulateQ impl₁' oa := by
  rw [← OracleComp.liftComp_eq_liftM]
  exact simulateQ_add_liftComp_left impl₁' impl₂' oa

/-- `liftM`-normal-form companion of `simulateQ_add_liftComp_right`; opt-in, see
`simulateQ_add_liftM_left`. -/
lemma simulateQ_add_liftM_right (ob : OracleComp spec₂' α) :
    simulateQ (impl₁' + impl₂') (liftM ob : OracleComp (spec₁' + spec₂') α) =
      simulateQ impl₂' ob := by
  rw [← OracleComp.liftComp_eq_liftM]
  exact simulateQ_add_liftComp_right impl₁' impl₂' ob

lemma simulateQ_liftComp_left_eq_of_apply
    (impl : QueryImpl (spec₁' + spec₂') m') (impl₁ : QueryImpl spec₁' m')
    (h : ∀ t, impl (Sum.inl t) = impl₁ t) (oa : OracleComp spec₁' α) :
    simulateQ impl (OracleComp.liftComp oa (spec₁' + spec₂')) =
      simulateQ impl₁ oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      rw [OracleComp.liftComp_bind, simulateQ_bind, simulateQ_bind]
      have hq :
          simulateQ impl
            (OracleComp.liftComp
              (liftM (spec₁'.query t) : OracleComp spec₁' (spec₁'.Range t))
              (spec₁' + spec₂')) = impl₁ t := by
        rw [OracleComp.liftComp_query]
        change simulateQ impl
          (liftM ((spec₁' + spec₂').query (Sum.inl t))) = impl₁ t
        rw [simulateQ_spec_query]
        exact h t
      rw [hq, simulateQ_spec_query]
      exact bind_congr fun u => ih u

lemma simulateQ_liftComp_right_eq_of_apply
    (impl : QueryImpl (spec₁' + spec₂') m') (impl₂ : QueryImpl spec₂' m')
    (h : ∀ t, impl (Sum.inr t) = impl₂ t) (oa : OracleComp spec₂' α) :
    simulateQ impl (OracleComp.liftComp oa (spec₁' + spec₂')) =
      simulateQ impl₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      rw [OracleComp.liftComp_bind, simulateQ_bind, simulateQ_bind]
      have hq :
          simulateQ impl
            (OracleComp.liftComp
              (liftM (spec₂'.query t) : OracleComp spec₂' (spec₂'.Range t))
              (spec₁' + spec₂')) = impl₂ t := by
        rw [OracleComp.liftComp_query]
        change simulateQ impl
          (liftM ((spec₁' + spec₂').query (Sum.inr t))) = impl₂ t
        rw [simulateQ_spec_query]
        exact h t
      rw [hq, simulateQ_spec_query]
      exact bind_congr fun u => ih u

end simulateQ_add_liftComp

/-- Simulating the trivial `HasQuery.toQueryImpl` handler back into `OracleComp spec` is the
identity (the composite of `HasQuery.toQueryImpl_eq_id'` and `simulateQ_id'`).

Like `toQueryImpl_eq_id'`, this is deliberately **not** `@[simp]`: globally it lets `simulateQ`
of a `unifFwdImpl`-style `toQueryImpl.liftTarget` handler fully reduce, which can re-enable a
backward induction-hypothesis rewrite and diverge. Pass it explicitly to `simp` (alongside the
opaque handler definition) to discharge a lifted-in computation, e.g.
`simp [myHandler, simulateQ_toQueryImpl]`; the `simulateQ_add_liftM_left`/`_right` and
`simulateQ_liftTarget` rungs are `@[simp]` and fire on their own. -/
lemma simulateQ_toQueryImpl {ι : Type*} {spec : OracleSpec ι} {α : Type u}
    (mx : OracleComp spec α) :
    simulateQ (HasQuery.toQueryImpl : QueryImpl spec (OracleComp spec)) mx = mx := by
  rw [HasQuery.toQueryImpl_eq_id', simulateQ_id']

section simulateQ_liftM

variable {ι₁' : Type} {ι₂' : Type}
  {spec₁' : OracleSpec ι₁'} {spec₂' : OracleSpec ι₂'}
  {α : Type} {m' : Type → Type v} [Monad m'] [LawfulMonad m']
  [MonadLiftT (OracleComp spec₁') (OracleComp spec₂')]
  [LawfulMonadLiftT (OracleComp spec₁') (OracleComp spec₂')]

lemma simulateQ_liftM_eq_of_query
    (impl : QueryImpl spec₂' m') (impl₁ : QueryImpl spec₁' m')
    (h : ∀ t, simulateQ impl
      (liftM (liftM (spec₁'.query t) :
        OracleComp spec₁' (spec₁'.Range t)) :
        OracleComp spec₂' (spec₁'.Range t)) = impl₁ t)
    (oa : OracleComp spec₁' α) :
    simulateQ impl (liftM oa : OracleComp spec₂' α) =
      simulateQ impl₁ oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t k ih =>
      rw [liftM_bind, simulateQ_bind, simulateQ_bind, h t, simulateQ_spec_query]
      exact bind_congr fun u => ih u

end simulateQ_liftM

end QueryImpl
