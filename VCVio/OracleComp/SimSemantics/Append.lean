/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.Coercions.Append

/-!
# Append/Add Operation for Simulation Oracles
-/

universe u v w

namespace QueryImpl

variable {spec₁ spec₂ : OracleSpec} {m n r : Type u → Type*}

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
def addLift {spec₁ spec₂ : OracleSpec} {m n r : Type u → Type*} [MonadLiftT m r] [MonadLiftT n r]
    (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ n) : QueryImpl (spec₁ + spec₂) r :=
  (impl₁.liftTarget r) + (impl₂.liftTarget r)

@[simp] lemma addLift_def {spec₁ spec₂ : OracleSpec}
    {m n r : Type u → Type*} [MonadLiftT m r] [MonadLiftT n r]
    (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ n) :
    (impl₁.addLift impl₂ : QueryImpl (spec₁ + spec₂) r) =
      (impl₁.liftTarget r) + (impl₂.liftTarget r) := rfl

end QueryImpl

-- open OracleSpec OracleComp Prod Sum

-- universe u v w

-- namespace SimOracle

-- variable {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁}
--   {spec₂ : OracleSpec ι₂} {α β γ : Type u}

-- /-- Given simulation oracles `so` and `so'` with source oracles `spec₁` and `spec₂` respectively,
-- with the same target oracles `specₜ`, construct a new simulation oracle from `specₜ`,
-- answering queries to either oracle set with queries to the corresponding simulation oracle.
-- NOTE: `n` can't be inferred from the explicit parameters, the use case needs to give context -/
-- def append {m₁ m₂ n : Type u → Type v} [MonadLiftT m₁ n] [MonadLiftT m₂ n]
--     (so : QueryImpl spec₁ m₁) (so' : QueryImpl spec₂ m₂) :
--     QueryImpl (spec₁ ++ₒ spec₂) n where impl
--   | query (inl i) t => so.impl (query i t)
--   | query (inr i) t => so'.impl (query i t)

-- infixl : 65 " ++ₛₒ " => append

-- variable {m₁ m₂ n : Type u → Type v} [MonadLift m₁ n] [MonadLift m₂ n]
--     (so : QueryImpl spec₁ m₁) (so' : QueryImpl spec₂ m₂)

-- @[simp]
-- lemma append_apply_inl (i : ι₁) (t : spec₁.Domain i) :
--     (so ++ₛₒ so' : QueryImpl _ n).impl (query (inl i) t) = so.impl (query i t) := rfl

-- @[simp]
-- lemma append_apply_inr (i : ι₂) (t : spec₂.Domain i) :
--     (so ++ₛₒ so' : QueryImpl _ n).impl (query (inr i) t) = so'.impl (query i t) := rfl

-- variable [AlternativeMonad n] [LawfulAlternative n] [LawfulMonad n]

-- @[simp]
-- lemma simulate_coe_append_left [AlternativeMonad m₁] [LawfulMonad m₁] [LawfulAlternative m₁]
--     [LawfulMonadLift m₁ n] [LawfulAlternativeLift m₁ n] (oa : OracleComp spec₁ α) :
--     simulateQ (so ++ₛₒ so') (liftM oa) = (liftM (simulateQ so oa) : n α) := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa hoa =>
--       simp at hoa
--       simp [hoa, append_apply_inl so so', Function.comp_def]
--   | failure => simp

-- @[simp]
-- lemma simulate_coe_append_right [AlternativeMonad m₂] [LawfulMonad m₂] [LawfulAlternative m₂]
--     [LawfulMonadLift m₂ n] [LawfulAlternativeLift m₂ n] (oa : OracleComp spec₂ α) :
--     simulateQ (so ++ₛₒ so') (liftM oa) = (liftM (simulateQ so' oa) : n α) := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | query_bind i t oa hoa =>
--       simp at hoa
--       simp [hoa, append_apply_inr so so', Function.comp_def]
--   | failure => simp

-- end SimOracle
