/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.SimSemantics.QueryImpl
import VCVio.Prelude
import ToMathlib.Control.OptionT

/-!
# Simulation Semantics for Oracles in a Computation

-/

open OracleComp Prod

universe u v w

variable {α β γ : Type u}

section simulateQ

/-- Given an implementation of `spec` in the monad `r`, convert an `OracleComp spec α` to a
implementation in `r α` by substituting `impl t` for `query t` throughout. -/
def simulateQ {ι} {spec : OracleSpec ι} {r : Type u → Type _} [Monad r]
    (impl : QueryImpl spec r) {α : Type u} (mx : OracleComp spec α) : r α :=
  PFunctor.FreeM.mapM impl mx

variable {ι} {spec : OracleSpec ι} {r m n : Type u → Type*}
    [Monad r] (impl : QueryImpl spec r)

@[simp, grind =, game_rule]
lemma simulateQ_pure (x : α) :
    simulateQ impl (pure x : OracleComp spec α) = pure x := rfl

@[simp, grind =, game_rule]
lemma simulateQ_bind [LawfulMonad r] (mx : OracleComp spec α) (my : α → OracleComp spec β) :
    simulateQ impl (mx >>= my) = simulateQ impl mx >>= fun x => simulateQ impl (my x) := by
  simp [simulateQ]

/-- Version of `simulateQ` that bundles into a monad hom. -/
@[reducible]
def simulateQ' [LawfulMonad r] (impl : QueryImpl spec r) : OracleComp spec →ᵐ r where
  toFun {_α} mx := simulateQ impl mx
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

@[simp, grind =, game_rule]
lemma simulateQ_query [LawfulMonad r] (q : OracleQuery spec α) :
    simulateQ impl (liftM q) = q.cont <$> (impl q.input) := by
  simp [simulateQ, PFunctor.FreeM.mapM.eq_def]

@[simp]
lemma simulateQ_query_bind [LawfulMonad r] (q : OracleQuery spec α)
    (ou : α → OracleComp spec β) : simulateQ impl (liftM q >>= ou) =
      liftM (impl q.input) >>= fun u => simulateQ impl (ou (q.cont u)) := by aesop

@[simp, grind =]
lemma simulateQ_map [LawfulMonad r] (mx : OracleComp spec α) (f : α → β) :
    simulateQ impl (f <$> mx) = f <$> simulateQ impl mx := by
  simp [map_eq_bind_pure_comp]

@[simp]
lemma simulateQ_seq [LawfulMonad r] (og : OracleComp spec (α → β)) (mx : OracleComp spec α) :
    simulateQ impl (og <*> mx) = simulateQ impl og <*> simulateQ impl mx := by
  simp [seq_eq_bind_map]

@[simp]
lemma simulateQ_seqLeft [LawfulMonad r] (mx : OracleComp spec α) (my : OracleComp spec β) :
    simulateQ impl (mx <* my) = simulateQ impl mx <* simulateQ impl my := by
  simp [seqLeft_eq_bind]

@[simp]
lemma simulateQ_seqRight [LawfulMonad r] (mx : OracleComp spec α) (my : OracleComp spec β) :
    simulateQ impl (mx *> my) = simulateQ impl mx *> simulateQ impl my := by
  simp [seqRight_eq_bind]

@[simp]
lemma simulateQ_ite (p : Prop) [Decidable p] (mx mx' : OracleComp spec α) :
    simulateQ impl (ite p mx mx') = ite p (simulateQ impl mx) (simulateQ impl mx') := by
  split_ifs <;> rfl

end simulateQ

variable {ι} {spec : OracleSpec ι} {n : Type u → Type v}
  [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)

lemma simulateQ_def (impl : QueryImpl spec n) (mx : OracleComp spec α) :
    simulateQ impl mx = PFunctor.FreeM.mapMHom impl mx := rfl

/-- `QueryImpl.id'` is an identity for `simulateQ` with implementaiton in `OracleComp spec`. -/
@[simp, grind =]
lemma simulateQ_id' (mx : OracleComp spec α) :
    simulateQ (QueryImpl.id' spec) mx = mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [h]

/-- Lifting queries to their original implementation has no effect on a computation. -/
lemma simulateQ_ofLift_eq_self {α} (mx : OracleComp spec α) :
    simulateQ (QueryImpl.ofLift spec (OracleComp spec)) mx = mx := by simp

section tests

variable {ι₁ ι₂ ι₃ ι₄}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄}

example (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₂))) :
    OptionT (OracleComp spec₂) α :=
  simulateQ impl₂ <|
    simulateQ impl₁ mx

example (mx : OracleComp spec₁ α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OptionT (OracleComp spec₃)))
    (impl₃ : QueryImpl spec₃ (OptionT (OracleComp spec₄))) :
    OptionT (OptionT (OracleComp spec₄)) α :=
  simulateQ impl₃ <| simulateQ impl₂ <| simulateQ impl₁ mx

example (mx : OptionT (OracleComp spec₁) α)
    (impl₁ : QueryImpl spec₁ (OracleComp spec₂))
    (impl₂ : QueryImpl spec₂ (OracleComp spec₃)) :
    OptionT (OracleComp spec₃) α :=
  simulateQ impl₂ <| simulateQ impl₁ <| mx

end tests
