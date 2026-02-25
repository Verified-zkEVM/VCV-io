/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.OracleComp

/-!
# Traversing Possible Paths of a Computation.

This file defines functions `allWhen` and `someWhen` that allow for traversing a computation's
structure to check some given predicates on each node, using a set of possible outputs for that
traversal. These definitions are `Prop` not `Bool` and should usually only be used in proofs,
not in defining an actual computation.
-/

open OracleSpec

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type v}

/-- Given that oracle outputs are bounded by `possible_outputs`, all query inputs in the
computation satisfy `Q` and all pure values satisfy `P`. -/
def allWhen (Q : spec.Domain → Prop) (P : {α : Type v} → α → Prop)
    (possible_outputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop := by
  induction oa using OracleComp.construct with
  | pure x => exact P x
  | query_bind q _ r => exact Q q ∧ ∀ x ∈ possible_outputs q, r x

/-- Given that oracle outputs are bounded by `possible_outputs`, some query input in the
computation satisfies `Q` or some pure value satisfyies `P`. -/
def someWhen (Q : spec.Domain → Prop) (P : {α : Type v} → α → Prop)
    (possible_outputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop := by
  induction oa using OracleComp.construct with
  | pure x => exact P x
  | query_bind q _ r => exact Q q ∨ ∃ x ∈ possible_outputs q, r x

variable {Q : spec.Domain → Prop} {P : {α : Type v} → α → Prop}
  {possible_outputs : (x : spec.Domain) → Set (spec.Range x)}

@[simp] lemma allWhen_pure (x : α) (Q : spec.Domain → Prop) (P : {α : Type v} → α → Prop)
    (possible_outputs : (x : spec.Domain) → Set (spec.Range x)) :
    (pure x : OracleComp spec α).allWhen Q P possible_outputs = P x := rfl

@[simp] lemma someWhen_pure (x : α) (Q : spec.Domain → Prop) (P : {α : Type v} → α → Prop)
    (possible_outputs : (x : spec.Domain) → Set (spec.Range x)) :
    (pure x : OracleComp spec α).someWhen Q P possible_outputs = P x := rfl

@[simp] lemma allWhen_query_bind (q : spec.Domain)
    (oa : spec.Range q → OracleComp spec α) :
    ((query q : OracleComp spec _) >>= oa).allWhen Q P possible_outputs ↔
      Q q ∧ ∀ x ∈ possible_outputs q, (oa x).allWhen Q P possible_outputs := by rfl

-- TODO: `allWhen_bind_iff` statement is INCORRECT for the `pure` case.
-- When `oa = pure x`:
--   LHS = `(ob x).allWhen Q P s`
--   RHS = `P x ∧ (ob x).allWhen Q P s`
-- The RHS imposes an extra `P x` constraint on intermediate values that the LHS does not.
-- A correct formulation might either:
--   (a) use a separate predicate for intermediate vs. final values, or
--   (b) only state the `⟸` direction (which is valid), or
--   (c) weaken the `pure` case in `allWhen` to `True` when used inside a bind.
-- @[simp] lemma allWhen_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
--     (oa >>= ob).allWhen Q P possible_outputs ↔ oa.allWhen Q P possible_outputs ∧
--       ∀ x ∈ oa.supportWhen possible_outputs, (ob x).allWhen Q P possible_outputs := by
--   sorry

end OracleComp
