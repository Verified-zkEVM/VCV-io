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

-- TODO: the following `allWhen`/`someWhen` lemmas were removed during remediation.
-- They may be useful once a full `supportWhen` API exists.

-- @[simp] lemma allWhen_pure (x : α) :
--     (pure x : OracleComp spec α).allWhen Q F possible_outputs := True.intro

-- @[simp] lemma someWhen_pure (x : α) :
--     (pure x : OracleComp spec α).someWhen Q F possible_outputs := True.intro

-- @[simp] lemma allWhen_query_iff (q : OracleQuery spec α) :
--     (q : OracleComp spec α).allWhen Q F possible_outputs ↔ Q q := by simp [allWhen]

-- @[simp] lemma allWhen_query_bind (q : OracleQuery spec α) (oa : α → OracleComp spec β) :
--     ((q : OracleComp spec α) >>= oa).allWhen Q F possible_outputs ↔
--       Q q ∧ ∀ x ∈ possible_outputs q, (oa x).allWhen Q F possible_outputs := by rfl

-- @[simp] lemma allWhen_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
--     (oa >>= ob).allWhen Q F possible_outputs ↔ oa.allWhen Q F possible_outputs ∧
--       ∀ x ∈ oa.supportWhen possible_outputs, (ob x).allWhen Q F possible_outputs := by
--   sorry

-- TODO: the following `NeverFail` lemmas used the old traversal-based `NeverFail` definition.
-- `NeverFail` is now a typeclass in `EvalDist/Defs/NeverFails.lean`.
-- Some of these (bind_iff, map_iff, etc.) are already covered by the new typeclass.
-- The ones below have no direct analog in the new design.

-- @[simp] instance [spec.FiniteRange] : DecidablePred (@OracleComp.NeverFail _ spec α) :=
--   fun oa => by induction oa using OracleComp.construct' with
--   | pure x => exact Decidable.isTrue (NeverFail_pure x)
--   | failure => exact Decidable.isFalse not_NeverFail_failure
--   | query_bind i t _ r =>
--       simpa only [Function.const_apply, NeverFail_bind_iff, NeverFail_query, support_query,
--         Set.mem_univ, forall_const, true_and] using Fintype.decidableForallFintype

-- @[simp] lemma NeverFail_guard (p : Prop) [Decidable p] (oa : OracleComp spec α) (h: oa.NeverFail) :
--     NeverFail (if p then oa else failure) ↔ p := by
--   split <;> simp [h] <;> trivial

end OracleComp
