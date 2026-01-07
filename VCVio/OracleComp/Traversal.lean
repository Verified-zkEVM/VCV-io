/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.OracleComp

/-!
# Traversing Possible Paths of a Computation.

This file defines functions `alwaysWhen` and `someWhen` that allow for traversing a computation's
structure to check some given predicates on each node, using a set of possible outputs for that
traversal. These definitions are `Prop` not `Bool` and should usually only be used in proofs,
not in defining an actual computaion.

The file also contains many special cases of these functions like `NeverFailWhen`.

-/

open OracleSpec

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type v}

section When

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

-- @[simp] lemma allWhen_pure (x : α) :
--     (pure x : OracleComp spec α).allWhen Q F possible_outputs := True.intro

-- @[simp] lemma someWhen_pure (x : α) :
--     (pure x : OracleComp spec α).someWhen Q F possible_outputs := True.intro

-- @[simp] lemma allWhen_failure_iff :
--     (failure : OracleComp spec α).allWhen Q F possible_outputs ↔ F := Iff.rfl

-- @[simp] lemma allWhen_query_iff (q : OracleQuery spec α) :
--     (q : OracleComp spec α).allWhen Q F possible_outputs ↔ Q q := by simp [allWhen]

-- @[simp] lemma allWhen_query_bind (q : OracleQuery spec α) (oa : α → OracleComp spec β) :
--     ((q : OracleComp spec α) >>= oa).allWhen Q F possible_outputs ↔
--       Q q ∧ ∀ x ∈ possible_outputs q, (oa x).allWhen Q F possible_outputs := by rfl

-- -- TODO: We need a full theory of `supportWhen` to make this work well.
-- @[simp] lemma allWhen_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
--     (oa >>= ob).allWhen Q F possible_outputs ↔ oa.allWhen Q F possible_outputs ∧
--       ∀ x ∈ oa.supportWhen possible_outputs, (ob x).allWhen Q F possible_outputs := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => {
--     simp [supportWhen]
--   }
--   | failure => {
--     simp [supportWhen]
--   }
--   | query_bind i t oa h => {
--     rw [bind_assoc, allWhen_query_bind]
--     simp [h, supportWhen]

--     sorry
--   }
-- TODO: We need a full theory of `supportWhen` to make this work well.
-- @[simp] lemma allWhen_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
--     (oa >>= ob).allWhen Q F possible_outputs ↔ oa.allWhen Q F possible_outputs ∧
--       ∀ x ∈ oa.supportWhen possible_outputs, (ob x).allWhen Q F possible_outputs := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => {
--     simp [supportWhen]
--   }
--   | failure => {
--     simp [supportWhen]
--   }
--   | query_bind i t oa h => {
--     rw [bind_assoc, allWhen_query_bind]
--     simp [h, supportWhen]
--     grind only [cases Or]
--   }

-- @[simp] lemma allWhen

end When

-- dt: All of this should be part of `evalDist` stuff now.

-- /-- `oa` never fails if when responses to queries `q` are in `possible_outputs q`. -/
-- def NeverFailWhen (oa : OracleComp spec α)
--     (possible_outputs : {α : Type v} → OracleQuery spec α → Set α) : Prop :=
--   oa.allWhen (fun _ => True) possible_outputs

-- /-- `oa` never fails even when queries can output any possible value. -/
-- @[reducible, inline] def NeverFail (oa : OracleComp spec α) : Prop :=
--   oa.NeverFailWhen fun _ => Set.univ

-- /-- `oa` might fail when responses to queries `q` are in `possible_outputs q`-/
-- def mayFailWhen (oa : OracleComp spec α)
--     (possible_outputs : {α : Type v} → OracleQuery spec α → Set α) : Prop :=
--   oa.someWhen (fun _ => False) possible_outputs

-- /-- `oa` might fail if queries can output any possible value. -/
-- @[reducible, inline] def mayFail (oa : OracleComp spec α) : Prop :=
--   mayFailWhen oa fun _ => Set.univ
-- TOOD: generalize when `hso` is `neverFailsWhen` for some other `poss`.
-- lemma neverFailsWhen_simulate {ι' : Type*} {spec' : OracleSpec ι'}
--     (oa : OracleComp spec α)
--     (possible_outputs : {α : Type v} → OracleQuery spec α → Set α)
--     (h : neverFailsWhen oa possible_outputs)
--     -- {m : Type v → Type _} [Monad m]
--     (so : QueryImpl spec (OracleComp spec'))
--     (h' : ∀ {α}, ∀ q : OracleQuery spec α, (so.impl q).support ⊆ possible_outputs q)
--     (hso : ∀ {α}, ∀ q : OracleQuery spec α, neverFails (so.impl q)) :
--     neverFails (simulateQ so oa) := by
--     sorry

-- -- TOOD: generalize when `hso` is `NeverFailWhen` for some other `poss`.
-- lemma NeverFailWhen_simulate {ι' : Type*} {spec' : OracleSpec ι'}
--     (oa : OracleComp spec α)
--     (possible_outputs : {α : Type v} → OracleQuery spec α → Set α)
--     (h : NeverFailWhen oa possible_outputs)
--     -- {m : Type v → Type _} [Monad m]
--     (so : QueryImpl spec (OracleComp spec'))
--     (h' : ∀ {α}, ∀ q : OracleQuery spec α, (so.impl q).support ⊆ possible_outputs q)
--     (hso : ∀ {α}, ∀ q : OracleQuery spec α, NeverFail (so.impl q)) :
--     NeverFail (simulateQ so oa) := sorry

-- lemma NeverFail_eq_oracleComp_construct (oa : OracleComp spec α) :
--     oa.NeverFail = OracleComp.construct
--       (fun _ ↦ True) (fun {β} _ _ r ↦ ∀ (x : β), r x) False oa := by
--   simp [NeverFail, NeverFailWhen, allWhen]

-- lemma NeverFail_eq_freeMonad_construct (oa : OracleComp spec α) :
--     oa.NeverFail = FreeMonad.construct
--       (fun t ↦ Option.rec False (fun _ ↦ True) t) (fun _ _ r ↦ ∀ x, r x) oa := by
--   simp [NeverFail, NeverFailWhen, allWhen]
--   rfl

-- @[simp]
-- lemma NeverFail_pure (x : α) : NeverFail (pure x : OracleComp spec α) := trivial

-- @[simp]
-- lemma NeverFail_query (q : OracleQuery spec α) : NeverFail (q : OracleComp spec α) := by
--   simp [NeverFail, NeverFailWhen, allWhen]

-- @[simp]
-- lemma NeverFail_query_bind_iff {q : OracleQuery spec α} {oa : α → OracleComp spec β} :
--     (liftM q >>= oa).NeverFail ↔ ∀ x, NeverFail (oa x) := by
--   simp [NeverFail, NeverFailWhen, allWhen]

-- alias ⟨NeverFail_query_bind, _⟩ := NeverFail_query_bind_iff

-- @[simp]
-- lemma not_NeverFail_failure : ¬ NeverFail (failure : OracleComp spec α) := fun h => h

-- @[simp]
-- lemma NeverFail_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
--     (oa >>= ob).NeverFail ↔ oa.NeverFail ∧ ∀ x ∈ oa.support, (ob x).NeverFail := by
--   induction oa using OracleComp.inductionOn with
--   | pure x => simp
--   | failure => simp
--   | query_bind _ _ r ih => simp [ih, forall_and]; tauto

-- alias ⟨NeverFail_bind, _⟩ := NeverFail_bind_iff

-- @[simp]
-- lemma NeverFail_map_iff (oa : OracleComp spec α) (f : α → β) :
--     NeverFail (f <$> oa) ↔ NeverFail oa := by
--   rw [map_eq_bind_pure_comp]
--   simp only [NeverFail_bind_iff, Function.comp_apply, NeverFail_pure, implies_true, and_true]

-- @[simp]
-- instance [spec.FiniteRange] : DecidablePred (@OracleComp.NeverFail _ spec α) :=
--   fun oa => by induction oa using OracleComp.construct' with
--   | pure x => exact Decidable.isTrue (NeverFail_pure x)
--   | failure => exact Decidable.isFalse not_NeverFail_failure
--   | query_bind i t _ r =>
--       simpa only [Function.const_apply, NeverFail_bind_iff, NeverFail_query, support_query,
--         Set.mem_univ, forall_const, true_and] using Fintype.decidableForallFintype

-- @[simp]
-- lemma NeverFail_guard (p : Prop) [Decidable p] (oa : OracleComp spec α) (h: oa.NeverFail) :
--     NeverFail (if p then oa else failure) ↔ p := by
--   split <;> simp [h] <;> trivial

end OracleComp
