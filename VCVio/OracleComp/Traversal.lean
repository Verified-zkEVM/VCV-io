/- 
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.EvalDist

/-!
# Traversing Possible Paths of a Computation

This file defines structural predicates for checking whether all or some reachable paths of an
`OracleComp` satisfy predicates on query nodes and final outputs, relative to a chosen set of
possible oracle outputs.

It also connects those structural predicates to the denotational set `supportWhen`, so proofs can
move cleanly between the syntax-level traversal view and the reachable-output view.
-/

open OracleSpec

universe u v w

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type v}

/-- Given that oracle outputs are bounded by `possibleOutputs`, every reachable query input in the
computation satisfies `queryPred`, and every reachable pure output satisfies `outputPred`. -/
def allPathsSatisfy (queryPred : spec.Domain → Prop) (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop := by
  induction oa using OracleComp.construct with
  | pure x => exact outputPred x
  | query_bind q _ ih => exact queryPred q ∧ ∀ x ∈ possibleOutputs q, ih x

/-- Given that oracle outputs are bounded by `possibleOutputs`, some reachable query input in the
computation satisfies `queryPred`, or some reachable pure output satisfies `outputPred`. -/
def somePathSatisfies (queryPred : spec.Domain → Prop) (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop := by
  induction oa using OracleComp.construct with
  | pure x => exact outputPred x
  | query_bind q _ ih => exact queryPred q ∨ ∃ x ∈ possibleOutputs q, ih x

/-- Output-only view of [`OracleComp.allPathsSatisfy`]: every output reachable under
`possibleOutputs` satisfies `outputPred`. -/
def allOutputsSatisfyWhen (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop :=
  oa.allPathsSatisfy (fun _ ↦ True) outputPred possibleOutputs

/-- Output-only view of [`OracleComp.somePathSatisfies`]: some output reachable under
`possibleOutputs` satisfies `outputPred`. -/
def someOutputSatisfiesWhen (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop :=
  oa.somePathSatisfies (fun _ ↦ False) outputPred possibleOutputs

variable {queryPred : spec.Domain → Prop} {outputPred : α → Prop}
  {possibleOutputs : (x : spec.Domain) → Set (spec.Range x)}

@[simp]
lemma allPathsSatisfy_pure (x : α)
    (queryPred : spec.Domain → Prop) (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x)) :
    (pure x : OracleComp spec α).allPathsSatisfy queryPred outputPred possibleOutputs =
      outputPred x := rfl

@[simp]
lemma somePathSatisfies_pure (x : α)
    (queryPred : spec.Domain → Prop) (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x)) :
    (pure x : OracleComp spec α).somePathSatisfies queryPred outputPred possibleOutputs =
      outputPred x := rfl

@[simp]
lemma allPathsSatisfy_query_bind (q : spec.Domain)
    (oa : spec.Range q → OracleComp spec α) :
    ((query q : OracleComp spec _) >>= oa).allPathsSatisfy queryPred outputPred possibleOutputs ↔
      queryPred q ∧
        ∀ x ∈ possibleOutputs q, (oa x).allPathsSatisfy queryPred outputPred possibleOutputs := by
  rfl

@[simp]
lemma somePathSatisfies_query_bind (q : spec.Domain)
    (oa : spec.Range q → OracleComp spec α) :
    ((query q : OracleComp spec _) >>= oa).somePathSatisfies queryPred outputPred possibleOutputs ↔
      queryPred q ∨
        ∃ x ∈ possibleOutputs q, (oa x).somePathSatisfies queryPred outputPred possibleOutputs := by
  rfl

lemma allOutputsSatisfyWhen_iff_supportWhen
    (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) :
    oa.allOutputsSatisfyWhen outputPred possibleOutputs ↔
      ∀ x ∈ oa.supportWhen possibleOutputs, outputPred x := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp [OracleComp.allOutputsSatisfyWhen, OracleComp.supportWhen_pure]
  | query_bind q oa ih =>
      simp only [OracleComp.allOutputsSatisfyWhen, OracleComp.allPathsSatisfy_query_bind,
        true_and, OracleComp.supportWhen_query_bind, Set.mem_iUnion, exists_prop]
      constructor
      · intro h x hx
        rcases hx with ⟨u, hu, hx⟩
        exact (ih u).1 (h u hu) x hx
      · intro h u hu
        exact (ih u).2 (fun x hx ↦ h x ⟨u, hu, hx⟩)

lemma someOutputSatisfiesWhen_iff_supportWhen
    (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) :
    oa.someOutputSatisfiesWhen outputPred possibleOutputs ↔
      ∃ x ∈ oa.supportWhen possibleOutputs, outputPred x := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp [OracleComp.someOutputSatisfiesWhen, OracleComp.supportWhen_pure]
  | query_bind q oa ih =>
      simp only [OracleComp.someOutputSatisfiesWhen, OracleComp.somePathSatisfies_query_bind,
        false_or, OracleComp.supportWhen_query_bind, Set.mem_iUnion, exists_prop]
      constructor
      · intro h
        rcases h with ⟨u, hu, hrest⟩
        rcases (ih u).1 hrest with ⟨x, hx, hPx⟩
        exact ⟨x, ⟨u, hu, hx⟩, hPx⟩
      · intro h
        rcases h with ⟨x, ⟨u, hu, hx⟩, hPx⟩
        exact ⟨u, hu, (ih u).2 ⟨x, hx, hPx⟩⟩

-- TODO: `allPathsSatisfy_bind_iff` statement is INCORRECT for the `pure` case.
-- When `oa = pure x`:
--   LHS = `(ob x).allPathsSatisfy Q P s`
--   RHS = `P x ∧ (ob x).allPathsSatisfy Q P s`
-- The RHS imposes an extra `P x` constraint on intermediate values that the LHS does not.
-- A correct formulation might either:
--   (a) use a separate predicate for intermediate vs. final values, or
--   (b) only state the `⟸` direction (which is valid), or
--   (c) weaken the `pure` case in `allPathsSatisfy` to `True` when used inside a bind.
-- @[simp] lemma allPathsSatisfy_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
--     (oa >>= ob).allPathsSatisfy Q P possibleOutputs ↔
--       oa.allPathsSatisfy Q P possibleOutputs ∧
--       ∀ x ∈ oa.supportWhen possibleOutputs, (ob x).allPathsSatisfy Q P possibleOutputs := by
--   sorry

end OracleComp
