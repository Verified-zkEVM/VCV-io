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

open scoped OracleSpec.PrimitiveQuery

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
  oa.allPathsSatisfy (fun _ => True) outputPred possibleOutputs

/-- Output-only view of [`OracleComp.somePathSatisfies`]: some output reachable under
`possibleOutputs` satisfies `outputPred`. -/
def someOutputSatisfiesWhen (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) : Prop :=
  oa.somePathSatisfies (fun _ => False) outputPred possibleOutputs

variable {queryPred : spec.Domain → Prop} {outputPred : α → Prop}
  {possibleOutputs : (x : spec.Domain) → Set (spec.Range x)}

@[simp]
lemma allPathsSatisfy_pure (x : α) :
    (pure x : OracleComp spec α).allPathsSatisfy queryPred outputPred possibleOutputs =
      outputPred x := rfl

@[simp]
lemma somePathSatisfies_pure (x : α) :
    (pure x : OracleComp spec α).somePathSatisfies queryPred outputPred possibleOutputs =
      outputPred x := rfl

@[simp]
lemma allPathsSatisfy_query_bind (q : spec.Domain)
    (oa : spec.Range q → OracleComp spec α) :
    ((query q : OracleComp spec _) >>= oa).allPathsSatisfy queryPred outputPred possibleOutputs ↔
      queryPred q ∧
        ∀ x ∈ possibleOutputs q, (oa x).allPathsSatisfy queryPred outputPred possibleOutputs :=
  Iff.rfl

@[simp]
lemma somePathSatisfies_query_bind (q : spec.Domain)
    (oa : spec.Range q → OracleComp spec α) :
    ((query q : OracleComp spec _) >>= oa).somePathSatisfies queryPred outputPred possibleOutputs ↔
      queryPred q ∨
        ∃ x ∈ possibleOutputs q, (oa x).somePathSatisfies queryPred outputPred possibleOutputs :=
  Iff.rfl

/-- Every output of `oa` reachable under `possibleOutputs` satisfies `outputPred` exactly when
`outputPred` holds throughout `oa.supportWhen possibleOutputs`. -/
lemma allOutputsSatisfyWhen_iff_supportWhen (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x)) (oa : OracleComp spec α) :
    oa.allOutputsSatisfyWhen outputPred possibleOutputs ↔
      ∀ x ∈ oa.supportWhen possibleOutputs, outputPred x := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [OracleComp.allOutputsSatisfyWhen, OracleComp.supportWhen_pure]
  | query_bind q oa ih =>
      simp only [OracleComp.allOutputsSatisfyWhen, OracleComp.allPathsSatisfy_query_bind,
        true_and, OracleComp.supportWhen_query_bind, Set.mem_iUnion, exists_prop] at ih ⊢
      grind

/-- Some output of `oa` reachable under `possibleOutputs` satisfies `outputPred` exactly when
`outputPred` holds at some point of `oa.supportWhen possibleOutputs`. -/
lemma someOutputSatisfiesWhen_iff_supportWhen (outputPred : α → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x)) (oa : OracleComp spec α) :
    oa.someOutputSatisfiesWhen outputPred possibleOutputs ↔
      ∃ x ∈ oa.supportWhen possibleOutputs, outputPred x := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [OracleComp.someOutputSatisfiesWhen, OracleComp.supportWhen_pure]
  | query_bind q oa ih =>
      simp only [OracleComp.someOutputSatisfiesWhen, OracleComp.somePathSatisfies_query_bind,
        false_or, OracleComp.supportWhen_query_bind, Set.mem_iUnion, exists_prop] at ih ⊢
      grind

/-- A bind satisfies a universal path property exactly when every path of the first computation
leads to a continuation that also satisfies that path property. -/
@[simp]
lemma allPathsSatisfy_bind_iff
    (queryPred : spec.Domain → Prop) (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).allPathsSatisfy queryPred outputPred possibleOutputs ↔
      oa.allPathsSatisfy queryPred
        (fun x => (ob x).allPathsSatisfy queryPred outputPred possibleOutputs)
        possibleOutputs := by
  induction oa using OracleComp.inductionOn <;>
    simp [monad_norm, OracleComp.allPathsSatisfy_query_bind, *]

/-- A bind satisfies an existential path property exactly when either the first computation
already satisfies it on some path, or one reachable continuation does. -/
@[simp]
lemma somePathSatisfies_bind_iff
    (queryPred : spec.Domain → Prop) (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).somePathSatisfies queryPred outputPred possibleOutputs ↔
      oa.somePathSatisfies queryPred
        (fun x => (ob x).somePathSatisfies queryPred outputPred possibleOutputs)
        possibleOutputs := by
  induction oa using OracleComp.inductionOn <;>
    simp [monad_norm, OracleComp.somePathSatisfies_query_bind, *]

/-- Output-only specialization of [`OracleComp.allPathsSatisfy_bind_iff`]. -/
@[simp]
lemma allOutputsSatisfyWhen_bind_iff (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).allOutputsSatisfyWhen outputPred possibleOutputs ↔
      oa.allOutputsSatisfyWhen
        (fun x => (ob x).allOutputsSatisfyWhen outputPred possibleOutputs)
        possibleOutputs := by
  simp only [allOutputsSatisfyWhen, allPathsSatisfy_bind_iff]

/-- Output-only specialization of [`OracleComp.somePathSatisfies_bind_iff`]. -/
@[simp]
lemma someOutputSatisfiesWhen_bind_iff (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).someOutputSatisfiesWhen outputPred possibleOutputs ↔
      oa.someOutputSatisfiesWhen
        (fun x => (ob x).someOutputSatisfiesWhen outputPred possibleOutputs)
        possibleOutputs := by
  simp only [someOutputSatisfiesWhen, somePathSatisfies_bind_iff]

/-- Output-only bind rule phrased directly in terms of reachable intermediate outputs. -/
lemma allOutputsSatisfyWhen_bind_iff_supportWhen (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).allOutputsSatisfyWhen outputPred possibleOutputs ↔
      ∀ x ∈ oa.supportWhen possibleOutputs,
        (ob x).allOutputsSatisfyWhen outputPred possibleOutputs := by
  rw [OracleComp.allOutputsSatisfyWhen_bind_iff]
  simp [OracleComp.allOutputsSatisfyWhen_iff_supportWhen]

/-- Existential output bind rule phrased directly in terms of reachable intermediate outputs. -/
lemma someOutputSatisfiesWhen_bind_iff_supportWhen (outputPred : β → Prop)
    (possibleOutputs : (x : spec.Domain) → Set (spec.Range x))
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).someOutputSatisfiesWhen outputPred possibleOutputs ↔
      ∃ x ∈ oa.supportWhen possibleOutputs,
        (ob x).someOutputSatisfiesWhen outputPred possibleOutputs := by
  rw [OracleComp.someOutputSatisfiesWhen_bind_iff]
  simp [OracleComp.someOutputSatisfiesWhen_iff_supportWhen]

end OracleComp
