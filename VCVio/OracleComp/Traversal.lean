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

end OracleComp
