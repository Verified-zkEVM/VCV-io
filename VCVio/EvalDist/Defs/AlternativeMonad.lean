/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Denotational Semantics Over `AlternativeMonad`.

This file defines a type-class for `HasEvalSet` when given an `AlternativeMonad` instance
on the base monad, enforcing that `failure` maps to the empty sub-distribution.

Compatibility conditions then force the correct semantics for `evalDist`, see _.
-/

open ENNReal HasEvalSet

universe u v w

variable {m : Type u → Type v} [AlternativeMonad m] {α β γ : Type u}

/-- Type-class for `HasEvalSet` when given an `AlternativeMonad` instance on the base monad,
enforcing that `failure` maps to the empty sub-distribution.
Compatibility conditions then force the correct semantics for `evalDist`, see below. -/
protected class HasEvalSet.LawfulFailure (m : Type u → Type v)
    [AlternativeMonad m] [HasEvalSet m] : Prop where
  support_failure' {α : Type u} : support (failure : m α) = ∅

open HasEvalSet (LawfulFailure)

@[simp, grind =]
lemma support_failure [HasEvalSet m] [LawfulFailure m] :
    support (failure : m α) = ∅ :=
  HasEvalSet.LawfulFailure.support_failure'

@[simp, grind =]
lemma finSupport_failure [HasEvalSet m] [LawfulFailure m] [HasEvalFinset m]
    [DecidableEq α] : finSupport (failure : m α) = ∅ := by grind

@[simp, grind =]
lemma probOutput_failure [HasEvalSPMF m] [LawfulFailure m]
    (x : α) : Pr[= x | (failure : m α)] = 0 := by simp only [probOutput_eq_zero_iff,
      support_failure, Set.mem_empty_iff_false, not_false_eq_true]

@[simp, grind =]
lemma probEvent_failure [HasEvalSPMF m] [LawfulFailure m]
    (p : α → Prop) : Pr[p | (failure : m α)] = 0 := by aesop

@[simp, grind =]
lemma probFailure_failure [HasEvalSPMF m] [LawfulFailure m] :
    Pr[⊥ | (failure : m α)] = 1 := by simp

@[simp, grind =]
lemma evalDist_failure [HasEvalSPMF m] [LawfulFailure m] :
    evalDist (failure : m α) = SPMF.mk (PMF.pure none) := by simp
