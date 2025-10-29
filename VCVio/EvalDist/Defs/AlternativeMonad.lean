/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Typeclasses for Denotational Semantics With Failure

Additional denotational type-classes for `AlternativeMonad` instances.

-/

open ENNReal

universe u v w

variable {m : Type u → Type v} [AlternativeMonad m] {α β γ : Type u}

section alternative

-- dt: for now I'm trying to stick with mixin type-classes for this type of thing.
-- /-- Extension of `HasEvalSPMF` that are lawful to an `AlternativeMonad` structure. -/
-- class HasAlternativeEvalSPMF (m : Type u → Type v) [AlternativeMonad m]
--     extends HasEvalSPMF m where
--   toSPMF_failure {α : Type u} : toSPMF (failure : m α) = 0

/-- Type-class for `hasEvalSPMF` when given an `AlternativeMonad` instance instead,
enforcing that `failure` maps to the empty sub-distribution. -/
protected class HasEvalSPMF.LawfulFailure (m : Type u → Type v)
    [AlternativeMonad m] [HasEvalSPMF m] : Prop where
  toSPMF_failure {α : Type u} : HasEvalSPMF.toSPMF (failure : m α) = 0

@[simp] lemma evalDist_failure [HasEvalSPMF m] [HasEvalSPMF.LawfulFailure m] :
    evalDist (failure : m α) = 0 := HasEvalSPMF.LawfulFailure.toSPMF_failure

/-- Type-class for `hasEvalSet` when given an `AlternativeMonad` instance instead,
enforcing that `failure` maps to the empty sub-distribution. -/
protected class HasEvalSet.LawfulFailure (m : Type u → Type v)
    [AlternativeMonad m] [HasEvalSet m] : Prop where
  support_failure' {α : Type u} : support (failure : m α) = ∅

@[simp] lemma support_failure [HasEvalSet m] [HasEvalSet.LawfulFailure m] :
    support (failure : m α) = ∅ := HasEvalSet.LawfulFailure.support_failure'

@[simp] lemma finSupport_failure [HasEvalSet m] [HasEvalSet.LawfulFailure m]
    [HasEvalFinset m] [DecidableEq α] : finSupport (failure : m α) = ∅ := by
  simp [finSupport_eq_iff_support_eq_coe]

end alternative
