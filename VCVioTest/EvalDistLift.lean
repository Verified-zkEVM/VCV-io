/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio
import VCVio.OracleComp.FinRatPMF

/-!
# Regression tests for the canonical `MonadLiftT _ SetM` lift path

These tests pin the canonical synthesis route from each monad with probabilistic
semantics to `SetM`, so that `support` on a `simulateQ`-result agrees with
`support` on its source `OracleComp` without any user-side `letI`/`Fintype`
plumbing in the proof body.

History: an earlier draft of the `evalDist`-as-`MonadLiftT` refactor left four
`sorry`s on lemmas of the form `support (simulateQ … oa) = support oa`, under
the (incorrect) belief that two `MonadLiftT (OracleComp spec) SetM` paths
existed. There is in fact only one direct path; the `MonadLiftT SPMF SetM`
instance is declared as `MonadLiftT` (not `MonadLift`), so Lean's
`monadLiftTrans` cannot chain through it. Each test below closes by
`inferInstance` or `simp` alone, which fails loudly if a future refactor
re-introduces the diamond.
-/

open OracleComp FinRatPMF

namespace EvalDistLiftTest

/-! ## Instance-resolution smoke tests

If these `inferInstance` calls regress, instance synthesis for the canonical
`MonadLiftT _ SetM` path has broken. -/

example : MonadLiftT (OracleComp coinSpec) SetM := inferInstance
example : MonadLiftT (OracleComp unifSpec) SetM := inferInstance
noncomputable example : MonadLiftT (OracleComp unifSpec) SPMF := inferInstance
noncomputable example : MonadLiftT (OracleComp coinSpec) SPMF := inferInstance
noncomputable example : EvalDistCompatible (OracleComp unifSpec) := inferInstance
noncomputable example : EvalDistCompatible (OracleComp coinSpec) := inferInstance

/-- `MonadLiftT FinRatPMF.Raw SetM` resolves to the direct instance, not via
the (non-transitive) `MonadLiftT SPMF SetM`. -/
noncomputable example : MonadLiftT FinRatPMF.Raw SetM := inferInstance
noncomputable example : EvalDistCompatible FinRatPMF.Raw := inferInstance

/-! ## `support_simulateQ` regression locks

These exercise the four formerly-`sorry`d lemmas. A future change that breaks
the canonical bridge (`EvalDistCompatible (OracleComp spec).support_eq_SPMF_support`
plus `evalDist_simulateQ`) would surface here. -/

example (oa : OracleComp coinSpec Bool) :
    support (simulateQ (finRatImpl (spec := coinSpec)) oa) = support oa := by
  simp

section ParamSpec

variable {ι : Type} {spec : OracleSpec ι}
    [spec.Inhabited] [∀ t : spec.Domain, FinEnum (spec.Range t)]

example {α : Type} (oa : OracleComp spec α) :
    support (simulateQ (finRatImpl (spec := spec)) oa) = support oa := by
  simp

example {α : Type} [DecidableEq α] (oa : OracleComp spec α) :
    finSupport (simulateQ (finRatImpl (spec := spec)) oa) = finSupport oa :=
  finRatImpl.finSupport_simulateQ oa

end ParamSpec

/-! ## `support_replicate` regression lock

The shape `support (replicate n oa) = {xs | length-and-elementwise predicate}`
held a `sorry` for the same reason; the lemma is now proved by induction. -/

example {α : Type} (n : ℕ) (oa : OracleComp coinSpec α) :
    support (oa.replicate n) = {xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} := by
  simp

end EvalDistLiftTest
