/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.HasFinEvalDist


/-!
# Computations that Never Fail

This file contains a type-class for computations `mx` in a monad `m` that never fail,
in the sense that `probFailure mx = 0`. Equivalently the sum of `probOutput` is `1`
and the corresponding `SPMF` is actually a `PMF`.

Typeclass inference is not very expensive because there is usually a unique syntax match.
-/

namespace HasEvalDist

variable {α β γ : Type _} {m : Type _ → Type _} [Monad m] [HasEvalDist m]

/-- `neverFails mx` means that `mx` will also return a (probabalistic) value. -/
class neverFails {α : Type _} {m : Type _ → Type _} [Monad m]
    [HasEvalDist m] (mx : m α) : Prop where
  mk :: probFailure_eq_zero : Pr[⊥ | mx] = 0

export neverFails (probFailure_eq_zero)

@[simp] instance neverFails_pure {x} : neverFails (pure x : m α) where
  probFailure_eq_zero := sorry

lemma neverFails_bind {mx : m α} {my : α → m β}
    (hx : neverFails mx) (hy : ∀ x, neverFails (my x)) : neverFails (mx >>= my) := by
  sorry

lemma neverFails_map [LawfulMonad m] {mx : m α}
    (h : neverFails mx) (f : α → β) : neverFails (f <$> mx) := by
  simp [map_eq_bind_pure_comp]
  apply neverFails_bind
  · assumption
  · simp

end HasEvalDist
