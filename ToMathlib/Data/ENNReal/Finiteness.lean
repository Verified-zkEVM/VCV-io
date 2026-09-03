/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.Tactic.Finiteness

/-!
# `finiteness` rules for finite sums

Mathlib registers `finiteness` rules for `+`, `*`, `-`, `⁻¹`, `/`, powers, and casts on
`ℝ≥0∞`, but not for `Finset.sum`. This module adds the sum rule, so that `finiteness` closes
`∑ a ∈ s, f a ≠ ∞` whenever it closes each summand; the `∀ a ∈ s` binder is introduced by the
rule set's `intros` rule.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- `finiteness` extension: a finite sum of `ℝ≥0∞`-valued terms is finite when every term is. -/
@[aesop (rule_sets := [finiteness]) safe apply]
protected theorem Finiteness.sum_ne_top {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞}
    (h : ∀ a ∈ s, f a ≠ ∞) : ∑ a ∈ s, f a ≠ ∞ :=
  ENNReal.sum_ne_top.2 h

end ENNReal
