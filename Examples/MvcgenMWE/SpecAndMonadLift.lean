/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Std.Tactic.Do

/-!
# MWE: `@[spec]` lookup fails through a `MonadLift` coercion

Minimal reproducer for the `mvcgen` spec-lookup issue when an operation
defined in a source monad `M` is used in a target monad `N` via a
`MonadLift M N` coercion.

## What fails

A `@[spec]` lemma registered on the *bare* head constant (`op`) fires
inside `M`, but the elaborator wraps `op` with `MonadLiftT.monadLift`
(= `liftM`) in `N`-contexts, and
`Lean.Elab.Tactic.Do.Spec.findSpec` keys syntactically on the head
constant in a `DiscrTree`, so the `op`-keyed spec never fires.

Empirically (with `lean4:v4.29.0`), **both** the `do`-block form and the
type-ascription form elaborate with head `MonadLiftT.monadLift`, so
*one* extra `@[spec]` keyed on `MonadLiftT.monadLift` is sufficient to
rescue both. A spec keyed only on `MonadLift.monadLift` fires in
*neither*.

`op` is marked `@[irreducible]` so `mvcgen` cannot solve the goal by
evaluating `op` symbolically; it must find a spec to make progress.
-/

open Std.Do

abbrev M : Type → Type := Id

abbrev N : Type → Type := StateT Nat Id

/-- Irreducible so `mvcgen` cannot unfold `op` and must use a `@[spec]`. -/
@[irreducible] def op : M Nat := pure 42

/-! ### Baseline: spec fires inside `M`. -/

@[spec] theorem op_spec :
    ⦃⌜True⌝⦄ (op : M Nat) ⦃⇓ r => ⌜r = 42⌝⦄ := by
  simp [op, Triple]

/-- Works in `M`: `op_spec` is found and closes the goal. -/
example : ⦃⌜True⌝⦄ (do let x ← op; pure x : M Nat) ⦃⇓ r => ⌜r = 42⌝⦄ := by
  mvcgen

/-! ### Case A: `do`-block coercion

The elaborator wraps `op` in `MonadLiftT.monadLift _`.
`mvcgen` cannot find `op_spec` because the head is not `op`. -/

example : ⦃⌜True⌝⦄
    (do let r ← (op : M Nat); pure r : N Nat)
    ⦃⇓ r => ⌜r = 42⌝⦄ := by
  mvcgen
  -- Leaves a stray WP over `MonadLiftT.monadLift op`.
  sorry

/-! ### Case B: Type-ascription coercion

`((op : M Nat) : N Nat)` also elaborates to `MonadLiftT.monadLift op`,
same problem. -/

example : ⦃⌜True⌝⦄ ((op : M Nat) : N Nat) ⦃⇓ r => ⌜r = 42⌝⦄ := by
  mvcgen
  sorry

/-! ### Case C: A spec keyed on `MonadLift.monadLift` does **not** help.

One might expect `MonadLift.monadLift`-keyed spec to fire via Lean's
built-in unfolding, since `MonadLiftT.monadLift = MonadLift.monadLift`
definitionally in the non-transitive case. It doesn't: `findSpec` uses
syntactic matching. -/

@[spec] theorem op_spec_MonadLift :
    ⦃⌜True⌝⦄ (MonadLift.monadLift (op : M Nat) : N Nat) ⦃⇓ r => ⌜r = 42⌝⦄ := by
  sorry

example : ⦃⌜True⌝⦄
    (do let r ← (op : M Nat); pure r : N Nat)
    ⦃⇓ r => ⌜r = 42⌝⦄ := by
  mvcgen  -- still leaves a WP over `MonadLiftT.monadLift op`
  sorry

/-! ### Case D: A spec keyed on `MonadLiftT.monadLift` rescues both A and B.

This is the only workaround we have found: register a second `@[spec]`
(on top of `op_spec`) keyed on `MonadLiftT.monadLift`. It rescues both
the `do`-block form and the ascription form. -/

@[spec] theorem op_spec_MonadLiftT :
    ⦃⌜True⌝⦄ (MonadLiftT.monadLift (op : M Nat) : N Nat) ⦃⇓ r => ⌜r = 42⌝⦄ := by
  sorry

example : ⦃⌜True⌝⦄
    (do let r ← (op : M Nat); pure r : N Nat)
    ⦃⇓ r => ⌜r = 42⌝⦄ := by
  mvcgen  -- closes the goal via `op_spec_MonadLiftT`

example : ⦃⌜True⌝⦄ ((op : M Nat) : N Nat) ⦃⇓ r => ⌜r = 42⌝⦄ := by
  mvcgen  -- closes the goal via `op_spec_MonadLiftT`

/-! ## Asks

1. Is there a single-`@[spec]` recipe that works in both coercion
   positions without having to forward to a `MonadLiftT.monadLift`-keyed
   restatement?

2. Would it be possible for
   `Lean.Elab.Tactic.Do.Attr.mkSpecTheorem` (on registration) and
   `Lean.Elab.Tactic.Do.Spec.findSpec` (on lookup) to canonicalise
   `MonadLiftT.monadLift` / `liftM` / `MonadLift.monadLift` chains
   (e.g. by simplifying with
   `Std.Do.WP.monadLift_trans` / `monadLift_refl`) before computing the
   `DiscrTree` key? That would make one `@[spec]` keyed on the raw `op`
   suffice, matching user expectations.
-/
