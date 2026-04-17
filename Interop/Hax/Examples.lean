/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Interop.Hax.Bridge

/-!
# Small end-to-end examples of the hax → VCVio bridge

A tiny `RustM`-style Rust function, lifted into `RustOracleComp`, plus
a one-oracle-query composition. The goal is a sanity check: the four
`@[simp]` boundary lemmas in `Interop.Hax.Bridge`
(`liftRustM_{ok,fail,div,pure}`) should be enough for `simp` to collapse
concrete lifted Rust programs to pure `RustOracleComp` terms, and the
composed `WP` shape from `Std.Do`'s `ExceptT.instWP` / `OptionT.instWP`
over `WP (OracleComp spec) .pure` should be what the user expects.
-/

open Std.Do OracleSpec OracleComp

namespace Interop.Hax.Examples

variable {ι : Type} {spec : OracleSpec ι}

/-! ### Source: hax-style `RustM` program

`addOrPanic x y` mimics a Rust function that adds two `Nat`s and panics
(`Error.integerOverflow`) if the result would exceed `UInt32.MAX`. The
shape `RustM α := ExceptT Error Option α` is exactly what hax emits for
an arithmetic operation with a panic path. -/

/-- Checked addition: returns `x + y` when it fits in 32 bits, otherwise
panics with `Error.integerOverflow`. No divergence path. -/
def addOrPanic (x y : Nat) : RustM Nat :=
  if x + y < 2 ^ 32 then pure (x + y) else RustM.fail .integerOverflow

/-! ### Lift into the oracle-aware target

`MonadLift RustM (RustOracleComp spec)` from `Interop.Hax.Bridge` kicks
in automatically, so `liftRustM` here is purely for elaboration
stability: we want `mvcgen` / `simp` to see the lift explicitly. -/

/-- Oracle-aware version of `addOrPanic`. The `spec` parameter is the
ambient `OracleSpec`; this particular computation does not issue any
oracle query, but the ambient monad now admits oracle queries composed
with it via `bind`. -/
def addOrPanicLifted (x y : Nat) : Interop.Rust.RustOracleComp spec Nat :=
  liftRustM (addOrPanic x y)

/-! ### Equality-level specs

For concrete outcomes the `@[simp]` boundary lemmas in `Bridge.lean`
reduce the lift to a `RustOracleComp` constructor, and the `if` splits
cleanly. These are the kinds of subgoals `mvcgen` reduces to once it
has peeled the transformer stack. -/

/-- When the sum fits, the lifted computation reduces to `ok (x + y)`. -/
theorem addOrPanicLifted_ok_of_lt (x y : Nat) (h : x + y < 2 ^ 32) :
    (addOrPanicLifted (spec := spec) x y) =
      Interop.Rust.RustOracleComp.ok (x + y) := by
  unfold addOrPanicLifted addOrPanic
  rw [if_pos h]
  rfl

/-- When the sum overflows, the lifted computation reduces to
`fail integerOverflow`, with the error rebranded through `errorOfHax`.
The trivial rebrand sends `Error.integerOverflow ↦
Interop.Rust.Error.integerOverflow`. -/
theorem addOrPanicLifted_fail_of_ge (x y : Nat) (h : ¬ x + y < 2 ^ 32) :
    (addOrPanicLifted (spec := spec) x y) =
      Interop.Rust.RustOracleComp.fail .integerOverflow := by
  unfold addOrPanicLifted addOrPanic
  rw [if_neg h]
  rfl

/-! ### Triple-level spec via `mvcgen`

Demonstrates the bridge in the intended Hoare-logic usage. When the
precondition `x + y < 2^32` holds, the lifted computation terminates
with value `x + y` and never panics or diverges.

This exercises the composed `Std.Do` WP stack: `ExceptT.instWP`
composes `OptionT.instWP` composes VCVio's `instWPOracleComp` in
`StdDoBridge.lean` (all three layers). `mvcgen` peels the transformer
stack and leaves a single arithmetic vc about the `if`; we introduce
the precondition, rewrite the `if` via `if_pos`, and let `simp` (using
our `@[simp]` `liftRustM_pure` lemma) close the resulting
`wp⟦pure _⟧`-goal.

The numeric-form rebinding `have h' : x + y < 4294967296 := h` is a
one-liner workaround for the fact that `mvcgen`/`simp` normalises
`2^32` to the decimal form `4294967296` inside the vc while leaving
the hypothesis at `2^32`; the two are definitionally equal in `Nat`.

VCVio's `WP (OracleComp spec) .pure` (in
`VCVio.ProgramLogic.Unary.StdDoBridge`) requires `[spec.Fintype]` and
`[spec.Inhabited]` for probability reasoning, so the Triple spec
carries those constraints. -/

section TripleSpec

set_option mvcgen.warning false

variable [spec.Fintype] [spec.Inhabited]

/-- `addOrPanicLifted` total-correctness spec. Under the no-overflow
precondition, the lifted hax computation never panics, never diverges,
and returns `x + y`. -/
theorem addOrPanicLifted_triple (x y : Nat) :
    ⦃⌜x + y < 2 ^ 32⌝⦄
    (addOrPanicLifted (spec := spec) x y)
    ⦃⇓ r => ⌜r = x + y⌝⦄ := by
  mvcgen [addOrPanicLifted, addOrPanic]
  intro h
  have h' : x + y < 4294967296 := h
  rw [if_pos h']
  simp [liftRustM_pure]

end TripleSpec

/-! ### Composition with an oracle query

The whole point of the lift is that `RustOracleComp spec` admits `bind`
with a genuine oracle query on the `OracleComp spec` layer, which
`RustM` cannot. Lean derives `MonadLiftT (OracleComp spec)
(RustOracleComp spec)` automatically by chaining
`MonadLift (OracleComp spec) (OptionT (OracleComp spec))` with
`MonadLift (OptionT ..) (ExceptT .. (OptionT ..))`; this keeps `mvcgen`
compositional (each layer is covered by a standard `@[spec]` rule). -/

/-- Query a uniform oracle for a value, convert it to `Nat`, then run
`addOrPanic` on it. Models a hybrid harness where the input to a
hax-generated function comes from randomness rather than a literal.

The do-block binds in `RustOracleComp spec`; the oracle query is
lifted via the derived `MonadLiftT (OracleComp spec)
(RustOracleComp spec)` chain, and the `liftRustM` call in the tail is
the hax bridge. -/
def oracleThenAdd (x : Nat) (t : ι) (coe : spec.Range t → Nat) :
    Interop.Rust.RustOracleComp spec Nat := do
  let y ← (liftM (query t) : OracleComp spec _)
  liftRustM (addOrPanic x (coe y))

/-! ### Triple-level spec on the oracle-composed program

The "genuine" boundary example: a `RustOracleComp`-shaped `Triple` on a
program that both queries an oracle and invokes a hax-style `RustM`
function. Under a universal no-overflow hypothesis on the oracle
response, the composed program always returns a value ≥ `x`. The proof
uses `mvcgen` to peel the transformer stack, the support-level
`wpProp` bridge for the single oracle query, and the equality-level
`addOrPanicLifted_ok_of_lt` to close the `liftRustM` tail. -/

section OracleTripleSpec

set_option mvcgen.warning false

variable [spec.Fintype] [spec.Inhabited]

/-- If the oracle's response can never push `x + coe y` above `2^32`,
then `oracleThenAdd` always returns a value `≥ x`. The interesting part
is that the precondition mentions the oracle response `y`, which is
universally quantified at the spec level because a well-typed spec on
`RustOracleComp spec` must hold for any oracle outcome. -/
theorem oracleThenAdd_triple (x : Nat) (t : ι) (coe : spec.Range t → Nat)
    (hbound : ∀ y : spec.Range t, x + coe y < 2 ^ 32) :
    ⦃⌜True⌝⦄
    (oracleThenAdd (spec := spec) x t coe)
    ⦃⇓ r => ⌜x ≤ r⌝⦄ := by
  mvcgen [oracleThenAdd, addOrPanic]
  rw [OracleComp.ProgramLogic.StdDo.wpProp_iff_forall_support]
  intro y _
  have hy : x + coe y < 4294967296 := hbound y
  rw [if_pos hy]
  simp only [liftRustM_pure, WPMonad.wp_pure, PostCond.noThrow]
  exact Nat.le_add_right x (coe y)

end OracleTripleSpec

end Interop.Hax.Examples
