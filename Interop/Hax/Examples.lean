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
`RustM` cannot. The `MonadLift (OracleComp spec) (RustOracleComp spec)`
instance from `Interop.Rust.Common` turns a single `query` into a
lifted `RustOracleComp` step, and the hax lift composes with it. -/

/-- Query a uniform oracle for a value, convert it to `Nat`, then run
`addOrPanic` on it. Models a hybrid harness where the input to a
hax-generated function comes from randomness rather than a literal.

The do-block binds in `RustOracleComp spec`; the oracle query is
lifted via `MonadLift (OracleQuery spec) (OracleComp spec)` composed
with `MonadLift (OracleComp spec) (RustOracleComp spec)`, and the
`liftRustM` call in the tail is the hax bridge. -/
def oracleThenAdd (x : Nat) (t : ι) (coe : spec.Range t → Nat) :
    Interop.Rust.RustOracleComp spec Nat := do
  let y ← (liftM (query t) : OracleComp spec _)
  liftRustM (addOrPanic x (coe y))

end Interop.Hax.Examples
