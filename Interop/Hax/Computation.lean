/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import Interop.Hax.Bridge
import Hax.rust_primitives.ops

/-!
# End-to-end hax example: `const fn computation(x: u32) -> u32`

This file takes a real hax-generated Lean function, proves a Hoare
triple for it on the `RustM` side, and transports the spec across the
bridge to `RustOracleComp`. It is the first example where the Rust
side is not a hand-crafted toy but actual hax output.

## Provenance

The Rust source lives in hax's test suite at
`tests/lean-tests/src/constants.rs`:

```rust
const fn computation(x: u32) -> u32 {
    x + x + 1
}
```

hax emits this (unchanged) as the following Lean definition; see
`test-harness/src/snapshots/toolchain__lean-tests into-lean.snap`,
which is hax's CI-checked reference output:

```lean
@[spec]
def computation (x : u32) : RustM u32 := do ((← (x +? x)) +? (1 : u32))
```

We reproduce the emitted definition verbatim below (the only cosmetic
change is the enclosing namespace).

## What this demonstrates

- The `RustM`-level Triple `computation_triple` is proved with hax's
  own `UInt32.haxAdd_spec` as the only side lemma. No hax tactics
  (`hax_mvcgen`, `bv_decide`) are needed for this function; plain
  `mvcgen` leaves three subgoals that close by `simp` with
  `UInt32.addOverflow_iff` plus `omega`.
- The oracle-lifted Triple `computationLifted_triple` is obtained by a
  single application of `triple_liftRustM` from `Interop.Hax.Bridge`.
  This is the intended end-to-end pattern: prove once on the hax side
  against hax's spec library, then transport to `RustOracleComp` for
  free.
-/

open Std.Do OracleSpec OracleComp

namespace Interop.Hax.Examples.Computation

set_option mvcgen.warning false

variable {ι : Type} {spec : OracleSpec ι}

/-- Hax-emitted Lean code for the Rust function

```rust
const fn computation(x: u32) -> u32 { x + x + 1 }
```

Reproduced verbatim from hax's `lean-tests` snapshot (only the
namespace qualification is different). `+?` is hax's checked-addition
operator on Rust integers; it returns `.fail .integerOverflow` when
the wraparound bit is set. -/
@[spec]
def computation (x : u32) : RustM u32 := do ((← (x +? x)) +? (1 : u32))

/-- `RustM`-level Triple for `computation`. Under the no-overflow
precondition `2 * x.toNat + 1 < 2^32`, the function returns
`2 * x.toNat + 1` in `Nat` representation.

Both internal additions are discharged by hax's own
`UInt32.haxAdd_spec` (registered with `@[specset int]`; we pass it
explicitly because we are not using `hax_mvcgen`). The side conditions
`¬ UInt32.addOverflow ..` reduce to `Nat` inequalities via
`UInt32.addOverflow_iff` and close by `omega`. -/
theorem computation_triple (x : u32) :
    ⦃⌜2 * x.toNat + 1 < 2 ^ 32⌝⦄
    (computation x)
    ⦃⇓ r => ⌜r.toNat = 2 * x.toNat + 1⌝⦄ := by
  -- `omega` cannot definitionally reduce `UInt32.toNat 1` to `1`;
  -- pulling it out as a visible hypothesis unlocks the arithmetic.
  have h1 : UInt32.toNat 1 = 1 := rfl
  mvcgen [computation, UInt32.haxAdd_spec]
  · -- vc1.h: first `+?` does not overflow: ¬ UInt32.addOverflow x x
    simp [UInt32.addOverflow_iff]; omega
  · -- vc2.success.success: both adds succeeded, postcondition holds
    intros; omega
  · -- vc3: second `+?` does not overflow: ¬ (x + x).addOverflow 1
    intros; simp [UInt32.addOverflow_iff]; omega

/-- Oracle-aware version of `computation`: just the bridge lift of
the hax-emitted function. Models what happens when a hax-extracted
helper needs to live inside a larger oracle-using protocol. -/
def computationLifted (x : u32) : Interop.Rust.RustOracleComp spec u32 :=
  liftRustM (computation x)

/-- Oracle-lifted Triple, obtained in one step from `computation_triple`
via the bridge's compositional boundary lemma `triple_liftRustM`.

The postcondition shape on the `RustOracleComp` side matches the hax
side exactly; the `errorOfHax` rebrand inside `triple_liftRustM` is
invisible because the precondition rules out the `fail` branch and
the success component of the postcondition does not mention errors. -/
theorem computationLifted_triple [spec.Fintype] [spec.Inhabited] (x : u32) :
    ⦃⌜2 * x.toNat + 1 < 2 ^ 32⌝⦄
    (computationLifted (spec := spec) x)
    ⦃⇓ r => ⌜r.toNat = 2 * x.toNat + 1⌝⦄ := by
  unfold computationLifted
  exact triple_liftRustM _ (computation_triple x)

end Interop.Hax.Examples.Computation
