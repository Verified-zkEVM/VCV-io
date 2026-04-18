/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Interop.Hax.Bridge
import Hax.rust_primitives.Cast
import Hax.rust_primitives.BVDecide
import Hax.Tactic

/-!
# End-to-end hax example: 32-bit addition with carry (`adc_u32`)

Reproduces hax's flagship `lean_adc` demo inside the `Interop` bridge.
Where `Computation.lean` closes its vc with plain `mvcgen` plus `omega`
and `Division.lean` does the same with `UInt32.haxDiv_spec`, this file
stresses the bigger-gun workflow:

* `hax_mvcgen` — the hax-customized `mvcgen` that indexes `@[specset bv]`
  annotations so all the bit-level specs for casts, shifts, and `u64`
  arithmetic are in scope automatically, and
* `bv_decide` — Lean's bit-blasting decision procedure, which discharges
  the residual `u32`/`u64` bitvector vcs without any user-supplied
  arithmetic reasoning.

Once the `RustM`-level spec is closed by `hax_mvcgen [...] <;> bv_decide`,
it is transported to `RustOracleComp` by a single application of
`triple_liftRustM` from `Interop.Hax.Bridge`, identically to
`Computation.lean` and `Division.lean`.

## Provenance

The Rust source lives in hax's test suite at
`examples/lean_adc/src/lib.rs`:

```rust
pub fn adc_u32(a: u32, b: u32, carry_in: u32) -> (u32, u32) {
    let wide: u64 = a as u64 + b as u64 + carry_in as u64;
    let sum: u32 = wide as u32;
    let carry_out: u32 = (wide >> 32u64) as u32;
    (sum, carry_out)
}
```

The Rust source also embeds, via `#[hax_lib::lean::after(...)]`, the
very Hoare triple we reproduce below. That triple is hax's own canonical
statement of ADC correctness; we copy it verbatim, substitute the
transport lemma on the oracle-lifted side, and keep the hax-side tactic
(`hax_mvcgen [..] <;> bv_decide`) unchanged.
-/

open Std.Do OracleSpec OracleComp

namespace Interop.Hax.Examples.Adc

variable {ι : Type} {spec : OracleSpec ι}

/-- Hax-style emission of `adc_u32`: widen the three `u32` inputs to `u64`
via `rust_primitives.hax.cast_op`, add them with the checked `+?`, then
cast the low 32 bits as `sum` and the high 32 bits as `carry_out`.

This is a hand-written reconstruction following the pattern used by hax
in `test-harness/src/snapshots/toolchain__literals into-lean.snap`
(see e.g. the `casts` function there). The real hax CLI would emit an
equivalent do-block for the Rust source in the module docstring. -/
@[spec]
def adc_u32 (a b carry_in : u32) : RustM (u32 × u32) := do
  let wide : u64 ←
    ((← ((← (rust_primitives.hax.cast_op a : RustM u64))
          +? (← (rust_primitives.hax.cast_op b : RustM u64))))
      +? (← (rust_primitives.hax.cast_op carry_in : RustM u64)))
  let sum : u32 ← (rust_primitives.hax.cast_op wide : RustM u32)
  let shifted : u64 ← wide >>>? (32 : u64)
  let carry_out : u32 ← (rust_primitives.hax.cast_op shifted : RustM u32)
  pure (sum, carry_out)

-- `RustM`-level spec for `adc_u32`: under the single-bit carry
-- precondition `carry_in ≤ 1`, the output `(sum, carry_out)` satisfies
-- `carry_out ≤ 1` and the canonical full-sum equation
-- `a64 + b64 + carry_in64 = sum64 + (carry_out64 <<< 32)` over `u64`.
-- Proof is a direct port of the hax `#[hax_lib::lean::after(...)]`
-- embedded theorem: `hax_mvcgen` peels the `RustM` do-block into a pure
-- BitVec vc using the `bv` specset, and `bv_decide` closes the
-- resulting 32-bit and 64-bit arithmetic goal.
set_option maxHeartbeats 1000000 in
-- `bv_decide` over the full 64-bit ADC equation is the heaviest proof
-- in the bridge; mirrors hax's own `lean_adc` example which also bumps
-- the heartbeats limit.
set_option mvcgen.warning false in
set_option hax_mvcgen.specset "bv" in
theorem adc_u32_spec (a b carry_in : u32) :
    ⦃⌜carry_in ≤ 1⌝⦄
    adc_u32 a b carry_in
    ⦃⇓ ⟨sum, carry_out⟩ =>
      ⌜carry_out ≤ 1 ∧
        UInt32.toUInt64 a + UInt32.toUInt64 b + UInt32.toUInt64 carry_in =
          UInt32.toUInt64 sum + (UInt32.toUInt64 carry_out <<< (32 : UInt64))⌝⦄ := by
  hax_mvcgen [adc_u32]
    <;> bv_decide (timeout := 90)

/-- Oracle-aware version of `adc_u32`: just the bridge lift of the
hax-emitted function. -/
def adc_u32_Lifted (a b carry_in : u32) : Interop.Rust.RustOracleComp spec (u32 × u32) :=
  liftRustM (adc_u32 a b carry_in)

/-- Oracle-lifted ADC spec, obtained by a single application of
`triple_liftRustM` on the hax-side `adc_u32_spec`. This is the big
demonstration of the bridge: after the hax-side proof is closed by the
heavyweight `hax_mvcgen <;> bv_decide` combination, transport to
`RustOracleComp` is one line of Lean — no extra tactic machinery, no
repeated `bv_decide`, no knowledge of the postcondition shape beyond
what `triple_liftRustM` asks for. -/
theorem adc_u32_Lifted_spec [spec.Fintype] [spec.Inhabited]
    (a b carry_in : u32) :
    ⦃⌜carry_in ≤ 1⌝⦄
    (adc_u32_Lifted (spec := spec) a b carry_in)
    ⦃⇓ ⟨sum, carry_out⟩ =>
      ⌜carry_out ≤ 1 ∧
        UInt32.toUInt64 a + UInt32.toUInt64 b + UInt32.toUInt64 carry_in =
          UInt32.toUInt64 sum + (UInt32.toUInt64 carry_out <<< (32 : UInt64))⌝⦄ := by
  unfold adc_u32_Lifted
  exact triple_liftRustM _ (adc_u32_spec a b carry_in)

end Interop.Hax.Examples.Adc
