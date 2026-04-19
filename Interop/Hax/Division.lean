/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Interop.Hax.Bridge
import Interop.Rust.Run
import Hax.rust_primitives.ops
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.Instances.ErrorT
import VCVio.EvalDist.Instances.OptionT
import VCVio.EvalDist.Fintype

/-!
# End-to-end hax example exercising `divisionByZero`

A second hax-style `RustM` example that complements `Computation.lean`.
Where `Computation.lean` only exercises the `.integerOverflow` branch of
`errorOfHax` (and only indirectly, via a no-overflow precondition), this
file exercises `.divisionByZero` directly at both the Hoare-logic and
equality levels.

## What this file covers

* `checkedDiv x y` — hax-style checked division: `x /? y` on `u32`,
  which panics with `.divisionByZero` when `y = 0`.
* `checkedDiv_triple` (RustM level) — total-correctness Triple using
  hax's own `UInt32.haxDiv_spec` under the `y ≠ 0` precondition.
* `checkedDivLifted_triple` — oracle-lifted Triple, obtained by
  `triple_liftRustM` from `Bridge.lean`. Exercises the transport lemma
  end-to-end on a function whose panic branch is division-by-zero
  rather than overflow.
* `checkedDivLifted_fail_of_zero` — equality-level check: when `y = 0`
  the lifted computation reduces to `fail .divisionByZero`, which is
  where `errorOfHax` actually moves the error constructor through the
  bridge (as opposed to the Triple case where the precondition rules
  the branch out).

## Why a separate file

Keeping this example separate from `Computation.lean` has two benefits:

* it isolates the `.divisionByZero` witness so a future error-enum
  refactor has an obvious regression target, and
* the proofs are ~identical in structure to `Computation.lean`, so the
  diff highlights what changes (the error constructor, the `haxDiv_spec`
  side condition) while keeping everything else constant.
-/

open Std.Do OracleSpec OracleComp

namespace Interop.Hax.Examples.Division

set_option mvcgen.warning false

variable {ι : Type} {spec : OracleSpec ι}

/-- Hax-style checked division on `u32`: `x /? y` reduces to
`if y = 0 then .fail .divisionByZero else pure (x / y)` by the
`rust_primitives.ops.arith.Div` instance shipped in
`Hax.rust_primitives.ops`. We wrap it in a top-level definition to give
it a name `mvcgen` can drive. -/
@[spec]
def checkedDiv (x y : u32) : RustM u32 := x /? y

/-- `RustM`-level Triple for `checkedDiv`. Under the non-zero precondition
`y ≠ 0`, the function returns `x.toNat / y.toNat`. Proof is a one-liner:
unfold `checkedDiv`, drive `mvcgen` with the `Div` instance, and close
the single vc by `UInt32.haxDiv_spec`. -/
theorem checkedDiv_triple (x y : u32) (h : y ≠ 0) :
    ⦃⌜True⌝⦄
    (checkedDiv x y)
    ⦃⇓ r => ⌜r.toNat = x.toNat / y.toNat⌝⦄ := by
  unfold checkedDiv
  exact UInt32.haxDiv_spec x y h

/-- Oracle-aware version of `checkedDiv`: just the bridge lift. Same
shape as `computationLifted` in `Computation.lean`, only the panic
branch differs. -/
def checkedDivLifted (x y : u32) : Interop.Rust.RustOracleComp spec u32 :=
  liftRustM (checkedDiv x y)

/-- Oracle-lifted Triple for division. Obtained in one step from
`checkedDiv_triple` via `triple_liftRustM`, with the `y ≠ 0`
precondition preserved. The `errorOfHax` rebrand inside
`triple_liftRustM` is again invisible at the Triple level because the
precondition rules out the panic branch; the equality-level lemma
below is the one that actually witnesses the rebrand. -/
theorem checkedDivLifted_triple [spec.Fintype] [spec.Inhabited]
    (x y : u32) (h : y ≠ 0) :
    ⦃⌜True⌝⦄
    (checkedDivLifted (spec := spec) x y)
    ⦃⇓ r => ⌜r.toNat = x.toNat / y.toNat⌝⦄ := by
  unfold checkedDivLifted
  exact triple_liftRustM _ (checkedDiv_triple x y h)

/-! ### Equality-level panic witnesses

Separate from the Triple specs above, we also record the two
equality-level outcomes of `checkedDivLifted` so that the
`errorOfHax` rebrand is exercised concretely:

* `checkedDivLifted_ok_of_ne_zero`: when `y ≠ 0`, the lifted
  computation reduces to `ok (x / y)`.
* `checkedDivLifted_fail_of_zero`: when `y = 0`, it reduces to
  `fail .divisionByZero` — this is the only place where the bridge's
  `errorOfHax .divisionByZero = .divisionByZero` rebrand actually
  fires, because the `RustM` tail is `RustM.fail .divisionByZero` by
  reduction of the `Div` instance.
-/

/-- When the divisor is nonzero, the lifted computation reduces to
`ok (x / y)` via `liftRustM_pure` on the `pure (x / y)` branch of the
`Div` instance. -/
theorem checkedDivLifted_ok_of_ne_zero (x y : u32) (h : y ≠ 0) :
    (checkedDivLifted (spec := spec) x y) =
      Interop.Rust.RustOracleComp.ok (x / y) := by
  unfold checkedDivLifted checkedDiv
  change liftRustM (if y = 0 then .fail .divisionByZero else pure (x / y)) = _
  rw [if_neg h]
  rfl

/-- When the divisor is zero, the lifted computation reduces to
`fail .divisionByZero`, i.e. the rebranded hax error constructor
coming out of `errorOfHax`. This is the concrete witness that the
bridge's error translation preserves the `divisionByZero`
constructor, complementing `Computation.lean` which only witnesses
`integerOverflow` indirectly. -/
theorem checkedDivLifted_fail_of_zero (x : u32) :
    (checkedDivLifted (spec := spec) x 0) =
      Interop.Rust.RustOracleComp.fail .divisionByZero := by
  unfold checkedDivLifted checkedDiv
  change liftRustM (if (0 : u32) = 0 then .fail .divisionByZero else pure (x / 0)) = _
  rw [if_pos rfl]
  rfl

/-! ### Probabilistic spec: panic probability over a uniform coin

Pulling everything together: `randomDiv x` flips a uniform bit `b ∈ Fin 2`
and either calls `checkedDivLifted x 0` (guaranteed division-by-zero
panic) or returns `x` deterministically. The panic probability is
exactly `1/2`, witnessed on the `.divisionByZero` error constructor.

This mirrors `tossedAdd_panic_prob` in `Examples.lean` but on a
different error constructor, so the probabilistic story is now tested
on at least two of the seven `Interop.Rust.Error` enum variants. -/

/-- Probabilistic harness: flip a uniform bit, run the division-by-zero
panic path on `b = 0` and return `x` on `b = 1`. -/
def randomDiv (x : u32) : Interop.Rust.RustOracleComp unifSpec u32 := do
  let b ← ($[0..1] : ProbComp (Fin 2))
  if b = 0 then checkedDivLifted x 0
  else pure x

/-- `.run.run` peel for `randomDiv`: after running the transformer
stack, we land at the canonical `OracleComp (Option (Except ε α))`
form. Proved in a single `simp only` using the reusable peel lemmas
from `Interop.Rust.Run`. -/
theorem randomDiv_run_run (x : u32) :
    (randomDiv x).run.run =
      ($[0..1] >>= fun b : Fin 2 =>
        pure (some (if b = 0 then
          (Except.error Interop.Rust.Error.divisionByZero : Except Interop.Rust.Error u32)
          else Except.ok x)) :
            OracleComp unifSpec (Option (Except Interop.Rust.Error u32))) := by
  unfold randomDiv
  simp only [checkedDivLifted_fail_of_zero,
    Interop.Rust.RustOracleComp.run_run_bind_liftM,
    apply_ite (f := fun x : Interop.Rust.RustOracleComp unifSpec u32 => x.run.run),
    Interop.Rust.RustOracleComp.run_run_fail,
    Interop.Rust.RustOracleComp.run_run_pure,
    apply_ite (pure (f := OracleComp unifSpec)), apply_ite some]

/-- Panic probability of `randomDiv` is exactly `1/2`: the sole panic
branch is triggered by the uniform draw `b = 0`, and it panics with
`.divisionByZero`, the rebranded hax error constructor. -/
theorem randomDiv_panic_prob (x : u32) :
    Pr[= some (Except.error Interop.Rust.Error.divisionByZero) |
        (randomDiv x).run.run] = 2⁻¹ := by
  rw [randomDiv_run_run, HasEvalSPMF.probOutput_bind_eq_sum_fintype]
  -- ∑ b : Fin 2, Pr[= b | $[0..1]] * Pr[= some (.error .divisionByZero) | pure _].
  -- Each factor of `Pr[= · | $[0..1]]` is `(1 + 1)⁻¹`; only `b = 0` gives a
  -- nonzero second factor (coefficient `1`), so the sum is `(1 + 1)⁻¹ = 2⁻¹`.
  simp [ProbComp.probOutput_uniformFin]
  norm_num

end Interop.Hax.Examples.Division
