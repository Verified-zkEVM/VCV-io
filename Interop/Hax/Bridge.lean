/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Hax.rust_primitives.RustM
import Interop.Rust.Common

/-!
# Bridge from `Hax.RustM` to `Interop.Rust.RustOracleComp`

Connects hax's Rust target monad (`RustM α := ExceptT Error Option α`, with
root-level `Error`) to VCVio's oracle-aware version
(`RustOracleComp spec α := ExceptT Interop.Rust.Error (OptionT (OracleComp spec)) α`).

Layer by layer the two monads differ only in that hax's innermost `Option` is
replaced by `OptionT (OracleComp spec)`; the `Error` types are nominally
distinct (one at `_root_`, one in `Interop.Rust`) but constructor-by-
constructor identical, so `errorOfHax` performs a trivial rebrand at the
boundary.

The Hoare-logic shape is preserved structurally: hax declares
`WP RustM (.except Error (.except PUnit .pure))` by `inferInstanceAs`, and
`Std.Do`'s `ExceptT.instWP` / `OptionT.instWP` compose VCVio's
`WP (OracleComp spec) .pure` (from `VCVio.ProgramLogic.Unary.StdDoBridge`) into
`WP (RustOracleComp spec) (.except Interop.Rust.Error (.except PUnit .pure))`.
The `WP` shapes match modulo the `Error` rebrand, which is why no bespoke
transformer lemmas are needed in this module.
-/

open Std.Do

namespace Interop.Hax

/-- Constructor-by-constructor rebrand from hax's root-level `_root_.Error` to
the mirrored `Interop.Rust.Error`. This is the only `Error`-level translation
the bridge needs; once applied, the inner layers line up definitionally. -/
def errorOfHax : _root_.Error → Interop.Rust.Error
  | .assertionFailure   => .assertionFailure
  | .integerOverflow    => .integerOverflow
  | .divisionByZero     => .divisionByZero
  | .arrayOutOfBounds   => .arrayOutOfBounds
  | .maximumSizeExceeded => .maximumSizeExceeded
  | .panic              => .panic
  | .undef              => .undef

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- Lift a hax `RustM` computation into the oracle-aware `RustOracleComp`.

The three cases of `RustM` map to the three cases of `RustOracleComp`:
* `RustM.ok v`   ↦ `pure v`          (successful return),
* `RustM.fail e` ↦ `throw (errorOfHax e)` (Rust panic, error rebranded),
* `RustM.div`    ↦ `RustOracleComp.div` (divergence).

The lift does not issue any oracle query, so it is the canonical "total,
oracle-free" embedding. -/
def liftRustM (x : RustM α) : Interop.Rust.RustOracleComp spec α :=
  match x with
  | RustM.ok v   => pure v
  | RustM.fail e => throw (errorOfHax e)
  | RustM.div    => Interop.Rust.RustOracleComp.div

instance : MonadLift RustM (Interop.Rust.RustOracleComp spec) where
  monadLift := liftRustM

/-! ### Constructor-level commutation

Each of the three pattern constructors of `RustM` has a matching constructor
in `RustOracleComp`; `liftRustM` commutes with them by reduction. These are
the boundary lemmas that `mvcgen` / `simp` need in order to peel off the
lift around a concrete `RustM` term and leave a pure `RustOracleComp`
statement behind. -/

@[simp]
theorem liftRustM_ok (v : α) :
    (liftRustM (RustM.ok v) : Interop.Rust.RustOracleComp spec α) =
      Interop.Rust.RustOracleComp.ok v :=
  rfl

@[simp]
theorem liftRustM_fail (e : _root_.Error) :
    (liftRustM (RustM.fail e) : Interop.Rust.RustOracleComp spec α) =
      Interop.Rust.RustOracleComp.fail (errorOfHax e) :=
  rfl

@[simp]
theorem liftRustM_div :
    (liftRustM (RustM.div : RustM α) : Interop.Rust.RustOracleComp spec α) =
      Interop.Rust.RustOracleComp.div :=
  rfl

/-! ### Monadic structure

`liftRustM` is a monad morphism: it preserves `pure` and `bind` up to the
`Error` rebrand. We state the `pure` case explicitly (`RustM.pure = RustM.ok`
is `rfl`); the `bind` case follows from the fact that `RustM` and
`RustOracleComp spec` are both `ExceptT`-over-some-`Option`-layer and the
lift is a nested `pure` on both layers. -/

@[simp]
theorem liftRustM_pure (v : α) :
    (liftRustM (pure v : RustM α) : Interop.Rust.RustOracleComp spec α) =
      pure v :=
  rfl

end Interop.Hax
