/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Hax.rust_primitives.RustM
import Interop.Rust.Common
import ToMathlib.Control.Monad.Hom

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

`liftRustM` is a monad morphism: it preserves `pure` and `bind` up to
the `Error` rebrand. We state the `pure` case explicitly
(`RustM.pure = RustM.ok` is `rfl`). The `bind` case follows by case
analysis on the `RustM` constructor, relying on the fact that the three
`RustOracleComp` constructor forms (`ok`, `fail`, `div`) absorb `bind`
the same way their `RustM` counterparts do.

We bundle the result in two ways:

* `LawfulMonadLift RustM (RustOracleComp spec)` — the lightweight,
  typeclass-driven path used by Lean's generic `liftM` tactics and by
  `Std.Do.WP` machinery under the hood.
* `MonadHom RustM (RustOracleComp spec)` — the bundled morphism from
  `ToMathlib.Control.Monad.Hom`, which transports arbitrary
  pure/bind-preserving properties (not only Hoare triples). In
  particular `triple_liftRustM` is one instance of the general
  pull-back-through-`MonadHom` pattern. -/

@[simp]
theorem liftRustM_pure (v : α) :
    (liftRustM (pure v : RustM α) : Interop.Rust.RustOracleComp spec α) =
      pure v :=
  rfl

/-- `liftRustM` commutes with `bind`: the lift of a sequenced Rust
program equals the sequenced lift, where the `fail`/`div` branches
short-circuit identically on both sides. -/
@[simp]
theorem liftRustM_bind {β : Type} (x : RustM α) (k : α → RustM β) :
    (liftRustM (x >>= k) : Interop.Rust.RustOracleComp spec β) =
      liftRustM x >>= fun a => liftRustM (k a) := by
  match x with
  | RustM.ok v   => rfl
  | RustM.fail e => rfl
  | RustM.div    => rfl

/-- `liftRustM` is a `LawfulMonadLift`: it preserves `pure` and `bind`.
This is the typeclass-level statement and is picked up automatically by
the generic `liftM` / `Std.Do.WP` machinery. -/
instance instLawfulMonadLiftRustM :
    LawfulMonadLift RustM (Interop.Rust.RustOracleComp spec) where
  monadLift_pure v := liftRustM_pure v
  monadLift_bind x k := liftRustM_bind x k

/-- `liftRustM` bundled as a monad morphism
`RustM →ᵐ RustOracleComp spec`. Equivalent in content to the
`LawfulMonadLift` instance above, but exposes the lift as a term-level
map so arbitrary `MonadHom`-indexed lemmas (e.g. `mmap_map`,
`mmap_seq`) transport along the bridge. -/
def liftRustMHom : RustM →ᵐ Interop.Rust.RustOracleComp spec :=
  MonadHom.ofLift _ _

@[simp]
theorem liftRustMHom_apply (x : RustM α) :
    (liftRustMHom (spec := spec)) x = liftRustM x := rfl

/-! ### `Triple`-level boundary transport

The following theorem is the main compositional content of the bridge: any
`Std.Do` `Triple` for `x : RustM α` induces a `Triple` for
`liftRustM x : RustOracleComp spec α`, with the postcondition transported
only through `errorOfHax` on the exception component. The precondition and
the success / divergence components are reused verbatim because both
monads have the same post-shape `.except _ (.except PUnit .pure)` and both
`Assertion` types reduce to `ULift Prop`.

This is the lemma that lets one port hax's upstream `@[spec]` library
into `RustOracleComp` wholesale: apply the lemma, then supply the hax
spec as the hypothesis. For concrete constructor-level programs the
`@[simp]` commutation lemmas above still do the job directly. -/

@[spec]
theorem triple_liftRustM [spec.Fintype] [spec.Inhabited]
    (x : RustM α)
    {Q : PostCond α (.except Interop.Rust.Error (.except PUnit .pure))}
    {P : Assertion (.except Interop.Rust.Error (.except PUnit .pure))}
    (h : Std.Do.Triple (ps := .except _root_.Error (.except PUnit .pure)) x P
          (Q.1, fun e => Q.2.1 (errorOfHax e), Q.2.2)) :
    Std.Do.Triple
      (liftRustM (spec := spec) x : Interop.Rust.RustOracleComp spec α)
      P Q := by
  match x with
  | RustM.ok v =>
    rw [Triple.iff] at h ⊢
    simpa [liftRustM_ok, Interop.Rust.RustOracleComp.ok,
      WPMonad.wp_pure] using h
  | RustM.fail e =>
    rw [Triple.iff] at h ⊢
    simpa [liftRustM_fail, Interop.Rust.RustOracleComp.fail, RustM.fail] using h
  | RustM.div =>
    rw [Triple.iff] at h ⊢
    change P ⊢ₛ wp⟦(Interop.Rust.RustOracleComp.div : Interop.Rust.RustOracleComp spec α)⟧ Q
    -- Both wps reduce to the divergence branch: `Q.2.2.1 ⟨⟩`.
    -- Use `WPMonad.wp_pure` on the inner `OracleComp` layer to eliminate the
    -- residual `⌜(Q.2.2.1 ⟨⟩).down⌝` wrapping VCVio's WP introduces, then
    -- match the RustM side which is structurally the same
    -- `pushOption ∘ pushExcept` with the inner `Id` instead of
    -- `OracleComp spec`.
    have hgoal :
        wp⟦(Interop.Rust.RustOracleComp.div : Interop.Rust.RustOracleComp spec α)⟧ Q
          = Q.2.2.1 ⟨⟩ := by
      change (PredTrans.pushExcept (PredTrans.pushOption
        (WP.wp (pure none :
          OracleComp spec (Option (Except Interop.Rust.Error α)))))).apply Q
            = _
      rw [WPMonad.wp_pure]
      rfl
    have hh :
        wp⟦(RustM.div : RustM α)⟧
            ((Q.1, fun e => Q.2.1 (errorOfHax e), Q.2.2) :
              PostCond α (.except _root_.Error (.except PUnit .pure)))
          = Q.2.2.1 ⟨⟩ := rfl
    rw [hgoal]
    rw [hh] at h
    exact h

end Interop.Hax
