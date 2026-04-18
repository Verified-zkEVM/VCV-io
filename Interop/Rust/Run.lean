/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Interop.Rust.Common

/-!
# Peeling the `RustOracleComp` transformer stack

The canonical intermediate form for any probabilistic / support / evalDist
claim on `RustOracleComp spec α` is
```
OracleComp spec (Option (Except Interop.Rust.Error α))
```
obtained by running the `ExceptT` and `OptionT` layers in that order.

This file collects the reusable peel lemmas that reduce common
`RustOracleComp` program shapes to this canonical form. They are all
`@[simp]` so `mvcgen` / `simp` can reduce programs automatically.

The main lemma is `RustOracleComp.run_run_bind_liftM`: a lifted oracle
call followed by a continuation peels to the underlying `OracleComp`
bind. This is the shape `mvcgen` / `simp` needs for any `RustOracleComp`
program that interleaves oracle queries with lifted `RustM` calls.

The constructor-level lemmas (`run_run_pure`, `run_run_fail`,
`run_run_div`) hold by `rfl` and are stated as `@[simp]` so the peel
can finish the job on closed programs.
-/

open Std.Do

namespace Interop.Rust.RustOracleComp

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-! ### Constructor-level `.run.run` lemmas

For the three `RustOracleComp` constructors (`ok`/`fail`/`div`) the
`.run.run` is a constant `pure`: `pure (some (.ok v))`, `pure (some (.error e))`,
or `pure none` respectively. Every constructor equation is `rfl`. -/

/-- `.run.run` of a successful Rust value (`pure` / `ok`). -/
@[simp]
theorem run_run_ok (v : α) :
    (Interop.Rust.RustOracleComp.ok v : Interop.Rust.RustOracleComp spec α).run.run
      = (pure (some (Except.ok v)) :
          OracleComp spec (Option (Except Interop.Rust.Error α))) :=
  rfl

/-- `.run.run` of `pure`, as `Monad.pure`. Same as `run_run_ok` but stated
in the `pure` form that `mvcgen`/`simp` tends to produce. -/
@[simp]
theorem run_run_pure (v : α) :
    ((pure v : Interop.Rust.RustOracleComp spec α)).run.run
      = (pure (some (Except.ok v)) :
          OracleComp spec (Option (Except Interop.Rust.Error α))) :=
  rfl

/-- `.run.run` of a panicking Rust computation (`throw` / `fail`). -/
@[simp]
theorem run_run_fail (e : Interop.Rust.Error) :
    (Interop.Rust.RustOracleComp.fail e : Interop.Rust.RustOracleComp spec α).run.run
      = (pure (some (Except.error e)) :
          OracleComp spec (Option (Except Interop.Rust.Error α))) :=
  rfl

/-- `.run.run` of `throw`, as `MonadExcept.throw`. Same as `run_run_fail`
but stated in the `throw` form that `mvcgen`/`simp` tends to produce. -/
@[simp]
theorem run_run_throw (e : Interop.Rust.Error) :
    ((throw e : Interop.Rust.RustOracleComp spec α)).run.run
      = (pure (some (Except.error e)) :
          OracleComp spec (Option (Except Interop.Rust.Error α))) :=
  rfl

/-- `.run.run` of a diverging Rust computation. -/
@[simp]
theorem run_run_div :
    (Interop.Rust.RustOracleComp.div : Interop.Rust.RustOracleComp spec α).run.run
      = (pure none :
          OracleComp spec (Option (Except Interop.Rust.Error α))) :=
  rfl

/-! ### Peel `.run.run` through `liftM`-bind

The core peel lemma: when a `RustOracleComp` program starts with a lifted
oracle call and continues with `>>= k`, running both transformer layers
produces the underlying `OracleComp` bind with the continuation's
`.run.run` pasted in. Every lift is of the form
`ExceptT.lift ∘ OptionT.lift` via the derived
`MonadLiftT (OracleComp spec) (RustOracleComp spec)` chain; the proof
commits to that shape via a single `change`, then applies the standard
`run_bind_lift` lemmas from `Init.Control.Lawful.Instances` for both
transformers. -/
@[simp]
theorem run_run_bind_liftM
    (oa : OracleComp spec α) (k : α → Interop.Rust.RustOracleComp spec β) :
    ((liftM oa : Interop.Rust.RustOracleComp spec α) >>= k).run.run
      = oa >>= fun a => (k a).run.run := by
  change (ExceptT.run ((ExceptT.lift (OptionT.lift oa) :
      Interop.Rust.RustOracleComp spec α) >>= k)).run = _
  simp only [ExceptT.run_bind_lift, OptionT.run_bind_lift]

/-- Specialization of `run_run_bind_liftM` to the pure lift (no continuation).
A lifted oracle computation, after running both transformers, is
`(fun a => some (Except.ok a)) <$> oa`: the oracle's value wrapped in
`Except.ok` (no panic) and `some` (no divergence). -/
@[simp]
theorem run_run_liftM (oa : OracleComp spec α) :
    (liftM oa : Interop.Rust.RustOracleComp spec α).run.run
      = (fun a => some (Except.ok a)) <$> oa := by
  have h := run_run_bind_liftM (spec := spec) oa
    (k := fun a => (pure a : Interop.Rust.RustOracleComp spec α))
  simp only [bind_pure, run_run_pure] at h
  rw [h]
  exact (map_eq_pure_bind _ oa).symm

end Interop.Rust.RustOracleComp
