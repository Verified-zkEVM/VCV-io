/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Interop.Hax.Bridge
import Interop.Rust.Run
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.Instances.ErrorT
import VCVio.EvalDist.Instances.OptionT
import VCVio.EvalDist.Fintype

/-!
# Small end-to-end examples of the hax → VCVio bridge

A tiny `RustM`-style Rust function, lifted into `RustOracleComp`, plus
a one-oracle-query composition and a probabilistic harness. The goals
are:

* the four `@[simp]` boundary lemmas in `Interop.Hax.Bridge`
  (`liftRustM_{ok,fail,div,pure}`) plus the composed `Std.Do` `WP` stack
  (`ExceptT.instWP` / `OptionT.instWP` over VCVio's
  `WP (OracleComp spec) .pure`) should suffice for `Triple`-level
  specs on lifted Rust programs,
* `RustOracleComp`'s `OracleComp`-layer also carries probabilistic
  content (`Pr[=]`, `support`, `evalDist`) that has no counterpart on
  `Hax.RustM`; `tossedAdd_panic_prob` demonstrates a panic probability
  of exactly `1/2`, a statement that only makes sense on the bridged
  monad.
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

/-! ### Probabilistic spec via the `OracleComp` layer

Everything so far was a `Triple`: universal over oracle outcomes, with
no probabilistic content. The point of dropping `Hax.RustM` into
`RustOracleComp spec` is that the `OracleComp spec` layer also carries
`HasEvalSPMF` (via the `ExceptT` / `OptionT` instances in
`VCVio.EvalDist.Instances.{ErrorT,OptionT}`), so quantitative claims
like `Pr[= some (.error e) | tossedAdd.run.run] = 1/2` are well-defined
and provable.

`tossedAdd` below is the minimum interesting example: a uniform bit
decides between a safe lifted `addOrPanic` call and one that is
guaranteed to overflow. Neither the hax Hoare spec nor the bridge
transport lemma `triple_liftRustM` can make the resulting probability
claim; it is a genuine VCVio-side addition on top of the bridge. -/

section ProbabilisticSpec

/-- Probabilistic harness: flip a uniform bit `b ∈ Fin 2` from
`unifSpec`, then dispatch to either `addOrPanicLifted 0 0` (always
returns `0`) or `addOrPanicLifted (2^32) 0` (always panics with
`Error.integerOverflow`). -/
def tossedAdd : Interop.Rust.RustOracleComp unifSpec Nat := do
  let b ← ($[0..1] : ProbComp (Fin 2))
  if b = 0 then addOrPanicLifted 0 0
  else addOrPanicLifted (2 ^ 32) 0

/-- Transformer-stack peel for `tossedAdd`: after running the `ExceptT`
and `OptionT` layers we land at the `OracleComp unifSpec` level with a
`bind` on `$[0..1]` whose continuation is a deterministic `pure`.

This is the canonical intermediate form for probability claims on
`RustOracleComp`: once we reach `OracleComp spec (Option (Except ε α))`
every `Pr[=]`, `support`, and `evalDist` lemma from VCVio applies
directly.

The proof is a one-liner thanks to the reusable peel lemmas in
`Interop.Rust.Run`: `run_run_bind_liftM` peels the `liftM $[0..1]`
bind, and `run_run_{pure,throw}` (via the constructor equations on the
two branches) handle the `then`/`else` tails. -/
theorem tossedAdd_run_run :
    tossedAdd.run.run =
      ($[0..1] >>= fun b : Fin 2 =>
        pure (some (if b = 0 then
          (Except.ok 0 : Except Interop.Rust.Error Nat)
          else Except.error .integerOverflow)) :
            OracleComp unifSpec (Option (Except Interop.Rust.Error Nat))) := by
  have h_ok : (addOrPanicLifted 0 0 : Interop.Rust.RustOracleComp unifSpec Nat)
      = pure 0 := by
    have := addOrPanicLifted_ok_of_lt (spec := unifSpec) 0 0 (by decide)
    simpa using this
  have h_fail : (addOrPanicLifted (2^32) 0 : Interop.Rust.RustOracleComp unifSpec Nat)
      = throw .integerOverflow :=
    addOrPanicLifted_fail_of_ge (spec := unifSpec) (2^32) 0 (by decide)
  unfold tossedAdd
  simp only [h_ok, h_fail,
    Interop.Rust.RustOracleComp.run_run_bind_liftM,
    apply_ite (f := fun x : Interop.Rust.RustOracleComp unifSpec Nat => x.run.run),
    Interop.Rust.RustOracleComp.run_run_pure,
    Interop.Rust.RustOracleComp.run_run_throw,
    apply_ite (pure (f := OracleComp unifSpec)), apply_ite some]

/-- Panic probability of `tossedAdd` is exactly `1/2`. This is the core
claim only statable on the VCVio side: the hax `Triple` layer is
universal over oracle outcomes and says nothing about probability, and
the `Hax.RustM` level has no oracle to sample at all. -/
theorem tossedAdd_panic_prob :
    Pr[= some (Except.error Interop.Rust.Error.integerOverflow) |
        tossedAdd.run.run] = 2⁻¹ := by
  rw [tossedAdd_run_run, HasEvalSPMF.probOutput_bind_eq_sum_fintype]
  -- ∑ x : Fin 2, Pr[= x | $[0..1]] * (if ... then 1 else 0).
  -- Both `Pr[= · | $[0..1]]` factors collapse to `(1 + 1 : ℝ≥0∞)⁻¹`, then the
  -- `x = 0` branch contributes `0` and the `x = 1` branch contributes the
  -- integer-overflow coefficient `1`, leaving `(1 + 1)⁻¹ = 2⁻¹`.
  simp only [ProbComp.probOutput_uniformFin]
  have h1 : ((1 : Fin 2) = 0) ↔ False := by decide
  simp [h1]
  norm_num

end ProbabilisticSpec

end Interop.Hax.Examples
