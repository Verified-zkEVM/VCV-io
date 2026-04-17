# Interop / Hax

Bridge from [hax](https://github.com/cryspen/hax)'s Lean backend (`Hax.RustM`)
to VCVio's `RustOracleComp`.

## Status

`require Hax` is **active** in `lakefile.lean`, pinned to commit
`492a34e3` (hax `main` as of 2026-04-16). Hax compiles cleanly against our
Lean v4.29.0 / Mathlib v4.29.0 stack: `lake build Hax` succeeds in 91 jobs
with 2 harmless `@[reducible]` warnings in hax's own
`rust_primitives/USize64.lean`.

Bridge code is in place:

- `Bridge.lean` — `errorOfHax`, `liftRustM`, the `MonadLift RustM
  (Interop.Rust.RustOracleComp spec)` instance, four `rfl`-level
  `@[simp]` commutation lemmas (`liftRustM_{ok,fail,div,pure}`), and
  the compositional `Triple`-level boundary lemma `triple_liftRustM`.
- `Examples.lean` — end-to-end demo: a checked-addition `RustM`
  function, two equality-level specs, a `Std.Do.Triple` spec driven by
  `mvcgen` (`addOrPanicLifted_triple`), an oracle-composed
  `RustOracleComp` program (`oracleThenAdd`), and a `Triple` spec on
  the oracle-composed program (`oracleThenAdd_triple`) that mixes a
  real `query` with a lifted `RustM` call.

`lake build Interop` succeeds across all of the above.

### `require` order

`require Hax` must appear *before* `require "leanprover-community" /
"mathlib"` in `lakefile.lean`. Mathlib's transitive pin of `Qq` has to win
over hax's `v4.29.0-rc1` pin, and Lake's conflict resolution takes the
**last** `require` of each dependency. `lake update` warns explicitly if
the order is wrong (`mathlib: failed to fetch cache`).

## What the bridge provides

On the monad side:

```
Hax.RustM α  :=  ExceptT _root_.Error Option α
     |
     | liftRustM (MonadLift)
     v
Interop.Rust.RustOracleComp spec α
             :=  ExceptT Interop.Rust.Error (OptionT (OracleComp spec)) α
```

`liftRustM` pattern-matches on the three cases of `RustM` and maps them to
the corresponding `RustOracleComp` constructors, rebranding the `Error`
enum constructor-by-constructor via `errorOfHax`. No oracle query is
issued by the lift.

On the Hoare-logic side, `Std.Do`'s `ExceptT.instWP` and `OptionT.instWP`
compose VCVio's `WP (OracleComp spec) .pure` (from
`VCVio.ProgramLogic.Unary.StdDoBridge`) into the same WP shape hax uses
for `RustM` itself, namely `.except Error (.except PUnit .pure)`, modulo
the `Error` rebrand. Because the shape matches, `mvcgen` walks lifted
Rust programs with no bespoke transformer lemmas; the `@[simp]`
commutation rules peel `liftRustM` off concrete constructors.

## Minimal example (see `Examples.lean`)

```lean
def addOrPanic (x y : Nat) : RustM Nat :=
  if x + y < 2 ^ 32 then pure (x + y) else RustM.fail .integerOverflow

def addOrPanicLifted (x y : Nat) : Interop.Rust.RustOracleComp spec Nat :=
  liftRustM (addOrPanic x y)

theorem addOrPanicLifted_triple (x y : Nat)
    [spec.Fintype] [spec.Inhabited] :
    ⦃⌜x + y < 2 ^ 32⌝⦄
    (addOrPanicLifted (spec := spec) x y)
    ⦃⇓ r => ⌜r = x + y⌝⦄ := by
  mvcgen [addOrPanicLifted, addOrPanic]
  intro h
  have h' : x + y < 4294967296 := h
  rw [if_pos h']
  simp [liftRustM_pure]
```

The `[spec.Fintype] [spec.Inhabited]` constraints are inherited from
VCVio's `WP (OracleComp spec) .pure` and are the only additional
obligation the oracle layer imposes.

## Compositional boundary lemma

`triple_liftRustM` in `Bridge.lean` transports a hax-side `Triple`
through the lift in one step:

```lean
theorem triple_liftRustM [spec.Fintype] [spec.Inhabited]
    (x : RustM α)
    {Q : PostCond α (.except Interop.Rust.Error (.except PUnit .pure))}
    {P : Assertion (.except Interop.Rust.Error (.except PUnit .pure))}
    (h : Std.Do.Triple (ps := .except _root_.Error (.except PUnit .pure)) x P
          (Q.1, fun e => Q.2.1 (errorOfHax e), Q.2.2)) :
    Std.Do.Triple
      (liftRustM (spec := spec) x : Interop.Rust.RustOracleComp spec α)
      P Q
```

The only move from the hax-side post-condition is rebranding the error
handler: `Q.2.1 ∘ errorOfHax` instead of `Q.2.1`. The success handler
(`Q.1`) and divergence handler (`Q.2.2`) are shared verbatim, which
reflects that `liftRustM` is the identity on those cases modulo the
transformer encoding. This lemma is what lets us reuse hax's own
`@[spec]` library downstream without reproving lifts pointwise.

## Oracle-composed Triple spec

`oracleThenAdd_triple` in `Examples.lean` is the "genuine" boundary
example: a `RustOracleComp`-shaped `Triple` on a program that both
issues an oracle query and invokes a hax-style `RustM` function.

```lean
def oracleThenAdd (x : Nat) (t : ι) (coe : spec.Range t → Nat) :
    Interop.Rust.RustOracleComp spec Nat := do
  let y ← (liftM (query t) : OracleComp spec _)
  liftRustM (addOrPanic x (coe y))

theorem oracleThenAdd_triple (x : Nat) (t : ι) (coe : spec.Range t → Nat)
    [spec.Fintype] [spec.Inhabited]
    (hbound : ∀ y : spec.Range t, x + coe y < 2 ^ 32) :
    ⦃⌜True⌝⦄
    (oracleThenAdd (spec := spec) x t coe)
    ⦃⇓ r => ⌜x ≤ r⌝⦄
```

The proof is `mvcgen` + the `wpProp`-to-`support` bridge from VCVio's
`StdDoBridge` for the single oracle step, then `simp` closes the
lifted `RustM` tail. The oracle query is lifted through the derived
`MonadLiftT (OracleComp spec) (RustOracleComp spec)` chain
(`OptionT.lift` composed with `ExceptT.lift`), not a direct
`MonadLift` instance; keeping the chain derived ensures `mvcgen` can
peel it via the standard `Spec.monadLift_{OptionT,ExceptT}` rules
rather than short-circuiting on a hand-written instance.

## Risks

- `_root_.Error` (hax) is namespace-collision-prone with anything else
  that defines a root-level `Error`. The mirrored `Interop.Rust.Error`
  is in its own namespace; rebranding happens at the boundary via
  `errorOfHax`, not throughout.
- Hax tactics (`Hax.Tactic.HaxMvcgen`) and the global `@[spec]`
  `DiscrTree` may interact with VCVio's `mvcgen`. If that becomes
  visible, quarantine hax tactic imports to `Interop/Hax/**` and keep
  `Interop.Hax.Bridge` tactic-free.
- See `docs/agents/interop.md` for the full risk list.

## Next steps

- Wire `triple_liftRustM` into a `@[spec]` attribute (currently a plain
  theorem) once we have a concrete hax example whose pre/post shapes
  let `mvcgen` index it cleanly.
- Port a non-trivial hax `@[spec]` fact and apply `triple_liftRustM` to
  it, verifying the rebrand of the error handler composes as expected
  with hax's own `_root_.Error` enum beyond the single
  `integerOverflow` constructor exercised in `Examples.lean`.
- State `liftRustM` as a more general `MonadHom` / `MonadMorphism` so
  that it transports any hax-side `Pr[_]`-style probabilistic spec, not
  just Hoare `Triple`s. Only needed once we have a probabilistic hax
  workflow.
