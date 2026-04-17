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
  (Interop.Rust.RustOracleComp spec)` instance, and four `rfl`-level
  `@[simp]` commutation lemmas (`liftRustM_{ok,fail,div,pure}`).
- `Examples.lean` — tiny end-to-end demo: a checked-addition `RustM`
  function, two equality-level specs, one `Std.Do.Triple` spec driven
  by `mvcgen`, and an oracle-composed `RustOracleComp` program mixing
  a `query` with a lifted `RustM` call.

`lake build Interop` succeeds across all of the above (2625 jobs).

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

- **Compositional** `Triple`-level boundary lemma: a transport of the
  form "`Triple x P Q` on `RustM` gives `Triple (liftRustM x) P Q'` on
  `RustOracleComp spec`, where `Q'.2.1 = Q.2.1 ∘ errorOfHax`". Useful
  for porting hax's own `@[spec]` library wholesale. Not yet needed for
  concrete programs since `mvcgen` + the `@[simp]` lemmas handle them.
- A bigger example that actually exercises oracle queries under a
  `RustOracleComp`-shaped spec (the current `oracleThenAdd` has no
  spec attached).
