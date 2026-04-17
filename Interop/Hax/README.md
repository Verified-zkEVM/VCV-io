# Interop / Hax

Bridge from [hax](https://github.com/cryspen/hax)'s Lean backend (`Hax.RustM`)
to VCVio's `RustOracleComp`.

## Status

`require Hax` is **active** in `lakefile.lean`, pinned to commit
`492a34e3` (hax `main` as of 2026-04-16). Hax compiles cleanly against our
Lean v4.29.0 / Mathlib v4.29.0 stack: `lake build Hax` succeeds in 91 jobs
with 2 harmless `@[reducible]` warnings in hax's own
`rust_primitives/USize64.lean`. No bridge code yet — the `MonadLift`
instance and boundary lemmas below are the next step.

Note: `require Hax` must appear *before* `require "leanprover-community" /
"mathlib"` in `lakefile.lean`. Mathlib's transitive pin of `Qq` has to win
over hax's `v4.29.0-rc1` pin, and Lake's conflict resolution takes the
**last** `require` of each dependency. `lake update` warns explicitly if
the order is wrong.

## Plan

When the hax require is enabled, add `Bridge.lean` here with:

```lean
import Hax.rust_primitives.RustM
import Interop.Rust.Common

namespace Interop.Hax

/-- Lift a hax `RustM` computation into the oracle-aware `RustOracleComp`
    over any `OracleSpec`. Since `Hax.RustM α := ExceptT Error Option α`
    and `RustOracleComp spec α := ExceptT Error (OptionT (OracleComp spec)) α`,
    the lift is the obvious "wrap the `Option` in `pure`" mapping. -/
instance {ι : Type} {spec : OracleSpec ι} :
    MonadLift Hax.RustM (Interop.Rust.RustOracleComp spec) where
  monadLift x := ⟨⟨pure x.run⟩⟩
```

Plus boundary lemmas on `Std.Do.Triple` showing that the lift preserves
`@[spec]`-keyed shapes from hax (`.except Error (.except PUnit .pure)`)
inside the equivalent VCVio shape.

## Risks

- `Hax.Error` collides with `Interop.Rust.Error` (they are isomorphic but
  not defeq). Convert at the boundary, not throughout.
- Hax tactics (`Hax.Tactic.HaxMvcgen`) and the global `@[spec]` `DiscrTree`
  may interfere with VCVio's `mvcgen`. Quarantine hax tactic imports to
  `Interop/Hax/**`.
- See `docs/agents/interop.md` for the full risk list.
