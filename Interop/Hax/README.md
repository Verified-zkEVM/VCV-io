# Interop / Hax

Bridge from [hax](https://github.com/cryspen/hax)'s Lean backend (`Hax.RustM`)
to VCVio's `RustOracleComp`.

## Status

Scaffolded but **not yet wired**. The hax `require` is commented out in
`lakefile.lean` (see top-level `Interop/README.md` for the exact line and
the rationale).

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
