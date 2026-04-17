# Interop / Aeneas

Bridge from [aeneas](https://github.com/AeneasVerif/aeneas)'s Lean backend
(`Aeneas.Std.Result`) to VCVio's `RustOracleComp`.

## Status

Scaffolded but **blocked on toolchain**. Aeneas `main`
(`ba600392`, `build-2026.04.17.152554-...`) is on `leanprover/lean4:v4.28.0-rc1`,
while VCVio is on `v4.29.0`. The require is therefore commented out in
`lakefile.lean` — `lake update` against this pin would fail until aeneas
ships a 4.29 build.

When that happens, the pin gets bumped (one line) and `Bridge.lean` is added
here.

## Plan

```lean
import Aeneas.Std.Primitives
import Interop.Rust.Common

namespace Interop.Aeneas

/-- Convert an aeneas `Result` to the equivalent `Interop.Rust.Error`-based
    `RustOracleComp`. The mapping is determined by the inductive cases:
    `ok v → RustOracleComp.pure v`,
    `fail e → RustOracleComp.fail (errorOfAeneas e)`,
    `div   → RustOracleComp.div`. -/
def ofResult {ι : Type} {spec : OracleSpec ι} {α : Type}
    (r : Aeneas.Std.Result α) : Interop.Rust.RustOracleComp spec α :=
  match r with
  | .ok v   => pure v
  | .fail e => Interop.Rust.fail (Interop.Rust.Error.ofAeneas e)
  | .div    => Interop.Rust.div

instance {ι : Type} {spec : OracleSpec ι} :
    MonadLift Aeneas.Std.Result (Interop.Rust.RustOracleComp spec) where
  monadLift := ofResult
```

Plus a boundary lemma showing that the aeneas WP shape (`.except Error .pure`)
maps into VCVio's via the lift.

## Risks

- `Aeneas.Std.Error` and `Hax.Error` are nominally distinct but structurally
  identical. We mirror the shared shape as `Interop.Rust.Error` and convert
  on lift.
- Aeneas's `Result` is an inductive (not a transformer), so its
  `Std.Do.WP` instance is bespoke. Lifting goes through pattern matching,
  not transformer composition.
- The `@[step]` and `step!` tactic infrastructure cannot be re-used; VCVio's
  `mvcgen` must drive proofs on the VCVio side.
- See `docs/agents/interop.md` for the full risk list.
