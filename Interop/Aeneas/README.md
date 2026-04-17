# Interop / Aeneas

Bridge from [aeneas](https://github.com/AeneasVerif/aeneas)'s Lean backend
(`Aeneas.Std.Result`) to VCVio's `RustOracleComp`.

## Status

Scaffolded but **blocked on upstream regressions**. Empirically verified
on 2026-04-17 against aeneas `main` (`ba600392`): Lake happily resolves
aeneas with our root Mathlib v4.29.0 and Lean v4.29.0 pins overriding
aeneas's `v4.28.0-rc1` manifest entries, but aeneas's source has **three
real regressions** against the v4.29 stack, and one of them is inside the
single file we need:

1. `Aeneas/Std/Primitives.lean:168:44` — kernel type mismatch in
   `CCPO (Result α) := inferInstanceAs (CCPO (FlatOrder .div))`. The
   `FlatOrder` / `CCPO` / `chain` / `is_sup` API changed between v4.28
   and v4.29. `Result α` itself still parses, but its `CCPO`/`MonoBind`
   instances do not elaborate, so we cannot import `Aeneas.Std.Primitives`
   at all.
2. `Aeneas/Tactic/Simproc/ReduceZMod/ReduceZMod.lean:83:10` —
   `Unknown constant Monoid.toNatPow` (renamed/removed in Mathlib v4.29).
3. `Aeneas/Tactic/Simp/RingEqNF/Tests.lean:113:11` — `ring_nf` leaves a
   different normal form under Mathlib v4.29, so a test's `exact h`
   mismatches. Tests only, not the main library.

Build coverage on the compatibility attempt was 1625/1662 jobs before the
three failures propagated. The require is therefore **commented out** in
`lakefile.lean`. Unblock by either:

- Waiting for upstream to bump aeneas to Lean v4.29 (a one-line `require`
  flip afterwards); or
- Maintaining a short patch series on a fork pinning the above three
  files and using that fork as the git source.

## Plan (applies once upstream ships a v4.29 build)

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
