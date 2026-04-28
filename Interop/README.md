# Interop

Experimental bridges that let VCVio reason about Lean code emitted by Rust
verification frontends (currently [hax](https://github.com/cryspen/hax) and
[aeneas](https://github.com/AeneasVerif/aeneas)).

## TCB Isolation Contract

The single most important property of this library is that **nothing in core
VCVio depends on it**. Pulling hax / aeneas into the build adds a sizeable
trusted computing base (extraction frontend, Charon, the backend's own
runtime axioms), and we never want a routine `lake build` of the core
framework to inherit that.

The contract is enforced at three levels:

1. **Lake**: `Interop` is its own `lean_lib` in `lakefile.lean`, sibling to
   `LatticeCrypto`/`Examples`. Cross-library imports are physical: a file
   under `VCVio/`, `LatticeCrypto/`, `LatticeCryptoTest/`, `Examples/`,
   `ToMathlib/`, `FFI/`, `VCVioWidgets/`, or `VCVioTest/` must never
   `import Interop.…`, `import Hax.…`, or `import Aeneas.…`.
2. **CI**: `scripts/check-interop-isolation.sh` greps for forbidden imports
   and exits non-zero on violation. `.github/workflows/interop-isolation.yml`
   runs it on every PR and on pushes to `main`.
3. **Reverse direction**: `Interop/**` is allowed to depend on `VCVio/**`,
   `ToMathlib/**`, hax (`Hax.…`), and aeneas (`Aeneas.…`), but **not** on
   `LatticeCrypto/**`, `Examples/**`, `LatticeCryptoTest/**`, `FFI/**`,
   `VCVioWidgets/**`, or `VCVioTest/**`.
   Those are themselves clients of VCVio. The same script checks this.

If you need to share infrastructure between Interop and another library,
move the shared piece into `VCVio/` first.

## Layout

```
Interop/
├── README.md             ← this file
├── Rust/                 ← framework-side Rust target monad (`RustOracleComp`)
│   ├── Common.lean       ← `RustOracleComp`, mirrored `Error`, `Std.Do.WP` glue
│   └── Run.lean          ← reusable `.run.run` peel lemmas for the
│                           `ExceptT / OptionT / OracleComp` stack, used
│                           by probabilistic proofs downstream
├── Hax/                  ← bridge to `Hax.RustM` (gated on hax require)
│   ├── README.md
│   ├── Bridge.lean       ← `liftRustM`, `errorOfHax`,
│   │                       `@[spec] triple_liftRustM`, `LawfulMonadLift`
│   │                       instance, bundled `MonadHom` (`liftRustMHom`)
│   ├── Examples.lean     ← hand-crafted demo: `addOrPanicLifted`,
│   │                       oracle-composed `oracleThenAdd`, probabilistic
│   │                       `tossedAdd` with `Pr[panic] = 1/2`
│   ├── Computation.lean  ← hax-emitted `x + x + 1` (first real hax source)
│   ├── Division.lean     ← hax-emitted `/?`: `.divisionByZero` end-to-end
│   ├── Adc.lean          ← hax `lean_adc`: 32-bit ADC via
│   │                       `hax_mvcgen <;> bv_decide`, transported by
│   │                       one application of `triple_liftRustM`
│   ├── Barrett.lean      ← hax `lean_barrett`: signed 32-bit Barrett
│   │                       reduction mod 3329, proven in-range via
│   │                       `hax_bv_decide` (bit-blast, 300s timeout)
│   └── CenteredBinomial.lean
│                         ← CBD(η = 1) sampler from `third_party/hax-cbd`;
│                           first randomized hax source. Deterministic
│                           `{-1, 0, 1}` range over all `u8` by
│                           `native_decide`; exact distribution
│                           `Pr[0] = 1/2`, `Pr[±1] = 1/4` on
│                           `sampleRandomCbd1 : RustOracleComp unifSpec i32`
└── Aeneas/               ← bridge to `Aeneas.Std.Result` (currently disabled)
    └── README.md
```

`Rust/Common.lean` is **self-contained**: it builds without hax or aeneas
loaded, by mirroring their shared `Error` enum and reconstructing the
`ExceptT Error (OptionT (OracleComp spec))` stack that hax's `RustM` collapses
into. The actual `MonadLift` instances from hax/aeneas live in `Hax/` and
`Aeneas/`, where they can use the upstream definitions.

## Git-pinned Backend Requires

`lakefile.lean` carries explicit git pins for both backends. Current state:

```lean
-- Hax: Lean 4.29.0-rc1 (compatible with our 4.29.0). Enabled.
require Hax from git
  "https://github.com/cryspen/hax" @ "492a34e3" / "hax-lib/proof-libs/lean"

-- Aeneas: upstream still on Lean 4.28.0-rc1. Disabled; three source
-- regressions against v4.29 (see `Interop/Aeneas/README.md`).
-- require aeneas from git
--   "https://github.com/AeneasVerif/aeneas" @ "ba600392" / "backends/lean"
```

Hax was empirically verified on 2026-04-17: `lake build Hax` succeeds (91
jobs), and Interop rebuilds incrementally with hax in scope. Aeneas at
`ba600392` fails three files under Lean/Mathlib v4.29 including the one
we need (`Aeneas/Std/Primitives.lean`); see `Interop/Aeneas/README.md`
for exact diagnostics.

### Require order matters

`require Hax` must appear **before** `require "leanprover-community" /
"mathlib"`. Hax transitively pins `Qq` at `v4.29.0-rc1`, Mathlib pins it
at the final release; Lake's conflict resolver takes the **last**
`require` of each dependency, so mathlib goes last to win. Wrong order
produces `mathlib: failed to fetch cache` on `lake update`.

We git-pin by default so reproducible builds are guaranteed. Bumping a
pin is a deliberate one-line change reviewed alongside any TCB delta.
