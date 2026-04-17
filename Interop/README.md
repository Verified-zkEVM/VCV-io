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
   runs it on every PR.
3. **Reverse direction**: `Interop/**` is allowed to depend on `VCVio/**`,
   `ToMathlib/**`, hax (`Hax.…`), and aeneas (`Aeneas.…`), but **not** on
   `LatticeCrypto/**`, `Examples/**`, `LatticeCryptoTest/**`, `FFI/**`, or
   `VCVioWidgets/**` (those are themselves clients of VCVio). The same
   script checks this.

If you need to share infrastructure between Interop and another library,
move the shared piece into `VCVio/` first.

## Layout

```
Interop/
├── README.md          ← this file
├── Rust/              ← framework-side Rust target monad (`RustOracleComp`)
│   └── Common.lean    ← `RustOracleComp`, mirrored `Error`, `Std.Do.WP` glue
├── Hax/               ← bridge to `Hax.RustM` (gated on hax require)
│   └── README.md
└── Aeneas/            ← bridge to `Aeneas.Std.Result` (gated on aeneas require)
    └── README.md
```

`Rust/Common.lean` is **self-contained**: it builds without hax or aeneas
loaded, by mirroring their shared `Error` enum and reconstructing the
`ExceptT Error (OptionT (OracleComp spec))` stack that hax's `RustM` collapses
into. The actual `MonadLift` instances from hax/aeneas live in `Hax/` and
`Aeneas/`, where they can use the upstream definitions.

## Git-pinned Backend Requires

`lakefile.lean` carries explicit, commented-out git pins for both backends.
Flip on whichever backend you need:

```lean
-- Hax: Lean 4.29.0-rc1 (compatible with our 4.29.0)
require Hax from git
  "https://github.com/cryspen/hax" @ "492a34e3..." / "hax-lib/proof-libs/lean"

-- Aeneas: currently Lean 4.28.0-rc1 — needs upstream bump before it links.
-- require Aeneas from git
--   "https://github.com/AeneasVerif/aeneas" @ "ba600392..." / "backends/lean"
```

We git-pin by default so reproducible builds are guaranteed. Bumping a pin
is a deliberate one-line change reviewed alongside any TCB delta.
