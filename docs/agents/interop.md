# Interop with Rust verification frontends (hax, aeneas)

`Interop/` is an experimental sibling to `LatticeCrypto/` whose job is to
let VCVio reason about Lean code emitted by Rust verification frontends:

- [hax](https://github.com/cryspen/hax): MIR → Lean/F\*/Coq/EasyCrypt/ProVerif/SSProve via a 35-phase OCaml engine. Lean target produces code in the `Hax.RustM := ExceptT Error Option` monad.
- [aeneas](https://github.com/AeneasVerif/aeneas): MIR → Lean/Coq/F\* via Charon's LLBC + functional translation. Lean target produces code in an inductive `Aeneas.Std.Result α := ok | fail | div`.

Both backends collapse panic + divergence into the same shape; VCVio adds
oracle access on top. The framework-side target monad is
`Interop.Rust.RustOracleComp`.

## TCB Isolation Contract

This is the headline guarantee: **adding `Interop/` does not increase the
trusted computing base (TCB) of core VCVio**.

Rust verification frontends drag in a sizeable trusted layer (extraction
engine, Charon's LLBC frontend, the backend's own runtime axioms), and we
never want a routine `lake build` of the core framework to inherit that.
The contract is therefore enforced at three levels:

1. **Lake**: `Interop` is its own `lean_lib` in `lakefile.lean`, sibling
   to `LatticeCrypto`/`Examples`. Cross-library imports are physical.
2. **CI**: `scripts/check-interop-isolation.sh` greps for forbidden
   imports. `.github/workflows/interop-isolation.yml` runs it on every PR
   and on pushes to `main`. The script also runs without a Lean toolchain,
   so it is fast and never blocks on Mathlib cache or build flakiness.
3. **Reverse direction**: `Interop/**` may import from `VCVio/**`,
   `ToMathlib/**`, `Hax.…`, and `Aeneas.…`, but **not** from
   `LatticeCrypto/**`, `Examples/**`, `LatticeCryptoTest/**`, `FFI/**`, or
   `VCVioWidgets/**`. Those libraries are themselves clients of VCVio, so
   Interop depending on them would create circular layering and pull
   user-facing libraries into the Interop TCB.

The isolation script accepts no flags besides `--help`; just run
`bash scripts/check-interop-isolation.sh` from the repo root.

If you need to share infrastructure between Interop and another library,
move the shared piece into `VCVio/` first.

## Layout

```
Interop/
├── README.md          ← contract summary + quick reference
├── Rust/              ← framework-side Rust target monad
│   └── Common.lean    ← `RustOracleComp`, mirrored `Error`, `Std.Do.WP` glue
├── Hax/               ← bridge to `Hax.RustM` (gated on hax require)
│   └── README.md      ← design + how to enable
└── Aeneas/            ← bridge to `Aeneas.Std.Result` (gated on aeneas require)
    └── README.md      ← design + toolchain blocker
```

`Rust/Common.lean` is **self-contained**: it builds without hax or aeneas
loaded. It mirrors the shared `Error` enum locally and defines

```lean
abbrev RustOracleComp (spec : OracleSpec ι) (α : Type) :=
  ExceptT Error (OptionT (OracleComp spec)) α
```

so that lifts from hax's `RustM = ExceptT Error Option` are the obvious
"wrap the `Option` in `pure`" mapping, and lifts from aeneas's `Result`
are case analysis. Both target `RustOracleComp spec`, giving us a single
oracle-aware Rust target monad for both backends.

## Git-pinned Backend Requires

`lakefile.lean` carries explicit, **commented-out** git pins for both
backends. Flip on whichever you need:

```lean
require Hax from git
  "https://github.com/cryspen/hax" @
  "492a34e3" / "hax-lib/proof-libs/lean"

require Aeneas from git
  "https://github.com/AeneasVerif/aeneas" @
  "ba600392" / "backends/lean"
```

We git-pin by default so reproducible builds are guaranteed; bumping a
pin is a deliberate one-line change reviewed alongside any TCB delta. The
isolation check runs regardless of whether the requires are active, so
the contract holds even mid-experiment.

## Toolchain Status (as of 2026-04-17)

- **VCVio**: `leanprover/lean4:v4.29.0`.
- **hax `492a34e3`**: `v4.29.0-rc1` — close enough that Lake can rebuild
  hax against our toolchain; expected to work with minor friction.
- **aeneas `ba600392`**: `v4.28.0-rc1` — **one minor version behind**. A
  `lake update` would currently fail; the require is commented out until
  upstream ships a 4.29 build (or we maintain a fork).

Bump the pins by editing the two `require` lines in `lakefile.lean` and
running `lake update Hax` (resp. `Aeneas`).

## Bridge Design (Reference)

When you flip on the hax require, add `Interop/Hax/Bridge.lean`:

```lean
import Hax.rust_primitives.RustM
import Interop.Rust.Common

namespace Interop.Hax

instance {ι : Type} {spec : OracleSpec ι} :
    MonadLift Hax.RustM (Interop.Rust.RustOracleComp spec) where
  monadLift x := ⟨⟨pure x.run⟩⟩
```

Plus boundary lemmas on `Std.Do.Triple` showing that the lift preserves
hax's WP shape (`.except Error (.except PUnit .pure)`) inside the
equivalent VCVio shape, since `ExceptT Error (OptionT _)` composes to
exactly that PostShape.

For aeneas, `Interop/Aeneas/Bridge.lean` will pattern-match on `Result`:

```lean
def ofResult {ι : Type} {spec : OracleSpec ι} {α : Type}
    (r : Aeneas.Std.Result α) : Interop.Rust.RustOracleComp spec α :=
  match r with
  | .ok v   => pure v
  | .fail e => Interop.Rust.RustOracleComp.fail (Interop.Rust.Error.ofAeneas e)
  | .div    => Interop.Rust.RustOracleComp.div
```

with `Interop.Rust.Error.ofAeneas` (and `.ofHax`) being constructor-by-
constructor maps from the upstream isomorphic enum.

## Risks and Open Questions

- **Duplicate `Error` enums**. `Hax.Error` and `Aeneas.Std.Error` are
  structurally identical but distinct types. We mirror as
  `Interop.Rust.Error` and convert at the boundary to avoid littering
  proofs with three-way coercions.
- **Hax `Std.Do` `@[spec]` `DiscrTree`**. Both hax and VCVio register
  `@[spec]` lemmas with `mvcgen`. Quarantine hax tactic imports to
  `Interop/Hax/**` so the global key set is loaded only when an Interop
  module asks for it.
- **Notation collisions**. The `⦃ ⦄ ⦃ ⦄` Hoare-triple notation is
  shared. Practice has been fine because both notations resolve through
  `Std.Do.Triple`, but be alert to `local notation` overrides in hax
  modules.
- **Loop combinators**. Hax's `RustM` has `Loop.MonoLoopCombinator`
  instances for `partial_fixpoint`. `RustOracleComp` doesn't yet, and
  may not need to if the lift comes after partial-fixpoint resolution
  on the hax side.
- **Aeneas tactic infrastructure** (`@[step]`, `step!`) cannot be reused
  on the VCVio side. Drive proofs with VCVio's `mvcgen` after lifting.
- **Verification Facade / Theatre concerns**. Both Charon and the hax
  engine are part of the TCB once a backend is enabled. Document any
  trusted assumption in `Interop/{Hax,Aeneas}/README.md`. See
  `vcvio-hax-aeneas-integration-council.md` in `~/Documents/Notes/` for
  the long-form risk analysis.

## Workflow

1. **Modify Interop only** for first-pass experiments. The CI isolation
   check will catch accidental cross-imports, but reviewing `git diff`
   for `VCVio/` paths catches them earlier.
2. **Run `bash scripts/check-interop-isolation.sh` locally** before
   pushing. It is fast and toolchain-free.
3. **`./scripts/update-lib.sh`** after adding new Lean files under
   `Interop/`; the umbrella `Interop.lean` regenerates.
4. **Bump pins explicitly**: edit the `require` line, run `lake update
   <Pkg>`, commit `lake-manifest.json` together with the pin change.
5. **Document any TCB delta** in `Interop/{Hax,Aeneas}/README.md` and
   cross-reference from PR descriptions.
