# VCV-io — AI Agent Guide

Formally verified cryptography proofs in Lean 4, built on Mathlib.

## Fast Start For Agents

If you are new to this repo, do this first:

1. Run `lake exe cache get && lake build`.
2. Read `Examples/OneTimePad.lean` for a compact modern proof (correctness and privacy).
3. Keep `VCVio/` as your default work area.
4. If probability lemmas fail unexpectedly, first check for `[spec.Fintype]` and `[spec.Inhabited]`.

`AGENTS.md` is the canonical guide. `CLAUDE.md` is a symlink to this file.

## What This Project Is

VCV-io is a foundational framework for reasoning about cryptographic protocols in the computational model. It provides:

- **`OracleComp spec α`**: A monadic type for computations with oracle access, defined as a free monad (`PFunctor.FreeM`) over a polynomial functor derived from `OracleSpec`.
- **`simulateQ`**: Operational semantics — substitutes oracle queries with concrete implementations via `QueryImpl`.
- **`evalDist`**: Denotational semantics — embeds computations into the `PMF` monad for probability reasoning. This is literally `simulateQ` with uniform distributions as the oracle implementation.
- **`ProbComp α`**: Abbreviation for `OracleComp unifSpec α` (pure probabilistic computation with no custom oracles).

## Repository Structure

```
VCVio/                     # Main library (the only part that matters for most work)
  OracleComp/              # Core computation type and oracle machinery
    OracleSpec.lean         # OracleSpec ι := ι → Type v (just a function!)
    OracleComp.lean         # OracleComp spec α := PFunctor.FreeM spec.toPFunctor
    OracleQuery.lean        # Single oracle query type
    ProbComp.lean           # ProbComp = OracleComp unifSpec, sampling notations
    SimSemantics/           # Oracle simulation: QueryImpl, simulateQ, state/reader/writer transformers
    QueryTracking/          # Counting, logging, caching, seeded oracles
    Constructions/          # GenerateSeed, Replicate, SampleableType
    Coercions/              # SubSpec (⊂ₒ), automatic lifting between oracle specs
    EvalDist.lean           # Bridge: evalDist, support, finSupport, probOutput/Event/Failure
  EvalDist/                # Denotational semantics machinery
    Defs/                   # Core: HasEvalSPMF, HasEvalPMF, support, probOutput, Pr[...] notation
    Monad/                  # Simp lemmas: probOutput_bind, support_pure, etc.
    Instances/              # EvalDist for OptionT, ErrorT, ReaderT
  CryptoFoundations/       # Crypto primitives and security definitions
    SecExp.lean             # Security experiments (SecExp, SecAdv)
    SymmEncAlg.lean         # Symmetric encryption
    AsymmEncAlg.lean        # Asymmetric encryption
    SignatureAlg.lean       # Signature schemes
    SigmaAlg.lean           # Σ-protocols
    FiatShamir.lean         # Fiat-Shamir transform
    Fork.lean               # Forking lemma (active research — has sorry)
    HardnessAssumptions/    # DDH, DLP, LWE, hard homogeneous spaces
    Asymptotics/            # Negligible functions, polynomial-time
  ProgramLogic/            # WIP: Hoare-style program logic (mostly stubs)
  Prelude.lean             # Declares aesop rule set [UnfoldEvalDist]
Examples/                  # Concrete crypto constructions (OneTimePad is the canonical complete example)
ToMathlib/                 # Upstream candidates for Mathlib (control theory, PFunctor, probability)
LibSodium/                 # FFI to C crypto libraries (experimental)
```

### Module Layering (dependency order)

```
ToMathlib → Prelude → EvalDist/Defs → OracleComp core → OracleComp/EvalDist bridge
  → {SimSemantics, QueryTracking, Constructions, Coercions, ProbComp}
  → CryptoFoundations → Examples
```

New files must respect this DAG. In particular, `EvalDist/` files must never import from `OracleComp/`.

`ProgramLogic/` is a WIP side branch. `Relational/Basic.lean` is an empty namespace, and `Unary/Examples.lean` is generic monad theory. Only `HoareTriple.lean` connects to the main library.

## Core Type Signatures

```lean
-- Oracle specification: just a function from index type to response type
def OracleSpec (ι : Type u) : Type _ := ι → Type v

-- Computation with oracle access: free monad over polynomial functor
def OracleComp {ι : Type u} (spec : OracleSpec ι) : Type w → Type _ :=
  PFunctor.FreeM spec.toPFunctor

-- Oracle implementation: just a function
@[reducible] def QueryImpl (spec : OracleSpec ι) (m : Type u → Type v) :=
  (x : spec.Domain) → m (spec.Range x)

-- Simulation: substitute oracle queries with implementations
def simulateQ [Monad m] (impl : QueryImpl spec m) : OracleComp spec α → m α

-- Pure probabilistic computation (no custom oracles)
abbrev ProbComp := OracleComp unifSpec
```

## Notation Reference

| Notation | Meaning | Defined in |
|----------|---------|------------|
| `Pr[= x \| mx]` | Probability of output `x` (`probOutput`) | `EvalDist/Defs/Basic.lean` |
| `Pr[p \| mx]` | Probability of event `p` (`probEvent`) | `EvalDist/Defs/Basic.lean` |
| `Pr[⊥ \| mx]` | Probability of failure (`probFailure`) | `EvalDist/Defs/Basic.lean` |
| `$ᵗ T` | Uniform type-level sampling (`uniformSample`, requires `SampleableType`) | `Constructions/SampleableType.lean` |
| `$ xs` | Uniform container selection (can fail) | `OracleComp/ProbComp.lean` |
| `$! xs` | Uniform container selection (never fails) | `OracleComp/ProbComp.lean` |
| `$[0..n]` | Uniform selection from `Fin n` | `OracleComp/ProbComp.lean` |
| `spec₁ + spec₂` | Combine oracle specs (was `++ₒ`, now uses standard `+`) | `OracleComp/OracleSpec.lean` |
| `⊂ₒ` | SubSpec relation (auto-lifts via `MonadLift`) | `Coercions/SubSpec.lean` |
| `→ₒ` | Singleton oracle spec `(T →ₒ U)` | `OracleComp/OracleSpec.lean` |
| `[]ₒ` | Empty oracle spec | `OracleComp/OracleSpec.lean` |
| `∘ₛ` | QueryImpl composition | `SimSemantics/Constructions.lean` |
| `⦃P⦄ comp ⦃Q⦄` | Hoare triple (scoped to `OracleComp.StateM`) | `ProgramLogic/Unary/HoareTriple.lean` |

**WARNING**: The README uses `[= x | comp]` notation (without `Pr` prefix) — this is outdated. Always use `Pr[...]`.

### Legacy API Migration (Do / Don't)

| Don't use | Do use |
|-----------|--------|
| `[= x \| comp]` | `Pr[= x \| comp]` |
| `++ₒ` | `+` |
| Commented legacy blocks as templates | Un-commented modern code paths and `Examples/OneTimePad.lean` |

## Critical Gotchas

### 1. `[spec.Fintype]` and `[spec.Inhabited]` are required for probability reasoning

Any file using `evalDist`, `probOutput`, `probEvent`, or `Pr[...]` on `OracleComp spec` needs these instances on the spec. Without them, typeclass resolution silently fails with confusing errors.

### 2. `autoImplicit` is `false` project-wide

Every variable must be explicitly declared. Do not rely on Lean's auto-implicit mechanism.

### 3. Core types are `@[reducible]` thin wrappers

`OracleSpec`, `QueryImpl`, and `OracleComp` are all defined as simple `def`/`abbrev`/`@[reducible]` over `PFunctor` machinery. Lean may unfold them aggressively. Use `OracleComp.inductionOn` / `OracleComp.construct` as canonical eliminators rather than pattern matching on `PFunctor.FreeM.pure`/`roll` directly.

### 4. `evalDist` IS `simulateQ`

They share the exact same code path: `evalDist` is `simulateQ` with `m = PMF` and uniform distributions. This identity is definitional (`rfl`).

### 5. `++ₒ` is dead — use `+`

The README and large amounts of commented-out code use `++ₒ` for combining oracle specs. The current API uses standard `+` (`HAdd`).

### 6. Commented-out code uses OLD API patterns

Files like `Fork.lean`, `HHS_Elgamal.lean`, `HHS_Sigma.lean`, and `RF_RP_Switching_alt.lean` contain large commented-out blocks that use obsolete patterns (`[= x | ...]`, `++ₒ`, `simulate'`, `getM`, `guard` via `Alternative`). **Only follow patterns in uncommented code.** Use `Examples/OneTimePad.lean` as the canonical reference for a completed proof.

### 6b. Preserve partial proof attempts (prefer `stop` over deletion)

When a proof attempt is not finished or is currently broken, prefer leaving the attempted structure in place and insert a local `stop`/checkpoint marker instead of deleting large proof blocks. This preserves search context and failed approaches for later agents to continue from.

### 7. Structure inheritance pattern for crypto primitives

Crypto structures (`SymmEncAlg`, `AsymmEncAlg`, `SignatureAlg`, `SecExp`) extend `OracleContext` or `ExecutionMethod`. Fill parent fields with anonymous field syntax:

```lean
@[simps!] def myAlg : SymmEncAlg ℕ (M := ...) (K := ...) (C := ...) where
  keygen n := ...
  encrypt k m := ...
  decrypt k σ := ...
  __ := unifSpec.defaultContext
```

### 8. Universe polymorphism

`OracleComp` has 3 universe parameters, `SubSpec` has 6. Universe unification errors are common when composing specs or building reductions. When stuck, check universe levels explicitly.

## Proof Patterns

### Tactics

- **`simp`** with project-specific simp lemmas is the starting point (most lemmas in `EvalDist/Monad/` are `@[simp]`)
- **`grind`** is the workhorse tactic. Many lemmas are tagged `@[grind =]` or `@[grind =>]`. The `=`/`=>` annotations matter.
- **`aesop`** with custom rule sets (e.g., `aesop (rule_sets := [UnfoldEvalDist])`) for evaluation/unfolding
- Standard Mathlib tactics (`rw`, `exact`, `apply`, `ext`, `congr`, `calc`) are used throughout

### Lemma Naming

Follow Mathlib convention: `{head_symbol}_{operation}_{rhs_form}`.

Examples: `probOutput_bind_eq_tsum`, `support_pure`, `simulateQ_map`, `evalDist_bind`.

Use `_iff` for biconditionals, `_congr`/`_mono` for relational lemmas, primed variants (`'`) for versions with weaker hypotheses.

### Structure/Class Names

Use UpperCamelCase: `ForkInput`, `QueryImpl`, `SecExp`, `SymmEncAlg`.

## Canonical Examples By Task

- Need a compact modern crypto proof flow (correctness + privacy): start with `Examples/OneTimePad.lean`.
- Working on oracle computation core behavior: read `VCVio/OracleComp/OracleComp.lean`.
- Working on probability/evaluation lemmas: read `VCVio/EvalDist/Monad/Basic.lean`.
- Working on subspec coercions/lifting issues: read `VCVio/OracleComp/Coercions/SubSpec.lean`.
- Touching forking-lemma research code: read uncommented parts of `VCVio/CryptoFoundations/Fork.lean`.

## Building

```bash
lake exe cache get && lake build
```

The `lake exe cache get` step downloads Mathlib's pre-compiled cache and is essential (building Mathlib from source takes hours).

### Adding New Files

After adding a new `.lean` file, run:

```bash
./scripts/update-lib.sh
```

This regenerates the root import files (`VCVio.lean`, `Examples.lean`, `ToMathlib.lean`). CI checks that these are up to date.

Then run `lake build` to verify imports and dependencies are still valid.

### Version Pinning

Lean toolchain and Mathlib version must stay in sync (both currently `v4.28.0`). When upgrading, update both `lean-toolchain` and `lakefile.lean`'s `require mathlib` line simultaneously, then run `lake update`.

### Linters

Several Mathlib-style linters are enabled as weak linters (warn, don't error). `longFile` caps at 1500 lines. The lint CI job is currently commented out in `build.yml`.

## Troubleshooting Quick Hits

### Probability lemmas fail with confusing typeclass errors

Check that your active `spec` has `[spec.Fintype]` and `[spec.Inhabited]` in scope before using `evalDist`, `probOutput`, `probEvent`, or `Pr[...]`.

### Universe mismatch errors around `SubSpec` or composed specs

`OracleComp` and `SubSpec` are highly universe-polymorphic. Introduce explicit universe parameters and explicit type annotations at composition boundaries.

### Unexpected import-cycle or layering failures

Re-check the layering DAG: `EvalDist/` must not import from `OracleComp/`, and new files must respect the stated module order.

## File Size Guideline

Files should stay under 1500 lines (enforced by `linter.style.longFile`). Line length soft limit is 100 characters.
