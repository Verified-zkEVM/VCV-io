# VCVio — AI Agent Guide

Machine-checked cryptographic proofs in Lean, built on Mathlib.

## Fast Start

1. Run `lake exe cache get && lake build`.
2. Read `Examples/OneTimePad/Basic.lean` for a compact modern proof (correctness and privacy).
3. Choose the work area by task: use `VCVio/` for oracle/probability/program-logic work, `LatticeCrypto/` for lattice schemes and reductions, and `LatticeCryptoTest/` for vectors or differential tests.
4. If probability lemmas fail unexpectedly, first check for `[IsProbabilitySpec spec]`
   or `[IsUniformSpec spec]` as appropriate.

`AGENTS.md` is the canonical guide. `CLAUDE.md` is a symlink to this file.

## Attribution, Headers, And Docstrings

Follow [`CONTRIBUTING.md`](CONTRIBUTING.md) for the repo's explicit attribution policy.

- New Lean files should use the standard copyright / license / authors header and a module docstring.
- For ordinary Lean source files, use the standard prologue layout: header, blank line, `module`, public imports, blank line, module docstring.
- Docstrings must be intrinsic and descriptive. Cross-reference live sibling definitions when helpful, but do not mention removed or renamed declarations, change history, or use reactive wording such as "replaces" or "renamed from".
- Preserve existing headers on routine edits.
- Only rewrite attribution when a file is genuinely new or materially replaced.
- Do not add a separate AI-attribution line.
- For inline section breaks within a Lean file, use Mathlib-style doc-comment headers `/-! ## Title -/` (or the multi-line `/-! ## Title \n\n explanation -/` form). **Do not use ASCII banners** such as `-- ====...===` flanking a `-- § Title` line. The `/-!` form is rendered by `doc-gen4`; ASCII banners are not, and they make the file feel artificially partitioned. If a section is large enough to want a loud header, it is usually large enough to want its own `namespace` or its own file. See *Section Headers Within A File* in [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Module Scopes

Active Lean libraries and tests use Lean's module system. Put declarations in a `public section`;
use `public meta section` for tactic and elaborator code. Existing ordinary source files use
`@[expose] public section` so pre-migration downstream definitional equalities remain available; new
files use plain `public section` and expose individual definitions with `@[expose]` where unfolding
is part of the intended API. The per-library count of broadly exposed files is a ceiling
(`scripts/check-expose-boundary.sh`, baseline `scripts/expose_boundary_baseline.tsv`): converting a
file lowers it, and raising it needs an explicit baseline change under review. Executable and
runtime implementation modules should use opaque `public section` when callers do not need to
unfold their definitions.

- Use `public import` for dependencies that form part of the module's transitive public surface and
  `public meta import` for exported tactic/elaborator dependencies.
- Use plain `import` for implementation-only dependencies. A proof module may use `import all` to
  access an unexposed implementation from the same dependency when proving its public API.
- Do not enable `backward.privateInPublic` or `backward.proofsInPublic`; resolve visibility and
  proof-metavariable issues directly.
- Keep the dormant `Interop` library outside this policy until it is migrated separately.

## What This Project Is

VCVio is a framework for formal cryptographic proofs built around `OracleComp spec α`, the free monad on the polynomial functor induced by an oracle signature `OracleSpec ι := ι → Type`. Its universal fold `simulateQ impl : OracleComp spec α → r α` is the unique monad morphism extending any `impl : QueryImpl spec r` to the free monad. For `OracleComp`, `support` is definitionally `simulateQ` into `SetM` with queries interpreted by `Set.univ`; the primary `evalDist` / `𝒟[…]` semantics is a successful-output Mathlib `Measure`, while `evalSPMF` / `𝒮[…]`, `probOutput`, and `Pr[…]` form the discrete compatibility surface backed by `simulateQ` into `PMF` using `[IsProbabilitySpec spec]`. Uniform cardinality lemmas and the `support`/probability bridge use `[IsUniformSpec spec]`, which bundles `[spec.Fintype]`, `[spec.Inhabited]`, and uniform sampling. `ProbComp α := OracleComp unifSpec α` specializes to computations whose only oracle is uniform selection.

The repo also includes a first-class lattice cryptography library under `LatticeCrypto/`, built on top of the `VCVio` framework. That layer contains generic lattice algebra plus ML-DSA, ML-KEM, and Falcon specifications, security statements, concrete implementations, and tests; the native FFI bridges live in the separate `Extern/` library.

## Repo Map

- `VCVio/`: generic oracle-computation framework, program logic, crypto abstractions, and generic reductions.
- `ToMathlib/`: local Mathlib-facing utilities and lemmas intended to remain below the framework layer.
- `Extern/`: native FFI surface — the `@[extern]` bindings (SHA-3/SHAKE, ML-KEM, ML-DSA, Falcon) and the FFI-backed concrete instances that reach them. No proof library may import it; the backing `extern_lib`s become empty stubs when `third_party/` submodules are absent.
- `LatticeCrypto/`: lattice-specific algebra, hardness assumptions, scheme definitions, security theorems, and concrete implementations.
- `HashSig/`: hash-based signatures — SLH-DSA (SPHINCS+, FIPS 205) proof-level specs and security. Peer of `LatticeCrypto/`; depends on `VCVio`/`ToMathlib` but nothing in those imports it back.
- `LatticeCryptoTest/`: ACVP vectors, executable regression tests, and cross-checks against native backends.
- `VCVioTest/`: framework smoke tests and test support modules.
- `VCVioWidgets/`: optional widget experiments and visualizations.
- `VCVioComplexity/`: optional isolated Lake package for the complexitylib-backed exact-machine
  substrate; it is not part of VCVio's default dependency graph.
- `Examples/`: compact framework examples such as OneTimePad, ElGamal, Schnorr, and program-logic tactic walkthroughs.
- `Interop/`: experimental bridges to Rust verification frontends (hax, aeneas). **Strict TCB isolation**: nothing in core VCVio depends on it. See `docs/agents/interop.md`.
- `csrc/`: C FFI shims used for differential testing against native ML-DSA, ML-KEM, and Falcon code.
- `third_party/`: native backends as git submodules; when they are not checked out (fresh clones, Lake dependency checkouts), the native `extern_lib` targets build as empty stub archives.

## Module Layering

For `VCVio/`:

```
ToMathlib → Prelude → EvalDist/Defs → OracleComp core → EvalDist bridge
  → {SimSemantics, QueryTracking, Constructions, Coercions, ProbComp}
  → {ProgramLogic, CryptoFoundations, CryptoFoundations/Asymptotics} → Examples
```

New files must respect this DAG. `EvalDist/` must never import from `OracleComp/`.

For `LatticeCrypto/`, the rough dependency direction is:

```
{Ring/*, DiscreteGaussian}
  → HardnessAssumptions
  → {MLDSA, MLKEM, Falcon}
  → Concrete implementations / security wrappers
  → Extern (FFI bindings + FFI-backed instances)
  → LatticeCryptoTest
```

Scheme-specific code in `LatticeCrypto/` may depend on `VCVio/CryptoFoundations`, but not the other way around.

The native FFI surface lives in `Extern/`: it may import `VCVio`, `LatticeCrypto`,
and `ToMathlib`, but no proof library (`VCVio/`, `ToMathlib/`, `LatticeCrypto/`,
`HashSig/`, `Examples/`, `VCVioWidgets/`, `Interop/`) may import `Extern.…`. That
keeps every proof library — and any downstream Lake project requiring VCVio —
link-safe when the `third_party/` submodules are absent. Enforced by
`scripts/check-extern-isolation.sh` on every PR.

For `Interop/`, the dependency contract is one-way:

```
Interop/{Hax,Aeneas,Rust}/  →  VCVio/, ToMathlib/, (Hax.…), (Aeneas.…)
```

`Interop/**` may **never** be imported from `VCVio/`, `LatticeCrypto/`,
`LatticeCryptoTest/`, `Examples/`, `ToMathlib/`, `Extern/`, `VCVioWidgets/`,
or `VCVioTest/`. This contract is enforced by
`scripts/check-interop-isolation.sh` and the
`Interop TCB Isolation` GitHub workflow on every PR.

## Critical Gotchas

1. **Probability assumptions are explicit.** `support` on `OracleComp spec` works for arbitrary specs. `evalSPMF` / `Pr[...]` need `[IsProbabilitySpec spec]`; `evalDist` / `𝒟[…]` additionally need an ambient `MeasurableSpace` on the result. Uniform/cardinality lemmas and `support ↔ Pr[= _] ≠ 0` need `[IsUniformSpec spec]`. Use `IsUniformSpec.ofFintypeInhabited` when you have `[spec.Fintype] [spec.Inhabited]` and intend uniform semantics.
2. **`autoImplicit = false` is set globally in `lakefile.lean`**. Do not add `set_option autoImplicit false` in individual files. Every variable must be explicitly declared.
3. **`evalSPMF` IS `simulateQ`** with `IsProbabilitySpec.toPMF`; under `[IsUniformSpec spec]` this is uniform. This is definitional (`rfl`). `evalDist` is its successful-output measure façade on the discrete compatibility path and agrees with the direct `FreeM.denote` measure fold when both specifications are present. These identities are internal to `VCVio/EvalDist/**` and `VCVio/OracleComp/**`: code outside those directories crosses them through the public equation lemmas (`evalSPMF_eq_simulateQ`, `probOutput_def`, `support_def`). Existing downstream `rfl` uses are grandfathered; new proofs use the public equations.
4. **`++ₒ` is dead** — use `+` for combining oracle specs.
5. **Commented-out code is legacy** — follow only uncommented code. Use `Examples/OneTimePad/Basic.lean` as canonical reference.
6. **Preserve partial proofs** with `stop` instead of deleting large proof blocks.
7. **Do not disable linters to silence errors**. Do not use `set_option linter.* false`, `set_option weak.linter.* false`, or add repo-level `leanOptions` that turn lints off to dodge a fixable issue. Fix the root cause instead. (The one deliberate, documented exception is `weak.linter.unicodeLinter, false` in `lakefile.lean`, off so FIPS-204 math notation and diacritics in cited author names are allowed.)
8. **Interop TCB isolation is mandatory**. Core VCVio (`VCVio/`, `ToMathlib/`, `LatticeCrypto/`, `Examples/`, `LatticeCryptoTest/`, `Extern/`, `VCVioWidgets/`, `VCVioTest/`) must never `import Interop.…`, `import Hax.…`, or `import Aeneas.…`. CI fails the PR if it does. See `docs/agents/interop.md`.
9. **Extern link-safety isolation is mandatory**. Proof libraries (`VCVio/`, `ToMathlib/`, `LatticeCrypto/`, `HashSig/`, `Examples/`, `VCVioWidgets/`, `Interop/`) must never `import Extern.…`: the native backends behind it are built as empty stubs whenever the `third_party/` submodules are absent — always the case for Lake dependency checkouts — so importing `Extern` would break downstream executable links. Test libraries may import it. Enforced by `scripts/check-extern-isolation.sh` in CI.

10. **`PMF`/`SPMF` is a retiring surface, not a coequal representation.** Upstream is dismantling `PMF` construction by construction — the pinned Mathlib already deprecates `PMF.bernoulli` and `PMF.binomial` for measure-valued replacements. New semantic code uses `Measure`/`Kernel`; a change that touches a file still carrying explicit `PMF`/`SPMF` identifiers should leave that source count lower than it found it. `scripts/check-pmf-boundary.sh` enforces a per-file ceiling on every build (a file absent from the baseline has an allowance of zero) and reports the actual source-count trend against the base ref on every pull request; comments and string literals do not count. This is a syntactic migration proxy, not semantic dependency analysis. `SPMF` counts because `SPMF := OptionT PMF`. `--ratchet` is the opt-in mode for a deliberate reduction pass, with holds recorded in `scripts/pmf_boundary_holds.tsv`. See `docs/reading/denotational-probability-semantics.md`.

For the full list, see `docs/agents/gotchas.md`.

## Naming Conventions

Follow Mathlib convention: `{head_symbol}_{operation}_{rhs_form}`.
Examples: `probOutput_bind_eq_tsum`, `support_pure`, `simulateQ_map`.
Structures use UpperCamelCase: `SecExp`, `SymmEncAlg`, `RelTriple`.

## Canonical Examples

- Compact modern crypto proof: `Examples/OneTimePad/Basic.lean`
- ElGamal IND-CPA via the generic one-time DDH lift: `Examples/ElGamal/Basic.lean`
- Schnorr sigma protocol (completeness, soundness, HVZK): `Examples/Schnorr/SigmaProtocol.lean`
- Oracle computation core: `VCVio/OracleComp/OracleComp.lean`
- Probability lemmas: `VCVio/EvalDist/Monad/Basic.lean`
- SubSpec / coercions: `VCVio/OracleComp/Coercions/SubSpec.lean`
- `QueryImpl` instrumentation primitives (`preInsert` / `postInsert` and their bridge lemmas): `VCVio/OracleComp/SimSemantics/QueryImpl/Constructions.lean`. Prefer these (or their downstream wrappers `withTraceBefore` / `withTrace` / `withCost` / `withLogging`) when wrapping a `QueryImpl` with a per-query side effect, so the generic theory in that file applies.
- DLog / CDH / DDH via HHS: `VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`
- Cost model / polynomial time: `VCVio/OracleComp/QueryTracking/CostModel.lean`
- Query cost / weighted expected cost: `VCVio/OracleComp/QueryTracking/QueryCost.lean`, `VCVio/OracleComp/QueryTracking/WriterCost.lean`
- Quantitative realizability, syntactic resource traces, and generic polynomial resource
  certificates:
  `PolyFun/Realizability/Quantitative.lean`,
  `PolyFun/Realizability/Quantitative/Resource.lean`
- Strict backend-relative oracle PPT crypto facade:
  `VCVio/CryptoFoundations/Asymptotics/ComputationalComplexity.lean`
- Proof-bearing oracle-handler closure seam:
  `VCVio/CryptoFoundations/Asymptotics/OracleClosure.lean`
- Conservative PPT certificate lookup:
  `VCVio/CryptoFoundations/Asymptotics/ComplexityTactics.lean`
- Syntactic ElGamal complexity canary:
  `Examples/ElGamal/ComputationalComplexity.lean`
- Optional exact complexitylib machine substrate:
  `VCVioComplexity/VCVioComplexity/Backend/TuringMachine.lean`
- Complexitylib polynomial adapter and end-to-end pure canary:
  `VCVioComplexity/VCVioComplexity/Backend/Polynomial.lean`,
  `VCVioComplexity/VCVioComplexity/Backend/PureCanary.lean`
- End-to-end complexitylib canary with one enabled fair-coin query:
  `VCVioComplexity/VCVioComplexity/Backend/OracleCanary.lean`
- Asymptotic security games: `VCVio/CryptoFoundations/Asymptotics/Security.lean`
- Negligible function algebra: `VCVio/CryptoFoundations/Asymptotics/Negligible.lean`
- Query enforcement: `VCVio/OracleComp/QueryTracking/Enforcement.lean`
- Seeded (Bellare-Neven) forking lemma: `VCVio/CryptoFoundations/SeededFork.lean`
- Replay-based forking lemma: `VCVio/CryptoFoundations/ReplayFork.lean`
- Independent products of computations: `VCVio/EvalDist/IndepProduct.lean`
- Drawing without replacement and its expected draw count: `VCVio/OracleComp/Constructions/WithoutReplacement.lean`, `ToMathlib/Probability/NegativeHypergeometric.lean`
- Expected values of `ℝ≥0∞`-valued functionals: `VCVio/EvalDist/Expectation.lean`
- Fischlin transform: `VCVio/CryptoFoundations/Fischlin/` (`Defs`, `CostAccounting`, `Completeness`, `KnowledgeSoundness`)
- Interaction type tree and path: `PolyFun/Interaction/Basic/TypeTree.lean`
- Two-party roles and strategies: `PolyFun/Interaction/TwoParty/Strategy.lean`
- Two-party composition and factorization: `PolyFun/Interaction/TwoParty/Compose.lean`
- Multiparty local views: `PolyFun/Interaction/Multiparty/Core.lean`
- Concurrent specs and frontiers: `PolyFun/Interaction/Concurrent/Spec.lean`, `PolyFun/Interaction/Concurrent/Frontier.lean`
- Concurrent processes and execution: `PolyFun/Interaction/Concurrent/Process.lean`
- Open systems (interfaces, composition): `PolyFun/Interaction/UC/OpenTheory.lean`
- Open processes (boundary traffic, UC bridge): `PolyFun/Interaction/UC/OpenProcess.lean` (monad-parametric `OpenProcess m Party Δ` with intrinsic `stepSampler` field and `OpenStep.boundaryTrace`)
- Concrete open-theory model: `PolyFun/Interaction/UC/OpenProcessModel.lean` (`openTheory Party m schedulerSampler` threads `TypeTree.Sampler` through `map` / `par` / `wire` / `plug`)
- UC emulation and security: `PolyFun/Interaction/UC/Emulates.lean`
- Computational UC observation layer: `VCVio/Interaction/UC/Computational.lean`
- Per-node samplers as data (`TypeTree.Sampler m tree` = `Decoration (fun X => m X) tree`): `PolyFun/Interaction/Basic/Sampler.lean`
- `TypeTree.Fintype` / `TypeTree.Nonempty` ornaments + canonical uniform sampler: `PolyFun/Interaction/Basic/TypeTreeFintype.lean`, `VCVio/Interaction/UC/Runtime.lean`
- Oracle-aware runtime semantics (monad-parametric process execution, `processSemanticsOracle`): `VCVio/Interaction/UC/Runtime.lean` (no `sampler` argument; pulled from `process.stepSampler`)
- End-to-end UC `ObservedCompEmulates 0` at a three-port boundary: `Examples/OneTimePad/UC.lean`
- Interaction examples: `PolyFunTest/Interaction/TwoParty/Examples.lean`, `PolyFunTest/Interaction/Multiparty/Examples.lean`, `PolyFunTest/Interaction/Concurrent/Examples.lean`
- Program logic tactics: `VCVio/ProgramLogic/Tactics.lean`
- Program logic tactic walkthroughs: `Examples/ProgramLogic/`
- Generic lattice ring layer: `LatticeCrypto/Ring/Core.lean`, `LatticeCrypto/Ring/Kernel.lean`, `LatticeCrypto/Ring/VectorBackend.lean`, `LatticeCrypto/Ring/Transform.lean`, `LatticeCrypto/Ring/NTTCert.lean` (matrix and structural butterfly-stage certificates), `LatticeCrypto/Ring/Norms.lean`, `LatticeCrypto/Ring/Rounding.lean`
- ML-DSA proof-level IDS: `LatticeCrypto/MLDSA/Scheme.lean`
- ML-DSA FIPS signing layer: `LatticeCrypto/MLDSA/Signature.lean`
- ML-KEM internal deterministic core: `LatticeCrypto/MLKEM/Internal.lean`
- ML-KEM top-level KEM wrapper: `LatticeCrypto/MLKEM/KEM.lean`
- Falcon GPV instantiation: `LatticeCrypto/Falcon/Scheme.lean`
- Lattice hardness assumptions: `LatticeCrypto/HardnessAssumptions/LearningWithErrors.lean`, `LatticeCrypto/HardnessAssumptions/ShortIntegerSolution.lean`
- Differential and vector tests: `LatticeCryptoTest/`
- Rust verification interop (hax / aeneas): `Interop/Rust/Common.lean`, `Interop/README.md`, `scripts/check-interop-isolation.sh`

## Program Logic Tactics

For new program-logic proofs, import `VCVio.ProgramLogic.Tactics`.
`VCVio.ProgramLogic.Notation` keeps notation plus compatibility macros, but
`Tactics.lean` is the canonical interactive proof mode.

For the tactic reference, proof-mode entry points, and workflow details, see
[`docs/agents/program-logic.md`](docs/agents/program-logic.md). The two
`@[vcspec]` and `@[wpStep]` registries are indexed via
`Lean.Meta.Sym.Pattern` / `Lean.Meta.Sym.DiscrTree`. `Sym.*` is under active
development in core Lean; see the *Internal Architecture* and *SymM
Stability Note* sections of that doc for the churn classes to watch at each
toolchain bump and the re-entry plan for the deferred symbolic
rewriter bridge (when it lands, `Sym.Simp.mkTheoremFromDecl` rebuilds the
bundle on demand).

## Building

```bash
lake exe cache get && lake build
```

`lake build` builds the seven proof libraries (the default targets); `lake build VCVio` is
the fast path for framework-only work. `./scripts/validate.sh` runs the per-PR CI checks
locally in CI's order (build and warning budget, umbrella check, boundary ratchets, style
linters, agent-docs checks); `--lint` adds `lake lint` (Batteries' environment linters over
the proof libraries, with the grandfathered findings listed in `scripts/nolints.json`: a
shrink-only baseline like the axiom one, so a fixed finding is removed from the file and a
new one fails the lint), `--test` adds `lake test` (the three test libraries, the smoke test,
and the SLH-DSA test executables), `--ffi` adds the native ML-KEM / ML-DSA / Falcon
executables to `--test`, and `--axioms` adds the axiom sweep.

CI runs the timed build on the non-test Lean libraries:
`ToMathlib`, `VCVio`, `LatticeCrypto`, `Extern`, `HashSig`, `Examples`,
and `VCVioWidgets`. The dormant `Interop` target remains excluded.
The timing report parses per-file build times only for that same set.
Test libraries and test executables are not part of the timed build; CI only
times the smoke module separately with `lake env lean VCVioTest/Smoke.lean`.

After the build, CI runs `./scripts/test-axiomsweep.sh` and then
`lake exe axiomsweep --check`: kernel-level axiom/`sorry` accounting for every
declaration in the non-test libraries, gated against the committed baseline
`scripts/axiom_baseline.json`. It fails on *new* `sorryAx` or non-standard-axiom
taint; after intentionally adding or closing a `sorry`, run
`lake exe axiomsweep --update-baseline` and commit the diff. `Interop` (the
declared TCB) is excluded — its boundary is enforced by the import-isolation
gate instead.

The baseline is an allowlist for `sorryAx` debt only. Native trust
(`native_decide`, which mints per-declaration `._native.` axioms) is held to a
zero-debt rule: anything outside the explicit `grandfatheredNativeTrust` list in
`scripts/AxiomSweep.lean` fails `--check` and cannot be greened by editing the
baseline, since accepting it would widen the trusted computing base. The
`VCVioAxiomSweepTestFixtures` library carries synthetic taint for the tool's own
tests and is deliberately excluded from every aggregate.

After adding new `.lean` files: `./scripts/update-lib.sh` (CI's `scripts/check-imports.sh`
fails when a regenerated umbrella would differ from the committed one).

Lean toolchain and Mathlib must stay in sync (both currently `v4.33.1`); the bump procedure
is in `CONTRIBUTING.md`. Keep files reasonably sized: Mathlib's file-length linter is on at
its default of 1500 lines, and each file above that carries a trailing
`set_option linter.style.longFile <ceiling>` (the linter's own ratchet: the ceiling only
moves down as the file is split, and the linter rejects a ceiling that is too generous).

## Further Reading

Before working in a specific area, read the relevant guide in `docs/agents/`:

- **Interaction runtime and UC integration**: [`docs/agents/interaction.md`](docs/agents/interaction.md)
- **Interop with Rust verification frontends (hax, aeneas)**: [`docs/agents/interop.md`](docs/agents/interop.md)
- **LatticeCrypto layout and workflows**: [`docs/agents/lattice.md`](docs/agents/lattice.md)
- **OracleComp / SubSpec / SimSemantics**: [`docs/agents/oracle-comp.md`](docs/agents/oracle-comp.md)
- **Query tracking / weighted cost / expected runtime**: [`docs/agents/query-tracking.md`](docs/agents/query-tracking.md)
- **Honest computational-complexity design and implementation status**:
  [`docs/design/computational-complexity.md`](docs/design/computational-complexity.md)
- **SLH-DSA general-`d` formalization, FIPS 205 conformance, KAT, and security stack plan**:
  [`docs/design/slh-dsa-fips205-generalization.md`](docs/design/slh-dsa-fips205-generalization.md)
- **Probability reasoning (EvalDist, ProbComp)**: [`docs/agents/probability.md`](docs/agents/probability.md)
- **Crypto primitives and reductions**: [`docs/agents/crypto.md`](docs/agents/crypto.md)
- **End-to-end crypto examples**: [`docs/agents/end-to-end-examples.md`](docs/agents/end-to-end-examples.md)
- **Program logic tactics**: [`docs/agents/program-logic.md`](docs/agents/program-logic.md)
- **All notation**: [`docs/agents/notation.md`](docs/agents/notation.md)
- **Proof workflows (game-hopping, reductions)**: [`docs/agents/proof-workflows.md`](docs/agents/proof-workflows.md)
- **Gotchas and troubleshooting**: [`docs/agents/gotchas.md`](docs/agents/gotchas.md)
- **Module visibility and the PolyFun façade**: [`docs/agents/module-system.md`](docs/agents/module-system.md)
- **Upstream alignment ledger (what Mathlib/core/cslib/PolyFun already own, with verdicts)**:
  [`docs/reading/upstream-alignment.md`](docs/reading/upstream-alignment.md)
