# VCV-io — AI Agent Guide

Formally verified cryptography proofs in Lean 4, built on Mathlib.

## Fast Start

1. Run `lake exe cache get && lake build`.
2. Read `Examples/OneTimePad/Basic.lean` for a compact modern proof (correctness and privacy).
3. Choose the work area by task: use `VCVio/` for oracle/probability/program-logic work, `LatticeCrypto/` for lattice schemes and reductions, and `LatticeCryptoTest/` for vectors or differential tests.
4. If probability lemmas fail unexpectedly, first check for `[spec.Fintype]` and `[spec.Inhabited]`.

`AGENTS.md` is the canonical guide. `CLAUDE.md` is a symlink to this file.

## Attribution, Headers, And Docstrings

Follow [`CONTRIBUTING.md`](CONTRIBUTING.md) for the repo's explicit attribution policy.

- New Lean files should use the standard copyright / license / authors header and a module docstring.
- For ordinary Lean source files, use the standard prologue layout: header, blank line, imports, blank line, module docstring.
- Docstrings must be intrinsic and descriptive. Cross-reference live sibling definitions when helpful, but do not mention removed or renamed declarations, change history, or use reactive wording such as "replaces" or "renamed from".
- Preserve existing headers on routine edits.
- Only rewrite attribution when a file is genuinely new or materially replaced.
- Do not add a separate AI-attribution line.

## What This Project Is

VCV-io provides `OracleComp spec α`, a monadic type for oracle-access computations (free monad over `OracleSpec`), with `simulateQ` for operational semantics and `evalDist` for denotational semantics (probability distributions). `ProbComp α` is the abbreviation for `OracleComp unifSpec α`.

The repo also includes a first-class lattice cryptography library under `LatticeCrypto/`, built on top of the `VCVio` framework. That layer contains generic lattice algebra plus ML-DSA, ML-KEM, and Falcon specifications, security statements, concrete implementations, FFI bridges, and tests.

## Repo Map

- `VCVio/`: generic oracle-computation framework, program logic, crypto abstractions, and generic reductions.
- `LatticeCrypto/`: lattice-specific algebra, hardness assumptions, scheme definitions, security theorems, and concrete implementations.
- `LatticeCryptoTest/`: ACVP vectors, executable regression tests, and cross-checks against native backends.
- `Examples/`: compact framework examples such as OneTimePad, ElGamal, and Schnorr.
- `csrc/`: C FFI shims used for differential testing against native ML-DSA, ML-KEM, and Falcon code.
- `third_party/`: vendored native backends used by the FFI and test harnesses.

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
  → LatticeCryptoTest
```

Scheme-specific code in `LatticeCrypto/` may depend on `VCVio/CryptoFoundations`, but not the other way around.

## Critical Gotchas

1. **`[spec.Fintype]` and `[spec.Inhabited]`** are required for probability reasoning (`evalDist`, `Pr[...]`).
2. **`autoImplicit = false` is set globally in `lakefile.lean`**. Do not add `set_option autoImplicit false` in individual files. Every variable must be explicitly declared.
3. **`evalDist` IS `simulateQ`** with uniform distributions. This is definitional (`rfl`).
4. **`++ₒ` is dead** — use `+` for combining oracle specs.
5. **Commented-out code is legacy** — follow only uncommented code. Use `Examples/OneTimePad/Basic.lean` as canonical reference.
6. **Preserve partial proofs** with `stop` instead of deleting large proof blocks.
7. **Do not disable linters to silence errors**. Do not use `set_option linter.* false`, `set_option weak.linter.* false`, or add repo-level `leanOptions` that turn lints off. Fix the root cause instead.

For the full list, see `docs/agents/gotchas.md`.

## Naming Conventions

Follow Mathlib convention: `{head_symbol}_{operation}_{rhs_form}`.
Examples: `probOutput_bind_eq_tsum`, `support_pure`, `simulateQ_map`.
Structures use UpperCamelCase: `SecExp`, `SymmEncAlg`, `RelTriple`.

## Canonical Examples

- Compact modern crypto proof: `Examples/OneTimePad/Basic.lean`
- ElGamal IND-CPA via DDH (hybrid argument): `Examples/ElGamal/Basic.lean`
- Schnorr sigma protocol (completeness, soundness, HVZK): `Examples/Schnorr.lean`
- Oracle computation core: `VCVio/OracleComp/OracleComp.lean`
- Probability lemmas: `VCVio/EvalDist/Monad/Basic.lean`
- SubSpec / coercions: `VCVio/OracleComp/Coercions/SubSpec.lean`
- DLog / CDH / DDH via HHS: `VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`
- Cost model / polynomial time: `VCVio/OracleComp/QueryTracking/CostModel.lean`
- Query runtime / weighted expected cost: `VCVio/OracleComp/QueryTracking/QueryRuntime.lean`
- Asymptotic security games: `VCVio/CryptoFoundations/Asymptotics/Security.lean`
- Negligible function algebra: `VCVio/CryptoFoundations/Asymptotics/Negligible.lean`
- Query enforcement: `VCVio/OracleComp/QueryTracking/Enforcement.lean`
- Forking lemma research: `VCVio/CryptoFoundations/Fork.lean`
- Fischlin transform: `VCVio/CryptoFoundations/Fischlin.lean`
- Interaction spec and transcript: `VCVio/Interaction/Basic/Spec.lean`
- Two-party roles and strategies: `VCVio/Interaction/TwoParty/Strategy.lean`
- Two-party composition and factorization: `VCVio/Interaction/TwoParty/Compose.lean`
- Multiparty local views: `VCVio/Interaction/Multiparty/Core.lean`
- Concurrent specs and frontiers: `VCVio/Interaction/Concurrent/Spec.lean`, `VCVio/Interaction/Concurrent/Frontier.lean`
- Concurrent processes and execution: `VCVio/Interaction/Concurrent/Process.lean`
- Open systems (interfaces, composition): `VCVio/Interaction/UC/OpenTheory.lean`
- Open processes (boundary traffic, UC bridge): `VCVio/Interaction/UC/OpenProcess.lean`
- Concrete open-theory model: `VCVio/Interaction/UC/OpenProcessModel.lean`
- UC emulation and security: `VCVio/Interaction/UC/Emulates.lean`
- Computational UC observation layer: `VCVio/Interaction/UC/Computational.lean`
- Oracle-aware runtime semantics (monad-parametric process execution, `processSemanticsOracle`): `VCVio/Interaction/UC/Runtime.lean`
- Interaction examples: `VCVio/Interaction/TwoParty/Examples.lean`, `VCVio/Interaction/Multiparty/Examples.lean`, `VCVio/Interaction/Concurrent/Examples.lean`
- Program logic tactics: `VCVio/ProgramLogic/Tactics.lean`
- Generic lattice ring layer: `LatticeCrypto/Ring/Core.lean`, `LatticeCrypto/Ring/Kernel.lean`, `LatticeCrypto/Ring/VectorBackend.lean`, `LatticeCrypto/Ring/Transform.lean`, `LatticeCrypto/Ring/Norms.lean`, `LatticeCrypto/Ring/Rounding.lean`
- ML-DSA proof-level IDS: `LatticeCrypto/MLDSA/Scheme.lean`
- ML-DSA FIPS signing layer: `LatticeCrypto/MLDSA/Signature.lean`
- ML-KEM internal deterministic core: `LatticeCrypto/MLKEM/Internal.lean`
- ML-KEM top-level KEM wrapper: `LatticeCrypto/MLKEM/KEM.lean`
- Falcon GPV instantiation: `LatticeCrypto/Falcon/Scheme.lean`
- Lattice hardness assumptions: `LatticeCrypto/HardnessAssumptions/LearningWithErrors.lean`, `LatticeCrypto/HardnessAssumptions/ShortIntegerSolution.lean`
- Differential and vector tests: `LatticeCryptoTest/`

## Program Logic Tactics

For new program-logic proofs, import `VCVio.ProgramLogic.Tactics`.
`VCVio.ProgramLogic.Notation` keeps notation plus compatibility macros, but
`Tactics.lean` is the canonical interactive proof mode.

For the tactic reference, proof-mode entry points, and workflow details, see
[`docs/agents/program-logic.md`](docs/agents/program-logic.md).

## Building

```bash
lake exe cache get && lake build
```

After adding new `.lean` files: `./scripts/update-lib.sh`

Lean toolchain and Mathlib must stay in sync (both currently `v4.28.0`). Files should stay under 1500 lines.

## Further Reading

Before working in a specific area, read the relevant guide in `docs/agents/`:

- **Interaction framework (specs, roles, concurrency)**: [`docs/agents/interaction.md`](docs/agents/interaction.md)
- **LatticeCrypto layout and workflows**: [`docs/agents/lattice.md`](docs/agents/lattice.md)
- **OracleComp / SubSpec / SimSemantics**: [`docs/agents/oracle-comp.md`](docs/agents/oracle-comp.md)
- **Query tracking / weighted cost / expected runtime**: [`docs/agents/query-tracking.md`](docs/agents/query-tracking.md)
- **Probability reasoning (EvalDist, ProbComp)**: [`docs/agents/probability.md`](docs/agents/probability.md)
- **Crypto primitives and reductions**: [`docs/agents/crypto.md`](docs/agents/crypto.md)
- **Program logic tactics**: [`docs/agents/program-logic.md`](docs/agents/program-logic.md)
- **All notation**: [`docs/agents/notation.md`](docs/agents/notation.md)
- **Proof workflows (game-hopping, reductions)**: [`docs/agents/proof-workflows.md`](docs/agents/proof-workflows.md)
- **Gotchas and troubleshooting**: [`docs/agents/gotchas.md`](docs/agents/gotchas.md)
