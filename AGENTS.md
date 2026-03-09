# VCV-io — AI Agent Guide

Formally verified cryptography proofs in Lean 4, built on Mathlib.

## Fast Start

1. Run `lake exe cache get && lake build`.
2. Read `Examples/OneTimePad.lean` for a compact modern proof (correctness and privacy).
3. Keep `VCVio/` as your default work area.
4. If probability lemmas fail unexpectedly, first check for `[spec.Fintype]` and `[spec.Inhabited]`.

`AGENTS.md` is the canonical guide. `CLAUDE.md` is a symlink to this file.

## What This Project Is

VCV-io provides `OracleComp spec α`, a monadic type for oracle-access computations (free monad over `OracleSpec`), with `simulateQ` for operational semantics and `evalDist` for denotational semantics (probability distributions). `ProbComp α` is the abbreviation for `OracleComp unifSpec α`.

## Module Layering

```
ToMathlib → Prelude → EvalDist/Defs → OracleComp core → EvalDist bridge
  → {SimSemantics, QueryTracking, Constructions, Coercions, ProbComp}
  → CryptoFoundations → Examples
```

New files must respect this DAG. `EvalDist/` must never import from `OracleComp/`.

## Critical Gotchas

1. **`[spec.Fintype]` and `[spec.Inhabited]`** are required for probability reasoning (`evalDist`, `Pr[...]`).
2. **`autoImplicit` is `false`** project-wide. Every variable must be explicitly declared.
3. **`evalDist` IS `simulateQ`** with uniform distributions. This is definitional (`rfl`).
4. **`++ₒ` is dead** — use `+` for combining oracle specs.
5. **Commented-out code is legacy** — follow only uncommented code. Use `Examples/OneTimePad.lean` as canonical reference.
6. **Preserve partial proofs** with `stop` instead of deleting large proof blocks.

For the full list, see `docs/agents/gotchas.md`.

## Naming Conventions

Follow Mathlib convention: `{head_symbol}_{operation}_{rhs_form}`.
Examples: `probOutput_bind_eq_tsum`, `support_pure`, `simulateQ_map`.
Structures use UpperCamelCase: `SecExp`, `SymmEncAlg`, `RelTriple`.

## Canonical Examples

- Compact modern crypto proof: `Examples/OneTimePad.lean`
- ElGamal IND-CPA via DDH (hybrid argument): `Examples/ElGamal.lean`
- Schnorr sigma protocol (completeness, soundness, HVZK): `Examples/Schnorr.lean`
- Oracle computation core: `VCVio/OracleComp/OracleComp.lean`
- Probability lemmas: `VCVio/EvalDist/Monad/Basic.lean`
- SubSpec / coercions: `VCVio/OracleComp/Coercions/SubSpec.lean`
- DLog / CDH / DDH assumptions: `VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`
- Forking lemma research: `VCVio/CryptoFoundations/Fork.lean`

## Building

```bash
lake exe cache get && lake build
```

After adding new `.lean` files: `./scripts/update-lib.sh`

Lean toolchain and Mathlib must stay in sync (both currently `v4.28.0`). Files should stay under 1500 lines.

## Further Reading

Before working in a specific area, read the relevant guide in `docs/agents/`:

- **OracleComp / SubSpec / SimSemantics**: [`docs/agents/oracle-comp.md`](docs/agents/oracle-comp.md)
- **Probability reasoning (EvalDist, ProbComp)**: [`docs/agents/probability.md`](docs/agents/probability.md)
- **Crypto primitives and reductions**: [`docs/agents/crypto.md`](docs/agents/crypto.md)
- **Program logic tactics**: [`docs/agents/program-logic.md`](docs/agents/program-logic.md)
- **All notation**: [`docs/agents/notation.md`](docs/agents/notation.md)
- **Proof workflows (game-hopping, reductions)**: [`docs/agents/proof-workflows.md`](docs/agents/proof-workflows.md)
- **Gotchas and troubleshooting**: [`docs/agents/gotchas.md`](docs/agents/gotchas.md)
