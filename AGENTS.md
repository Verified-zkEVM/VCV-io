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
  → {ProgramLogic, CryptoFoundations, CryptoFoundations/Asymptotics} → Examples
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
- DLog / CDH / DDH via HHS: `VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`
- Cost model / polynomial time: `VCVio/OracleComp/QueryTracking/CostModel.lean`
- Asymptotic security games: `VCVio/CryptoFoundations/Asymptotics/Security.lean`
- Negligible function algebra: `VCVio/CryptoFoundations/Asymptotics/Negligible.lean`
- Query enforcement: `VCVio/OracleComp/QueryTracking/Enforcement.lean`
- Forking lemma research: `VCVio/CryptoFoundations/Fork.lean`
- Fischlin transform: `VCVio/CryptoFoundations/Fischlin.lean`
- Program logic tactics: `VCVio/ProgramLogic/Tactics.lean`

## Program Logic Tactics

For new program-logic proofs, import `VCVio.ProgramLogic.Tactics`.
`VCVio.ProgramLogic.Notation` keeps notation plus coarse compatibility macros, but
`Tactics.lean` is the canonical interactive proof mode.

Internally the implementation is split between
`VCVio/ProgramLogic/Tactics/Unary.lean` and
`VCVio/ProgramLogic/Tactics/Relational.lean`;
the umbrella import is still the intended default.

- **Proof-mode entry**: `by_equiv`, `game_trans`, `by_dist`, `by_upto`, `by_hoare`
- **Relational stepping**: `rvcgen_step`, `rvcgen`,
  `rel_conseq`, `rel_inline`, `rel_dist`
- **Unary stepping**: `wp_step` (raw `wp` goals), `qvcgen_step` (`Triple` or probability goals,
  spec-aware, auto probability lowering), `qvcgen_step inv I` (explicit loop invariant)
- **Unary exhaustive**: `qvcgen` (exhaustive `Triple` / probability goal decomposition with
  auto lowering, auto loop invariants, support-cut synthesis, and support/indicator leaf closure),
  `qvcgen using cut` (one explicit bind step then exhaustive), `qvcgen inv I` (explicit loop
  invariant then exhaustive)
  (`wp_step` / `qvcgen_step` also understand bounded iteration via `replicate`, `List.mapM`,
  and `List.foldlM`)
- **Expectation normalization**: `exp_norm`
- **Probability equalities**: plain `qvcgen_step` heuristically dispatches swap / congruence on
  `Pr[...] = Pr[...]` goals; use `qvcgen_step rw`, `qvcgen_step rw under n`,
  `qvcgen_step rw congr`, and `qvcgen_step rw congr'` for explicit control.

Quick usage notes:

- `by_equiv` enters the coupling-based `RelTriple` shell intentionally.
- `rvcgen_step` lowers `GameEquiv` / `evalDist` equality goals into `RelTriple`,
  then tries the obvious relational rule for the current shape.
- `rvcgen_step using t` interprets `t` by goal shape:
  bind cut relation, random/query bijection, traversal input relation,
  or `simulateQ` state invariant.
- `rvcgen` repeats relational VCGen across all open goals until stuck.
  When exactly one local hypothesis works as a `using` hint, `rvcgen_step` / `rvcgen`
  auto-consume it. If 0 or ≥ 2 viable hints exist, ambiguity is kept explicit.
  The relational finish pass also handles postcondition weakening
  (`relTriple_post_mono` + assumption) automatically.
- `qvcgen_step` accepts both `Triple` and probability goals (`Pr[p | oa] = 1`,
  `Pr[= x | oa] = 1`, etc.), automatically lowering probability goals into the `Triple`
  engine before decomposing.
- `qvcgen using cut` performs one explicit bind step with `cut`, then runs the exhaustive driver.
- `qvcgen inv I` applies an explicit loop invariant `I`, then runs the exhaustive driver.
- `qvcgen_step using cut` specifies an explicit intermediate postcondition for a bind step.
- `qvcgen_step inv I` applies a loop invariant `I` to a `replicate`/`foldlM`/`mapM` goal,
  leaving pre-to-invariant, step-preservation, and invariant-to-post subgoals.
- `qvcgen_step rw` performs one explicit bind-swap rewrite; `qvcgen_step rw under n` keeps
  `n` shared outer binds fixed while swapping deeper draws on one side.
- `qvcgen_step rw congr` exposes one shared bind plus its support hypothesis;
  `qvcgen_step rw congr'` exposes one shared bind without the support hypothesis.
- `qvcgen` auto-detects loop invariants: when a `Triple I (replicate n oa) (fun _ => I)` goal
  (or `foldlM`/`mapM` equivalent) has a step-preservation hypothesis in context, it applies
  `triple_replicate_inv` / `triple_list_foldlM_inv` / `triple_list_mapM_inv` automatically.
- `qvcgen` final pass also tries `triple_support`, `triple_propInd_of_support`,
  `triple_probEvent_eq_one`, and `triple_probOutput_eq_one` for support-sensitive leaf closure.
- `rvcgen_step` covers synchronized `replicate`, `List.mapM`, and `List.foldlM`
  goals directly; use `using Rin` for non-equality input relations on the traversal/fold cases.
- `qvcgen_step` auto-lowers probability goals, then decomposes a `Triple` bind,
  auto-closes the spec subgoal via `solve_by_elim`, falls back to backward WP
  (`triple_bind_wp`), handles `ite`/`dite`/`match` splitting, and auto-detects loop
  invariants for `replicate`/`foldlM`/`mapM`.
- `qvcgen` is the exhaustive driver: lowers probability goals, decomposes `Triple` goals
  across all open branches, closes spec subgoals and loop invariants from context,
  synthesizes support-based intermediate postconditions when no explicit spec is available,
  normalizes residual `wp` terms, applies support/indicator leaf closure, then runs bounded
  local consequence search.
- `exp_norm` normalizes indicator (`propInd`) and expectation (`wp`) arithmetic.
- `by_upto bad` applies the existing identical-until-bad TV-distance bound for `simulateQ`.

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
