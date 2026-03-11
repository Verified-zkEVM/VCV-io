# Gotchas and Troubleshooting

## Critical (Will Bite You Immediately)

### 1. `[spec.Fintype]` and `[spec.Inhabited]` required for probability

Any file using `evalDist`, `probOutput`, `probEvent`, or `Pr[...]` on `OracleComp spec` needs these instances on the spec. Without them, typeclass resolution silently fails with confusing errors.

**Symptom**: "failed to synthesize instance" mentioning `Fintype` or `PFunctor.Fintype`.

**Fix**: Add `[spec.Fintype] [spec.Inhabited]` to your variable/hypothesis list.

### 2. `autoImplicit` is `false` project-wide

Every variable must be explicitly declared. Do not rely on Lean's auto-implicit mechanism.

**Symptom**: "unknown identifier" for variables you expected Lean to infer.

### 3. `evalDist` IS `simulateQ`

They share the exact same code path: `evalDist` is `simulateQ` with `m = PMF` and uniform distributions as the oracle implementation. This identity is definitional (`rfl`).

### 4. `++ₒ` is dead — use `+`

The README and large amounts of commented-out code use `++ₒ` for combining oracle specs. The current API uses standard `+` (`HAdd`).

### 5. Commented-out code uses OLD API patterns

Files like `Fork.lean`, `Sigma.lean`, and `RF_RP_Switching_alt.lean` contain large commented-out blocks that use obsolete patterns (`[= x | ...]`, `++ₒ`, `simulate'`, `getM`, `guard` via `Alternative`). **Only follow patterns in uncommented code.** Use `Examples/OneTimePad.lean` as the canonical reference.

## Type System

### 6. `query t` is `OracleQuery`, not `OracleComp`

`query t : OracleQuery spec _`, not `OracleComp spec _`. To use `evalDist` on it, write `evalDist (liftM (query t) : OracleComp spec _)`. Bare `evalDist (query t)` causes `Monad (OracleQuery spec)` errors.

### 7. Core types are `@[reducible]` thin wrappers

`OracleSpec`, `QueryImpl`, and `OracleComp` are all `def`/`abbrev`/`@[reducible]` over `PFunctor` machinery. Lean may unfold them aggressively. Use `OracleComp.inductionOn` / `OracleComp.construct` as canonical eliminators rather than pattern matching on `PFunctor.FreeM.pure`/`roll`.

### 8. Universe polymorphism

`OracleComp` has 3 universe parameters, `SubSpec` has 6. Universe unification errors are common when composing specs or building reductions.

**Fix**: Use `{ι : Type*}` instead of `{ι : Type u}` to let universes resolve independently. Keep `α β : Type` (not `Type u`).

## Proof Patterns

### 9. `probOutput_bind_eq_tsum` is `@[grind =]` but NOT `@[simp]`

`simp` won't unfold `probOutput` of a bind. Use `rw [probOutput_bind_eq_tsum]` or `grind`.

### 10. Plain `qvcgen_step` may solve a probability equality when you only wanted a rewrite

On `Pr[...] = Pr[...]` goals, plain `qvcgen_step` heuristically tries swap, congruence, and
small bounded compositions. If you need to rewrite and continue, use `qvcgen_step rw` for a
top-level swap, `qvcgen_step rw under 1` under one shared bind prefix, or
`qvcgen_step rw congr` / `qvcgen_step rw congr'` to expose a shared outer bind. The manual pattern is:
```lean
simp only [← probEvent_eq_eq_probOutput ...]
rw [probEvent_bind_bind_swap]
simp only [probEvent_eq_eq_probOutput]
```

### 11. Avoid `guard` in experiments

Use `return (b == b')` or `return decide (r x w)` instead. `guard` requires `OptionT` / `Alternative`.

## Module Structure

### 12. `EvalDist/` must never import from `OracleComp/`

Check the module layering DAG before adding imports:
```
ToMathlib → Prelude → EvalDist/Defs → OracleComp core → EvalDist bridge
  → {SimSemantics, QueryTracking, Constructions, Coercions, ProbComp}
  → {ProgramLogic, CryptoFoundations} → Examples
```

### 13. Preserve partial proof attempts with `stop`

When a proof attempt is not finished or is currently broken, insert a local `stop` marker instead of deleting large proof blocks. This preserves search context for later agents.

### 14. `OracleComp.inductionOn` is the canonical eliminator

Pattern: `| pure x => ... | query_bind t oa ih => ...`. Use `simulateQ_bind`, `simulateQ_query`, `simulateQ_pure` simp lemmas in the `query_bind` case. See `simulateQ_id'` in `SimSemantics/SimulateQ.lean` for a clean example.

### 15. Full cutover, no backward-compatibility shims

When refactoring APIs, notations, or proof infrastructure, update all call sites in one
pass. Do not add deprecated aliases, migration wrappers, or compatibility layers.

## Build and Tooling

### 16. Always run `lake exe cache get` before `lake build`

Building Mathlib from source takes hours. Always fetch the precompiled cache first.

### 17. After adding new `.lean` files, run `./scripts/update-lib.sh`

This regenerates root import files (`VCVio.lean`, `Examples.lean`, `ToMathlib.lean`). CI checks they're up to date.

### 18. Lean toolchain and Mathlib version must stay in sync

Both currently `v4.28.0`. When upgrading, update both `lean-toolchain` and `lakefile.lean`'s `require mathlib` line simultaneously.

### 19. Use public references in shared docs

When a proof framework follows an external paper, cite the public paper by title, venue,
or URL rather than pointing agents at a repo-local file path.

### 20. Public reference papers are authoritative for design work

For relational program logic, start with
*A Quantitative Probabilistic Relational Hoare Logic* ([ERHL25](../../REFERENCES.md#erhl25)).

### 21. Agent guidance files must be committed

Agents dispatched to `git worktree` clones need to read `AGENTS.md`, `docs/agents/`, and any other guidance files. Ensure these are committed so all worktrees see them.
