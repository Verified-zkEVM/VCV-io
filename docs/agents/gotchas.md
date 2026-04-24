# Gotchas and Troubleshooting

## Critical (Will Bite You Immediately)

### 1. `[spec.Fintype]` and `[spec.Inhabited]` required for probability

Any file using `evalDist`, `probOutput`, `probEvent`, or `Pr[...]` on `OracleComp spec` needs these instances on the spec. Without them, typeclass resolution silently fails with confusing errors.

**Symptom**: "failed to synthesize instance" mentioning `Fintype` or `PFunctor.Fintype`.

**Fix**: Add `[spec.Fintype] [spec.Inhabited]` to your variable/hypothesis list.

### 2. `autoImplicit = false` is set globally in `lakefile.lean`

Every variable must be explicitly declared. Do not rely on Lean's auto-implicit mechanism,
and do not add `set_option autoImplicit false` in individual files.

**Symptom**: "unknown identifier" for variables you expected Lean to infer.

### 3. `evalDist` IS `simulateQ`

They share the exact same code path: `evalDist` is `simulateQ` with `m = PMF` and uniform distributions as the oracle implementation. This identity is definitional (`rfl`).

### 4. `++ₒ` is dead — use `+`

The README and large amounts of commented-out code use `++ₒ` for combining oracle specs. The current API uses standard `+` (`HAdd`).

### 5. Commented-out code uses OLD API patterns

Files like `Fork.lean`, `Sigma.lean`, and `RF_RP_Switching_alt.lean` contain large commented-out blocks that use obsolete patterns (`[= x | ...]`, `++ₒ`, `simulate'`, `getM`, `guard` via `Alternative`). **Only follow patterns in uncommented code.** Use `Examples/OneTimePad/Basic.lean` as the canonical reference.

## Type System

### 6. `query` resolves to `HasQuery.query`; use `spec.query` for the primitive

The bare `query` identifier is the `export`ed `HasQuery.query`, so writing `query t : OracleComp spec _` produces a monadic value directly and works with `evalDist`. The primitive single-query syntax `OracleQuery spec _` is `OracleSpec.query` (marked `protected`); reach it via dot notation `spec.query t` (or the fully qualified `OracleSpec.query t`) when you need to apply `liftM`, project `OracleQuery.cont`, or pattern-match on the query structure.

### 7. Core types are `@[reducible]` thin wrappers

`OracleSpec`, `QueryImpl`, and `OracleComp` are all `def`/`abbrev`/`@[reducible]` over `PFunctor` machinery. Lean may unfold them aggressively. Use `OracleComp.inductionOn` / `OracleComp.construct` as canonical eliminators rather than pattern matching on `PFunctor.FreeM.pure`/`roll`.

### 8. Universe polymorphism

`OracleComp` has 3 universe parameters, `SubSpec` has 3 (`u, v, w`: indices `ι : Type u`, `τ : Type v`, shared response universe `w`). Universe unification errors are still common when composing specs or building reductions because the lens-style `MonadLift` parent can drag extra metavariables in.

**Fix**: Use `{ι : Type*}` instead of `{ι : Type u}` to let universes resolve independently. Keep `α β : Type` (not `Type u`).

## Proof Patterns

### 9. `probOutput_bind_eq_tsum` is `@[grind =]` but NOT `@[simp]`

`simp` won't unfold `probOutput` of a bind. Use `rw [probOutput_bind_eq_tsum]` or `grind`.

### 10. Plain `vcstep` may solve a probability equality when you only wanted a rewrite

On `Pr[...] = Pr[...]` goals, plain `vcstep` heuristically tries swap, congruence, and
small bounded compositions. If you need to rewrite and continue, use `vcstep rw` for a
top-level swap, `vcstep rw under 1` under one shared bind prefix, or
`vcstep rw congr` / `vcstep rw congr'` to expose a shared outer bind. The manual pattern is:
```lean
simp only [← probEvent_eq_eq_probOutput ...]
rw [probEvent_bind_bind_swap]
simp only [probEvent_eq_eq_probOutput]
```

### 11. Avoid `guard` in experiments

Use `return (b == b')` or `return decide (r x w)` instead. `guard` requires `OptionT` / `Alternative`.

### 12. `do`-notation bind uses a different `Bind` instance (Lean 4.29+)

Lean 4.29 changed `do`-block elaboration so the desugared bind may use a `Bind` instance
that differs syntactically from `Monad.toBind`. This means `pure_bind`, `bind_assoc`, and
`bind_pure` won't fire via `simp` or `rw` on goals produced by `do` notation.

**Symptom**: `simp [pure_bind]` or `rw [bind_assoc]` does nothing on a `do`-block goal.

**Fix**: Use the restated lemmas from `ToMathlib.Control.Lawful.Basic` (namespace `LawfulMonad`):
`do_pure_bind`, `do_bind_pure`, `do_bind_assoc`, `do_bind_pure_comp`, `do_map_bind`,
`do_bind_map_left`. All are `@[simp]`.

## Module Structure

### 13. `EvalDist/` must never import from `OracleComp/`

Check the module layering DAG before adding imports:
```
ToMathlib → Prelude → EvalDist/Defs → OracleComp core → EvalDist bridge
  → {SimSemantics, QueryTracking, Constructions, Coercions, ProbComp}
  → {ProgramLogic, CryptoFoundations} → Examples
```

### 14. Preserve partial proof attempts with `stop`

When a proof attempt is not finished or is currently broken, insert a local `stop` marker instead of deleting large proof blocks. This preserves search context for later agents.

### 15. `OracleComp.inductionOn` is the canonical eliminator

Pattern: `| pure x => ... | query_bind t oa ih => ...`. Use `simulateQ_bind`, `simulateQ_query`, `simulateQ_pure` simp lemmas in the `query_bind` case. See `simulateQ_id'` in `SimSemantics/SimulateQ.lean` for a clean example.

### 16. Full cutover, no backward-compatibility shims

When refactoring APIs, notations, or proof infrastructure, update all call sites in one
pass. Do not add deprecated aliases, migration wrappers, or compatibility layers.

### 17. Module organization: no thin re-export umbrellas except at the repository top level

When splitting a file into a folder of submodules, do **not** add a sibling `X.lean`
whose only content is a chain of `import X.A; import X.B`. Each caller imports the
specific submodule it actually uses.

**Allowed umbrellas** (strictly top-level roots only): the auto-generated root imports
maintained by `./scripts/update-lib.sh` and used by CI, currently `VCVio.lean`,
`ToMathlib.lean`, `Examples.lean`, `LatticeCrypto.lean`, `LatticeCryptoTest.lean`.
When a new top-level root is added, extend this list alongside it.

**Not allowed**: umbrellas inside a subdirectory (e.g. a top-level
`VCVio.CryptoFoundations.FiatShamir` umbrella beside the `VCVio/CryptoFoundations/FiatShamir/`
folder, or a `VCVio.OracleComp` umbrella beside the `VCVio/OracleComp/` folder). Even if a module "feels
cohesive", callers must import the specific submodule they use.

## Build and Tooling

### 18. Always run `lake exe cache get` before `lake build`

Building Mathlib from source takes hours. Always fetch the precompiled cache first.

### 19. Do not disable linters to silence warnings

Do not add `set_option linter.* false`, `set_option weak.linter.* false`, or repo-level
`leanOptions` that turn lints off just to get a clean build. Treat linter failures as real
problems and fix the underlying declaration, proof, naming, or formatting issue instead.

### 20. After adding new `.lean` files, run `./scripts/update-lib.sh`

This regenerates root import files (`VCVio.lean`, `Examples.lean`, `ToMathlib.lean`). CI checks they're up to date.

### 21. Lean toolchain and Mathlib version must stay in sync

Both currently `v4.28.0`. When upgrading, update both `lean-toolchain` and `lakefile.lean`'s `require mathlib` line simultaneously.

### 22. Use public references in shared docs

When a proof framework follows an external paper, cite the public paper by title, venue,
or URL rather than pointing agents at a repo-local file path.

### 23. Public reference papers are authoritative for design work

For relational program logic, start with
*A Quantitative Probabilistic Relational Hoare Logic* ([ERHL25](../../REFERENCES.md#erhl25)).

### 24. Agent guidance files must be committed

Agents dispatched to `git worktree` clones need to read `AGENTS.md`, `docs/agents/`, and any other guidance files. Ensure these are committed so all worktrees see them.
