# Program Logic Tactics Next Steps

This is a local planning and delegation note for VCVio's program-logic tactics.
It is intentionally not tracked in git.

The current branch is the VCVio-native `@[vcspec]` backward-rule cutover after
PR #353 and PR #355.

## Current State

- VCVio keeps the public tactic vocabulary: `vcgen`, `rvcgen`, `vcstep`,
  `rvcstep`, `@[vcspec]`, and `@[wpStep]`.
- VCVio no longer owns unary Hoare bracket notation.
  User-facing `⦃ pre ⦄ c ⦃ post ⦄` comes from Loom's `Std.Do'.Triple`
  notation.
- Numeric proposition indicators use `𝟙⟦P⟧`.
  Loom's `⌜P⌝` remains reserved for pure proposition assertions.
- `eRelTriple` has been deleted.
  Quantitative relational triples are stated as
  `Std.Do'.RelTriple ... epost⟨⟩ epost⟨⟩`, backed by the `eRelWP` carrier.
- `VCVio.ProgramLogic.Tactics.Common.Backward` owns
  `VCSpecBackwardRule`, the backward-rule cache, predicate-carrier fixing,
  unary folded `Triple` consequence construction, and direct raw
  `Std.Do'.wp` / `Std.Do'.rwp` consequence application.
- `@[wpStep]` is now a cached SymM rewrite layer.
  The old `rw` / `simp only` fallback has been removed.
- Raw unary `wp` equality goals route through cached `@[wpStep]` before
  lower-bound `@[vcspec]` dispatch.
- Relational one-sided bind rules remain explicit through `rvcstep left` and
  `rvcstep right`.
  They are intentionally not part of default `rvcgen`.

## Locked Decisions

1. Keep VCVio's public tactic vocabulary.
2. Do not reintroduce public `@[lspec]` or `@[lspec_spike]` names.
3. `@[vcspec]` owns spec theorem registration.
4. Keep `eRelWP` as the quantitative relational semantics, but do not restore
   `eRelTriple`.
5. Keep `@[wpStep]` as the equational rewrite registry, backed internally by
   cached Sym rewrite rules.
6. Full cutover for each subsystem.
   Do not keep permanent compatibility shims or parallel fallback paths after a
   subsystem moves to cached/direct application.
7. Preserve VCVio ergonomics: native replay text, candidate diagnostics,
   explicit theorem steps, local hints, relational continuation naming,
   probability lowering, and coupling helpers.
8. Relational automation should expose strategy choices.
   Do not make one-sided bind splitting aggressive by default.

## Validation Baseline

Use these commands after tactic changes in this area:

```bash
lake build VCVio.ProgramLogic.Tactics.Common.Backward
lake build VCVio.ProgramLogic.Tactics.Common.WpStepDispatch
lake build VCVio.ProgramLogic.Tactics.Unary.Internals
lake build VCVio.ProgramLogic.Tactics.Relational.Internals
lake build Examples.ProgramLogic.UnaryStep
lake build Examples.ProgramLogic.UnaryTriple
lake build Examples.ProgramLogic.UnaryProbability
lake build Examples.ProgramLogic.RelationalStep
lake build Examples.ProgramLogic.RelationalDerived
lake build
python3 scripts/check-agent-docs.py
lake exe lint-style
```

## Immediate Work Queue

### 1. Preserve Replay And Diagnostics

Status: improved.
Unary `vcgen?` and relational `rvcstep?` now have guarded replay examples.
Relational failure diagnostics have a guard showing source `@[vcspec]`
candidates rather than generated helper names.

Remaining:

- Add a stable unary failure-diagnostic guard if one can be made to fail before
  producing ordinary theorem premises.
- Continue checking that replay text stays VCVio-native after each migration.

### 2. Cache Key Completeness

Status: audited for current global declarations.

Current `VCSpecBackwardRule` key:

- declaration name;
- raw-versus-folded goal mode;
- normalized `VCSpecKind` cache tag.

Invariant:

- Only global declarations use the shared cache.
- Local hypotheses and syntax proofs build fresh rules because they can share
  pretty names while carrying different closed-over terms.
- Carrier, WP/RWP instance, exception-post, and state arguments remain
  abstracted in the cached proof and are reopened freshly at each application.

If future local or structurally specialized entries are cached, widen the key to
include expression identity rather than reusing the global-declaration key.

### 3. Migrate Structural Families One At A Time

Status: the deterministic relational cached `@[vcspec]` path now includes
pure-pure leaves for both the propositional and quantitative carriers. Default
`rvcstep` also closes identity quantitative uniform-sampling and query leaves
without an explicit bijection hint.

Next candidates:

1. Controlled one-sided relational bind leaves only through explicit
   `rvcstep left` / `rvcstep right` commands.
2. Traversal/sequence-style relational structural families.
3. Probability lowering and equality-specific helpers, only after earlier
   families are stable.

Guardrails:

- Preserve replay.
- Preserve local hint behavior.
- Add one focused acceptance example per migrated family.
- Do not migrate a structural family just to reduce code duplication if it
  worsens proof authoring.
