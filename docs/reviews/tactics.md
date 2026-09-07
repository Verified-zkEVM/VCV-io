# Theorem registration and tactic usability review

Review this PR for opportunities to simplify existing proofs through the library's tactic APIs.
Treat this as an advisory proof-usability review. Preserve theorem statements, assumptions,
algorithm definitions, module boundaries, and the trusted computing base.

## Standing references

- [#636](https://github.com/Verified-zkEVM/VCVio/pull/636): expectation and probability registrations,
  support-aware monotonicity, finiteness, and measured simplifications in real consumers.
- [#642](https://github.com/Verified-zkEVM/VCVio/pull/642): bind bounds through expectation algebra
  and the program-logic `wp` façade.
- `docs/agents/probability.md`, `docs/agents/program-logic.md`, and
  `docs/reading/upstream-alignment.md`: current conventions and the broader registration inventory.

Resolve the PR's exact head and prerequisite stack. Reference PRs explain the approach; they do
not prove that an API exists or is imported on the reviewed head. Recheck old ledger observations
against the current source and pinned dependencies.

## Review procedure

1. Inspect changed proofs and affected consumers. Look across `gcongr`, `finiteness`, `positivity`,
   `fun_prop`, `simp`, congruence, `ext`, cast tactics, `@[vcspec]`, and `@[wpStep]`.
2. Classify each obstacle: missing registration, unsuitable theorem statement, missing public
   bridge, normalization, missing import, or tactic implementation limitation. Prefer existing
   upstream support; add a small public bridge only when a concrete consumer needs it.
3. Try an actual replacement. Prefer a proof that states the mathematical step directly, exposes
   useful support hypotheses, and composes with subsequent tactics. Keep direct proofs when
   automation adds complexity or only disguises the same work.
4. Check the replacement in the containing source module with its actual imports and local
   context. A scratch theorem importing the original theorem is not validation of its replacement.
   Check affected consumers and compare elaboration costs as well as proof length.
5. Report each accepted candidate with the declaration and location, before/after proof, required
   imports or registrations, prerequisite commit(s), exact validation command/result, and benefit.
   Distinguish source-module compilation, snippet-only checks, and unverified suggestions.
6. Record failed attempts as reproducible usability gaps, including the residual goal and why the
   obvious tactic did not work. Do not claim that a failed search establishes a missing upstream API.

## Registration contracts

- Preserve weak assumptions. A pointwise probability fallback must not acquire support instances.
- Keep support-aware monotonicity ahead of unrestricted fallbacks, and test the resulting binders.
- Use `expectedValue` for bind-bound calculations and the public `wp` head for program logic.
  Use explicit bridge rewrites or `change` when the tactic indexes a different expression head.
- An arbitrary expectation need not be finite. Require a finite bound or finite-support reasoning;
  never register a rule that silently assumes integrability, nonzero mass, or nonempty types.
- `finiteness` accepts explicit hypotheses and unfolding hints. For local abbreviations, try a
  targeted `change` or `dsimp only` first. Cardinality denominators may need the explicit
  `Mathlib.Tactic.Positivity.Finset` import.
- Register concrete function heads with `fun_prop`; unrestricted eliminator theorems that conclude
  `Measurable f` are proof tools, not useful global search rules.
- Orient normalization rules deliberately. Avoid broad support-expansion or quantifier-producing
  registrations that create `simp`/`grind` loops. Keep VCGen witness search opt-in.
- Add focused ordinary-import canaries for every new behavior, including negative cases and
  successful replay of suggestions. No linter suppressions or new axiom debt.

## Deliverables

Simplification findings are advisory, not correctness defects. Missing compiler tools, a failing
baseline, or unavailable prerequisites must be reported explicitly; they cannot count as successful
verification. The automated review discovers candidates and does not certify or apply a patch.

Prepare accepted changes on separate follow-up branches based on recorded PR heads. Separate
prerequisite integration from proof edits, preserve the original PR branches, and export patches.
Include a review report with successful examples, validation evidence, performance observations,
and a ranked backlog. Publication of branches is a separate action.
