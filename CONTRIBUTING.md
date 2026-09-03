# Contributing to VCVio

Thanks for contributing.

Start with:

- [`README.md`](README.md) for the project overview
- [`AGENTS.md`](AGENTS.md) for repo workflow, module layering, and proof guidance
- the relevant guides under [`docs/agents/`](docs/agents/)

Before sending work for review:

- Run `lake exe cache get && lake build`.
- After adding new `.lean` files, run `./scripts/update-lib.sh`.
- Avoid leaving `sorry` in finished work unless the change is explicitly meant to preserve partial work.
- Keep repo-wide Lean options in `lakefile.lean`. Do not restate `autoImplicit = false` with per-file `set_option` lines.
- Do not disable linters locally or globally to make warnings disappear. Fix the underlying issue instead of adding `set_option linter.* false`, `set_option weak.linter.* false`, or repo-level linter suppressions.

## Attribution And File Headers

This repo uses explicit Lean file headers. Every new Lean file should start with the standard header:

```lean
/-
Copyright (c) CURRENT_YEAR Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
```

Replace `CURRENT_YEAR` with the calendar year when the file is created.

Use the following attribution policy:

1. **New files**: Add the standard header with the current year and the author name(s) that should be credited for the new file.
2. **Routine edits to existing files**: Preserve the existing header. Do not rewrite attribution just because you touched the file.
3. **Substantial rewrites or replacements**: If a file is effectively replaced with new content, or an old file is renamed/recreated as a genuinely new file, update the header to reflect the new authorship.
4. **Copied or ported material**: If a new file is derived from an existing file or external source and substantial original structure/content remains, preserve any required upstream attribution and add current credited authors as appropriate.
5. **AI assistance**: Do not add a separate AI-attribution line. Use the repo's normal header format and list only the credited author name(s).

When in doubt, prefer:

- preserving attribution on incremental edits
- updating attribution only when the file is genuinely new or materially replaced

## Documentation Expectations

- Every ordinary Lean source file should have a module docstring near the top using `/-! ... -/`.
- Import-only umbrella modules such as `VCVio.lean`, `LatticeCrypto.lean`, and `Examples.lean`, along with `lakefile.lean`, should stay bare.
- Public definitions and major theorems should have declaration docstrings using `/-- ... -/`.
- Module docstrings should give a concise title and summary, and include notation or references when that context materially helps a reader.
- Declaration docstrings should describe what a definition is or what a theorem states, not how it evolved.
- Docstrings must be intrinsic and descriptive. Cross-reference live definitions when helpful, but do not mention removed or renamed declarations, change history, or reactive phrases such as "replaces" or "renamed from".
- If a file cites papers, include a references section in the module docstring or cite the source clearly in the surrounding docs.
- For ordinary Lean source files, use this prologue layout:
  1. copyright / license / authors header
  2. one blank line
  3. `module`
  4. public and private imports
  5. one blank line
  6. module docstring
  Keep exactly one blank line between these blocks.

## Module Scopes

All active Lean libraries and tests use the module system. Put ordinary declarations in a
`public section` and tactic/elaborator declarations in a `public meta section`. Existing source
files generally use `@[expose] public section` to preserve pre-migration definitional equality;
new definitions can instead be exposed individually with `@[expose]` when unfolding is part of
their intended public API. Executable and runtime implementation modules should use opaque
`public section` when callers do not need to unfold their definitions.

Use `public import` for a dependency that downstream importers should receive transitively,
`public meta import` for exported compile-time dependencies, and plain `import` for a private
implementation dependency. `import all` is appropriate in a proof module that deliberately needs
an imported module's private implementation. Do not use the transitional
`backward.privateInPublic` or `backward.proofsInPublic` options.

Cross-package `import all PolyFun.…` is forbidden: add a public PolyFun law or API instead. See
[`docs/agents/module-system.md`](docs/agents/module-system.md) for the visibility decision tree and
the long-term VCVio/PolyFun boundary.

`LatticeCryptoTest.lean` is intentionally curated rather than generated because its executable
modules define colliding root-level `main` declarations. For the same reason, `HashSigTest` has no
generated root umbrella; build its named executables and modules directly.

### Section Headers Within A File

Use Mathlib-style doc-comment section headers, **not** ASCII banners.

For an inline section break inside a Lean file, use a one-line docstring header that doc-gen will render in the generated documentation:

```lean
/-! ## Section title -/
```

Or, for a section with its own paragraph of explanation:

```lean
/-!
## Section title

Optional paragraph describing what the section contains.
-/
```

Do **not** use ASCII banners such as:

```lean
-- ============================================================================
-- § Section title
-- ============================================================================
```

ASCII banners are visually loud, do not appear in the generated documentation, and make the file feel partitioned in a way that the type system does not enforce. Prefer the `/-!` form, which both reads as natural prose and surfaces in `doc-gen4` output. If a section is large enough to warrant its own banner, it is usually large enough to warrant its own `namespace` or its own file.

## Style Notes

- Keep imports at the top of the file.
- Follow Mathlib naming conventions where possible. See the [Mathlib naming guide](https://leanprover-community.github.io/contribute/naming.html) for the full set of rules. The capitalization rules in particular:
  - Terms of `Prop`s (e.g. proofs, theorem names) use `snake_case`.
  - `Prop`s and `Type`s (or `Sort`) (inductive types, structures, classes) are in `UpperCamelCase`.
  - Functions are named the same way as their return values (e.g. a function of type `A → B → C` is named as though it is a term of type `C`).
  - All other terms of `Type`s (basically anything else) are in `lowerCamelCase`.
- Respect the module layering documented in [`AGENTS.md`](AGENTS.md).
- Use `/-! ## Title -/` doc-headers, not ASCII banners, for inline section breaks (see *Documentation Expectations* above).

## Tactic Gate Files

`VCVioTest/ProbabilityTactics.lean`, `VCVioTest/MonadProbability.lean`, `VCVioTest/GrindFailFast.lean`
and their siblings are the *tactic gates*: they state what the basic tactics must do on the whole
(see *Normal forms and the tactic contract* in [`docs/agents/probability.md`](docs/agents/probability.md)).
Four rules keep them honest:

1. **One terminal call.** A positive entry is `by <one tactic>` (or a term): `simp`, `grind`,
   `gcongr`, `finiteness`, `simp [S]`, `simp only [S]`.
2. **Known gaps are machine-checked and self-expiring.** Where the expected tactic does not close
   a goal, the entry is a *gap pair*: `fail_if_success (tac; done)` on its own line, then the
   working closer, with a dated `gap(tac, YYYY-MM-DD): reason` comment. The guard errors the moment
   the set improves, so the PR that closes a gap must also retire its guard. One guard covers a
   family of same-shaped entries when the family is named in the section note.
3. **No multi-call scripts.** A `;`/multi-line script is allowed only as the closer of a gap pair.
   A one-call entry that stops closing is fixed in the simp/grind set or filed as a dated gap pair;
   it is never fixed by adding a second call.
4. **Normalizers pin their normal form.** Where a set is a normalizer rather than a closer
   (`simp only [monad_norm]`, `handler_step`), the entry is `simp only [S]` followed by
   `guard_target =ₛ <expected form>` and then a closer.

Warnings in `VCVioTest` fail CI (the *Check canary warning budget* step), so a stale entry cannot
linger as a warning.

## Licensing

This project is licensed under Apache 2.0. By contributing, you agree that your contributions are licensed under the same terms.
