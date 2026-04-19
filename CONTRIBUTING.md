# Contributing to VCV-io

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
  3. imports
  4. one blank line
  5. module docstring
  Keep exactly one blank line between these blocks.

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
- Follow Mathlib naming conventions where possible.
- Respect the module layering documented in [`AGENTS.md`](AGENTS.md).
- Use `/-! ## Title -/` doc-headers, not ASCII banners, for inline section breaks (see *Documentation Expectations* above).

## Licensing

This project is licensed under Apache 2.0. By contributing, you agree that your contributions are licensed under the same terms.
