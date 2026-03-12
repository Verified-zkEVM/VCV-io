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

- Every Lean file should have a module docstring near the top using `/-! ... -/`.
- Public definitions and major theorems should have declaration docstrings using `/-- ... -/`.
- If a file cites papers, include a references section in the module docstring or cite the source clearly in the surrounding docs.

## Style Notes

- Keep imports at the top of the file.
- Follow Mathlib naming conventions where possible.
- Respect the module layering documented in [`AGENTS.md`](AGENTS.md).

## Licensing

This project is licensed under Apache 2.0. By contributing, you agree that your contributions are licensed under the same terms.
