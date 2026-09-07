## Summary

<!-- What changes and why. When a Mathlib, core, or Batteries lemma or idiom replaces a local
one, cite the row in docs/reading/upstream-alignment.md. -->

## Verification

<!-- The commands run locally, e.g. `lake build <libs> VCVioTest`, `lake exe axiomsweep --check`,
`./scripts/update-lib.sh`, `bash scripts/check-pmf-boundary.sh`, `lake exe lint-style <libs>`,
`python3 scripts/check-agent-docs.py`. -->

## Checklist

- [ ] New files carry the standard header and module docstring (`CONTRIBUTING.md`, *Attribution
      And File Headers*); docstrings are intrinsic, with no change history or "renamed from" wording.
- [ ] New files use plain `public section` with per-declaration `@[expose]` (*Module Scopes*), and
      the expose-boundary baseline was lowered in this PR if a file was converted.
- [ ] `./scripts/update-lib.sh` leaves the umbrella files unchanged, and
      `lake exe axiomsweep --check` passes with `scripts/axiom_baseline.json` untouched (or the
      baseline diff is explained above).
- [ ] No `set_option linter.* false`, no deprecated aliases (`docs/agents/gotchas.md` §18, §23),
      and no native FFI test executables on the PR path.
- [ ] Documentation touched by the change is updated and `python3 scripts/check-agent-docs.py`
      passes.
- [ ] If a simp/grind/gcongr set changed: the gate files under `VCVioTest/` gained one-call
      entries, no proof gained a second tactic call outside a dated gap pair, and the before/after
      line counts of the touched proofs are listed above.
