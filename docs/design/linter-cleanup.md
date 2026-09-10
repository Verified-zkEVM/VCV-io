# Linter cleanup and remaining migration groups

This records the suppression audit and the first implementation pass against the pinned
Lean/Mathlib v4.33.1 dependencies. The implementation unifies lint execution, removes the
active file-length overrides, and reduces declaration exceptions without widening the
baseline. Remaining declaration migrations are grouped below by their effect on callers.

## Audit and results

All 1,643 original environment exceptions reproduced in a fresh seven-library census;
none were stale or duplicated. Configuration problems concerned coverage and baseline
maintenance, rather than spurious findings.

| Environment linter | Original exceptions | Remaining exceptions |
| --- | ---: | ---: |
| `docBlame` | 968 | 579 |
| `defsWithUnderscore` | 399 | 345 |
| `unusedArguments` | 217 | 165 |
| `simpNF` | 16 | 0 |
| `tacticDocs` | 42 | 0 |
| `synTaut` | 1 | 0 |
| **Total** | **1,643** | **1,089** |

The 554 removed entries are fixes, not transferred suppressions. No `@[nolint]`, local
linter disable, or baseline addition was introduced. `scripts/nolints-style.txt` has no
exception entries.

The deliberate Unicode policy remains in `lakefile.lean`: cited author names and FIPS
notation require characters outside Mathlib's allowlist. The optional `VCVioComplexity`
package has the same Unicode policy and remains outside the root package's driver.
Dormant `Interop/Hax/CenteredBinomial.lean` retains its local `nativeDecide` linter override;
the generated `third_party/hax-cbd` extraction retains its unused-variable override.
Those belong to the separate Interop migration and generator policy. Interop keeps its
existing source-style coverage and stays outside environment linting and proof imports.

## Shared lint execution

Like Mathlib, cslib, and PolyFun, VCVio uses Batteries' environment linters and Mathlib's
source-style implementation. `scripts/lint.py` coordinates those upstream executables;
it defines no replacement Lean lint rules. The Lake driver derives proof libraries from
the default library targets.

There are two reasons for a coordinator instead of a direct `runLinter` driver:

* Batteries' pinned update mode overwrites `scripts/nolints.json` once per root and does
  not reject stale entries. Each root now runs in a fresh process and temporary directory.
  Results are unioned, checked for additions, and atomically pruned only after every root
  completes. Normal linting rejects both stale entries and unlisted findings. PR and merge
  queue CI also reject baseline additions relative to the merge base.
* The pinned Mathlib style CLI scans the imports of its input modules. Passing leaf test
  modules directly missed 75 of the original 81 test files. Temporary import lists now
  include every source in the covered roots, including untracked local files, without
  compiling test executable modules together. Filename clashes and executable Lean files
  are checked by the same entry point locally and in CI.

`lake lint` runs both passes. `lake lint -- --style-only` selects source checks;
`lake lint -- --env-only --no-build` checks existing proof oleans. After fixing findings,
`lake lint -- --prune-baseline` builds the libraries and safely removes obsolete entries.
`--base-ref REF` additionally enforces the baseline subset check against the merge base.
Do not run upstream `runLinter --update` against the repository baseline directly.

The redundant `modulesUpperCamelCase` option was removed. The explicit 1500-line limit
remains: Mathlib's downstream default does not impose that limit. Mathlib-specific script
and import-infrastructure options are already off by default, so no extra disables were
copied from dependency configurations.

`scripts/update-lib.sh` also handles the upstream generator's successful status 1 when
one umbrella changes, verifies the result, and continues through the other libraries.
Regression tests cover that behavior and failure propagation, plus lint source coverage,
per-library collection, interrupted runs, malformed baselines, atomic writes, and rejection
of baseline additions.

## Completed source groups

* **Documentation and parser registration:** documented widgets, tactic planner data and
  internals, and FXR arithmetic. Tactic alternatives share canonical documented syntax via
  `inherit_doc` and `tactic_alt`; generated parser names are explicit. The accepted tactic
  spellings remain unchanged. Widget environment linting has no remaining findings.
* **Proof aliases and redundant rules:** theorem-valued abbreviations in the complexity
  façade use `alias`, preserving names and types. Redundant simp registrations were removed
  while retaining their named lemmas; the pure failure rule has explicit priority because
  lower semantic layers need it before the general `NeverFail` API is available. The unused
  syntactic tautology in `ProbComp` was removed.
* **Unused assumptions:** generalized structural query-bound lemmas and their handler,
  caching, logging, and cryptographic callers. Removed unused private assumptions and
  several unnecessary `NeverFail` premises. The resulting caller generalizations extend
  through the stateful Fiat–Shamir reduction. PMF-bearing files touched by these fixes also
  reduce their explicit backend usage through public probability equations.
* **A contained naming migration:** the 35 FXR underscore names use camel case, with the
  Extern instance and Falcon test callers updated together. Examples include `fxrMul`,
  `fxcAdd`, `vectFFT`, and `gmTable`. There are no deprecated aliases. Independent private
  NTRU solver placeholders and C reference names retain their own identities.
* **File length:** six oversized modules were split into 17 responsibility-based modules.
  Query bounds separate basic and simulation rules; unary tactics separate rules, steps,
  and the driver; relational tactics separate steps and the driver; Fischlin knowledge
  soundness separates extraction, potential, and induction; the stateful Fiat–Shamir chain
  separates simulation, fork bounds, and reduction; relational simulation separates basic,
  epsilon, state-dependent, and resource rules. Every original module remains a public
  import façade. Previously exposed definitions retain individual exposure where needed.

## Remaining groups, in migration order

1. **Documentation without signature changes (579 findings).** Continue by module, reading
   definitions and documenting fields as well as their structures. Useful next batches are
   Falcon `SmallPrimeNTT` (25), SealedSender `AspectObservation` (20), `Control.Monad.Ordered`
   (17), and ML-KEM `Encoding` (17). Use inherited documentation only for actual aliases or
   matching implementations; do not hide public declarations to remove documentation debt.

2. **Additional theorem generalizations (part of 165 unused-argument findings).** Work from
   `QueryImpl.Constructions`, tracing, logging, and writer-cost lemmas toward their callers.
   Separate theorem assumptions from dictionaries carried by executable definitions or
   typeclass instances. Re-run both compiler and environment linters after each dependency
   layer: a premise becomes unused in a wrapper only after its callee is generalized.
   Coordinate changes in probability files with the existing PMF retirement boundary.

3. **Inference-sensitive instance changes (the rest of the unused-argument group).** In
   particular, keep `instNeverFailOfLawfulMonadLiftTPMF`'s lawfulness premise until the class
   interface is addressed: deleting it directly leaves unresolved monad metavariables in
   downstream instance inference. Validate a replacement against `SubSpec`, `StateT.Basic`,
   and Loom coherence, rather than treating the unused-argument report as a purely textual
   deletion. Also check explicit `@declaration` applications when reducing public binders.

4. **Definition and namespace naming (345 findings).** Migrate contained arithmetic families
   such as `BigInt31` and `SmallPrimeNTT` with their callers first. The larger groups in
   `TweakableHash.SM_DT_*`, asymmetric encryption's `IND_CPA` API, and `KeyEncapMech` include
   namespace and projection names; plan each as an atomic family migration. Update structure
   literals, projections, qualified references, and tests together. These require more
   downstream edits than documentation or theorem generalization and should not be mixed
   into unrelated proof changes.

For every batch, use the shared driver to prune the baseline, preserve import façades, and
run `./scripts/validate.sh --lint --test --axioms` along with
`bash scripts/check-pmf-boundary.sh --ratchet origin/main`. Baseline reductions are consequences
of checked source fixes, not targets achieved by renaming exceptions or weakening lint sets.
