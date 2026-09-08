# Making the standard Lake commands cover VCVio validation

Audit date: 2026-09-08. Repository snapshot: `2cff040e` (after #659), plus the scripting
repairs in #679 at `c431d109`. Dependency pins are unchanged: Lean/Mathlib 4.33.1.
This is an implementation estimate, not a change to the validation policy.

## Recommendation

Make `lake build && lake test && lake lint` the ordinary correctness gate. Lake already supports
package test and lint drivers; no replacement build system or upstream feature is needed to
make those commands orchestrate our checks. Use `&&` in automation: with semicolons, a successful
last command can hide an earlier failure in the shell's final exit status.

There are two separate projects:

1. **Consolidate entry points:** move the existing checks behind Lake drivers, initially reusing
   the Python/shell implementations. Estimated **5–10 engineer-days**, including CI parity tests.
   This can happen before the compatibility debt is retired.
2. **Remove temporary machinery:** replace adapters where upstream APIs actually cover their
   semantics, retire migration baselines, and port remaining tooling where that reduces maintenance.
   This is a series of proof/API projects, not a prerequisite for the first project.

The three commands should cover the deterministic checks for the root package. Clean downstream
installation, the optional complexity package, native backends, and hosted reporting still need
explicit CI configurations. Moving those checks into an always-networked root `lake test` would
make routine testing slower and compromise the existing package isolation.

## What already works

[`lakefile.lean`](../../lakefile.lean) declares seven default proof libraries and a `@[test_driver]`
that builds the three test libraries and runs smoke and SLH-DSA executables. Native ML-KEM,
ML-DSA, and Falcon executables are selected with `lake test -- --ffi`.

`lake lint` is configured as `batteries/runLinter` over the seven proof libraries. It does **not**
currently mean the complete CI lint policy. CI instead invokes Batteries separately for each
library to bound memory, and runs Mathlib's text linter and repository checks separately.

The installed 4.33.1 Lake source also supplies `builtinLint`, `--builtin-lint`, and
`--builtin-only`. Its implementation builds selected roots and reads persistent text/environment
lint results. This is a candidate for consolidation, not evidence that it covers every Batteries
or Mathlib linter or understands our baseline. Compare actual diagnostics before replacing either
runner. `--record-exceptions` writes linter suppressions into source and is incompatible with our
policy; it is not a migration strategy.

## Inventory of wrappers and manual checks

Estimates below are engineering effort for integration or removal, with a working pinned toolchain
and one maintainer familiar with the repository. Rows overlap; do not sum them as independent jobs.

| Surface and evidence | Why it exists / current gap | Destination and retirement condition | Effort |
|---|---|---|---|
| [`validate.sh`](../../scripts/validate.sh), [`build-project.sh`](../../scripts/build-project.sh), CI command blocks | Duplicate sequencing, library lists, flags, and exit handling. #679 fixes dropped flags and missing test-warning enforcement. Even the wrapper omits CI's executable-bit and case-clash checks. | One Lake test driver and one lint driver; CI calls them. Keep the old scripts as argument-preserving deprecated entry points briefly, then remove them and their wrapper-specific tests. | 1–2 days |
| [`check-warning-log.py`](../../scripts/check-warning-log.py) | `lake build` permits warnings. CI rejects root-library warnings except existing `sorry` warnings; tests permit none. Replayed dependency and native-stub warnings require scope filtering. | Initially invoke the same checker from the drivers. Later replace textual matching with verified native lint/diagnostic handling or strict warning configuration once debt and warning scopes permit it. `--wfail` alone rejects all logged warnings, including accepted ones; it is not a drop-in replacement. | 1–2 days to integrate; 2–4 days to replace after prerequisites |
| Batteries driver, [`nolints.json`](../../scripts/nolints.json) | CI uses one process per library; plain `lake lint` currently processes all roots in one process. The baseline permits historic findings and Batteries does not report stale allowances. Its `--update` overwrites the file per root, so aggregate updates are unsafe. | A `@[lint_driver]` with per-library processes and read-only baseline checks. Build roots before linting, so stale oleans cannot supply a false pass. Evaluate builtin lint parity before retiring Batteries or its allowlist. | 1–2 days orchestration; 2–3 days parity investigation |
| Mathlib `lint-style`, [`nolints-style.txt`](../../scripts/nolints-style.txt), tracked-file checks in [`linting.yml`](../../.github/workflows/linting.yml) | Text lint coverage uses explicit libraries and Git-discovered tests because test roots are not uniform. Executable bits and case collisions are checked only in CI. | Include all three in `lake lint`; derive module coverage once. Preserve Git-index checks for modes/collisions and avoid GNU-only shell flags on macOS. The style exceptions file is currently empty apart from comments. | 0.5–1 day |
| [`check-imports.sh`](../../scripts/check-imports.sh), [`update-lib.sh`](../../scripts/update-lib.sh) | The checker regenerates, saves, compares, and restores nine umbrellas. Bare `mk_all --check` includes curated `LatticeCryptoTest`, umbrella-less `HashSigTest`, and synthetic axiom fixtures; dormant Interop has a different header. | Use upstream `mk_all --lib X --module --check` for each of the eight module umbrellas and `--lib Interop --check` for Interop. This avoids write-and-restore now, without forcing all libraries into one shape. Keep explicit generation as a developer repair command. | 0.5–1 day, including missing-file/stale-file/nonmutation fixtures |
| [`AxiomSweep.lean`](../../scripts/AxiomSweep.lean), [`test-axiomsweep.sh`](../../scripts/test-axiomsweep.sh), [`axiom_baseline.json`](../../scripts/axiom_baseline.json) | Kernel acceptance permits declared axioms and `sorry`; CI imposes a stricter trust contract and tests its checker. This is policy, not a Lean compatibility defect. | Run checker fixtures under `lake test` and the real census under `lake lint`. Keep the census even after the sorry baseline reaches zero. Never include synthetic fixture taint in the production census. | 0.5–1 day integration; 1–3 days if porting the fixture harness to Lean |
| [`check-pmf-boundary.sh`](../../scripts/check-pmf-boundary.sh), baseline and [`pmf_boundary_holds.tsv`](../../scripts/pmf_boundary_holds.tsv) | Temporary Measure/Kernel migration guard over explicit PMF/SPMF tokens. Holds name SPMF, exact-sampling instances, the PMF-to-measure bridge, and the symmetric-encryption compatibility adapter. | Run ceiling checks under `lake lint` and fixtures under `lake test` now. Retire the baseline only after consumer migration; a zero-use boundary may remain. The opt-in touched-file `--ratchet` is **not** a current CI gate; do not silently enable it. | 0.5 day integration; semantic migration requires separate scoping |
| [`check-expose-boundary.sh`](../../scripts/check-expose-boundary.sh), [`count-expose-boundary.py`](../../scripts/count-expose-boundary.py) | Broad `@[expose] public section` retains historical downstream unfolding; the per-library ceiling prevents further growth. A token count does not establish semantic transparency. | `lake lint` owns the ceiling; tests own fixtures. Narrow exposure with ordinary-import downstream canaries, then remove the migration allowances when appropriate. | 0.5 day integration; retirement is a library-by-library API review |
| PolyFun, Interop, Extern, and complexity [`check-*-isolation.sh`](../../scripts/check-interop-isolation.sh) / [`check-polyfun-boundary.sh`](../../scripts/check-polyfun-boundary.sh) | The compiler accepts imports the project's dependency/TCB policy forbids, including reaching through PolyFun's public boundary. These remain useful after compatibility cleanup. | Persistent repository lint rules, with fixtures in `lake test`. Prefer a shared import-header parser and explicit library classifications to repeated regexes. Preserve coverage of unimported source files. | 0.5–1 day integration; 2–4 days shared parser/port |
| Python [`check-agent-docs.py`](../../scripts/check-agent-docs.py), [`extract-doc-fragments.py`](../../scripts/extract-doc-fragments.py) | Markdown paths, tactic/notation coverage, and generated fragments are outside Lean elaboration. #679 fixes Python annotation compatibility, not a proof issue. | Call read-only checks from `lake lint`; keep Python if it remains the simplest implementation. A Lean rewrite is optional, not necessary for standard commands. | 0.5 day integration; 2–4 days optional port |
| `nativeSrcPresent` / `buildNativeStub` in [`lakefile.lean`](../../lakefile.lean), [`ffi-check.yml`](../../.github/workflows/ffi-check.yml) | Dependency checkouts lack submodules, while native archives participate in downstream executable linking. Empty stubs preserve proof-only consumer links. Full native tests need C sources and a compiler. | Keep explicit `lake test -- --ffi` in its own configuration. Consider a separate native package to remove stubs from proof-only dependencies. Do not silently fetch submodules during default root tests or treat absent backends as passed native tests. | 0.5–1 day shared test plumbing; 3–7 days package split and link-matrix validation |
| Scratch downstream consumer in [`build.yml`](../../.github/workflows/build.yml) | Tests ordinary public imports, universe-polymorphic simulation laws, and linking with no native submodules. An in-repo successful build cannot establish this. | Extract a committed fixture package and give it normal Lake commands. CI still provisions a clean no-submodule checkout; an explicit integration command can reproduce it locally. | 1–2 days |
| [`VCVioComplexity/scripts/test.sh`](../../VCVioComplexity/scripts/test.sh), [`check-trust.sh`](../../VCVioComplexity/scripts/check-trust.sh), [`compatibility-preflight.sh`](../../VCVioComplexity/scripts/compatibility-preflight.sh) | Separate optional package, manual test-library build, trust probes plus source scan, and pinned expected upstream failures. Preflight recognizes four composition and six asymptotics diagnostics; normal success means no **unexpected** failure. | Give the child package its own test/lint drivers. Port upstream failures, require positive builds with `--require-upstream-stack`, replace diagnostic-text expectations with compiled API canaries, and only then remove compatibility preflight. Keep child dependencies out of the root graph. | 1–2 days drivers; 3–10 days initial upstream-port investigation/repair, with lower confidence |
| Timing/report wrappers in [`build_timing_report.sh`](../../scripts/build_timing_report.sh), CI cache/artifact/comment steps | Measure clean vs warm builds and publish historical comparisons; require hosted history and a controlled environment. They are not proof correctness gates. | Wrap standard commands externally. Keep clean-build, cache-restoration, artifact, PR-summary, release, and merge-queue behavior in CI. | 0.5–1 day workflow simplification |

The isolation row covers `check-polyfun-boundary.sh`, `check-interop-isolation.sh`,
`check-extern-isolation.sh`, and `check-complexity-backend-isolation.sh`. Existing fixture scripts
for the PolyFun, PMF, exposure, and complexity boundaries belong in the test driver, together with
the import-check and validation-harness regressions while those implementations remain.

## Temporary debt versus permanent checks

Committed allowances at the audited snapshot, **not a fresh count of active violations**:

| Allowance | Snapshot | Consequence |
|---|---|---|
| Environment lint | 1,643 entries: 968 `docBlame`, 399 `defsWithUnderscore`, 217 `unusedArguments`, 42 `tacticDocs`, 16 `simpNF`, 1 `synTaut` | Most debt is documentation/API shape, not simply stale simp attributes. Fixing naming can affect active downstream PRs. Remove stale entries, but do not promise mechanical deletion of all entries. |
| Axiom debt | 40 sorry-tainted declarations, zero nonstandard entries; native-trust grandfather list empty | This counts transitive taint, not 40 independent proof holes. Solving it is research work; retain kernel-level accounting regardless. |
| PMF/SPMF | 111 file ceilings totaling 1,939 permitted occurrences; five explicit ratchet holds | Migration size cannot be inferred from occurrence count alone. Preserve exact-sampling semantics and measure-bridge equations. |
| Broad exposure | Per-library ceilings total 484 files | Retirement needs downstream definitional-equality checks, not just deleting attributes. |

Loom2's `Std.Do'`/three-parameter predicate-transformer APIs, the probability compatibility
facade, PolyFun handler aliases, and dormant Hax/Aeneas bridges explain some of this debt. They do
not inherently require Bash or Python. Ordinary compile-time canaries can check compatible Lean
APIs; [the upstream alignment ledger](upstream-alignment.md) and
[internal duplication record](internal-duplication.md) track the semantic design work separately.

## Proposed command contract

| Command | Required coverage |
|---|---|
| `lake build` | Seven proof libraries, pinned dependencies, and existing elaboration-time linters. Preserve incremental builds; no GitHub API, destructive clean, network provisioning, or test-only native link requirement. |
| `lake test` | Three test libraries; smoke and pure-Lean executables; boundary/checker regression fixtures; scoped test-warning enforcement; failure propagation from every child command. Native tests remain explicit. |
| `lake lint` | Fresh root artifacts, bounded-memory environment lint, text lint including tests, source/index hygiene, generated umbrellas, docs, isolation and migration ceilings, scoped proof-warning enforcement, and production axiom census. All checks read-only. |

Store the proof roots, test-module policy, generated umbrellas, and excluded fixtures in one
reviewable configuration. These sets overlap but are not interchangeable. In particular, scanning
only imported modules can miss a new unimported source file; scanning only Git-tracked files can
miss local additions. Specify and test both local-source and committed-index behavior.

CI can retain parallel jobs and their required status names while invoking shared driver phases.
Do not remove protected job names or run each complete suite repeatedly just to preserve labels.
The default three commands must exercise the union of those phases.

## Delivery sequence and estimate

1. **Coverage contract and inventory fixture: 1–2 days.** Encode the root/test/umbrella sets and map
   every deterministic CI gate to a driver phase. Add failing examples for stale umbrellas,
   warnings, forbidden imports, missing files, doc drift, synthetic taint, and child failures.
2. **Consolidated Lake drivers: 2–4 days.** Reuse checker implementations, bound lint processes,
   use read-only `mk_all --check`, and route CI and developer entry points through the same phases.
3. **Parity and removal of redundant orchestration: 2–4 days.** Exercise clean and warm caches,
   changed and newly added modules, macOS/Linux, no-submodule clones, and standalone lint after
   edits. Compare failures and exit codes with CI before removing shell entry points.

That is the **5–10 day** near-term project. Allow **another 1–3 engineer-weeks** for selected
Lean-native checker ports, upstream linter parity work, and optional-package/consumer plumbing.
These ranges overlap the inventory rows; they are not additive promises about all debt retirement.

For substantive holdovers, budget a **2–3 day scoping pass** before committing to a schedule.
Provisional planning envelopes: **2–6 engineer-weeks** for lint-debt cleanup (including API review),
**4–12+ engineer-weeks** for PMF and broad-exposure migration together, and **1–3 weeks** for the
optional upstream compatibility ports if changes remain localized. Confidence is low until pilot
files and affected downstream consumers are checked. No responsible completion estimate follows
from the sorry-taint count; scope the missing mathematical results separately.

Acceptance is behavioral: every injected violation that fails the current CI correctness checks
must also fail the standard command sequence, with no baseline growth, disabled linters, hidden
native-test skips, or source mutation. A fixture for a skipped/unreachable module is essential.
Record clean and incremental elapsed time and peak memory so parity does not introduce an
unusable local lint command.

## What remains outside the default root sequence

- Native FFI differential testing with initialized submodules and platform compiler support.
- A fresh downstream consumer build with native submodules deliberately absent.
- The optional `VCVioComplexity` package's own build/test/lint sequence.
- Dormant Interop backend validation once compatible upstream dependencies are enabled.
- PR-base trend reports, clean/warm timing comparisons, cache/artifact handling, hosted summaries,
  releases, and merge-queue/protection checks.

The first three are real integration coverage, not optional substitutes for root correctness.
They should have documented Lake entry points and CI configurations, but should not turn routine
root testing into dependency installation or environmental mutation.

## Evidence and limits

This audit read the committed workflows, Lake configuration, scripts, baselines, and child-package
preflight. Upstream API claims were checked against the locally installed toolchain's
`Lake/CLI/Help.lean`, `Lake/CLI/Main.lean`, and `Lake/CLI/BuiltinLint.lean`, and pinned dependency
sources `mathlib/scripts/mk_all.lean` and `batteries/scripts/runLinter.lean`. In particular,
`mk_all --check` returns a nonzero status for missing/stale files without writing them, and Lake's
builtin lint mode is opt-in with the currently configured driver.

No whole-suite builtin/Batteries equivalence experiment or new complexitylib port was performed
for this document. The expected upstream diagnostics are the preflight's recorded contract, not
a new claim that all upstream heads still fail. Estimates are maintainer planning judgments.
