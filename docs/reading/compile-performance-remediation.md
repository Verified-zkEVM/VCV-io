# Compile-performance remediation

## Implemented source changes

The two small, independently validated local fixes are in
[draft PR #668](https://github.com/Verified-zkEVM/VCVio/pull/668). The profiling and
prototype branch is stacked on that branch so these reports and experiments can
be reviewed separately:

- `LatticeCrypto/MLKEM/Concrete/Encoding.lean`: use `decide +kernel` for
  `packByte_bitOf_fin`, avoiding the 256-case elaborated proof. The earlier paired
  file replay measured a 40.8% median reduction. This uses kernel checking, not
  native trust.
- `VCVio/ProgramLogic/Tactics/Unary/Internals.lean`: use concrete, left-associated
  `List.append` in the two probability planners. The earlier paired replay
  measured a 9.8% median reduction. Supplying the element type early avoids
  speculative dotted-constructor diagnostics that scan the whole environment.

Those percentages are **file-level**, not whole-build improvements. See the
[original investigation](compile-performance-investigation.md) for traces,
complete-command bisection, failed controls, and causal evidence.

`ToMathlib/Perf.lean` supplies an opt-in indexed goal-difference implementation,
its general equivalence theorem, and two `TacticInfo` adapters. It does not
register a linter or change existing tactics. `VCVioTest/Perf.lean` covers empty,
disjoint, reordered, and duplicate goal lists. Generated umbrellas include these
modules. The measurement tooling supports whole-build timelines and explicit
native-plugin experiments, without changing Lake or Lean defaults.

No instance priorities, thread defaults, linter settings, public theorem
statements, or executable encoding definitions were changed.

## Whole-build evidence: a separate optimization axis

Baseline is `ffd0ca198fe6e640c0dd7f0f9c599943caacbf64`, Lean/Mathlib `v4.33.1`,
macOS arm64, 14 logical CPUs. Measurements build all seven non-test libraries;
dependency caches are warm but each clean run rebuilds the project. Native
submodules are absent, so Extern uses its documented stub archives. These numbers
do not predict Ubuntu CI with native backends present.

One fresh diagnostic profile covered **553 modules** in 167.94s. Compiler children
used 1680.91 CPU-seconds, with 53.88 CPU-seconds outside those recorded module
processes. The five highest-CPU modules account for only **3.67%** of module CPU.
Optimizing only those files therefore leaves most compilation work untouched.

The profiler reports substantial cumulative import loading (1152.99s) and
interpretation (846.06s), alongside instance synthesis (126.65s), simplification
(114.88s), tactics (73.25s), and elaboration (53.70s). **These categories overlap,
can include waiting, and are not exclusive CPU shares.** They motivate shared
frontend/metaprogram experiments, but do not prove that a particular linter or
import routine is the largest source of avoidable CPU work. The remaining
attribution task needs native stack sampling with an exclusive cost breakdown.

The duration-weighted import path had 41 modules and cost 127.17s. It crossed
`PRFTagReader.Auth → Collision → BadEvent → PRFTagReader` before returning through
the reduction/table/hybrid files. These dependencies serialize proofs that do
not all need each other's results. Removing selected edges in the fixed-weight
model shortens the PRF path from 125.80s to 100.22s, but the overall modeled path
only drops to 123.07s because the bottleneck switches to another branch.
**This graph calculation is not a measured build speedup.**

| Experiment | Baseline median | Candidate median | Decision |
| --- | ---: | ---: | --- |
| Earlier consolidation, three clean pairs | 134.48s | 132.02s | 1.83%; below the 3% gate; not applied |
| Eight-file import cleanup, one clean pair | 129.33s | 145.21s | 12.3% slower in this pair; inconclusive, not accepted |
| Import cleanup + local fixes + unary split + Perf | — | — | First screen run terminated by SIGTERM; no valid comparison |

An unrelated project's full Lean build was also observed during the attempted
combined screen. Its processes were not stopped. The SIGTERM's cause was not
established, and a terminated build is not counted as a fast build. The final
correctness build succeeded after recovery. No whole-build speedup is claimed;
the three-pair screen and five-pair confirmation remain unfinished.

## Independent import-cleanup patch

[`import-cleanup.patch`](../../scripts/compile_performance/candidates/import-cleanup.patch)
contains eight import-only edits, with no proof changes. It replaces unnecessary
PRF umbrellas and proof dependencies with `Defs` or `IdealHandlers`, and adds
explicit `Auth`, `Table`, `BadEvent`, and relational imports where actually needed.
Public top-level umbrellas remain intact. Internal submodule transitive surfaces
are intentionally narrower; downstream clients may need explicit imports.

The patch compiled with all seven libraries and the three test libraries, and
preserved existing public declaration names/types. It is kept **separate from the
working-tree fixes**, pending a reliable import-only timing comparison. It is
published separately as [draft PR #669](https://github.com/Verified-zkEVM/VCVio/pull/669).

`lake shake --keep-public --explain Examples.PRFTagReader` was run read-only on
the built candidate. It additionally suggested removing two implied public
imports in `PRFTagReader.Defs` (`StateT.PreservesInv` and `QueryBound`). These were
not blindly applied or included in the measured eight-file candidate. Review
each proposed edge change, preserve intentional façades, and rebuild all targets
after selecting changes. The command exits nonzero when it has suggestions;
that is not a Lean compilation failure. The pinned
[Lake help](https://github.com/leanprover/lean4/blob/v4.33.1/src/lake/Lake/CLI/Help.lean)
documents its analysis, preservation options, and `--fix` behavior.

## Other implemented experiments

### Unary core/dispatcher split

[`unary-split.patch`](../../scripts/compile_performance/candidates/unary-split.patch)
moves unary strategies into `Unary.Core` and retains the original `Internals`
module as the dispatcher. Only its relational branch needs the relational tactic
implementation. Same-package `import all` shares private helpers without exporting
them. Original names, statements and declaration bodies are preserved, apart
from the two concrete-append fixes included in this patch.

The split passes the complete library/test build and public API comparison.
It exposes more parallelism, but adds another module's import/serialization cost.
It is not in the working tree because its whole-build timing gate is unresolved.
Do not combine this patch with `unary-expected-type.patch`, which it includes.

### Reusable state-handler support law

[`handler-support-reuse.patch`](../../scripts/compile_performance/candidates/handler-support-reuse.patch)
contains a checked generic law that peels an `extendState` support membership
into a base-handler witness, reused at three invariant-proof branches in Chain.
It adds no simplifier registration. The diagnostic version keeps the law private;
if a beneficial version emerges, its natural owner is `StateT.StateProjection`.

Applying the law to the main signing-support proof retained extra intermediate
existential variables and broke the existing witness decomposition. This exposes
a real design issue: a useful normalization API needs to compose the base
handler and auxiliary-state transformation **before** expanding all product
witnesses. Merely extracting the outer support equation is insufficient.

The successful three-branch candidate had a 4.301s median versus 4.210s original,
winning only one of five measured pairs after a warmup pair (counterbalanced
order). The machine was not exclusively idle, so this is diagnostic evidence,
not a precise regression estimate. It provides no reason to land the change.
The earlier Chain/Compatibility restricted-simp patches also remain experiments.

### Shared metaprograms and upstream work

The `ToMathlib.Perf` microbenchmark used 200 interpreted `#eval` iterations per
size. At 256 goals, list membership took 1.071s versus 0.117s indexed; at 64,
0.069s versus 0.028s. At 1–16 goals indexing was slower. The implementation
preserves order and multiplicity, but actual linter goal-size distributions have
not been measured. Do not install it globally or pick a crossover threshold from
this single synthetic run.

Narrow native linter plugins reduced CPU in three isolated module probes by
roughly 3–7%, with byte-identical diagnostics. Wall results were mixed: General
improved, Chain was essentially unchanged, and Unary was slightly slower.
Loading the broader `Mathlib.Init` plugin crashed with SIGSEGV. Loading Header
alone also failed because DirectoryDependency must be loaded first; the ordered
plugin replay succeeded. These are opt-in probes, not a recommendation to enable
package-wide precompilation. Lake's
[build documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
describes the additional native build work involved.

The strongest upstream Lean candidate remains lazy construction of dotted-name
suggestions in `Lean.Elab.App`: preserve the eventual error text while avoiding
`reverseFieldLookup` for discarded speculative errors. The retained
`DottedConstructor.lean.txt` reproducer checks the local workaround by `rfl`.
No upstream compiler patch or PR was published. For Mathlib, measure realistic
goal-list sizes and native/interpreted stacks before considering an adaptive
goal-difference implementation. Header already caches library-root lookup; a
second cache is not an informed fix.

## Validation and reproduction

Worktrees, raw logs, traces, API snapshots and recoverably moved build trees are
under `.lake/compile-performance/`. The final validation checkout mirrors every
tracked/non-ignored Lean source in the working tree; it has the valid 4.33.1
dependency cache, unlike the original stale 4.33.0 artifacts.

- Seven non-test libraries plus `VCVioTest`, `LatticeCryptoTest`, `HashSigTest` build.
- Direct smoke check, axiom-sweep fixtures and `axiomsweep --check` pass; no new
  axiom/sorry taint, no nonstandard axioms.
- Existing 20,169 public declaration names/types are preserved; four opt-in Perf
  declarations are added. This comparison erases binder macro scopes and metadata,
  not named arguments or global constants. It is not a comparison of proof bodies.
- Warning budget, PMF boundary, Extern/Interop isolation, PolyFun boundary and
  complexity-backend isolation pass. No baselines or suppressions were changed.
- Generated umbrellas are checked; nine measurement-tool regression tests pass.

The native executable test programs were not run with real backends. Representative
real-edit rebuild measurements, an exclusive full-build CPU breakdown, and idle
screening/confirmation pairs are still outstanding. Keep these limits distinct
from the successful compilation and API checks.

Individual compact results and patch hashes are retained in
[`remediation-measurements.json`](../../scripts/compile_performance/remediation-measurements.json).
The [runner instructions](../../scripts/compile_performance/README.md) and
[whole-build protocol](../../scripts/compile_performance/whole-build-method.md)
describe how to resume: compare import-only and layout-only arms separately,
then their combination; freeze a qualifying candidate before confirmation.
Do not mix widely separated timing batches or accept profiler timings as clean
wall-time improvements. Lean's
[performance guide](https://github.com/leanprover/lean4/blob/master/doc/perf.md)
and the [profiling wiki](https://vca.epfl.ch/wiki/lean-profiling/) provide the
tracing and native-sampling background for the remaining attribution work.
