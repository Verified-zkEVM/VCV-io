# Compile-performance experiments

See [the investigation report](../../docs/reading/compile-performance-investigation.md)
for the original local-file findings and limitations. `measurements.json` contains individual uninstrumented
measurements, including source/setup hashes, not profiler-derived estimates.

See [the remediation report](../../docs/reading/compile-performance-remediation.md)
for current source changes, independent patch status, shared-tooling probes and
whole-build limitations. `remediation-measurements.json` retains the new compact
results, including unsuccessful experiments; raw artifacts stay under `.lake/`.

## Replay a module

Use Python 3.9+ on macOS or Linux. First build the target under the pinned toolchain.
The runner consumes Lake's recorded invocation and `.setup.json`, including plugins,
module visibility and project options. It rejects stale toolchains/checkouts and
keeps all generated artifacts outside Lake's build tree.

```sh
python3 scripts/profile_compile.py VCVio.OracleComp.Coercions.Add \
  --output .lake/compile-performance/files --label baseline
python3 scripts/profile_compile.py VCVio.OracleComp.Coercions.Add \
  --output .lake/compile-performance/files --label profile --runs 1 --warmup 0 --profile
python3 scripts/profile_compile.py VCVio.OracleComp.Coercions.Add \
  --output .lake/compile-performance/files --label trace --runs 1 --warmup 0 --trace
```

Choose a new label for each experiment. Use `--root /absolute/checkout` for an
isolated worktree; dependencies must already be built there. `--source` substitutes
a scratch source while retaining the original module setup and output facets.
Preserve its import header: `importArts` in the setup does **not** itself replace
the source imports (`imports?` is a distinct, optional field).

`--option Elab.async=false` supports synchronous prefix bisection. Cut only at
complete command boundaries and append `#exit`; an unfinished doc-comment or
declaration is not a valid timing control. Retain dependencies needed by the slice.
Do not count failing compilations as faster successes.

Scope `set_option trace.Meta.synthInstance true in` or
`set_option trace.Meta.Tactic.simp.rewrite true in` to a suspect declaration in a
scratch copy. For detailed scoped Firefox profiles use `set_option trace.profiler
true in`, then pass `--option trace.profiler.threshold=0`,
`--option trace.profiler.output.pp=true` and
`--option trace.profiler.output=/absolute/profile.json`. Open the resulting file in
Firefox Profiler. Avoid tracing entire large files at threshold zero.

On macOS, `--sample` samples the actual Lean child for two seconds; OS permissions
may require approval. It is diagnostic only, and may miss work outside that window.
Wall times exclude sampler shutdown; a failed sampler still makes the runner fail.
Linux users can wrap the recorded command with their installed native profiler.

Use uninstrumented serial runs for comparisons. Warm each variant, then alternate
original/candidate invocations at least five times; keep async settings and output
facets identical. CPU is summed across threads and may exceed wall time. Peak RSS
is reported in bytes. The runner's timeout kills the direct Lean child; it is not a
general process-tree sandbox. Full-build timings must be collected separately;
see [the whole-build protocol](whole-build-method.md).

### Native metaprogram probes

`--plugin /absolute/library.dylib` (or `.so` on Linux) is repeatable and records
each library's hash. Build plugins with the pinned toolchain and pass dependencies
before their consumers. On this checkout, the Header linter plugin needs the
DirectoryDependency plugin first. A missing dependency produces a loader error;
it is not a completed measurement. The broader `Mathlib.Init` native probe crashed
and is not recommended. No plugins are enabled by default.

`GoalDifference.lean.txt` benchmarks the opt-in `ToMathlib.Perf` implementation
against list membership using `#eval`. Copy it into `.lake/compile-performance/`
and run with `lake env lean` after building `ToMathlib.Perf`. It checks output
lengths; the general equivalence theorem and `VCVioTest.Perf` check semantics.
This microbenchmark is not an end-to-end linter benchmark. Hash-set construction
cost can outweigh lookup savings on small goal lists.

## Candidate status

- `encoding-kernel.patch`: kernel-checked decision proof, not `native_decide`.
- `unary-expected-type.patch`: concrete append operations, unchanged association.
- `add-local-diagnostic.patch`: **diagnostic only**, local instances and a self-lift
  canary. Not an approved change to the exported instance graph.
- `chain-simp-only.patch` and `compatibility-simp-only.patch`: negative/weak
  experiments retained for reproducibility, not recommended production changes.
- `handler-support-reuse.patch`: checked three-branch Chain experiment; no measured
  benefit. Its private generic support law is not added to the production API.

Patches are in `candidates/`, relative to baseline
`ffd0ca198fe6e640c0dd7f0f9c599943caacbf64`. `import-cleanup.patch` is an independent,
import-only change set; it does not contain the local proof/planner edits.
`unary-split.patch` contains the experimental core/dispatcher split **and** the
two concrete-append fixes; do not combine it with `unary-expected-type.patch`.
Apply only selected patches in a disposable checkout with `git apply --check`
first; do not apply every experiment as a proposed fix. `DottedConstructor.lean.txt` is a
small reproducer (stored outside the library sources). Copy it to a scratch
`.lean` file and replay it with the Unary.Internals setup; its final `rfl` checks
that the explicit-append version preserves the definition's value.

Instrumentation can emit development-option lint warnings. These were retained,
not suppressed; profiling options are absent from the two validated candidates.
