# Whole-build measurement protocol

`profile_build.py` records a complete seven-library Lake build. Python 3.9+
and POSIX are required. Keep results and worktrees inside the repository:

```sh
python3 scripts/profile_build.py --root .lake/compile-performance/worktrees/baseline \
  --output .lake/compile-performance/whole-build --label baseline-1 --clean
```

`--clean` moves the project's existing `.lake/build` to the result directory's
`saved-project-build`; it does not delete it, clean dependencies, or alter the
installed toolchain. Each label must be new. Avoid simultaneous builds during
comparisons. Dependency caches and native-submodule state must match between arms.

## Instrumentation

Add `--instrument` to substitute a temporary toolchain view whose compiler
wrappers forward to the pinned binaries and emit per-process JSON. Lean arguments,
module setup, public visibility, and output facets are preserved. `--profile`
adds Lean's textual profiler, except in files containing `#guard_msgs`, where
profiler messages would invalidate expected diagnostics. These files still build
and remain checked; their exclusion is recorded. Tracing is never used for the
acceptance timings.

```sh
python3 scripts/profile_build.py --root .lake/compile-performance/worktrees/baseline \
  --output .lake/compile-performance/whole-build --label timeline --clean --instrument
python3 scripts/analyze_build_profile.py .lake/compile-performance/whole-build/timeline \
  --build-dir .lake/compile-performance/worktrees/baseline/.lake/build \
  --output .lake/compile-performance/whole-build/timeline/analysis.json
```

Analyze before replacing the build artifacts, or point `--build-dir` at their
saved location. `directImports` uses the pinned Lean tuple schema; transitive
`importArts` is not used to infer direct edges. Failed builds, missing metadata,
duplicate module runs, and inconsistent timestamps are rejected. Start-only
records do not count as completed compilations.

The analyzer distinguishes the longest duration-weighted import path from the
observed last-finishing dependency chain. A module's recorded launch gap starts
at its last recorded direct dependency's completion; it can include queued work,
cached dependency/facet checks, and wrapper startup. It is not automatically
avoidable scheduler waste. Compiler occupancy counts active processes, not CPU
utilization. Cumulative profiler entries overlap and must not be summed into
exclusive CPU percentages. Peak RSS values must not be summed as simultaneous
memory consumption.

The shared timestamp clock is `clock_gettime(CLOCK_MONOTONIC)`, because Python 3.9
on macOS gives `time.monotonic()` a process-relative origin. Records include CPU,
context switches, source hashes and generated artifact sizes; the parent records
commit, tracked diff, dependency-manifest hash, thread-related environment,
command, platform, and hashes of tracked and non-ignored untracked Lean sources.
System load averages are coarse context, not a CPU or
memory-pressure trace. Avoid machine sleep during measurements.

`--threads N --instrument` supplies Lean's supported per-file `-jN` argument
without changing Lake's own parallelism. This is diagnostic, not a portable
recommendation. `--lake-config key=value` forwards an explicit Lake `-K` option;
the project must implement that option for it to affect builds. No scheduling
default is inferred from one machine or from widely separated batches.

## Acceptance

Screen with three counterbalanced clean-build pairs. Confirm the frozen candidate
with five additional pairs using uninstrumented invocations and unchanged target
sets. Require at least a 3% median wall reduction, greater than twice the baseline
relative median absolute deviation, and wins in at least four confirmation pairs.
Keep separate arms for source-layout changes, previous local fixes, and their
combination. A leaf-file win alone does not satisfy this gate.

Check public declaration names/types, tests, smoke, axiom and warning budgets,
and module boundaries. Inspect representative real-edit rebuilds separately
from no-op cache hits. Never remove proofs, omit target libraries, or disable
linters to manufacture a result. Preserve original import façades when moving
declarations, and treat changes to private names separately from public APIs.

Run the recorder/analyzer tests with:

```sh
PYTHONPYCACHEPREFIX=.lake/compile-performance/python-cache python3 scripts/test_build_profile.py
```
