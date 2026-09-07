# Compile-performance investigation

## Outcome

Investigated ten CI-slow modules and deeply profiled the five slowest in isolated
local replays. Three causal mechanisms have actionable experimental fixes:
computation-lift instance backtracking, a large enumerated byte proof, and
speculative dotted-constructor elaboration that scans the entire environment.
Two protocol modules were localized to expensive handler/state simplifications;
their restricted-simp experiments do not justify large proof rewrites yet.

This report records the original local-file investigation. The Encoding and Unary
fixes have since been applied to the working tree; see the
[remediation report](compile-performance-remediation.md) for the implementation,
whole-build experiments, and current acceptance decisions. Candidate patches,
a small elaboration reproducer, individual measurements, and the replay runner
are in [scripts/compile_performance](../../scripts/compile_performance/README.md).
The Add instance change remains diagnostic.

## Scope and measurement

Baseline: `ffd0ca198fe6e640c0dd7f0f9c599943caacbf64`, Lean/Mathlib `v4.33.1`,
macOS arm64. CI reference: [successful baseline run](https://github.com/Verified-zkEVM/VCVio/actions/runs/33853954985),
Build Project job `100962918918`. The timed libraries are `ToMathlib`, `VCVio`,
`LatticeCrypto`, `Extern`, `HashSig`, `Examples`, and `VCVioWidgets`; test libraries
and dormant Interop are not in that timing population.

The existing local artifacts used Lean 4.33.0, so they were not reused as valid
4.33.1 measurements. A detached checkout under
`/private/tmp/vcvio-compile-perf.GpdqNw/repo` was populated with copy-on-write caches,
refreshed with `lake exe cache get`, and successfully built under the pinned
toolchain. Subsequent work moved into repository-local worktrees under
`.lake/compile-performance/worktrees/`; the original path above identifies the
historical measurements only. Native submodules are absent in these experiments,
so Extern uses its intended stubs.

The runner replays each actual Lake invocation, including module setup, options,
plugins, and Lean/C output generation, but redirects outputs away from dependencies.
It measures Lean compilation, not a no-op Lake cache hit, dependency builds, or a
native C compiler invocation. First-pass ranking uses one warmup plus five serial
uninstrumented runs with the original asynchronous elaboration setting.

| Module (abbreviated) | CI seconds | Local median seconds | Local range |
| --- | ---: | ---: | ---: |
| OracleComp.Coercions.Add | 26 | 4.598 | 4.590–4.634 |
| FiatShamir.Sigma.Stateful.Chain | 26 | 4.195 | 4.184–4.207 |
| MLKEM.Concrete.Encoding | 19 | 3.451 | 3.424–3.456 |
| FiatShamir.Sigma.Stateful.Compatibility | 20 | 3.251 | 3.245–3.297 |
| ProgramLogic.Tactics.Unary.Internals | 17 | 3.215 | 3.205–3.236 |
| ProgramLogic.Tactics.Relational.Internals | 17 | 3.037 | 3.029–3.053 |
| Examples.ProgramLogic.RelationalStep | 15 | 2.829 | 2.823–2.849 |
| FiatShamir.Sigma.Fork | 18 | 2.817 | 2.801–2.826 |
| ProgramLogic.Relational.SimulateQ | 20 | 2.724 | 2.707–2.743 |
| Fischlin.KnowledgeSoundness | 17 | 2.707 | 2.689–2.713 |

These are ten CI-selected slow files, not an exhaustive isolated timing of every
module. CI numbers include a different machine and concurrent build pressure;
they are not directly comparable to local seconds. The local top five determine
the deep-dive set, rather than assuming CI's order is intrinsic.

Each deep dive used `--profile`, a nested Firefox trace, and complete-command
prefix controls. Focused type-class/rewrite traces and macOS native sampling were
added where useful. Imports-only controls retained each original import header:
Add 1.041s, Chain 1.190s, Encoding 1.033s, Compatibility 1.144s, Unary 1.333s
(single diagnostic runs). These are approximate floors, not subtractable constants.

For candidate comparisons, round zero warmed both variants, then five rounds ran
original followed by candidate, serially and without profiling. This limits drift
but does not randomize order. Later original times drifted above the first-pass
baseline; all improvement percentages below use the paired batch, not mixed batches.

| Candidate | Original median (range), s | Candidate median (range), s | Median reduction |
| --- | --- | --- | ---: |
| Add: local guarded query-lift shortcut | 5.131 (5.001–5.231) | 2.763 (2.709–2.860) | 46.2% |
| Encoding: `decide +kernel` | 3.829 (3.717–4.075) | 2.267 (2.227–2.467) | 40.8% |
| Unary: concrete `List.append` | 3.685 (3.595–3.747) | 3.325 (3.273–3.440) | 9.8% |
| Chain: one restricted `simpa only` | 4.463 (4.352–4.526) | 4.346 (4.269–4.400) | 2.6% |
| Compatibility: restricted simplification | 3.598 (3.480–4.020) | 3.538 (3.491–3.770) | 1.7% |

Percentages describe these local file replays, not total build acceleration or
formal confidence intervals. Summed CPU medians changed 6.202→3.799s (Add),
8.930→6.965s (Encoding), 6.579→6.236s (Unary), 16.288→14.871s (Chain), and
8.007→7.532s (Compatibility). Concurrent task CPU and cumulative profiler totals
can exceed wall time; they must not be read as percentages of elapsed time.

## 1. Add: search through the wrong intermediate monads

Location: `VCVio/OracleComp/Coercions/Add.lean`, especially examples at 341–371.
The first 283 lines compile in about 1.35s; prefixes through 339 and 363 take
2.14s and 3.35s. The costly work is concentrated in the coercion examples, not
merely the definitions or import count. The full-file profile reports 2.92s
cumulative instance synthesis. Four-oracle reassociations with an internal
subspec coercion cost roughly 0.20–0.28s each in that profile.

A scoped `trace.Meta.synthInstance` on the example at 365 records **669 new
goals**, 182 applications of `instMonadLiftT`, 181 of
`instMonadLiftTOfMonadLift`, and 181 of `SubSpec.toMonadLift`. Search enters the
query-to-free-monad lifting route, then tries to produce an impossible lift from
the source computation back into a target query. Transitivity leaves an unknown
intermediate monad, and coproduct left/right alternatives multiply failed paths.
The trace includes repeated irrelevant inhabitation/uniform-instance searches.

This is consistent with the generic transitive `MonadLiftT` instance and the
deliberately low-priority computation lift documented in `Coercions/SubSpec.lean`
at 372–395. The issue is not simply “many type classes”: it is the ordering and
shape of search through an underconstrained intermediate monad. Lean's
[instance-synthesis reference](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/)
explains candidate priorities and treatment of metavariables.

The diagnostic shortcut synthesizes `MonadLiftT` between the two **query
signatures**, then constructs `OracleComp.liftComp` directly. A priority-900
shortcut was too late; requiring only `MonadLift` missed chained query embeddings.
Priority 1100 with the transitive query premise produced the large improvement.

Crucial negative result: that shortcut alone **breaks reflexive lift `rfl`**.
An additional priority-1200 local identity instance restores the tested normal
form; the candidate includes this canary and passes the existing Add examples.
It is not evidence that exporting these instances is safe for every downstream
definitional equality or universe combination. No global instance change is
recommended for immediate landing. An informed fix should constrain the bad
search route or use explicit lifts at the hot call sites, with a dedicated
coercion-coherence and normal-form regression suite before changing priorities.

## 2. Encoding: proof construction, not byte computation itself

Location: `LatticeCrypto/MLKEM/Concrete/Encoding.lean:78`, private theorem
`packByte_bitOf_fin`. Its original `fin_cases n <;> rfl` enumerates all 256 inputs.
The profile attributes about 838ms to metavariable instantiation, 259ms to the
case tactic's interpretation, and 180ms to kernel checking at that declaration.
Synchronous before/after prefixes take 1.083s and 2.812s. The costly generated
proof and its elaboration are the target, rather than changing the executable
encoding algorithm.

Ordinary `decide` hit the default recursion-depth limit and was rejected; that
failed compilation is not counted as a speedup. `decide +kernel` succeeds without
raising limits and leaves a compact decision-proof construction for the kernel.
Its diagnostic kernel time was about 260ms, while the large metavariable
instantiation hotspot disappeared. The complete file and its subsequent lemmas
check successfully.

This is kernel reduction, **not native evaluation** and not an expansion of the
trusted computing base. The distinction is explicit in pinned
[Lean's Decide implementation](https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Elab/Tactic/Decide.lean),
where the kernel branch builds/checks an auxiliary decision proof separately from
the native branch. The one-line candidate preserves the theorem statement,
visibility, and executable definitions.

## 3. Unary planner: eager diagnostic suggestions during speculative elaboration

Locations: `VCVio/ProgramLogic/Tactics/Unary/Internals.lean:1385` and `:1424`,
`probEqPlannerActionPlans` and `probEqPlannerActionPlansForDepth`. These tiny
definitions concatenate planner lists and a literal of `.congr`,
`.congrNoSupport`, and `.swap` constructors.

The whole-file profile initially exposed about 126ms and 123ms of elaboration
at these unexpectedly small definitions. A threshold-zero scoped trace shows
roughly 298ms combined exclusive time in six dotted-identifier elaborations with
expected types still `?m.28` or `?m.55`. A sample of the actual Lean process
contains `Lean.Elab.Term.reverseFieldLookup` on active stacks.

The mechanism is visible in pinned
[Lean.Elab.App](https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Elab/App.lean#L1510):
`reverseFieldLookup` folds over **all environment constants** to collect names.
`resolveDottedIdentFn` calls it eagerly to build suggestions when the expected
type cannot be determined. Overloaded `HAppend` leaves the literal's element
type unsettled during speculative elaboration; error construction is expensive
even though a later elaboration attempt succeeds.

Replacing the two overloaded append expressions with concrete `List.append`
applications supplies the element type earlier. The retained version preserves
the original left association. A small reproducer with the same imports and a
three-constructor enum reproduces roughly 166ms in `.congr`/`.congrNoSupport`/
`.swap` under the overloaded expression; the explicit expression does not show
that hotspot. Its equality is checked by `rfl`.

The local fix is narrow and keeps the planner's action order unchanged. An
upstream fix worth investigating would avoid environment-wide suggestion scans
for discarded speculative errors, or index reverse field lookup. That is a
proposed upstream direction, not an implemented/compiler-benchmarked fix.

## 4. Chain: tuple-existential simplification and repeated inhabitation work

Location: `VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/Chain.lean:761`,
`forkLoggedImpl_sign_support`, plus other hot simplifications around 383, 470,
1372 and 2011. Whole-file cumulative `simp` time is 6.33s, instance synthesis
2.24s, and kernel checking 271ms. Work is distributed across asynchronous proofs;
there is no single 6.33-second serial tactic.

The selected proof expands `extendState`, `flattenStateT`, `mapStateTBase`, nested
simulations and support maps to expose a six-component existential witness.
Synchronous prefixes before/after this lemma take 4.333s and 4.907s. The selected
`simpa` is about 457ms in the original profile.

Its rewrite trace contains 57 `not_isEmpty_of_nonempty`, 21 `nonempty_prod`, and
10 `isEmpty_prod` rewrites, alongside five `Prod.exists` rewrites and handler
unfolding. This establishes repeated product inhabitation/emptiness normalization
while simplifying the witness type, rather than attributing everything vaguely to
the size of the ambient simp set. Rewrite counts alone do not measure their CPU cost.

`simpa?` produced a 21-lemma `simpa only` list that still checks. Whole-file wall
gain is only 2.6%, although summed CPU decreases. The stronger next experiment is
a reusable support/state-transformer equation with an explicit witness shape,
so callers avoid re-expanding handlers and re-normalizing tuple existentials.
That would require an API/proof refactor and coverage of the other hot lemmas;
this investigation does not establish that it improves the total build.

## 5. Compatibility: repeated normalization across state and simulator layers

Location: `VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/Compatibility.lean:445`,
`cmaRealLoggedProdImpl_lift_query_eq_cmaRealAppendProdImpl`. It splits uniform,
random-oracle cache hit/miss, and signing cases. The profile reports 2.91s
cumulative simplification for the file and about 270ms for the selected signing
simplification. Synchronous before/after prefixes take 2.939s and 3.503s.

The focused trace records 27 `bind_pure_comp`, 21 `map_eq_bind_pure_comp`,
20 `StateT.run_mk`, and 13 `Function.comp_apply` rewrites. Handler expansion repeats
across four branches. Nested `mapStateTBase`/`flattenStateT`, pure/bind and function
composition normal forms account for concrete repeated work. No rewrite loop has
been demonstrated; the trace is finite, and repeated names alone do not prove one.

Restricting to `simp?` suggestions did not initially close the signing branch.
Additional `bind_assoc`, `Function.comp_apply`, `pure_bind`, and a final `rfl` were
needed. The resulting patch checks but has only a 1.7% median wall improvement
with overlapping ranges. It is retained as a negative/weak experiment, not a
recommended verbose replacement. A shared handler-composition equality is a
better-informed next hypothesis; its benefit remains unmeasured.

## Controls, limitations, and interpretation

- Source bisection preserved imports and complete commands, with synchronous
  before/after controls where async work could cross the boundary. It localized
  declarations without replacing proofs with `sorry`.
- One Add prefix cut after a doc-comment failed to parse and was discarded.
  An initial import control containing only `module` was also discarded: setup
  `importArts` is not the optional `imports?` override. Corrected controls retained
  the actual imports, as required by pinned `Lean/Setup.lean`.
- Profiling and detailed tracing are separate from timing comparisons. Initial
  profile runs combined stdout/stderr and could interleave JSON messages; the
  runner now separates them. Focused follow-up traces use separate streams.
- The first native sample failed OS permissions; the approved retry succeeded.
  Sleeping worker-thread samples are not interpreted as compiler CPU cost.
- Git history was inspected, but no validated fast historical endpoint with a
  compatible toolchain was established. No historical `git bisect` regression
  claim is made. Source-prefix bisection supplies the localization here; a future
  historical bisect needs a repeatable threshold and passing endpoint builds.
- No linters, visibility safeguards, heartbeat limits, or trust checks were
  disabled. Development trace-option warnings are confined to scratch probes.
- PMF/SPMF-bearing production files were not edited. The two selected candidate
  files do not introduce that retiring surface. Add's identity failure is
  explicitly retained as evidence against blindly changing global priorities.

## Validation and artifacts

Both selected candidates were applied together only in the detached checkout.
The seven-library build passed before and after (3960 jobs). For each controlled
build, the project's `.lake/build` directory was moved aside intact; dependency
artifacts remained cached. Baseline wall/CPU were 135.27s / 1380.43s; candidate
wall/CPU were 138.56s / 1375.99s. This single pair demonstrates **no overall
wall-time improvement** (candidate 2.4% slower), despite the isolated file gains.
It is not enough to establish a build-level regression either. The earlier
131.34s setup build included cache/toolchain refresh effects and is excluded
from this comparison.

Downstream validation passed:

- `lake build VCVioTest LatticeCryptoTest`: 3769 jobs, 15.51s wall.
- `lake env lean VCVioTest/Smoke.lean`: 1.99s; subsequent seven-library warm
  rebuild: 1.34s (cache-hit timing, not a compile-time comparison).
- `./scripts/test-axiomsweep.sh`: executable fixture matrix passed.
- `lake exe axiomsweep --check`: 17,878 declarations across 553 modules;
  40 existing sorry-tainted declarations, **zero non-standard-axiom taint**,
  no new axiom/sorry taint. The baseline was not modified.
- Extern isolation, Interop isolation, and PMF/SPMF boundary checks.

These are library compilation and smoke checks, not execution of every native
cryptographic differential test; the native backends were absent. The Add local
instance experiment passed its file's examples and explicit identity canary, but
was deliberately excluded from downstream candidate validation.

The runner passed Python syntax checking, actual successful replays, invalid-run
count rejection, duplicate-label rejection, stale-toolchain rejection, and a
forced timeout test that recorded the killed child and a nonzero exit status.
The Python syntax check needed OS approval for the system bytecode-cache path;
it did not change production source. No historical bisect or hardware-counter
profiling was claimed.

The persistent small artifacts are the report, runner, measurements, five
candidate patches and dotted-constructor reproducer. Full local logs, profiles,
prefix probes and the native sample are archived at
`.lake/compile-performance/investigation.tar.gz`; they are intentionally not
committed because they include large machine-specific traces. The detached
checkout and saved build trees remain available under the temporary directory
above. Individual run records include commands, source/setup hashes, exit status,
CPU, RSS and output paths.

## Performance guidance used

The workflow follows Lean's [core performance guide](https://github.com/leanprover/lean4/blob/master/doc/perf.md)
and [profiler guide](https://github.com/leanprover/lean4/blob/master/script/PROFILER_README.md):
identify expensive declarations, narrow instrumentation, distinguish elaboration,
kernel and compiler work, and measure an uninstrumented candidate. The
[EPFL profiling wiki](https://vca.epfl.ch/wiki/lean-profiling/) supplies practical
profiling context. Options/defaults were checked against the installed 4.33.1
sources rather than assuming older wiki examples still match. Claims about the
three concrete mechanisms above are supported by local traces and pinned source,
not inferred solely from general optimization advice.
