# Denotational Probability Semantics

> Status: accepted design baseline, 2026-08-21.
>
> This document records the decision reached from
> [`probability-semantics-landscape.md`](probability-semantics-landscape.md) and the executable
> evidence in [`measure-semantics-spike.md`](measure-semantics-spike.md). It is the default for new
> probability-semantics work and resolves the recommendations tracked in
> [VCVio issue #532](https://github.com/Verified-zkEVM/VCVio/issues/532); the landscape remains the
> evidence ledger.

## Decision

VCVio will use a stratified semantics rather than search for one carrier that imitates every
property of `SPMF`:

| Need | Canonical semantic object |
|---|---|
| Qualitative possible returns | PolyFun/Lean return-support and weakest-precondition interfaces |
| Closed, lossless computation | Mathlib `Measure α` plus `IsProbabilityMeasure` |
| Computation parameterized by environment or state | Mathlib `Kernel ρ α` / `Kernel σ (α × σ)` |
| Explicit option, exception, or writer effect | Total measure on `Option α`, `Except ε α`, or `α × ω` |
| Returned values of a possibly nonterminating computation | Subprobability `Measure α` obtained by discarding cutoff mass |
| Finite and infinite execution traces | Probability measure on paths, constructed from measurable kernels |
| Executable exact finite sampling | `FinRatPMF.Raw`; this is an implementation representation, not the denotation |
| Existing proof notation | `evalDist` and `Pr[...]` as a discrete compatibility façade |

Plain Mathlib measures and kernels are the semantic boundary. VCVio will not introduce a global
`Monad Measure`, nor wrap measures merely to make unrestricted Lean functions look measurable.
Where a missing general-purpose lemma or measurable-space instance is needed, it is staged in
`ToMathlib` for now.

## Public surfaces

### Free polynomial programs

[`VCVio/EvalDist/PFunctorMeasure.lean`](../../VCVio/EvalDist/PFunctorMeasure.lean) provides:

- `PFunctor.IsMeasureSpec`, assigning a probability measure to each operation's answer type;
- `PFunctor.FreeM.denote`, with `pure` interpreted by `Measure.dirac` and an operation interpreted
  by `Measure.bind`;
- an unconditional bind law for discrete operation answers;
- a one-operation continuous composition theorem whose measurability and probability hypotheses
  are explicit;
- `IsProbabilityMeasure` for every discrete-answer program;
- equality with the legacy PMF fold and bridges for singleton and measurable predicate events.

`IsProbabilitySpec` remains available during migration. Its induced `IsMeasureSpec` and the
agreement theorem are the compatibility route; new semantic definitions should accept
`IsMeasureSpec` when they do not inherently require point masses or enumeration.

### Monad transformer stacks

[`VCVio/EvalDist/MeasureSemantics.lean`](../../VCVio/EvalDist/MeasureSemantics.lean) packages a
lossless interpretation as `ProbabilitySemantics m`. Transformer semantics do not erase effects:

- `optionT` denotes the underlying `m (Option α)`;
- `exceptT` denotes the underlying `m (Except ε α)`;
- `writerT` denotes the underlying `m (α × ω)`;
- `readerTKernel` is a kernel from environments to results;
- `stateTKernel` is a kernel from initial states to result/final-state pairs.

This is deliberately not a family of global `MonadLiftT` instances. There is no canonical reader
environment or initial state, and flattening option/error immediately would choose a failure policy
before a proof asks for one. Proofs can observe the enriched measure with Mathlib events and maps;
`Measure.dropNone` is the explicit success-only observer.

### Possible nontermination

[`VCVio/EvalDist/ResumptionMeasure.lean`](../../VCVio/EvalDist/ResumptionMeasure.lean) gives a
PolyFun `Resumption` two finite-fuel observations and their returned-output limit:

- `truncateMeasure k computation : Measure (Option β)` is total; `none` means that no result was
  observed within the fuel budget;
- `outputMeasure k computation : Measure β` discards only that cutoff mass and has total mass at
  most one;
- `returnedMeasure computation : Measure β` is the monotone supremum of `outputMeasure` over all
  fuel bounds and has total mass at most one.

These definitions keep three events distinct: a returned `none`, a returned error, and not yet
returning. Any eventual limit semantics must preserve that distinction.

The infinite-trace layer is intentionally not fabricated from arbitrary `Resumption` values.
PolyFun resumptions are probability-free and their continuation functions are arbitrary Lean
functions. A trace law therefore needs a measurable presentation of the coalgebra: measurable
state and observation spaces, a Markov transition kernel, and compatible finite marginals. Once
that interface exists, Mathlib's Ionescu--Tulcea trajectory kernel or projective-limit machinery is
the intended construction.

## The measurability rule

The decisive boundary is simple:

- a function out of a discrete measurable space is automatically measurable;
- an arbitrary Lean continuation out of a continuous answer type is not;
- a `Kernel α β` is exactly a measurable function `α → Measure β` and therefore carries the proof
  needed for composition.

Consequently, VCVio promises ergonomic monadic equations for discrete programs and kernel-based
composition for continuous/state-indexed semantics. It does not promise a universal
`FreeM.denote_bind` theorem for continuous interfaces without a measurable-program invariant.

This is also why merely fixing the output type does not solve the coalgebraic problem. The state
transition itself must be measurable. Kernel construction sites expose that obligation, and the
resulting kernels compose using Mathlib's existing laws.

## Proof-facing compatibility

The migration is denotation-first, not notation-first:

1. Existing `Pr[...]`, support, finite-sum, and crypto theorem statements remain stable.
2. Correspondence lemmas reinterpret those theorems as facts about `Measure`.
3. New continuous, conditional, stateful, or process semantics use `Measure`/`Kernel` directly.
4. Discrete client lemmas migrate only when the measure-backed surface is at least as convenient.

The current gates cover a continuous Gaussian query and continuation, PMF/measure equality, an
arbitrary discrete measurable event, a one-time-pad theorem, effect-preserving transformers,
reader/state Markov kernels, and finite plus limit observations of a delayed resumption.

## Representation policy

New code follows these rules:

1. Use `Measure`, `ProbabilityMeasure`, and `Kernel` names from Mathlib in semantic statements.
2. Use `Measure.sum` and `Measure.dirac` for new discrete distributions unless an executable
   representation is the actual subject.
3. Keep `PMF`/`SPMF` in compatibility adapters and existing discrete proofs while they migrate;
   do not build new foundational APIs around it, and prefer to leave a file's coupling lower than
   you found it. This is a floor and a direction: the surface is retiring, not merely frozen.
4. Keep `FinRatPMF.Raw` for computation and prove that its denotation agrees with a measure.
5. Put missing general measurable-space instances and Mathlib-facing lemmas in `ToMathlib`.
6. Do not open Mathlib, Lean, or cslib contributions during this design migration. A
   probability-free improvement that belongs intrinsically to PolyFun may be proposed there, but
   VCVio-specific probability policy stays in VCVio.

## The retirement budget

Upstream is retiring `PMF`, and this is visible in the pinned tree rather than only in a proposal:
`Mathlib/Probability/ProbabilityMassFunction/` already deprecates `PMF.bernoulli` and
`PMF.binomial` in favour of `ProbabilityTheory.bernoulliMeasure` and `ProbabilityTheory.binomial`.
The core, `toOuterMeasure`, and `toMeasure` are not yet marked, but the family is being dismantled
construction by construction. The direction is settled; only pacing is open.

[`scripts/check-pmf-boundary.sh`](../../scripts/check-pmf-boundary.sh) is therefore a retirement
mechanism, not a freeze. It counts explicit standalone `PMF`/`SPMF` identifiers in Lean source,
excluding comments and string literals. That count is a reviewable syntactic proxy for migration
work, not a semantic dependency analysis. It has three modes:

- **ceiling** (every build, blocking): no file may exceed its recorded count. A file absent from
  the baseline has an allowance of zero, so new coupling cannot appear without an explicit,
  reviewable baseline change.
- **report** (pull requests, advisory): scans the base ref and prints the aggregate and largest
  per-file source-count deltas, so every change surfaces its effect on the retiring surface.
- **ratchet** (opt-in, not in CI): every touched file that still carries coupling must decrease,
  unless [`scripts/pmf_boundary_holds.tsv`](../../scripts/pmf_boundary_holds.tsv) records a reason.
  This is the tool for a deliberate reduction pass.

The middle mode is advisory rather than blocking on purpose. Enforcing decrease-on-touch was tried
against the open stack first, and it would have failed every ready pull request: #542 only touches
`OracleComp/OracleSpec.lean` because that file carries one incidental `PMF` mention, and #540
restructures the Rényi files, moving 27 occurrences out of one and 29 into another while closing a
`sorry`. A gate that turns unrelated work into a boundary failure gets neutralised by holds, and
the holds then rot. The ceiling is the hard invariant; the report is what keeps the trend visible.

`SPMF` counts toward both, because `SPMF := OptionT PMF` makes every use a transitive `PMF`
dependency. Counting only bare `PMF` measured 935 occurrences across 78 files; counting both
measures 2146 across 120 — so 42 files carried coupling that the guard could not see at all.
Compound names such as `FinRatPMF` still do not count.

Updating the baseline, or adding a hold, is an explicit review action and not a routine response to
CI. A hold should name what would let it be removed.
[`scripts/test-pmf-boundary.sh`](../../scripts/test-pmf-boundary.sh) fixtures both modes, including
the `SPMF`-versus-`PMF` overlap that would otherwise double-count.

## Local Mathlib-facing utilities

The `ToMathlib` surface is intentionally small. Each entry below was checked against the pinned
Mathlib tree, and each carries the condition under which it should be deleted.

| Local declaration | Upstream status (checked 2026-08-22) | Delete when |
|---|---|---|
| `PMF.toMeasure_bind` | Mathlib has `toMeasure_pure` and `toMeasure_map`, but for `bind` only the applied `toMeasure_bind_apply` | the measure-level equality lands upstream, or `PMF` is removed and the lemma becomes moot |
| `BitVec` discrete instances | `MeasurableSpace/Instances.lean` covers `Bool`, `ℕ`, `ℤ`, `ℚ`, `Fin n`, `ZMod n`; not `BitVec` | `BitVec` joins that file |
| `Option` coproduct measurable space | Mathlib has `Sum.instMeasurableSpace`; no `Option` counterpart found | an `Option` instance lands upstream |
| `Except` coproduct measurable space | `Except` is its own inductive (`Init/Prelude.lean`), not `Sum`, so `Sum.instMeasurableSpace` does not apply | an `Except` instance lands upstream, or `Except` is redefined via `Sum` |
| `Measure.dropNone` | **Overlaps `Measure.comap some`** — see below | the overlap is resolved in favour of upstream |
| `Measure.bind_mono_right`, `Measure.iSup_apply_of_monotone` | no counterpart found: Mathlib has no `Measure.bind` monotonicity lemma, and no measure-specific `iSup`-applied-to-a-set lemma for monotone families | either lands upstream |

**The `dropNone` overlap, recorded rather than left implicit.** `Measure.comap f μ s = μ (f '' s)`
for injective `f` with measurable images (`Measure.comap_apply`), and `some` satisfies both under
the coproduct structure, so `dropNone` and `comap some` agree on measurable sets. The `bind`
formulation is kept because `comap` is guarded by a `dif` on those side conditions, which every
downstream rewrite would then have to discharge, whereas `bind` composes directly with the Giry
structure used everywhere else here. An agreement lemma would make Mathlib's `comap` API reachable
and is worth adding; its absence is a gap in this file, not a reason for the definition.

These declarations should track upstream naming and hypotheses closely. No VCVio-specific oracle
policy belongs in this layer.

## Settled questions

- **Total outcome or subprobability result?** Both, at different observation layers: effects use a
  total outcome measure; success-only and termination observations use a submeasure.
- **Failure or divergence?** Returned failure is data. Divergence is missing output mass. Cutoff is
  an approximation marker, not either one.
- **Point distribution or measure-valued query specification?** Measure-valued is the general
  semantic capability. The pointwise PMF capability remains a discrete compatibility input.
- **Discrete measurable spaces?** Install concrete lawful instances, such as `BitVec`, and
  coproduct/product constructions. Do not install a blanket finite-type instance that could
  compete with Borel structures.
- **How does state compose?** As a kernel retaining final state, not by fixing an initial state and
  pretending that evaluation is a monad morphism.
- **Does proof notation change now?** No. `Pr[...]` remains, with measure correspondence theorems.
- **What owns infinite computation structure?** PolyFun owns probability-free resumptions,
  truncation, and coalgebra. VCVio supplies probabilistic readings; Mathlib supplies kernels and
  measure extension theorems.

## Remaining work

The following are implementation questions, not reasons to reopen the architecture:

1. prove the returned-measure fixpoint/continuity laws and formulate almost-sure termination;
2. formulate the smallest measurable-coalgebra interface that yields finite prefix kernels and an
   Ionescu--Tulcea trace law;
3. port expectation, independent-product, coupling, total-variation, and Rényi statements to
   measure-first foundations while retaining discrete corollaries;
4. connect indicator integrals and kernel composition to the evolving `Std.WP`/`vcgen` surface;
5. add denotation theorems from `FinRatPMF.Raw` to finite measures;
6. reassess local utilities at every Mathlib/PolyFun/cslib/toolchain update and delete them as soon
   as stable upstream surfaces subsume them.

Higher design churn is acceptable while completing these items. Compatibility is required at the
proof-facing boundary, not for internal representations that upstream is already steering away
from.
