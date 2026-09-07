# Probability Semantics for Computations: Landscape and Design Options

> Status: historical evidence survey and decision record. For current implementation guidance,
> use [`denotational-probability-semantics.md`](denotational-probability-semantics.md) and
> [`docs/agents/probability.md`](../agents/probability.md).
>
> Original snapshot: 2026-08-21. Section 19 preserves that audit in its original time context.
> Section 20 records the focused 2026-08-30 recheck against current VCVio `main`, VCVio's pinned
> PolyFun checkout, and PolyFun's canonical `main`. Unless §20 explicitly supersedes a volatile
> fact, read it as a claim about the original snapshot rather than current upstream state.
>
> The original repository snapshot used Mathlib/PolyFun `v4.32.2`; implementation findings were
> rechecked on the then-current Mathlib `v4.33.0` and PolyFun `v4.33.2` pins. Open-PR descriptions
> and upstream-`master` observations are explicitly identified below.
>
> **Evidence discipline.** Every claim that upstream already provides something must
> be checked mechanically — reading the declaration in the pinned tree, or `exact?`
> against it — never by grepping for a name. PolyFun#144 had to retract four such
> claims from its own companion survey for exactly this reason. Each entry in §19
> records the method as well as the verdict.

## Purpose

At the original snapshot, VCVio gave probabilistic meaning to computations through `SPMF`, a
small `OptionT PMF` layer. That design had been unusually effective for cryptographic proofs:
it supports ordinary Lean monad notation, point probabilities, finite sums, failure,
couplings, statistical distance, and a fairly strong program logic. It is also sitting
on top of an upstream abstraction, `PMF`, that Mathlib is actively trying to retire in
favor of measures.

This is not just a representation-change question. The surrounding projects now need
several meanings of “probability semantics”:

- exact finite distributions for existing VCVio and ArkLib games;
- qualitative reachability independent of any choice of probabilities;
- expectations, costs, couplings, and divergences;
- measure-theoretic independence and conditioning for Bluebell;
- bounded and unbounded execution for PolyFun's coalgebraic computations;
- a semantic base that can be exposed through `mvcgen`, VCVio's `vcgen`, and Iris-style
  weakest preconditions.

The central conclusion of this survey is that no single upstream type is a drop-in
replacement for every role currently played by `SPMF`. The robust common direction is
to separate the roles first, preserve the existing proof-facing API during experiments,
and decide the quantitative backend only after testing the alternatives against real
consumers.

## Executive Summary

The following decisions look safe independently of the eventual distribution backend.

1. **Qualitative support belongs to `MonadAttach`, not to probability.** PolyFun's
   exact `MonadAttach` support gives a probability-independent account of possible
   returns. The implementation proposed in the original survey has since landed and is
   included in VCVio's PolyFun pin; see §20.
2. **Discrete and general probability should be different capability layers.** A
   pointwise `α → ℝ≥0∞` API is excellent on discrete types and wrong as the universal
   interface for continuous measures. Conversely, raw `Measure` is too measurability-
   sensitive to be a plain Lean monad on all types.
3. **Explicit failure and divergence are different.** Existing `OptionT` failure is an
   observable outcome. Nontermination of an infinite computation is missing output
   mass. A single `none` should not silently mean both.
4. **Infinite computation has two useful semantics.** The distribution of terminating
   outputs is a subprobability measure; the distribution of finite and infinite traces
   is a probability measure on paths, assuming a lossless probabilistic environment.
   Almost-sure termination connects the two but does not identify them.
5. **Do not expose `MonadLiftT m Measure` as the general solution.** Mathlib's Giry bind
   composes measures only along measurable functions. A measure-native layer must make
   measurable spaces and kernel measurability explicit, or specialize to the discrete
   `⊤` measurable space where every function is measurable.
6. **Keep the current `evalDist`/`Pr[...]` surface during migration.** It is the stable
   interface used throughout VCVio and ArkLib. Backend correspondence theorems should
   come before any attempt to rewrite clients.
7. **The 2026-08-21 urgency picture separated backend pressure from program-logic
   churn.** At that snapshot, `PMF` was untouched at Mathlib `v4.34.0-rc1`, and the PR
   that would deprecate the type was a draft, so no upstream deadline forced a backend
   choice. Meanwhile the *program-logic* substrate was moving quickly:
   `mvcgen` is being retired in favour of `vcgen`, Loom's WP design is landing in Lean
   core, and VCVio's `loom2` pin targets an already-superseded toolchain. The scarce
   resource is attention on the program-logic side, not the distribution side, and the
   two migrations should not be scheduled into the same window (§2.5.1, §5.3).

The unresolved architectural choice is whether the long-term quantitative core should
be:

- `SPMF` with first-class views into Mathlib measures;
- discrete Mathlib measures as the primary finite semantics;
- a locally bundled subprobability measure/kernel built over Mathlib `Measure`;
- or, most plausibly, a stratified combination of these.

The experiments now select the stratified combination. This document retains the rejected
alternatives and evidence; the accepted interfaces and migration policy are recorded in the
design baseline linked above.

## 1. Vocabulary: Several Notions Currently Called Support or Failure

The first design task is to stop overloading a few convenient words.

| Notion | Intended meaning | Natural interface | Important restriction |
|---|---|---|---|
| Return reachability | A value can be returned along some execution | `MonadAttach.CanReturn`; exact monadic support | No probability is required |
| Discrete atomic support | The singleton `{x}` has nonzero mass | `μ {x} ≠ 0`, or a point-mass function | Meaningful for atomic/discrete semantics |
| Topological support | Every neighborhood of `x` has positive measure | Mathlib `Measure.support` | Requires topology; not computational reachability |
| Almost-sure property | A measurable event has complement of measure zero | `μ s = 1`, `∀ᵐ x ∂μ, p x` | Does not imply every reachable value satisfies `p` |
| Explicit failure | The program returns a distinguished failure result | A total distribution on `Option α` or `Except ε α` | Failure is observable output mass |
| Divergence/loss | No return value is produced | A subprobability measure on `α` | Total mass is below one |
| Fuel exhaustion | A finite observation has not resolved yet | `Option α` in a bounded run | Must be discarded, not counted as final failure, when taking an output limit |
| Infinite trace | The complete sequence of states, queries, or answers | A probability measure on a path space | Requires consistent measurable finite-prefix semantics |

For existing finite `OracleComp`, nontermination is not an issue: its free-monad syntax
is well-founded. `OptionT` genuinely represents failure. PolyFun `ITree`, resumptions,
and returning dynamical computations introduce the new possibility that every finite
run is unresolved while the computation continues forever.

There is also an important logical asymmetry:

- exact return support can be defined for arbitrary monads using the operational laws
  of `MonadAttach`;
- nonzero singleton probability characterizes support only in a discrete atomic model;
- a continuous distribution can assign probability zero to every singleton while still
  having nonempty topological support.

Therefore the existing bridge “`x ∈ support` iff `Pr[= x] ≠ 0`” should remain a theorem
for discrete compatible semantics, not the definition of support in the general theory.

## 2. VCVio Semantics at the Original Snapshot

### 2.1 `SPMF` and observable probabilities

[`ToMathlib/ProbabilityTheory/SPMF.lean`](../../ToMathlib/ProbabilityTheory/SPMF.lean)
defines

```lean
def SPMF := OptionT PMF
```

Thus `SPMF α` is definitionally a probability mass function on `Option α`:

- `some x` carries successful output mass;
- `none` carries failure or missing mass;
- `gap` is the mass at `none`;
- bind multiplies and sums point masses in the expected discrete way.

This encoding has two useful readings that coincide for finite computations:

1. a total distribution over the explicit outcome type `Option α`;
2. a subprobability distribution on `α`, obtained by forgetting `none`.

They stop coinciding as explanations once `none` must distinguish explicit failure from
bounded-run cutoff or divergence.

[`VCVio/EvalDist/Defs/Basic.lean`](../../VCVio/EvalDist/Defs/Basic.lean) exposes the
current public observation layer. Given `[MonadLiftT m SPMF]`, it provides:

- `evalDist mx : SPMF α`;
- `probOutput mx x` and `Pr[= x | mx]`;
- `probEvent mx p` and `Pr[p | mx]`;
- `probFailure mx` and `Pr[⊥ | mx]`.

The event probability is already phrased through the outer measure associated to the
underlying PMF, while most proof lemmas reduce it back to countable sums. This is a useful
existing bridge: clients see discrete notation, but the event-level definition already
acknowledges measure semantics.

### 2.2 `SemanticsVia` is an existing abstraction seam

[`VCVio/EvalDist/Defs/Semantics.lean`](../../VCVio/EvalDist/Defs/Semantics.lean)
defines `SemanticsVia m Obs`. It separates:

- an internal semantic monad `Sem`;
- a monad morphism `interpret : m α → Sem α`;
- an observation `observe : Sem α → Obs α`.

The observation does not have to be a monad morphism. This matters for stateful or
instrumented computations whose hidden state is discarded only at the observation
boundary. `SPMFSemantics` and `PMFSemantics` are current specializations.

This is a better migration seam than requiring every source monad to lift directly into
every future probability representation. A measure-oriented design should preserve the
idea even if it changes the observation capabilities.

### 2.3 Oracle semantics

[`VCVio/OracleComp/EvalDist.lean`](../../VCVio/OracleComp/EvalDist.lean) gives the free
oracle computation two separate interpretations:

- `[IsProbabilitySpec spec]` assigns a `PMF` to every query and folds the free monad via
  `simulateQ`;
- the `SetM` interpretation sends every query to `Set.univ` and defines qualitative
  support independently of probability.

`IsUniformSpec` strengthens `IsProbabilitySpec` with finite/inhabited result types and
uniform query distributions. Under this stronger assumption, `EvalDistCompatible`
connects qualitative support to nonzero output probability. This division is already
conceptually close to the desired long-term one; the main improvement is to give the
qualitative half a standard upstream interface and the quantitative half a backend not
tied to deprecated PMF APIs.

### 2.4 Existing quantitative theory

The current SPMF layer is not only an evaluator. It supports a significant body of
theory that a replacement must either preserve or deliberately supersede.

| Capability | Representative source | Backend-sensitive content |
|---|---|---|
| Point/event/failure algebra | [`EvalDist/Monad`](../../VCVio/EvalDist/Monad) | Countable sums and point masses |
| Finite support | [`EvalDist/Defs/Support.lean`](../../VCVio/EvalDist/Defs/Support.lean) | Enumeration and membership bridges |
| Expectations | [`EvalDist/Expectation.lean`](../../VCVio/EvalDist/Expectation.lean) | `ℝ≥0∞` sums, increasingly close to `lintegral` |
| Independent products | [`EvalDist/IndepProduct.lean`](../../VCVio/EvalDist/IndepProduct.lean) | Product distributions and factorization |
| Total variation | [`EvalDist/TVDist.lean`](../../VCVio/EvalDist/TVDist.lean) | Discrete pointwise definition |
| Rényi divergence | [`EvalDist/RenyiDivergence.lean`](../../VCVio/EvalDist/RenyiDivergence.lean) | Discrete density ratios |
| Couplings | [`ToMathlib/ProbabilityTheory/Coupling.lean`](../../ToMathlib/ProbabilityTheory/Coupling.lean) | An SPMF on a product with fixed marginals |
| Optimal finite couplings | [`ToMathlib/ProbabilityTheory/OptimalCoupling.lean`](../../ToMathlib/ProbabilityTheory/OptimalCoupling.lean) | Finite-dimensional compactness |
| Expected query cost | [`QueryCost.lean`](../../VCVio/OracleComp/QueryTracking/QueryCost.lean) and [`WriterCost.lean`](../../VCVio/OracleComp/QueryTracking/WriterCost.lean) | Expectations of instrumented runs |
| Relational logic | [`ProgramLogic/Relational`](../../VCVio/ProgramLogic/Relational) | Coupling existence and quantitative relational WP |
| Executable finite distributions | [`FinRatPMF.lean`](../../ToMathlib/ProbabilityTheory/FinRatPMF.lean), [`EvalDist/Instances/FinRatPMF.lean`](../../VCVio/EvalDist/Instances/FinRatPMF.lean) | Array-backed `Raw` representation and its `SameDist` quotient |

The last row deserves emphasis, because it is easy to forget when reasoning about
"the" backend. `FinRatPMF` is a **third** discrete representation already in tree:
`FinRatPMF.Raw α` is an array of `(α × ℚ≥0)` pairs with a computable `Monad`
instance, and `FinRatPMF α` is its quotient by distributional equality. It reaches
the generic API through its own `MonadLift Raw PMF` and `MonadLiftT Raw SetM`
instances rather than through `SPMF`.

Its existence constrains the design in a way none of the backend options in §8
address on their own: whatever becomes primary, an **executable** discrete layer has
to survive, and `Measure` is irreducibly noncomputable. The realistic reading is that
`FinRatPMF.Raw` stays the computational representation and the backend question is
only about the *denotational* one — but that should be stated, not assumed.

The measure-theory migration is easiest for expectations and event probabilities, whose
natural general form is an integral. It is harder for finite support, pointwise distance
formulas, and existing automation whose normal forms explicitly contain `tsum`.

### 2.5 Program logic and automation

VCVio now has three related relational carriers:

- a `Prop`-valued exact-coupling layer;
- a probability-valued layer;
- an `ℝ≥0∞` quantitative expectation layer.

The coherence results in
[`ProgramLogic/Relational/Loom`](../../VCVio/ProgramLogic/Relational/Loom) show that this
is not merely duplication: indicator postconditions connect qualitative couplings to
quantitative mass, and probability is a bounded presentation of the quantitative value.

[`docs/agents/program-logic.md`](../agents/program-logic.md) documents two automation
families:

- Lean core `mvcgen`, built around `Std.Do`, `WPSound`, and `MonadAttach`;
- VCVio `vcgen`/`rvcgen`, which understands probability notation, raw expectation `wp`,
  oracle simulation, coupling rules, and VCVio-specific registries.

The long-term goal should not be to make probability semantics depend on a particular
tactic. Instead:

1. semantic laws should be stated at the appropriate carrier;
2. `WPSound`/`MonadAttach` should provide the common qualitative adequacy boundary;
3. `mvcgen` and `vcgen` should consume shared laws where their proof modes overlap;
4. VCVio should retain domain-specific quantitative and relational automation.

#### 2.5.1 The upstream side of this picture is moving

Three facts about Lean core were not visible when the paragraphs above were first
written, and together they change what "consume shared laws" will mean.

**There are two WP layers in core, not one.** `Std.Do` — the layer `mvcgen` drives — is
`PostShape`-indexed and `SPred`-based, effectively `Prop`-valued. Alongside it, Lean
`v4.33.0` ships `Std.Internal.Do`, which is **lattice-generic**:

```lean
class abbrev Assertion (α : Type w) := CompleteLattice α        -- Lean.Order, not Mathlib
class WP (Prog : Type u) (Value : outParam _) (Pred : outParam _) (EPred : outParam _)
    [Assertion Pred] [Assertion EPred] where
  wpTrans : Prog → PredTrans Pred EPred Value
  wp_trans_monotone (x : Prog) : wpTrans x |>.monotone
```

Pre- and postconditions are compared with `⊑` rather than implication, so an `ℝ≥0∞`
assertion carrier is expressible directly. On Lean master this layer has moved out of
`Internal` into a public `Std.WP` namespace.

**`mvcgen` is being retired.** `mvcgen'` was renamed to `vcgen` (lean4#14146,
2026-06-22); `vcgen` lives in `Lean.Elab.Tactic.VCGen` and dispatches on `Std.WP.wp`;
`experimental.vcgen` gates it (lean4#14870); and `mvcgen` is deprecated on master
(`deprecated_syntax … "use `vcgen` instead" (since := "2026-08-21")`). That deprecation
is *not* in `v4.34.0-rc2`, so it lands in v4.35.

**This is Loom's design arriving upstream.** VCVio's quantitative and relational
program logic is built on the pinned [`loom2`](https://github.com/quangvdao/loom2)
fork, whose `Loom.WP` is `WP m Pred EPred` with `Assertion` as a `CompleteLattice`
alias over `Lean.Order` — structurally the same class, by the same author as
`Std.Internal.Do`. VCVio already supplies the `Lean.Order.{PartialOrder,
CompleteLattice}` adapters for `ℝ≥0∞` and for its `Prob` carrier.

Two consequences for this document:

- The eventual port of VCVio's program logic from `Std.Do'` (loom2) to `Std.WP` (core)
  is a **rename-and-repoint, not a redesign**. That is a much better position than the
  original §12.4 assumed, and it means the `ℝ≥0∞` carrier is a safe long-term bet.
- `loom2` is nevertheless the most fragile pin in the stack: it targets a Lean
  **v4.32.0** toolchain, it is a personal fork rather than a released library, and its
  upstream successor is still in an `Internal` namespace at v4.34. It should be tracked
  in this document as a first-class dependency risk, not left implicit.

What core's `vcgen` will *not* absorb is the domain layer: lowering `Pr[…]` and
`evalDist`-equality goals into `wp` goals, oracle-query specs, `simulateQ` stepping,
support/indicator leaf closure, and the `@[vcspec]` / `@[wpStep]` registries. Core does
expose extension points for these (the `@[spec]` database, `vcgen [terms]`, and
`mvcgen_trivial_extensible`).

One immediate consequence is a name collision rather than a semantic one: core already
declares a bare `vcgen` tactic token at `v4.33.0`, so VCVio's `vcgen` now shares a
leading token with it and survives only by careful syntax-kind splitting.

## 3. Consumers at the Original Snapshot

### 3.1 VCVio examples

Representative canaries cover different parts of the API:

- [`Examples/OneTimePad/Basic.lean`](../../Examples/OneTimePad/Basic.lean) exercises
  finite uniform sampling, distribution equality, support, and privacy;
- [`Examples/EvalDistCompatible/Basic.lean`](../../Examples/EvalDistCompatible/Basic.lean)
  demonstrates why qualitative and quantitative interpretations must be separately
  supplied through transformers;
- [`Examples/ProgramLogic/UnaryProbability.lean`](../../Examples/ProgramLogic/UnaryProbability.lean)
  and [`Relational.lean`](../../Examples/ProgramLogic/Relational.lean) exercise expectation
  and coupling proof modes;
- [`Examples/OneTimePad/UC.lean`](../../Examples/OneTimePad/UC.lean) tests observation
  through the monad-parametric interaction runtime.

A viable migration must preserve these proof shapes or provide mechanical, well-
documented replacements.

### 3.2 ArkLib

[ArkLib](https://github.com/Verified-zkEVM/ArkLib) has two distinct dependencies on the
current probability stack.

First, protocol and security definitions use VCVio computations and `Pr[...]` notation.
Those clients should benefit from a compatibility-preserving VCVio migration.

Second, ArkLib has its own finite probability library, notably
[`Data/Probability/Notation.lean`](https://github.com/Verified-zkEVM/ArkLib/blob/main/ArkLib/Data/Probability/Notation.lean)
and
[`Data/Probability/Instances.lean`](https://github.com/Verified-zkEVM/ArkLib/blob/main/ArkLib/Data/Probability/Instances.lean).
It works directly with `PMF`, uniform finite distributions, count/cardinality formulas,
`tsum`, mapping, and outer measures. These lemmas support Schwartz–Zippel bounds,
collision estimates, proximity arguments, and many explicit finite averages.

The coupling is tighter than "has its own lemmas" suggests. ArkLib's sampling notation
*elaborates into `PMF` do-notation*: `$ᵖ` is literally `PMF.uniformOfFintype`, and

```lean
Pr_{ let x ←$ᵖ F; let y ←$ᵖ F }[x = y]
```

expands to `(do let x ← PMF.uniformOfFintype F; …; return x = y) True`, applying the
resulting `PMF Prop` at `True`. Supporting lemmas then unfold `PMF.bind`, `PMF.pure`,
and `DFunLike.coe` directly. So `PMF` is not merely a representation ArkLib's lemmas
mention — it is the elaboration target of its surface syntax, and any replacement must
either preserve that elaboration or come with a notation migration.

ArkLib also pins VCVio `v4.32.2`, two releases behind. Getting it onto a current VCVio
is a prerequisite for, not a consequence of, any semantic change.

Consequently “migrate VCVio” is not enough to migrate ArkLib. The eventual plan needs a
standalone discrete probability façade with strong finite-sum and uniformity lemmas,
whether its representation is `PMF`, `DiscreteMeasure`, or `Measure.sum` of Dirac masses.

### 3.3 Coalgebraic execution

Current VCVio main contains the bridge to PolyFun dynamical computations in
[`OracleComp/Coinductive`](../../VCVio/OracleComp/Coinductive):

- `Machine.lean` identifies oracle machines with returning `DynComputation`s;
- `Responder.lean` gives stateful randomized handlers in `SPMF`;
- `WiredRun.lean` evaluates a machine for a finite fuel budget;
- `Bridge.lean` embeds finite `OracleComp` syntax into `ITree`.

PolyFun `v4.32.2` supplies the probability-free structure:

- `DynComputation.unroll` and `runWith` produce a bounded `FreeM` computation with an
  `Option` result;
- `Resumption.truncate` agrees with bounded unrolling;
- `Run_n` packages finite multi-step behavior;
- `DynSystem.Run` and `ITree` describe potentially infinite behavior.

An earlier VCVio development contained `RunLimit`, which discarded unresolved `none`
mass from each truncation, proved the resulting SPMFs monotone, and took their ω-supremum.
It provided a fixpoint equation, almost-sure termination, and approximate implementation
bounds. That file is not on current main, so it is evidence and a test specification—not
an API to restore unchanged.

The upstreamed PolyFun layer is now better factored than the old implementation: it owns
finite truncation and coalgebraic structure without importing probability. VCVio can add
one or more probabilistic readings downstream.

## 4. Mathlib Probability Infrastructure

### 4.1 The active PMF transition

The Mathlib version pinned by VCVio still contains the familiar `PMF` monad. Current
upstream work points elsewhere:

- [mathlib4#42821](https://github.com/leanprover-community/mathlib4/pull/42821),
  **“deprecate PMF”**, proposes expressing discrete distributions as sums of scaled
  Dirac measures;
- [mathlib4#42908](https://github.com/leanprover-community/mathlib4/pull/42908)
  adds measure-bind commutation infrastructure intended to replace `PMF.bind_comm`;
- [mathlib4#42909](https://github.com/leanprover-community/mathlib4/pull/42909)
  moves finite uniform distributions from PMF to `Measure`;
- [mathlib4#34138](https://github.com/leanprover-community/mathlib4/pull/34138)
  proposes `DiscreteMeasure α`, represented by a weight function and interpreted as a
  sum of Dirac measures.

All four were open at the snapshot date, but they are **not one program** and their
statuses differ in ways that matter:

- **#42821 is a draft.** It deprecates the `PMF` *type* itself
  (`@[deprecated ... (since := "2026-07-31")]`) along with `instFunLike`, `PMF.ext`,
  `PMF.support`, and `PMF.toOuterMeasure`. Being a draft, it is the weakest of the four
  as a scheduling signal.
- **#42908 and #42909 are non-draft** and are #42821's prerequisites.
- **#34138 (`DiscreteMeasure`) is a separate, older proposal** by a different author,
  opened 2026-01-19 and last touched 2026-07-28. #42821 does *not* endorse it; the
  spelling that PR's description names as preferred is `Measure.sum` together with
  `Measure.dirac`, citing `ProbabilityTheory.poissonMeasure` and `geometricMeasure` as
  the models. Treating `DiscreteMeasure` as the destination would be a bet against the
  PR that actually drives the deprecation.

Two further facts change the urgency in opposite directions.

**The transition is further along than "all open" suggests.** Released Mathlib already
deprecates the PMF *distributions*: `PMF.bernoulli` in favour of
`ProbabilityTheory.bernoulliMeasure` (since 2026-04-07) and the `PMF.binomial` family in
favour of `ProbabilityTheory.binomial` (since 2026-04-07 and 2026-05-29). The idiom is
visible in their definitions — `bernoulliMeasure x y p := toNNReal p • dirac x +
toNNReal (σ p) • dirac y` over an arbitrary `[MeasurableSpace X]`, and
`poissonMeasure r := Measure.sum (fun n ↦ … • .dirac n)`. So the direction is not
speculative; it is shipping, one distribution at a time.

**But nothing is forced yet.** At `v4.34.0-rc1` the `PMF` type carries no deprecation
and `PMF.uniformOfFinset` / `uniformOfFintype` / `ofMultiset` are unchanged. The v4.34
cycle is therefore a preparation window rather than a deadline.

VCVio should align with the direction, adopt the `Measure.sum`/`Measure.dirac` spelling
in anything it writes new, and still avoid depending on the draft PR's exact
declarations until they merge and survive a release cycle.

### 4.2 Giry bind is not an ordinary Lean monad

[`MeasureTheory/Measure/GiryMonad.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Measure/GiryMonad.lean)
equips `Measure α` with a measurable space, `join`, and `bind`. The defining law is the
expected integral:

```text
(μ.bind κ) s = ∫⁻ x, κ x s ∂μ
```

but only when `s` is measurable and `κ` is appropriately measurable. The monad laws
likewise carry measurability hypotheses. This is the correct Giry monad on the category
of measurable spaces and measurable functions, not a `LawfulMonad Measure` on Lean's
category of all types and functions.

This distinction rules out a direct global replacement such as:

```lean
-- Deliberately not a proposed interface
instance : Monad Measure := ...
```

For discrete computation semantics one can use `@Measure α ⊤`, where every function is
measurable. This is a valuable adapter, but it must stay explicit: installing `⊤` as an
ambient measurable-space instance would conflict with applications that need a genuine
Borel or generated σ-algebra.

### 4.3 Probability and finite measures

Mathlib provides bundled
[`ProbabilityMeasure`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean)
and
[`FiniteMeasure`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean)
types. These are subtypes of `Measure` with total-mass properties and useful topologies,
maps, normalization, and integral APIs.

At the snapshot date there is no corresponding general bundled type for measures with
`μ univ ≤ 1`, nor a standard sub-Markov-kernel class. `IsZeroOrProbabilityMeasure` and
`IsZeroOrMarkovKernel` allow only mass zero or mass one; they do not represent arbitrary
termination probabilities.

A local subprobability wrapper would therefore fill a real gap rather than merely rename
an upstream structure. The likely mathematical core is small:

```lean
structure SubprobabilityMeasure (α : Type*) [MeasurableSpace α] where
  toMeasure : Measure α
  measure_univ_le_one : toMeasure Set.univ ≤ 1
```

The engineering work is not small: it needs measurable map/bind, laws, an order and
directed-sup theory, probability normalization, and bridges to discrete observations.
Because `Measure α` is a complete lattice, increasing-chain suprema are promising. The
mass-at-most-one subtype is closed under directed suprema; it should not be assumed
closed under arbitrary suprema.

### 4.4 Kernels and infinite processes

Mathlib's
[`Probability/Kernel`](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Probability/Kernel)
library supplies measurable kernels, Markov kernels, composition, products,
disintegration, conditional distributions, and categorical presentations such as
[`Stoch`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Probability/Kernel/Category/Stoch.lean).
Mathlib also already exposes the Giry construction as the functor
[`MeasCat.Giry`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Category/MeasCat.lean).
That categorical surface confirms the semantic direction, but it does not turn `Measure` into an
unrestricted `Type → Type` monad usable by `FreeM.liftM`; measurable morphisms remain the arrows.

For infinite behavior, two upstream constructions are particularly relevant:

- the
  [Ionescu–Tulcea trajectory kernel](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean)
  extends consistent sequential kernels to measures on countable trajectories;
- the
  [projective-measure](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Constructions/Projective.lean)
  and
  [Kolmogorov process](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Probability/Process/Kolmogorov.lean)
  infrastructure constructs measures from compatible finite-dimensional marginals.

These are a natural match for PolyFun finite prefixes, but they are not automatic. An arbitrary
`Resumption` does not carry measurable state or continuation data. A
probabilistic coalgebra must provide measurable state/direction spaces, measurable
transition kernels, and compatibility between finite-prefix laws. Starting with finite
or countable discrete interfaces avoids many of the hardest measurable-space issues and
is sufficient for present cryptographic examples.

### 4.5 Gaps around distances and couplings

Mathlib has strong ingredients—product measures, marginals, signed-measure total
variation, Radon–Nikodym derivatives, and log-likelihood ratios—but it does not currently
offer a single probability-distance and coupling API that directly replaces VCVio's
discrete `TVDist`, Rényi, and `SPMF.IsCoupling` stack.

This suggests an incremental split:

- put genuinely general measure lemmas near Mathlib abstractions;
- retain discrete formulas as corollaries or a discrete façade;
- generalize VCVio couplings to measures on products only when a concrete consumer needs
  it;
- avoid blocking the basic evaluator migration on a complete divergence library.

## 5. cslib and PolyFun

### 5.1 cslib

[cslib](https://github.com/leanprover/cslib) is relevant primarily below the semantics
layer.

- [`Cslib/Foundations/Data/PFunctor/Free.lean`](https://github.com/leanprover/cslib/blob/v4.32.0/Cslib/Foundations/Data/PFunctor/Free.lean)
  contains the polynomial free-monad foundation used by PolyFun and VCVio.
- [`Cslib/Probability/PMF.lean`](https://github.com/leanprover/cslib/blob/v4.32.0/Cslib/Probability/PMF.lean)
  contains temporary PMF utilities such as products, marginals, uniform transport, and
  posterior distributions.
- cslib's perfect-secrecy and secret-sharing developments still consume PMF directly,
  while its PAC-learning development is already measure-theoretic.
- [cslib#731](https://github.com/leanprover/cslib/pull/731) and
  [cslib#803](https://github.com/leanprover/cslib/pull/803) continue the free-monad and
  polynomial-functor upstreaming path.
- [cslib#813](https://github.com/leanprover/cslib/pull/813) is cleaning up the crypto
  development against Mathlib abstractions while still exercising PMF, making it a
  useful secondary migration canary.

The likely ownership boundary is:

- cslib: generic computation syntax and broadly reusable discrete/measure lemmas;
- Mathlib: measure theory, kernels, distributions, and general probability;
- PolyFun: probability-free algebraic and coalgebraic computation structure;
- VCVio: probability semantics for oracle computations, cryptographic observations,
  couplings, cost, and migration façades.

This boundary should be revisited if cslib adopts Mathlib's PMF migration, but cslib is
not presently an alternative semantic backend.

### 5.2 PolyFun support and weakest preconditions

At the original snapshot, two PolyFun PRs proposed removing important accidental dependencies
between probability and program logic. Both have since landed, and both commits are ancestors of
VCVio's current PolyFun pin:

- [PolyFun#138](https://github.com/Verified-zkEVM/PolyFun/pull/138) defines exact monadic
  support through Lean core's `MonadAttach`, adding the introduction laws needed to show
  that `MonadAttach.support` is exact;
- [PolyFun#139](https://github.com/Verified-zkEVM/PolyFun/pull/139) adds free-monad weakest
  preconditions, `WPSound` adequacy through `MonadAttach`, and an `mvcgen` bridge.

The desired layering is:

```text
PolyFun FreeM / MonadAttach / wpFold
            │
            ├── qualitative support and WPSound
            │
            └── VCVio interpretations
                 ├── discrete probability
                 ├── expectation / quantitative WP
                 ├── measure or kernel semantics
                 └── coupling / relational semantics
```

`SetM` can remain a useful implementation and theorem-proving target, but public support should
use the upstream `MonadAttach` vocabulary. The required PolyFun surface is now available at the
VCVio pin. This keeps PolyFun probability-free and lets VCVio change distribution representations
without changing reachability.

#### 5.2.1 The wider PolyFun upstream-alignment push

At the original audit, #138 and #139 were two of six non-draft PRs in flight. All six
subsequently landed. The table records both their architectural role and the exact commits included
in VCVio's current PolyFun pin:

| PR | Included commit | Content | Bearing on this document |
|---|---|---|---|
| [#138](https://github.com/Verified-zkEVM/PolyFun/pull/138) | `f51fb3d` | Exact monadic support over core `MonadAttach` | Makes qualitative return support probability-independent. |
| [#139](https://github.com/Verified-zkEVM/PolyFun/pull/139) | `fe2a140` | Free-monad weakest preconditions, `Std.Do` quarantine, and `WPSound` adequacy | Supplies the generic program-logic boundary described above. |
| [#141](https://github.com/Verified-zkEVM/PolyFun/pull/141) | `3355f18` | `docs/reading/upstream-alignment.md`, an adopt/keep/upstream/track ledger | The companion survey to this one. The two should cross-reference rather than re-derive; §19 here is the analogue of its method section. |
| [#142](https://github.com/Verified-zkEVM/PolyFun/pull/142) | `f7e1234` | Bridges `Control/Bisimulation.lean` onto cslib's `LTS`; transports Sangiorgi's Lemma 4.2.10 | Shrinks §11's trace work: the *qualitative* process equivalences come from cslib, leaving only the probabilistic limit to invent. Delay bisimulation has no cslib counterpart and is flagged as an upstream contribution candidate. |
| [#143](https://github.com/Verified-zkEVM/PolyFun/pull/143) | `7d1daac` | Settles the monad-morphism hierarchy | Directly ratifies §2.2 — see below. |
| [#144](https://github.com/Verified-zkEVM/PolyFun/pull/144) | `814952a` | Hygiene: duplicate `Category PFunctor` instances, `Filter`-based temporal operators, `MonoidHom.compLeft` | Non-breaking for VCVio; also the source of the retraction that motivates §19's evidence discipline. |

**#143 matters more than its size suggests.** It settles the division as: when a
morphism is *canonical for the pair* and should be found by instance search, it is
core's `MonadLift` / `MonadLiftT` with `LawfulMonadLift` / `LawfulMonadLiftT`, whose
two fields are exactly the `pure` and `bind` laws; when a morphism is *data* — chosen
at the call site, composed, passed around — it is PolyFun's bundled `MonadHom`
(`m →ᵐ n`), with `MonadHom.ofLift` as the one-way bridge and deliberately no converse
instance.

That is precisely the shape VCVio's semantics layer already has.
[`EvalDist/Defs/Basic.lean`](../../VCVio/EvalDist/Defs/Basic.lean) argues at length for
declaring the `SPMF` and `SetM` lifts as `MonadLiftT` rather than `MonadLift`, and
`SemanticsVia.interpret : m →ᵐ Sem` is the bundled case. §2.2's claim that
`SemanticsVia` is the right migration seam therefore stops being a local convention and
becomes an instance of an upstream-settled rule — which is a meaningfully stronger
argument for keeping it through any backend change.

One tracking note: #143 deliberately leaves `MonadHom`'s explicit `(α : Type u)` field
shape unaligned with the in-flight Batteries draft *because VCVio defines `MonadHom`s
directly*. If `MonadHom` is ever upstreamed to Batteries, that divergence becomes a
VCVio-visible rename.

### 5.3 loom2

VCVio depends on [`loom2`](https://github.com/quangvdao/loom2) for `Std.Do'`,
`PredTrans`, `EPost`, `RelTriple`, and `rwp` — the substrate under
`VCVio/ProgramLogic/{Unary,Relational}/Loom/`. It is omitted from the layering picture
above, and it should not be: it is the least stable link in the chain.

- It is pinned to a single commit and targets a Lean **v4.32.0** toolchain, while VCVio
  is moving to v4.33/v4.34.
- It is a personal fork, not a released library, so it has no version cadence to track.
- Its design is being absorbed into Lean core as `Std.Internal.Do` → `Std.WP`, by the
  same author (see §2.5.1).

The right posture is *track and plan an exit*, not *replace now*: the upstream successor
is still in an `Internal` namespace at v4.34 and has been refactored repeatedly. But the
exit should be costed before the backend decision in §13 Phase 4, because a
program-logic port and a distribution port landing simultaneously would be much harder to
review than either alone.

#### 5.3.1 Delta audit

The surface is narrower than the dependency's prominence suggests. VCVio imports exactly
four loom2 modules — `Loom.WP.Basic`, `Loom.ExceptPost`, `Loom.Triple.Basic`, and
`Loom.Triple.SpecLemmas` — and does so from only five files
([`Unary/Loom/{Qualitative,Probabilistic,Quantitative}.lean`](../../VCVio/ProgramLogic/Unary/Loom),
[`Tactics/Unary/Internals.lean`](../../VCVio/ProgramLogic/Tactics/Unary/Internals.lean),
and [`ToMathlib/Control/Monad/RelWP.lean`](../../ToMathlib/Control/Monad/RelWP.lean)).
Everything else reaches Loom through the `Std.Do'` namespace, which is mentioned in 22
files — so the *import* boundary is already tight, and it is the namespace, not the
dependency graph, that would have to be swept.

| VCVio uses (`Std.Do'.…`) | Sites | `Std.Internal.Do` (v4.33/v4.34) | `Std.WP` (master) | Verdict |
|---|---|---|---|---|
| `WP`, `wp` | 156 | `WP`, `WP.wp` | `Std.WP.WP`, `Std.WP.wp` | **Rename.** Same four-parameter class, same `⊑`-ordered monotone `PredTrans`. |
| `Assertion` | 34 | `class abbrev Assertion := CompleteLattice` | same | **Rename.** Still `Lean.Order`, not Mathlib. |
| `Triple`, `Triple.iff`, `Triple.bind` | 54 | `structure Triple` | `Std/WP/Triple/` | **Rename.** |
| `Spec.get_StateT`, `set_StateT`, `read_ReaderT`, `modifyGet_StateT`, `monadLift_*` | 12 | `StateT.instWPMonad`, `ReaderT.instWPMonad` | `Std/WP/Monad/Instances.lean` | **Rename**, but re-derive against upstream's instance shape rather than porting the lemmas. |
| `EPost.nil`, `EPost.nil.mk`, `EPost.cons`, `EPost.cons.mk`, `EPost.cons.pushOption` | 74 | `EPost.Nil`, `EPost.Cons` (capitalised) | **Restructured to `EStack`** | **Reshape — the one substantial item.** |
| `WriterT.apply_wp`, `wp_tell`, `wp_pure` | 6 | absent | absent | **VCVio-owned already** — declared inside `namespace Std.Do'` in [`Unary/Loom/Quantitative.lean`](../../VCVio/ProgramLogic/Unary/Loom/Quantitative.lean). Moves with VCVio; only the enclosing namespace changes. |
| `RelTriple`, `rwp`, `RelWP` and their rules | 99 | absent | absent | **Stays downstream.** No relational layer upstream in either tree. |

**The `EPost` → `EStack` reshape is the only part that is not a rename.** Upstream has
replaced the nil/cons *structures* with a right-nested product chain terminated by
`EStackEnd := Unit`, presented through notation:

```lean
EStack⟨⟩            = EStackEnd                    -- Unit
EStack⟨x⟩           = x × EStackEnd
EStack⟨x, xs…⟩      = x × EStack⟨xs…⟩
estack⟨…⟩                                          -- the corresponding values
```

so `ExceptT` is now `WPMonad (ExceptT ε m) Pred ((ε → Pred) × EPred)`. The translation is
mechanical — `EPost.nil ↦ EStack⟨⟩`, `EPost.nil.mk ↦ estack⟨⟩`, `EPost.cons X R ↦ X × R`,
`EPost.cons.mk x r ↦ (x, r)` — but it is a change of *shape*, not just of name, so
anything that currently closes by `rfl` or by structure-eta on `EPost` needs rechecking.
At 74 sites this is the item worth scheduling deliberately.

**What the port would gain**, beyond removing the fork: upstream has capabilities Loom
does not — `WPConjunctive` and `PreservesSup`, a frame layer (`WP.Frames`), loop
`Invariant` / `RepeatInvariant` / `RepeatVariant`, assertion and `ForIn` gadgets, and a
soundness module. Several of these are things VCVio's tactics currently approximate.

**Gating conditions**, in order: `Std.WP` must be public in a *release* (not master);
`vcgen` must be out from behind `experimental.vcgen`; and the `EStack` presentation must
have stopped moving. None of these hold at v4.34, so the recommendation for that cycle is
to record this table and re-check it at each toolchain bump, not to port.

## 6. Bluebell and Iris Requirements

The
[`Verified-zkEVM/iris-lean`](https://github.com/Verified-zkEVM/iris-lean) fork contains
active Bluebell work. The development snapshot inspected for this survey has the following shape:

- `MeasureOnSpace Ω` bundles a measurable space with a measure on that space;
- `PSpace Ω` adds `IsProbabilityMeasure`;
- the resource algebra orders probability spaces by extension of σ-algebras;
- separating conjunction is based on independent product structure;
- `CompatibleKernel` and `Measure.bind` interpret joint conditioning;
- `PMF` still presents the discrete distributions named in Bluebell assertions;
- the attempted `Iris.Wp` instance for `OracleComp` is unfinished.

This matches the semantics in the
[Bluebell paper](https://arxiv.org/abs/2402.18708): measure-theoretic independence and
conditioning are foundational, while the object language samples discrete
distributions. It also exposes a useful architectural lesson: “use measures” need not
mean “remove every discrete distribution object from syntax and proofs.”

For VCVio interoperability, Bluebell needs at least:

1. a total output probability measure for terminating, non-failing programs, or an
   explicit policy for failure;
2. measurable kernels for stateful commands and conditioning;
3. product/marginal laws connecting independent computations to independent probability
   spaces;
4. a bridge from event probabilities and couplings to Bluebell's assertions;
5. a weakest-precondition adequacy theorem for the chosen OracleComp semantics.

Iris itself should remain parametric in the object language and its WP. The VCVio layer
should provide an instance/adequacy bridge rather than moving OracleComp or probability
definitions into Iris.

## 7. A Stratified Target Architecture

The following layers are compatible with every backend option in the next section.

### Layer A: qualitative computation semantics

Owns:

- `CanReturn`, `Ensures`, and exact monadic support;
- free-monad `wpFold` and `WPSound`;
- support-sensitive correctness lemmas and qualitative VC generation.

Depends on `MonadAttach` and PolyFun, not on Mathlib probability.

### Layer B: discrete quantitative observations

Owns:

- point probability, event probability, and explicit failure probability;
- finite support/cardinality formulas and uniform sampling;
- the stable `evalDist`/`Pr[...]` compatibility surface;
- countable sums used heavily by cryptographic proofs.

It may be represented by SPMF, a discrete measure, or a measure under `⊤`; consumers
should rely on its laws rather than representation-specific PMF constructors.

### Layer C: measurable probability and kernels

Owns:

- probability measures on arbitrary measurable spaces;
- measurable map/bind and state-transition kernels;
- products, conditioning, independence, and integration;
- the semantic objects consumed by Bluebell and general process theory.

It cannot have unconstrained plain-monad laws. Measurability belongs in its interfaces.

### Layer D: partiality and limits

Owns:

- subprobability output semantics;
- increasing chains of resolved finite runs;
- divergence/loss mass and almost-sure termination;
- least-fixpoint or ω-supremum equations.

For an explicit program error, use an outcome type inside this layer. For example,
`SubprobabilityMeasure (Except ε α)` distinguishes returned errors from divergence.

### Layer E: trace semantics

Owns:

- measures on finite and infinite paths;
- cylinder events and finite-prefix marginals;
- safety/liveness observations that are not determined by final output;
- the connection between PolyFun `Run`, ITree traces, and probabilistic responders.

Layers D and E should have a theorem connecting termination events to output mass, not a
definition identifying their carriers.

### Layer F: program-logical observations

Owns:

- expectation transformers `wp μ post = ∫⁻ x, post x ∂μ`;
- indicator/event bridges;
- relational liftings and couplings;
- `mvcgen`/`vcgen` rules derived from semantic composition;
- Iris/Bluebell adequacy instances.

This layer should depend on capabilities from the layers above rather than on the name of
the concrete distribution type.

## 8. Backend Options

### Option 1: Keep SPMF primary and add measure views

Define and strengthen canonical views such as:

```text
SPMF α  →  ProbabilityMeasure (Option α) under the discrete σ-algebra
SPMF α  →  subprobability Measure α by discarding `none`
```

Then prove that `probOutput`, `probEvent`, `probFailure`, bind, map, expectation, and
uniform sampling agree with their measure interpretations.

**Advantages**

- smallest migration cost;
- preserves all current monad and pointwise proof ergonomics;
- gives Bluebell a measure boundary without rewriting VCVio;
- allows upstream PMF changes to be absorbed inside a compatibility module.

**Risks**

- VCVio continues owning a type built on an upstream abstraction intended for
  deprecation;
- infinite limits and general measurable spaces remain secondary;
- new work may continue to accrete around SPMF-specific formulas.

**Choose this option if** the PMF deprecation leaves no comparably ergonomic discrete
type and most consumers need only finite/countable probability.

### Option 2: Make discrete Mathlib measures primary

Interpret every discrete result in `@Measure α ⊤`, or in a bundled probability measure
over that measurable space. Define pure/bind/map wrappers whose laws use the fact that
all functions from `⊤` are measurable. Keep `evalDist` and `Pr[...]` as a façade, but
derive their laws from measures and `Measure.sum`/Dirac formulas.

**Advantages**

- directly follows Mathlib's announced PMF direction;
- event probabilities, integration, products, and Bluebell interoperability become
  native;
- discrete and general semantics share the same underlying measure type.

**Risks**

- pointwise and finite-support ergonomics must be rebuilt;
- the measurable-space parameter is easy to hide incorrectly with typeclass inference;
- an arbitrary discrete `Measure` is not automatically finite or probability-valued;
- `OptionT` and existing monad-transformer instances need new wrappers or semantic laws.

**Choose this option if** Mathlib's discrete-measure and uniform-measure work lands with
enough bind, support, and finite-sum infrastructure to keep cryptographic proofs concise.

**A spelling caveat that cuts both ways.** Mathlib states its own discrete results over
an *ambient* `[MeasurableSpace α]`, adding `[MeasurableSingletonClass α]` for pointwise
lemmas — that is how `bernoulliMeasure`, `poissonMeasure`, and #42821's rewritten
`uniformOfFinset` are all phrased. VCVio cannot follow suit, because `α` in
`OracleComp spec α` is an arbitrary `Type u` with no such instance, so it must carry
`⊤` explicitly.

Mechanically this is fine, and better than it first appears: `instance :
@DiscreteMeasurableSpace α ⊤` holds, `DiscreteMeasurableSpace.toMeasurableSingletonClass`
supplies the singleton class, and `MeasurableSet.of_discrete` / `Measurable.of_discrete`
discharge every side condition. Under `⊤` every set is measurable and every function is
measurable, so `Measure.bind_apply`, `bind_bind`, `dirac_bind`, and `lintegral_bind`
apply unconditionally and `@Measure · ⊤` really is a lawful monad — which is exactly
what §4.2 says raw `Measure` is not.

The cost is downstream rather than internal: because the spellings differ, a discrete
façade written this way is **harder to upstream** than one written in Mathlib's idiom,
and Mathlib's own discrete lemmas will need `⊤`-instantiated restatements rather than
applying verbatim. Any prototype under this option should measure that restatement cost
explicitly, since it is the main hidden expense and it does not show up in a
proof-length comparison of the finished lemmas.

### Option 3: Introduce a bundled subprobability measure/kernel

Build a small VCVio or ToMathlib wrapper around `Measure` with total mass at most one,
plus a measurable sub-Markov-kernel analogue. Give the discrete specialization a
monadic API under `⊤`, and use directed suprema for coalgebraic output limits.

**Advantages**

- models divergence directly;
- unifies finite failure-aware computation with unbounded machines;
- supports measure integration and measurable kernels;
- gives the historical `RunLimit` construction a general Mathlib foundation.

**Risks**

- largest local foundational burden;
- must carefully distinguish handler loss from program divergence;
- may duplicate future Mathlib work;
- general bind laws cannot avoid measurability conditions.

**Choose this option if** coinductive execution and partial correctness become near-term
requirements and no upstream subprobability abstraction is forthcoming.

### Option 4: Use kernels/`Stoch` as the organizing semantics

View a computation from input `X` to output `Y` as a Markov or sub-Markov kernel and use
kernel composition as sequencing. This aligns well with stateful machines, Bluebell,
conditional distributions, and category-theoretic readings of PolyFun.

This is best understood as a long-term organizing model, not an immediate replacement
for the proof-facing monad. It still needs a discrete façade, a partiality story, and
adapters from Lean functions and free-monad handlers.

**Choose this option as the primary presentation if** measurable state spaces and process
composition become more important than arbitrary-Type monad programming. Otherwise use
it as the semantic layer beneath more ergonomic APIs.

## 9. Evaluation Matrix

The decision should be based on proof spikes, not only aesthetic fit.

| Criterion | SPMF + views | Discrete `Measure` | Bundled subprobability | Kernel-organized |
|---|---|---|---|---|
| Preserve current proofs | Excellent | Medium | Medium | Low without façade |
| Align with Mathlib PMF direction | Medium | Excellent | Good | Excellent |
| Point probabilities and finite sums | Excellent | Must rebuild | Must rebuild discrete layer | Must rebuild discrete layer |
| General measurable spaces | View only | Good | Excellent | Excellent |
| Explicit failure | Native `Option` | Outcome type | Outcome type | Outcome type |
| Divergence/missing mass | Encodable, but overloaded | Needs mass invariant | Native | Needs sub-Markov variant |
| Increasing output limits | Existing experimental theory | Measure lattice | Intended core feature | Via component measures |
| Infinite trace measures | Separate construction | Good substrate | Good substrate | Best fit |
| Bluebell conditioning/independence | Adapter required | Native measure boundary | Native measure boundary | Native |
| Ordinary Lean monad ergonomics | Excellent | Only discrete wrapper | Only discrete wrapper | Poor at raw kernel level |
| Transformer integration | Existing | New semantic instances | New semantic instances | New adapters |
| Upstream dependency risk | PMF deprecation | Open discrete PRs | Local API ownership | Large Mathlib API surface |

No row dominates. A likely end state is stratified: exact `MonadAttach` support, an
ergonomic discrete façade, Mathlib measures/kernels at interoperability boundaries, and
a subprobability layer only where nontermination requires it.

## 10. Candidate Interfaces

These are discussion sketches, not accepted names or signatures.

### 10.1 Keep observation separate from interpretation

Retain the `SemanticsVia` idea:

```text
source computation
  ──interpret──▶ internal semantic computation
  ──observe────▶ discrete distribution / measure / trace law
```

This continues to handle `StateT`, `ReaderT`, interaction runtimes, and hidden runtime
state without pretending observation is a monad morphism.

### 10.2 Discrete measure capability

A discrete semantics can quantify no ambient measurable-space instance and state its
target explicitly as `@Measure α ⊤`. Its laws can include:

- total mass or mass-at-most-one;
- pure is Dirac;
- bind is discrete Giry bind;
- event probability agrees with the measure of the event;
- atomic support agrees with `MonadAttach.support` under an explicit compatibility
  assumption.

This is the measure analogue of the current `MonadLiftT m SPMF` plus
`EvalDistCompatible` stack.

### 10.3 General measure capability

A general semantics must receive measurable spaces as data and expose either:

- a measure for closed computations;
- a kernel for computations with input/state;
- or a functor/morphism in Mathlib's measurable-space category.

The bind law must mention measurable continuations. It should not be forced into
`LawfulMonadLiftT`.

### 10.4 Query distributions

Three compatible migration shapes for `IsProbabilitySpec` should be compared in the
spikes:

1. retain PMF-valued queries and convert only at the final observation;
2. change queries to bundled discrete probability measures;
3. hide the representation behind a `QueryDistribution` API with point, event, and
   measure views.

The third offers the most insulation but creates a new abstraction that must justify
itself through simpler downstream code.

## 11. Coalgebraic Probability Semantics

### 11.1 Terminating-output submeasure

For a returning `DynComputation` and probabilistic responder:

1. run for fuel `k`, obtaining a distribution on `Option β`;
2. discard unresolved `none`, yielding a subprobability measure on `β`;
3. prove these resolved-output measures form an increasing chain;
4. take the supremum over `k`;
5. prove the one-step fixpoint equation and leastness;
6. define almost-sure termination as total output mass one.

For finite `OracleComp.toITree`, the chain eventually stabilizes and must agree with the
ordinary `evalDist` measure view. For genuinely infinite machines it may converge only in
the limit.

If responders themselves can lose mass, the output mass deficit combines responder loss
and divergence. A plain subprobability measure cannot recover the cause. Applications
that care must either require lossless/Markov responders or enrich traces/outcomes with a
loss reason.

### 11.2 Trace measure

For trace semantics:

1. give each state/query a measurable answer kernel;
2. construct the law of every finite prefix;
3. prove restriction of the `(n+1)`-prefix law equals the `n`-prefix law;
4. invoke Ionescu–Tulcea or a projective-limit theorem to obtain the path measure;
5. prove cylinder-event probabilities agree with bounded execution;
6. identify termination and returned-value events in the path space.

This semantics assigns probability to nonterminating paths instead of dropping them. It
is the appropriate basis for liveness, transcript properties, and probabilistic temporal
reasoning.

### 11.3 Relationship between the two

The desired theorem is schematically:

```text
outputSubmeasure event
  = traceMeasure {paths that eventually return a value in event}
```

Almost-sure termination says the eventual-return event has trace measure one. Only then
does the output submeasure become a probability measure.

## 12. Program Logic Consequences

### 12.1 Unary expectation transformers

The measure-native quantitative WP is:

```text
wp μ post = ∫⁻ x, post x ∂μ
```

For subprobability semantics, missing mass contributes nothing, giving the usual partial-
correctness/expectation-transformer reading. Indicator postconditions recover event
probabilities. The tower property/`lintegral_bind` supplies the bind rule.

VCVio's current `ℝ≥0∞` carrier is therefore a strong candidate for the stable program-
logic interface even if the distribution representation changes.

### 12.2 Relational logic

A general coupling is a measure on a product whose marginals are the two observed
measures. Exact pRHL postconditions require that the coupling gives full mass to the
relation. Approximate logics additionally need divergences or approximate liftings.

The current SPMF coupling layer should be generalized only after one representative
proof establishes which Mathlib marginal and measurability APIs are usable. Finite
coupling proofs can remain discrete corollaries.

### 12.3 Bluebell/Iris

Bluebell needs more than an expectation transformer: its separating conjunction and
joint-conditioning modality inspect probability-space and kernel structure. A useful
integration should therefore expose both:

- a measure/kernel denotation for semantic adequacy and ownership assertions;
- WP laws for automation and ordinary program proofs.

The integration should not encode Bluebell independence solely through a scalar `wp`;
that would discard exactly the factorization information Bluebell is designed to track.

### 12.4 `mvcgen` and `vcgen`

The division of labor should be:

- upstream `vcgen` (and `mvcgen` while it lasts): generic structural reasoning justified
  by `WPSound` and `MonadAttach`;
- VCVio's unary tactic: event/expectation normalization, oracle-query rules, support
  bridges, loops, and probability arithmetic;
- VCVio `rvcgen`: coupling and quantitative relational rules;
- Iris proof mode: resource-sensitive reasoning after a VCVio/Bluebell WP instance is
  proved adequate.

Shared theorem registries or adapters are desirable; a forced merger of the tactic
implementations is not a prerequisite for semantic convergence.

Two corrections to how this section was originally phrased, following §2.5.1.

**The upstream tactic is `vcgen`, not `mvcgen`.** `mvcgen` is deprecated on Lean master
in favour of `vcgen`, which dispatches on `Std.WP.wp` rather than `Std.Do`'s
`PostShape`-indexed `WP`. Anything written against `mvcgen` — including PolyFun#139's
bridge — will need retargeting, and the natural time to do it is the same cycle in which
`Std.WP` becomes public.

**`vcgen` is already a taken name.** Lean `v4.33.0` declares a bare `vcgen` tactic token
in `Std/Tactic/Do/Syntax.lean`, plus a low-priority stub in `Init/Tactics.lean`. VCVio's
own `vcgen` therefore shares a leading token with a core tactic that is under active
development and is about to become *the* VC generator. Renaming VCVio's is cheap now and
gets steadily less so; more importantly, once VCVio's domain tactic is layered *on top
of* core's, having two tactics named `vcgen` in scope stops being merely confusing.

This does not change the division of labor above. It changes who owns the name.

## 13. No-Regret Roadmap

This section preserves the staged roadmap from the original survey. Dated disposition notes record
the parts rechecked on 2026-08-30; unannotated bullets remain design history, not a claim that work
is still pending on current `main`.

### Phase 0: vocabulary and source map

- Maintain this document as the cross-project index.
- Mark every volatile statement as pinned, open-PR, historical, or proposed.
- Record decisions and rejected options here rather than in transient PR comments.

### Phase 1: qualitative support cutover

The PolyFun #138/#139 prerequisites have landed and are included in VCVio's pin. The remaining
VCVio work is to:

- expose PolyFun's exact support surface for `OracleComp`, which already inherits
  `PFunctor.FreeM.instExactMonadAttach` through its reducible free-monad definition; do not add a
  competing `OracleComp` instance;
- add exact `MonadAttach` instances only for compatibility transformers or semantic carriers that
  do not already inherit one;
- redefine the public support API through `MonadAttach.support` where possible;
- prove compatibility aliases for existing `SetM` support lemmas;
- keep probability/support equivalences as discrete compatibility theorems;
- use `WPSound` to connect upstream `mvcgen` results to support-sensitive correctness.

In the original staging, this phase was intended not to change `evalDist`.

### Phase 2: measure bridge without backend replacement

**Current disposition (2026-08-30):** the measure-primary surface and its discrete compatibility
bridge are on `main`. The bullets below are the original acceptance goals, retained to explain what
the bridge was required to demonstrate.

- Add canonical total-measure and output-submeasure views of SPMF. At the original snapshot, the
  PMF/FreeM measure bridge, point/event correspondence, and option success observer were already
  implemented.
- Prove pure, bind, map, event, point, failure, uniform, expectation, and product correspondence.
- Re-express a small set of existing theorems through those views while keeping their
  public statements unchanged.
- Provide the minimum adapter Bluebell needs to consume an OracleComp output measure.

This phase produces reusable evidence for every later option.

### Phase 3: focused architecture spikes

Run the experiments in the next section against the same pinned release. Record proof
size, typeclass friction, compile time, and missing upstream lemmas. Do not migrate the
main API during the spikes.

### Phase 4: backend decision

The accepted design chooses a stratified Measure/Kernel denotational boundary while retaining the
discrete proof façade. The following remain migration gates rather than reasons to reopen that
boundary:

- the Mathlib PMF/discrete-measure PRs have a stable outcome;
- the finite proof and ArkLib canaries are no worse than the current surface;
- the coalgebraic spike demonstrates an honest partiality/limit story;
- the Bluebell spike demonstrates conditioning and independence interoperability;
- the coupling spike identifies a viable relational path.

The decision may explicitly choose a hybrid rather than one universal type.

### Phase 5: compatibility-first migration

- Keep `evalDist`, `Pr[...]`, and program-logic theorem shapes as the first compatibility
  layer.
- Port foundational lemmas before applications.
- Port one example and one ArkLib consumer per capability before bulk changes.
- Deprecate representation-specific declarations only after replacements compile in both
  repositories.
- Stage generic measure/discrete lemmas in `ToMathlib` and remove them when stable upstream
  equivalents land; do not open Mathlib, Lean, or cslib PRs during this design migration.

### Phase 6: infinite trace semantics

- Output submeasures, their fuel monotonicity, and the returned-output supremum are implemented for
  PolyFun resumptions with lossless discrete responders.
- Add trace measures only after measurable-state and prefix-compatibility interfaces are
  clear.
- Prove finite-program agreement and almost-sure-termination bridges before exposing a
  public “run forever” API.

## 14. Required Spikes and Acceptance Gates

### Spike A: discrete measure correspondence

Implement a private prototype proving:

- SPMF event probability equals the discrete measure of the corresponding `some` image;
- point/failure probabilities are singleton measures;
- SPMF bind agrees with `Measure.bind` under `⊤`;
- uniform finite sampling agrees with the upstream measure construction or an explicit
  sum of Dirac measures.

**Gate:** the One-Time Pad correctness/privacy proof can be restated through the measure
view without materially more measurable-space boilerplate.

### Spike B: standalone finite probability

Port one ArkLib uniform-cardinality lemma and one Schwartz–Zippel/collision-style lemma
to the candidate discrete layer.

**Gate:** proofs retain finite sums, point probabilities, and cardinality automation at
roughly current complexity. A backend that makes these proofs substantially harder must
ship a façade before it can be selected.

### Spike C: output limits

Use a simple geometric/rejection-style `DynComputation`:

- define resolved-output truncations;
- prove monotonicity;
- take a measure or subprobability supremum;
- prove the fixpoint equation and total-mass convergence.

The generic foundations are implemented: resolved truncations are monotone, their measure
supremum is pointwise on measurable events, and its total mass is at most one. The
geometric/rejection canary, fixpoint law, finite-program agreement, and termination convergence
remain.

**Gate:** divergence is represented as missing mass without conflating it with a returned
`none`, and the finite `OracleComp` case agrees with `evalDist`.

### Spike D: trace extension

Construct finite prefix laws for a finite-state probabilistic responder and extend them
to an infinite trace measure.

**Gate:** cylinder probabilities reduce to bounded `runWith`, and the measurable-space
requirements can be packaged without making PolyFun probability-dependent.

### Spike E: couplings and distance

Port one exact relational proof and one total-variation or Rényi bound to measure views.

**Gate:** marginals, relation-full-mass statements, and discrete corollaries have stable
APIs; identify explicitly which distance lemmas remain VCVio-owned.

### Spike F: Bluebell and WP

Give a finite OracleComp fragment a measure/kernel denotation and connect it to one
Bluebell distribution-ownership or joint-conditioning rule. Prove `wp_pure` and
`wp_bind` for the same semantics and expose them to a minimal `mvcgen`/`vcgen` example.

**Gate:** Bluebell can use VCVio semantics without importing SPMF internals, while VCVio
users retain ordinary discrete probability notation.

## 15. Ownership and Upstreaming Guide

| Work item | Preferred home | Reason |
|---|---|---|
| Exact monadic return support | Lean core / PolyFun | Probability-independent control semantics |
| FreeM folds and generic coalgebraic truncation | cslib / PolyFun | Reusable computation structure |
| General measure, kernel, integral, and uniform-measure lemmas | ToMathlib for now | Follow Mathlib closely without opening upstream work during the design migration |
| Generic discrete-measure conveniences | ToMathlib for now | Keep migration utilities local and easy to delete when upstream subsumes them |
| Experimental bundled subprobability type | ToMathlib initially | Prove the API and reassess its long-term home after the design migration |
| Oracle query probability interpretation | VCVio | Oracle-specific semantic policy |
| `evalDist`, `Pr[...]`, crypto distances, and reduction lemmas | VCVio | Stable crypto-facing API |
| Finite consumer canaries | Examples and ArkLib | Validate ergonomics on real proofs |
| Probability-space ownership and joint conditioning | Bluebell/Iris | Logic-specific resource semantics |

## 16. Questions the Backend Decision Must Answer

1. Is the primary result of a finite computation a total measure on an outcome type or a
   subprobability measure on successful values?
2. Which failures are returned results, and which losses represent divergence or an
   invalid environment?
3. Do query specifications expose point weights, probability measures, or an abstract
   distribution capability?
4. Is discrete `⊤` carried explicitly in definitions, or hidden behind a wrapper?
5. Which semantics must compose as an ordinary Lean monad, and which compose as
   measurable kernels?
6. What is the minimal correspondence theorem needed to keep `Pr[...]` statements
   unchanged?
7. Which current SPMF theorems are truly discrete and which should become integral or
   kernel theorems?
8. Does output-limit semantics need to distinguish responder loss from nontermination?
9. Which class of PolyFun state and direction spaces is promised a trace measure?
10. What does Bluebell need as data, beyond scalar expectations and event probabilities?
11. Which semantic laws are shared by `mvcgen`, `vcgen`, and Iris, and which remain
    domain-specific?
12. What upstream stability threshold is required before deprecating VCVio declarations?

## 17. Source Index

### VCVio and examples

- [`ToMathlib/ProbabilityTheory/SPMF.lean`](../../ToMathlib/ProbabilityTheory/SPMF.lean)
- [`VCVio/EvalDist/Defs/Basic.lean`](../../VCVio/EvalDist/Defs/Basic.lean)
- [`VCVio/EvalDist/Defs/Semantics.lean`](../../VCVio/EvalDist/Defs/Semantics.lean)
- [`VCVio/EvalDist/Defs/Support.lean`](../../VCVio/EvalDist/Defs/Support.lean)
- [`VCVio/OracleComp/EvalDist.lean`](../../VCVio/OracleComp/EvalDist.lean)
- [`VCVio/EvalDist/Expectation.lean`](../../VCVio/EvalDist/Expectation.lean)
- [`VCVio/EvalDist/TVDist.lean`](../../VCVio/EvalDist/TVDist.lean)
- [`VCVio/EvalDist/RenyiDivergence.lean`](../../VCVio/EvalDist/RenyiDivergence.lean)
- [`ToMathlib/ProbabilityTheory/Coupling.lean`](../../ToMathlib/ProbabilityTheory/Coupling.lean)
- [`ToMathlib/ProbabilityTheory/OptimalCoupling.lean`](../../ToMathlib/ProbabilityTheory/OptimalCoupling.lean)
- [`ToMathlib/ProbabilityTheory/FinRatPMF.lean`](../../ToMathlib/ProbabilityTheory/FinRatPMF.lean)
- [`VCVio/EvalDist/Instances/FinRatPMF.lean`](../../VCVio/EvalDist/Instances/FinRatPMF.lean)
- [`ToMathlib/Probability/ProbabilityMassFunction/TotalVariation.lean`](../../ToMathlib/Probability/ProbabilityMassFunction/TotalVariation.lean)
- [`ToMathlib/Probability/ProbabilityMassFunction/RenyiDivergence.lean`](../../ToMathlib/Probability/ProbabilityMassFunction/RenyiDivergence.lean)
- [`ToMathlib/Probability/ProbabilityMassFunction/TailSums.lean`](../../ToMathlib/Probability/ProbabilityMassFunction/TailSums.lean)
- [`VCVio/ProgramLogic`](../../VCVio/ProgramLogic)
- [`VCVio/ProgramLogic/Unary/Loom`](../../VCVio/ProgramLogic/Unary/Loom)
- [`VCVio/ProgramLogic/Relational/Loom`](../../VCVio/ProgramLogic/Relational/Loom)
- [`VCVio/OracleComp/Coinductive`](../../VCVio/OracleComp/Coinductive)
- [`Examples/OneTimePad/Basic.lean`](../../Examples/OneTimePad/Basic.lean)
- [`Examples/EvalDistCompatible/Basic.lean`](../../Examples/EvalDistCompatible/Basic.lean)
- [`Examples/OneTimePad/UC.lean`](../../Examples/OneTimePad/UC.lean)

### Mathlib

- [Giry monad](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Measure/GiryMonad.lean)
- [Probability measures](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean)
- [Finite measures](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean)
- [Kernel definitions](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Probability/Kernel/Defs.lean)
- [Kernel composition](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Probability/Kernel/Composition)
- [Ionescu–Tulcea](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Probability/Kernel/IonescuTulcea)
- [Projective measures](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Constructions/Projective.lean)
- [Kolmogorov extension](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Probability/Process/Kolmogorov.lean)
- [PMF deprecation PR](https://github.com/leanprover-community/mathlib4/pull/42821)
- [Measure bind commutation PR](https://github.com/leanprover-community/mathlib4/pull/42908)
- [Uniform finite measure PR](https://github.com/leanprover-community/mathlib4/pull/42909)
- [DiscreteMeasure PR](https://github.com/leanprover-community/mathlib4/pull/34138)

### PolyFun and cslib

- [PolyFun](https://github.com/Verified-zkEVM/PolyFun)
- [Exact MonadAttach support PR](https://github.com/Verified-zkEVM/PolyFun/pull/138)
- [FreeM WP and mvcgen PR](https://github.com/Verified-zkEVM/PolyFun/pull/139)
- [Upstream-alignment survey PR](https://github.com/Verified-zkEVM/PolyFun/pull/141)
- [cslib LTS bridge PR](https://github.com/Verified-zkEVM/PolyFun/pull/142)
- [Monad-morphism hierarchy PR](https://github.com/Verified-zkEVM/PolyFun/pull/143)
- [Upstream-reuse hygiene PR](https://github.com/Verified-zkEVM/PolyFun/pull/144)
- [cslib](https://github.com/leanprover/cslib)
- [cslib FreeM/W-type PR](https://github.com/leanprover/cslib/pull/731)
- [cslib PFunctor PR](https://github.com/leanprover/cslib/pull/803)
- [cslib crypto cleanup PR](https://github.com/leanprover/cslib/pull/813)

### Lean core and Loom

- [`Init/Control/MonadAttach.lean`](https://github.com/leanprover/lean4/blob/master/src/Init/Control/MonadAttach.lean)
- [`Std/Do/WP/Sound.lean` (`WPSound`)](https://github.com/leanprover/lean4/blob/master/src/Std/Do/WP/Sound.lean)
- [`Std/Internal/Do/` (lattice-generic WP; public `Std/WP/` on master)](https://github.com/leanprover/lean4/tree/master/src/Std/WP)
- [`Lean/Elab/Tactic/VCGen/`](https://github.com/leanprover/lean4/tree/master/src/Lean/Elab/Tactic/VCGen)
- [lean4#14146 — rename `mvcgen'` to `vcgen`](https://github.com/leanprover/lean4/pull/14146)
- [lean4#14870 — `experimental.vcgen` option](https://github.com/leanprover/lean4/pull/14870)
- [lean4#14874 — deprecate `mvcgen`](https://github.com/leanprover/lean4/pull/14874)
- [loom2](https://github.com/quangvdao/loom2)

### Downstream and logic work

- [ArkLib](https://github.com/Verified-zkEVM/ArkLib)
- [ArkLib probability conventions](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/wiki/probability-conventions.md)
- [Bluebell paper](https://arxiv.org/abs/2402.18708)
- [Verified-zkEVM iris-lean](https://github.com/Verified-zkEVM/iris-lean)
- [Lean community iris-lean](https://github.com/leanprover-community/iris-lean)
- [`docs/reading/mathlib-integration-shape.md`](mathlib-integration-shape.md)
- [`docs/reading/denotational-probability-semantics.md`](denotational-probability-semantics.md)
- [`docs/reading/measure-semantics-spike.md`](measure-semantics-spike.md)
- [`docs/agents/probability.md`](../agents/probability.md)
- [`docs/agents/program-logic.md`](../agents/program-logic.md)

## 18. Updating This Document

When an upstream PR lands or a spike is completed:

1. keep the original snapshot date and add a new dated disposition rather than silently rewriting
   history;
2. link the merged declaration and release tag;
3. record which decision criterion changed;
4. add the canary result, including proof/API regressions;
5. move accepted decisions into the relevant agent guide while keeping the alternatives
   and rationale here;
6. add a later-status entry such as §20, including **how** the claim was checked; do not mutate a
   historical verification result into a present-tense claim.

Point 6 is not bookkeeping. The failure mode this document is most exposed to is
asserting that upstream already provides something on the strength of a name — the
abstraction exists, the name matches, the claim goes in. PolyFun#144 had to retract four
such entries from the companion survey after checking them properly with `exact?`; each
turned out to be an upstream *contribution* candidate rather than a reuse one, which is
close to the opposite conclusion. A name is a hypothesis. The declaration in the pinned
tree is the evidence.

Two corollaries worth stating explicitly:

- Distinguish *open*, *draft*, *merged-on-master*, and *in-a-release*. A draft PR is
  the weakest signal of the four and should never be cited as though it were scheduled.
- Record the version a fact was checked at. "Mathlib has no coupling API" is a claim
  about a tree, not about Mathlib forever.

The document is complete when it ceases to be needed: the chosen architecture is stable,
the compatibility migration is documented in the ordinary probability guide, and the
remaining alternatives are only historical context.

## 19. Original Verification Log (2026-08-21)

Independent re-verification pass, 2026-08-21. "Pinned tree" means the checkouts under
`.lake/packages/` (Mathlib and cslib at `v4.33.0`, PolyFun at `v4.32.2`); "toolchain"
means `~/.elan/toolchains/leanprover--lean4---v4.33.0/src/lean`; PR and tag statuses were
read through the GitHub API rather than from PR prose.

### 19.1 Confirmed

| Claim | Method |
|---|---|
| `SPMF := OptionT PMF`, its `FunLike`, and the `SPMF.mk`/`toPMF` round-trips | Read `ToMathlib/ProbabilityTheory/SPMF.lean` |
| `SemanticsVia` / `SPMFSemantics` / `PMFSemantics` as described in §2.2 | Read `VCVio/EvalDist/Defs/Semantics.lean` in full |
| `probEvent` is defined through `PMF.toOuterMeasure` | Read `VCVio/EvalDist/Defs/Basic.lean` |
| `IsProbabilitySpec.toPMF` is PMF-valued; `IsUniformSpec` adds `Fintype`/`Inhabited`/uniformity | Read `VCVio/OracleComp/EvalDist.lean` |
| `support` is `MonadLiftT m SetM`-based | Read `VCVio/EvalDist/Defs/Support.lean`; `SetM` located at `Mathlib/Data/Set/Functor.lean` |
| Mathlib has **no** `Monad Measure` instance | Grepped `Mathlib/MeasureTheory/Measure/GiryMonad.lean` for an instance declaration |
| `Measure.bind_apply` requires `MeasurableSet s` and `AEMeasurable`; `bind_bind` and `dirac_bind` carry measurability, `bind_dirac` does not | Read the signatures in `GiryMonad.lean` |
| No bundled subprobability type and no sub-Markov-kernel class in Mathlib | Grepped all of `Mathlib/` for `Subprobability`/`IsSubMarkovKernel`; only `IsZeroOrMarkovKernel` and `IsZeroOrProbabilityMeasure` exist |
| **No coupling API and no TV/Rényi divergence between measures** in Mathlib | Grepped `Mathlib/Probability/` for `IsCoupling`/`Coupling`; enumerated `Mathlib/InformationTheory/` — only `KullbackLeibler` |
| Giry/ProbabilityMeasure/FiniteMeasure/Kernel/Ionescu–Tulcea/Projective/Kolmogorov/Stoch all exist | Checked each path in the pinned tree |
| PolyFun `v4.32.2` has **no** `MonadAttach` | Grepped the pinned PolyFun checkout |
| `DynComputation.unroll`, `runWith`, `Resumption.truncate`, `Run_n`, `ITree` exist | Grepped the pinned PolyFun checkout (`Run_n` is in `Dynamical/RunN.lean`) |
| `RunLimit.lean` existed historically | `git log --all --name-only -- '*RunLimit*'` → commits `cc976bb3`, `35f2af63`, `c73a676c` |
| All nine originally cited PR numbers existed and were open at the audit date | GitHub API |

### 19.2 Corrected

| # | Original claim | Verified state | Method |
|---|---|---|---|
| C1 | §4.1 presents four Mathlib PRs as one program | #42821 is a **draft**; #34138 is a separate older proposal (2026-01-19, last touched 2026-07-28, different author) that #42821 does not endorse | GitHub API `isDraft`/`createdAt`/`author`; read #42821's description |
| C2 | "PMF … Mathlib is actively trying to retire" | True and *partly landed*: the PMF distributions are already deprecated in released v4.33, but the `PMF` type is untouched at `v4.34.0-rc1` | Grepped `Mathlib/Probability/ProbabilityMassFunction/` for `@[deprecated]` at the pin; fetched `Basic.lean` and `Uniform.lean` at tag `v4.34.0-rc1` |
| C3 | Option 2 ≈ "discrete `Measure` under `⊤`" | Mathlib's own spelling is ambient `[MeasurableSpace α] [MeasurableSingletonClass α]`. `⊤` still works for VCVio and makes every side condition automatic, but diverges from upstream — see the caveat in §8 | Read `bernoulliMeasure`, `poissonMeasure`, `geometricMeasure`, and #42821's rewritten `uniformOfFinset`; confirmed `instance : @DiscreteMeasurableSpace α ⊤` and `DiscreteMeasurableSpace.toMeasurableSingletonClass` in `MeasurableSpace/Defs.lean` |
| C4 | §2.5/§12.4 treat `mvcgen` as the upstream tactic | `mvcgen` is deprecated on Lean master in favour of `vcgen` (since 2026-08-21); **not** deprecated at `v4.34.0-rc2`, so it lands in v4.35 | Fetched `Std/Tactic/Do/Syntax.lean` at tag `v4.34.0-rc2` and at master; lean4 PR list for `mvcgen`/`vcgen` |
| C5 | — (omitted) | `Std.Internal.Do` exists at v4.33/v4.34 with a lattice-generic `WP`; public as `Std.WP` on master, which core's `vcgen` dispatches on | Read `Std/Internal/Do/{Assertion,WP/Basic}.lean` in the toolchain; fetched `Lean/Elab/Tactic/VCGen/WPApp.lean` from master |
| C6 | — (omitted) | `loom2` is pinned at a Lean `v4.32.0` toolchain and supplies the `Std.Do'` substrate; its design is the one core is absorbing | Read the loom2 checkout's `lean-toolchain` and `Loom/WP/Basic.lean`; compared authorship with `Std/Internal/Do/Assertion.lean` |
| C7 | — (omitted) | `FinRatPMF` is a third, executable discrete backend with its own lifts | Read `ToMathlib/ProbabilityTheory/FinRatPMF.lean` and `VCVio/EvalDist/Instances/FinRatPMF.lean` |
| C8 | §3.2 understates ArkLib's coupling | ArkLib's `Pr_{…}[…]` *elaborates into* `PMF` do-notation; it also pins VCVio `v4.32.2` | Fetched `ArkLib/Data/Probability/Notation.lean` and `lakefile.toml` |
| C9 | — (omitted) | PolyFun#141–#144 are the companion survey and its follow-through | GitHub API; read each PR body and file list |
| C10 | §17 omits several in-tree sources | Added `FinRatPMF`, the `ToMathlib/Probability/ProbabilityMassFunction/` files, the `Loom` subtrees, and the Lean-core/loom2 section | Directory listing of the repo |
| C11 | §18 lacks an evidence standard | Added, prompted by PolyFun#144 retracting four "adopt" entries from #141 after checking them with `exact?` | Read #144's description |

### 19.3 Measured exposure

Across the non-test libraries (`VCVio/`, `ToMathlib/`, `Examples/`, `LatticeCrypto/`,
`HashSig/`): **884** lexical occurrences of bare `PMF` — i.e. excluding `SPMF`, `FinRatPMF`,
and longer identifiers — across **74** files; **2718** `PMF` substrings occur across 123 files
when derived names are counted. 575 lemma/theorem declarations live under `VCVio/EvalDist/` and
204 under `ToMathlib/Probability*`.

Densest files, by bare-`PMF` count: `ProgramLogic/Relational/Quantitative.lean` (138),
`EvalDist/TVDist.lean` (81),
`ToMathlib/Probability/ProbabilityMassFunction/RenyiDivergence.lean` (76),
`.../TotalVariation.lean` (75), `ToMathlib/ProbabilityTheory/SPMF.lean` (69),
`ToMathlib/ProbabilityTheory/Coupling.lean` (45), and `EvalDist/Defs/Basic.lean` (32).

The point of the second number is that the migration cost is concentrated, not uniform: the top
seven files carry 516 of the 884 direct occurrences — 58%, just under three fifths — and four of
them are distance/coupling files whose content §4.5 already identifies as having no upstream
counterpart. That is a different problem from the evaluator migration and should be scheduled
separately.

These are historical bare-`PMF` measurements, not the current CI allowance. The later
[`scripts/check-pmf-boundary.sh`](../../scripts/check-pmf-boundary.sh) guard deliberately counts
both standalone `PMF` and `SPMF`, because every explicit `SPMF` use retains a transitive `PMF`
dependency. At the 2026-08-30 VCVio base, its committed
[`scripts/pmf_boundary_baseline.tsv`](../../scripts/pmf_boundary_baseline.tsv) contains 1,923
occurrences across 109 files. The earlier bare-`PMF` breakdown above superseded an even older
revision produced with `grep -c`, which counted matching *lines* rather than occurrences; its
aggregate totals were unaffected, but its per-file breakdown was not.

### 19.4 Release timing at the original audit

At the original audit, Lean's cadence was about four weeks: `v4.31.0` 2026-06-15, `v4.32.0`
2026-07-13, `v4.33.0` 2026-08-10, with `v4.34.0` expected around 2026-09-07. Lean, Mathlib, and
cslib then carried `v4.34.0-rc2`; PolyFun's newest tag was `v4.33.2`. PolyFun #138 was still open,
so no tagged PolyFun release carried `MonadAttach` and that workstream had nothing to build against
yet. This paragraph is retained as scheduling evidence from that date; §20 supersedes its PolyFun
status.

This line went stale twice in a day — `v4.33.1` was current when §19 was first written, and again
when it was first corrected. Re-check tags and source pins at the moment of editing rather than
trusting a recent reading.

## 20. Focused Reverification (2026-08-30)

This pass updates the facts that control how VCVio readers should act on the PolyFun discussion.
It does not silently re-date the broader Mathlib, Lean, cslib, ArkLib, or Bluebell audit in §19.

### 20.1 Frozen revisions

| Tree | Revision | Role in this check |
|---|---|---|
| VCVio canonical `main` | `f9dc47d9dacfc5cb51dae9f92f1e34cb5ce2cc24` | Repository state whose documentation is being corrected |
| PolyFun pinned by VCVio | `c0c923693fc827a41d17116579a0c16ed4873b19` | Dependency surface VCVio can actually use |
| PolyFun canonical `main` | `3937f7ff0830cca33d6b35a24aef55bcbe3b6bc9` | Freshness check; the VCVio pin is an ancestor of this revision |

The pin, rather than the newest upstream head, is the authority for VCVio API guidance. The
upstream head is recorded separately so that “present in PolyFun main” is not conflated with
“available to this VCVio checkout.”

### 20.2 PolyFun PR disposition

The six PolyFun commits discussed in §5.2 are ancestors of both VCVio's pin and PolyFun's canonical
`main`:

| PR | Commit included in the VCVio pin | Current consequence |
|---|---|---|
| [#138](https://github.com/Verified-zkEVM/PolyFun/pull/138) | `f51fb3d` | Exact `MonadAttach` support is available; it is no longer a proposed prerequisite. |
| [#139](https://github.com/Verified-zkEVM/PolyFun/pull/139) | `fe2a140` | Free-monad WP and `WPSound` adequacy are available. |
| [#141](https://github.com/Verified-zkEVM/PolyFun/pull/141) | `3355f18` | The companion upstream-alignment survey is part of the pinned tree. |
| [#142](https://github.com/Verified-zkEVM/PolyFun/pull/142) | `f7e1234` | The cslib LTS bridge is part of the pinned tree. |
| [#143](https://github.com/Verified-zkEVM/PolyFun/pull/143) | `7d1daac` | The monad-morphism hierarchy used by the architectural argument is settled at the pin. |
| [#144](https://github.com/Verified-zkEVM/PolyFun/pull/144) | `814952a` | The upstream-reuse cleanup and its evidence-discipline corrections are part of the pin. |

This changes the operational reading of the roadmap: Phase 1's upstream prerequisites are
satisfied, but the downstream VCVio cutover tasks listed there remain real work. A landed
dependency surface is an invitation to implement the migration, not evidence that the migration
has already happened.

### 20.3 Documentation and implementation disposition

The measure-semantics spike, accepted baseline, PMF boundary guard, and measure-primary probability
surface are all present on VCVio `main`. Readers should therefore follow this order:

1. use [`docs/agents/probability.md`](../agents/probability.md) for current proof and API guidance;
2. use [`denotational-probability-semantics.md`](denotational-probability-semantics.md) for the
   accepted architecture and migration policy;
3. use [`measure-semantics-spike.md`](measure-semantics-spike.md) for implementation evidence and
   known friction;
4. return to this survey for the rejected options, original upstream audit, and dated
   re-verification records.

### 20.4 Method

- Read the VCVio dependency revision from `lakefile.lean` and confirmed the materialized checkout
  with `git rev-parse HEAD`.
- Read the declarations and module docstrings at the pin rather than inferring APIs from filenames
  or PR descriptions.
- For each of #138, #139, and #141–#144, ran `git merge-base --is-ancestor` against the VCVio pin
  and PolyFun canonical `main`.
- Confirmed that the accepted design documents and their referenced implementation files exist on
  VCVio `main`.
