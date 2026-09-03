# Probability Reasoning (EvalDist and ProbComp)

For the cross-project survey of SPMF, Mathlib measures and kernels, PolyFun
coalgebraic limits, ArkLib, Bluebell/Iris, and possible long-term migration paths, see
[`Probability Semantics for Computations: Landscape and Design Options`](../reading/probability-semantics-landscape.md).
The accepted design for new work is
[`Denotational Probability Semantics`](../reading/denotational-probability-semantics.md): use
Mathlib measures for closed denotations, kernels for environment/state-indexed computations,
effect-preserving outcome types for transformers, and keep `Pr[...]` as the discrete compatibility
surface. [`docs/reading/`](../reading/README.md) indexes the full design record.

The primary notation is now measure-valued: `𝒟[mx] : Measure α`. The former finite distribution
API is explicit as `evalSPMF mx` / `𝒮[mx]`. `Pr[...]` remains the discrete compatibility façade;
theorems `probOutput_eq_evalSPMF_toMeasure`, `probEvent_eq_evalSPMF_toMeasure`, and
`probFailure_eq_evalSPMF_toMeasure` state its meaning through the explicit compatibility measure.
Direct `FreeM` measure semantics has corresponding `FreeM.evalDist_apply_singleton` and
`FreeM.evalDist_apply_setOf` coherence lemmas. This split is intentional. An unconditional
`Eq.rec` law for `Pr[...]` only needs equality of result types in the discrete façade, whereas a
measure denotation also depends on the selected `MeasurableSpace`; type equality does not identify
those structures. We therefore do not install a blanket finite-type measurable-space instance.

`evalDist_eq_evalSPMF_toMeasure` is the sole deprecated whole-denotation bridge. It applies to the
canonical compatibility adapter; measure-native semantics should remain on `𝒟[…]` instead of
round-tripping through the finite backend.

## Core Definitions

| Definition | Type | Notation | Defined in |
|-----------|------|----------|------------|
| `evalDist mx` | `Measure α` | `𝒟[mx]` | `EvalDist/Defs/Measure.lean` |
| `evalSPMF mx` | `SPMF α` | `𝒮[mx]` | `EvalDist/Defs/Basic.lean` |
| `probOutput mx x` | `ℝ≥0∞` | `Pr[= x \| mx]` | `EvalDist/Defs/Basic.lean` |
| `probEvent mx p` | `ℝ≥0∞` | `Pr[p \| mx]` | `EvalDist/Defs/Basic.lean` |
| `probFailure mx` | `ℝ≥0∞` | `Pr[⊥ \| mx]` | `EvalDist/Defs/Basic.lean` |
| `support mx` | `Set α` | — | `EvalDist/Defs/Support.lean` |
| `finSupport mx` | `Finset α` | — | `EvalDist/Defs/Support.lean` |

### Kernel-valued interfaces

Use a `Measure α` for a closed computation and a `Kernel ρ α` when `ρ` is a semantic input:
an environment, initial state, public parameter, or previous protocol state. Do not encode the
input by immediately fixing it and returning a bare measure; doing so discards the measurability
needed for composition and data-processing theorems.

| Definition | Purpose | Defined in |
|-----------|---------|------------|
| `IsSubprobabilityKernel κ` | Every value of `κ` has total mass at most one | `ToMathlib/Probability/Kernel/Subprobability.lean` |
| `evalDistKernel f hf` | Measurable computation family `ρ → m α` as a kernel | `EvalDist/Kernel.lean` |
| `evalDistKernelOfDiscrete f` | Discrete-input specialization | `EvalDist/Kernel.lean` |
| `ReaderT.evalDistKernel` | Reader environment as kernel input | `EvalDist/Kernel.lean` |
| `StateT.evalDistKernel` | Initial state to result/final-state kernel | `EvalDist/Kernel.lean` |
| `ProbResponder.answerKernel` | Stateful interactive answer transition | `OracleComp/Coinductive/Responder.lean` |

`IsSubprobabilityKernel` is closed under `Kernel.const`, `restrict`, `map`, `comap`, `comp`,
`prod`, and powers. It implies `IsFiniteKernel`, so Mathlib's s-finite composition API is
available without restating a finiteness bound. A lossless family should additionally expose an
`IsMarkovKernel` instance or theorem.

`ProbabilitySemantics` is the total/lossless semantics bundle used by transformer adapters.
The lower-level `MeasureSemanticsVia` continues to describe potentially lossy surface semantics.

For `ProbResponder`, the kernel is authoritative. `ProbResponder.IsExecutable` optionally carries
a coherent SPMF realization for machine execution; the deprecated `ProbResponder.answer` is just
that bridge. Executable state and answer spaces must have measurable singletons, so equality with
the authoritative kernel determines every executable point mass and therefore the entire SPMF.
Pullback along an interface lens preserves executability only when the transported answer space
also has measurable singletons. This separate capability is important: abstract cryptographic
caches need not be countable, while a kernel-native responder need not have any executable SPMF
realization.

#### Adoption audit

| Area | Decision | Rationale / next integration point |
|------|----------|------------------------------------|
| Closed `evalDist`, advantages, couplings | Keep `Measure` | There is no semantic input to bundle. |
| `ReaderT` and `StateT` observations | Use `Kernel` now | Environment/state is exactly the kernel input; use the adapters above. |
| Stateful responders and wired rounds | Use `Kernel` now | `answerKernel`, `stepAgainstKernel`, and kernel powers model transitions compositionally. |
| Executable `QueryImpl`, `simulateQ`, machine runs | Keep monadic/SPMF syntax | These are programs and evaluators; cross to kernels at observation boundaries. |
| KL/data-processing continuations | Use `Kernel` now | `KLDivergence.denoteKernel` is implemented through `evalDistKernelOfDiscrete`. |
| Query tracing, caches, costs, enforcement | Migrate observations, not handlers | Add kernel views of their `StateT` runs when a theorem composes distributions across states. |
| Crypto functions parameterized by keys/messages/security parameter | Add kernels when composed probabilistically | A plain function remains clearer until measurability or data processing is actually used. |
| UC/open-process runtime | Defer to an observation boundary | Structural process syntax has no canonical measurable space; bundle a kernel only for a chosen execution/observation model. |
| Program-logic predicates and tactics | Keep computation syntax | Their job is to reason before denotation. Add kernel bridge lemmas, not kernel-valued syntax. |

When introducing a new kernel, require the real measurable-space assumptions or bundle them with
the semantic object. Do not install global `MeasurableSpace := ⊤` instances merely to discharge a
proof. For an intentionally discrete local model, `evalDistKernelOfDiscrete` or a locally bundled
measurable space is the explicit escape hatch.

### Measure-native interfaces

| Definition | Purpose | Defined in |
|-----------|---------|------------|
| `Measure.etvDist` / `Measure.tvDist` | Total variation on arbitrary subprobability measures | `ToMathlib/MeasureTheory/Measure/TotalVariation.lean` |
| `measureETVDist` / `measureTVDist` | Total variation directly on `𝒟[…]` | `EvalDist/MeasureTVDist.lean` |
| `Measure.Coupling` | Joint measure with prescribed marginals | `ToMathlib/MeasureTheory/Measure/Coupling.lean` |
| `MeasureProgramLogic.RelWP` | Almost-everywhere relational postcondition under a measure coupling | `ProgramLogic/Relational/Measure.lean` |
| `MeasureProgramLogic.eRelWP` | Best coupled `lintegral` post-expectation | `ProgramLogic/Relational/Measure.lean` |

## ProbComp and Sampling

`ProbComp α = OracleComp unifSpec α` — computations with only uniform sampling.

### Sampling notations

| Notation | Function | Type | Requirement |
|----------|----------|------|-------------|
| `$ᵗ T` | `uniformSample` | `ProbComp T` | `[SampleableType T]` |
| `$[0..n]` | `uniformFin n` | `ProbComp (Fin (n + 1))` | — |
| `$[n⋯m]` | `uniformRange n m` | `ProbComp (Fin (m + 1))` | `n < m` |
| `$ xs` | `uniformSelect` | `OptionT ProbComp β` | `[HasUniformSelect cont β]` |
| `$! xs` | `uniformSelect!` | `ProbComp β` | `[HasUniformSelect! cont β]` |

### SampleableType instances

Available for: `Bool`, `Fin n` (for `[NeZero n]`), `ZMod n`, `BitVec n`, `α × β` (from components), `Vector α n`, `Fin n → α`, `Matrix`.

### HasUniformSelect instances

- `$ xs` works for `List`, `Finset`, `Array` (can fail with `none` on empty)
- `$! xs` works for `Vector α (n+1)`, `List.Vector α (n+1)` (guaranteed non-empty)

## Simp Lemma Catalog

### Pure

| Lemma | Statement |
|-------|-----------|
| `evalDist_pure` | `𝒟[(pure x : m α)] = Measure.dirac x` |
| `evalSPMF_pure` | `evalSPMF (pure x : m α) = pure x` |
| `probOutput_pure` | `Pr[= x \| pure y] = if x = y then 1 else 0` |
| `probOutput_pure_self` | `Pr[= x \| pure x] = 1` |
| `probEvent_pure` | `Pr[p \| pure x] = if p x then 1 else 0` |
| `probFailure_pure` | `Pr[⊥ \| pure x] = 0` |
| `support_pure` | `support (pure x) = {x}` |

### Bind

| Lemma | Statement |
|-------|-----------|
| `evalDist_bind` | measure bind, with measurable continuation |
| `evalDist_bind_of_discrete` | measure bind on a discrete source space |
| `evalSPMF_bind` | `evalSPMF (mx >>= my) = evalSPMF mx >>= fun x => evalSPMF (my x)` |
| `probOutput_bind_eq_tsum` | `Pr[= y \| mx >>= my] = ∑' x, Pr[= x \| mx] * Pr[= y \| my x]` |
| `probEvent_bind_eq_tsum` | `Pr[q \| mx >>= my] = ∑' x, Pr[= x \| mx] * Pr[q \| my x]` |
| `probFailure_bind_eq_add_tsum` | `Pr[⊥ \| mx >>= my] = Pr[⊥ \| mx] + ∑' x, Pr[= x \| mx] * Pr[⊥ \| my x]` |
| `support_bind` | `support (mx >>= my) = ⋃ x ∈ support mx, support (my x)` |
| `finSupport_bind` | `finSupport (mx >>= my) = (finSupport mx).biUnion (fun x => finSupport (my x))` |

### Bind (constant continuation)

| Lemma | Statement |
|-------|-----------|
| `probOutput_bind_const` | `Pr[= y \| mx >>= fun _ => my] = (1 - Pr[⊥ \| mx]) * Pr[= y \| my]` |
| `probEvent_bind_const` | `Pr[p \| mx >>= fun _ => my] = (1 - Pr[⊥ \| mx]) * Pr[p \| my]` |

### Map

| Lemma | Statement |
|-------|-----------|
| `evalSPMF_map` | `evalSPMF (f <$> mx) = f <$> evalSPMF mx` |
| `probEvent_map` | `Pr[q \| f <$> mx] = Pr[q ∘ f \| mx]` |
| `probFailure_map` | `Pr[⊥ \| f <$> mx] = Pr[⊥ \| mx]` |
| `support_map` | `support (f <$> mx) = f '' support mx` |
| `probOutput_map_injective` | `f.Injective → Pr[= f x \| f <$> mx] = Pr[= x \| mx]` |

### Bind swapping

| Lemma | Use |
|-------|-----|
| `probEvent_bind_bind_swap` | Swap two independent binds (used internally by `vcstep` probability-equality rewrites) |
| `probOutput_bind_congr` | Congruence: equal on support → equal probability |
| `probEvent_bind_congr` | Same for events |

### Zero / membership

| Lemma | Use |
|-------|-----|
| `probOutput_eq_zero_of_not_mem_support` | `x ∉ support mx → Pr[= x \| mx] = 0` |
| `probOutput_bind_eq_tsum_subtype` | Restrict tsum to `support mx` |
| `probOutput_bind_eq_sum_finSupport` | Finite sum over `finSupport` |

## Decision Tree: Which Lemma Do I Reach For?

1. **Goal is `Pr[= y | mx >>= my] = ...`?**
   → Start with `probOutput_bind_eq_tsum`

2. **Goal is `Pr[p | mx >>= my] = ...`?**
   → Start with `probEvent_bind_eq_tsum`

3. **Need to swap two binds?**
   → Use `vcstep` if the swap should close the equality
   → Use `vcstep rw` / `vcstep rw under n` if you need an explicit rewrite step

4. **Need `Pr[= y | f <$> mx]`?**
   → If `f` is injective: `probOutput_map_injective`
   → Otherwise: `probOutput_map_eq_tsum_subtype` or `probOutput_map_eq_sum_finSupport_ite`

5. **Need to restrict a sum to support?**
   → `probOutput_bind_eq_tsum_subtype` or `probOutput_bind_eq_sum_finSupport`

6. **Continuation doesn't depend on result?**
   → `probOutput_bind_const` / `probEvent_bind_const`

7. **Two computations have same distribution?**
   → For legacy coupling lemmas, show `evalSPMF oa = evalSPMF ob`, or use
     `relTriple_eqRel_of_evalSPMF_eq`. For Mathlib probability results, compare `𝒟[oa]` and `𝒟[ob]`.

## `grind` vs `simp` on Probability Goals

`grind` and `simp` have complementary strengths here, and reaching for the wrong one is the most
common way to get a `grind` that hangs.

**Use `simp` to compute a concrete probability or factor structure.** `simp` evaluates
`Pr[= x | $ᵗ T]`, `Pr[p | $ᵗ T]`, products of uniform draws, etc.; `grind` is not an `ℝ≥0∞`/`Fintype.card`
arithmetic engine and will not finish these (it fails fast).

**Use `grind` for symbolic / membership / directed-iff goals.** Equiprobability
(`Pr[= x | $ᵗ T] = Pr[= y | $ᵗ T]`), `x ∈ support (…)`, `Pr[= x | mx] = 0 ↔ x ∉ support mx`, and
similar are squarely in `grind`'s wheelhouse.

**Why some characterization lemmas are `@[simp]` but not `@[grind]`.** A characterization whose RHS
introduces an *unbounded* quantifier or set over the support —
`Pr[…] = 0/1 ↔ ∃/∀ x ∈ support …`, `support = {x}`, `support = ∅` — is a `grind` **saturation
hazard**: as `grind` case-splits the iff it instantiates and Skolemizes the support quantifier into
fresh witnesses, which the always-tagged `bind`-expansion lemmas (`support_bind`,
`probFailure_bind_eq_add_tsum`, `mem_support_bind_iff`, …) re-expand into yet more `support`/`Pr[…]`
terms, with no finite grounding (`support ($ᵗ α) = Set.univ` is infinite). The hazard is
**combinatorial, not per-lemma**: no single one of these lemmas saturates `grind` on its own (restore
any one and a `grind` that should fail fast stays fast), but tagged *together* they form a re-trigger
cycle — restoring all of them makes that same `grind` run ~25× longer. The **hub of the cycle is the
`probEvent_eq_one_iff` family**: its RHS `Pr[⊥|mx]=0 ∧ ∀ x∈support, p x` couples the `probEvent`,
`probFailure`, and `support` layers at once (drop it and the blow-up roughly quarters). So that
family, together with the `∃`-Skolemizing `probEvent_ne_zero_iff` and the `probEvent_eq_zero_iff`
families, is kept `@[simp]`-only (fixed orientation, no case-split — safe). The *directed
single-variable* membership bridges (`probOutput_eq_zero_iff : … ↔ x ∉ support`, `probOutput_pos_iff`,
`mem_finSupport_iff`, `mem_finSupport_iff_mem_support`) are confluent and stay `@[grind =]`.

Lemmas kept `@[simp]`-only by this rule (in `EvalDist/Defs/Basic.lean` unless noted):
`probEvent_eq_zero_iff(')`, `probEvent_ne_zero_iff(')`, `probEvent_eq_one_iff(')`,
`one_eq_probEvent_iff(')`, `probOutput_eq_one_iff`, `one_eq_probOutput_iff`, `probFailure_eq_one_iff`;
and `mem_support_bind_iff` / `mem_finSupport_bind_iff` (untagged — `support_bind` / `finSupport_bind`
are the `simp` forms).

**Support-quantifier lemmas verified safe in isolation, kept `@[grind =]`.** A few carry the support
quantifier yet sit *outside* the `probEvent_eq_one_iff` hub cycle and add no measurable `grind` cost
on their own, so they keep their `grind` tag: `probEvent_pos_iff(')`, `probOutput_eq_one_iff'` (the
mirror of the never-dropped `one_eq_probOutput_iff'` — both are the `finSupport`-singleton form), and
`probFailure_bind_eq_zero_iff` (in `EvalDist/Monad/Basic.lean`). These are safe **only while the hub
family stays `@[simp]`-only**: re-tagging the `probEvent_eq_one_iff` family alongside them re-forms the
saturation cycle. `VCVioTest/LongChainPrograms.lean` is the 10+-step stress benchmark for exactly
this.

**If a `grind` proof needs one of these, re-supply it locally:** `grind [probEvent_eq_zero_iff]`. This
keeps the bridge out of the default set (so naive `grind` on a probability goal fails fast instead of
hanging) while letting the proof that genuinely needs it opt in.

**`Set.Nonempty`-phrased companions stay in the default `grind` set.** `grind` keeps `Set.Nonempty`
atomic (it does not unfold it to `∃ x ∈ support`), so a characterization phrased via `Nonempty`
carries the same information without the saturating quantifier. `probFailure_eq_one_iff_not_nonempty`
(`Pr[⊥ | mx] = 1 ↔ ¬ (support mx).Nonempty`) is the `grind`-friendly companion to the `simp`-only
`probFailure_eq_one_iff` (`… ↔ support mx = ∅`); reach for the `Nonempty` form when a `grind` proof
needs to reason about a computation failing (or not) with probability one.
`support_uniformSample_nonempty` (`(support ($ᵗ α)).Nonempty`, `@[grind]`) closes the loop, letting
`grind` conclude e.g. `Pr[⊥ | $ᵗ α] ≠ 1` end-to-end.

The event-probability versions follow the same recipe with the *filtered* support `{x ∈ support mx | p x}`
(the reachable outputs satisfying `p`): `probEvent_eq_zero_iff_not_nonempty`
(`Pr[ p | mx] = 0 ↔ ¬ {x ∈ support mx | p x}.Nonempty`) is the `@[grind =]` companion to the
`simp`-only `probEvent_eq_zero_iff`. Its sibling `probEvent_ne_zero_iff_nonempty` (`Pr[ p | mx] ≠ 0 ↔ …`)
exists but is deliberately **untagged**: the trio of `Nonempty` companions tagged together re-forms
a saturation cycle in the *generic-monad* context (`grind` on the `probEvent_eq_one_iff` statement
shape times out instead of failing fast; dropping any one of the three restores fail-fast), and
dropping the `≠ 0` sibling is free — `grind` recovers `≠ 0 ↔ Nonempty` from the kept
`= 0 ↔ ¬ Nonempty` form by classical negation. The `Pr[…] = 1` companions are deliberately
*omitted* entirely: a `Nonempty`-phrased `probEvent_eq_one` keeps its `Pr[⊥ | mx] = 0` conjunct,
which re-couples it to the hub family; the `= 1` cases use `grind [probEvent_eq_one_iff]` opt-in
instead. `VCVioTest/GrindFailFast.lean` gates all of this: each dropped lemma has a
`fail_if_success grind` + `grind [<lemma>]` example over a generic `m`, so both a bad re-tag
(bare `grind` starts succeeding) and a new saturation (the timeout escapes `fail_if_success`)
fail the build loudly.

**Monad/functor laws normalise structure for `grind`.** `bind_pure`, `bind_assoc`, and
`map_pure` are tagged `@[grind =]` (in `EvalDist/Monad/Basic.lean`); `pure_bind` is already in the
default set from core (`attribute [grind <=] pure_bind` in `Init.Control.Lawful`), so it is not
re-tagged here. They are confluent rewrites, so
`grind` collapses a computation's structure (`mx >>= pure = mx`, `pure a >>= f = f a`, …) *before*
falling into `probOutput`/`tsum` expansion — turning what would otherwise be a `grind` *explosion* on
a `bind`/`pure`-shaped probability/support/distribution equality into a quick solve
(`Pr[= x | mx >>= pure] = Pr[= x | mx]`, `𝒮[do let x ← mx; pure x] = 𝒮[mx]`,
`support (do let b ← $ᵗ Bool; pure b) = Set.univ` all close by bare `grind`). `bind_pure_comp` /
`map_eq_bind` are omitted (function argument under a binder, unindexable). A *non-trivial*
`<$>` / `if` / `<*>` does not normalise to a `pure`, so those structured equalities stay
`simp`-terminal.

**Independent products factor via `@[grind norm]`, not E-matching.** The second factor of
`Pr[= z | (·, ·) <$> mx <*> my]` sits under a binder (`Seq.seq`'s `Unit → _` thunk), which
`grind`'s pattern compiler cannot index — tagging the factorization lemma `@[grind =]` yields an
"invalid pattern" error (so do `pure_seq`/`seq_pure`). The escape is `grind`'s *normalization*
phase: `probOutput_seq_map_prod_mk_eq_mul` is `@[simp high, grind norm]`, so bare `grind` factors
the applicative spelling (and closes e.g. equiprobability of a uniform product). The `bind`-spelled
product (`do let x ← mx; let y ← my; pure (x, y)`) remains `simp`-only — the second draw sits under
`bind`'s continuation, which the seq-keyed norm rule does not reach.

**`grind norm` can starve E-matching — use it sparingly.** Norm rules rewrite goal/hypothesis
terms *before* E-matching, so a norm rule whose result no longer matches the `@[grind =]` patterns
disconnects them. Concretely: `@[grind norm] bind_pure_comp` (`mx >>= fun a => pure (f a)` →
`f <$> mx`) closes a couple of `target(grind)` gaps but breaks the `replicate` gates — the goal's
do-block normalises to a `<$>` form while the E-matching-side `replicate` unfolds stay in `bind`
form, and the E-graph never connects the two. It is therefore deliberately **not** tagged. Gate any
new `@[grind norm]` candidate against all of `VCVioTest/{ProbabilityTactics,MonadProbability,`
`LongChainPrograms,GrindFailFast}.lean` before keeping it.

**Structural additions to the default set** (all gated in `VCVioTest/GrindFailFast.lean`):
`OracleComp.replicate` unfolds (`replicate_zero`, `replicate_succ_bind`, `replicate_pure`,
`replicateTR_*` — the proof-level loop combinator; core already grind-tags the `List.mapM` /
`foldlM` / `forIn` layer), `Functor.map_map`, `probEvent_False`/`probEvent_false`, and the
`simulateQ` routing layer (`QueryImpl.add_apply_inl/inr`, `simulateQ_add_liftComp_left/right`,
the `withBadFlag`/`withBadUpdate`/`flattenStateT` run-shapes, `simulateQ_option_elim(M)`). The
`simulateQ_add_liftComp` pair also *fixes a saturation*: bare `grind` used to time out on a routed
`simulateQ (impl₁ + impl₂)` goal over a lifted computation.

`VCVioTest/ProbabilityTactics.lean` is the living benchmark and **gate** for all of this: a broad
corpus of probability / event / failure / support / distribution facts organised by category, each
closed by a single *terminal* tactic. Where a fact closes by **both** `simp` and `grind`, both are
kept (the mirror), so each tactic stays exercised on that shape; where only one closes, the gap is a
`target(simp)` / `target(grind)` note. A regression in either tactic surfaces there in isolation.
When adding probability automation, add the corresponding battery rows.

`VCVioTest/MonadProbability.lean` is the **generic-`m`** companion: the same gate over an abstract
monad `m` with the EvalDist instance stack (`[LawfulMonadLiftT m SPMF]`, …) and over the concrete
transformers (`OptionT`, `ExceptT`, `SPMF`, `Id`), where the lemmas are actually stated. It surfaces
facts `ProbComp` masks — chiefly the **failure factor**: over a monad that can fail,
`Pr[= y | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[= y | my]` and `Pr[⊥ | mx <* my]` /
`Pr[⊥ | mf <*> mx]` are inclusion–exclusion (`Pr[⊥|a] + Pr[⊥|b] - Pr[⊥|a]*Pr[⊥|b]`); both collapse
to the `ProbComp` forms only because `Pr[⊥] = 0` there. New API filled along the way:
`probOutput_map` (the `probOutput`/`<$>` companion to `probEvent_map`, `@[grind =]`), `support_guard`,
and the `orElse` (`<|>`) probability lemmas for `OptionT (OracleComp spec)` (`probFailure_orElse` etc.).

**Opting out downstream.** VCVio deliberately extends the *default* `grind` set — the monad laws
above plus the probability/support bridges — and these tags are inherited by every project that
imports it. All of the standard escape hatches work if a downstream `grind` call misbehaves:
disable a rule per call (`grind [-bind_pure]`), ignore the default set entirely
(`grind only [the, lemmas, you, want]`), or unset a tag for a whole file
(`attribute [-grind] bind_pure`). `grind?` reports a minimal `grind only [...]` call for a goal it
closes, which is the easiest way to make a fragile call site independent of the default set.

## Common Mistakes

1. **Missing probability spec classes**: on `OracleComp spec`, `evalSPMF`/`probOutput`/`Pr[...]` require `[IsProbabilitySpec spec]`. Uniform/cardinality lemmas and support-probability lemmas require `[IsUniformSpec spec]`, not just `[spec.Fintype] [spec.Inhabited]`. Use `IsUniformSpec.ofFintypeInhabited spec` when a concrete finite inhabited spec should use uniform sampling. `𝒟[...]` additionally needs an ambient `MeasurableSpace` on the output.

2. **Carrying duplicate probability instances**: do not add a separate `[IsProbabilitySpec spec]` when `[IsUniformSpec spec]` is already in scope. `IsUniformSpec` extends `IsProbabilitySpec`; a second instance can make instance search ambiguous and may not describe the same distributions.

3. **Using `support` when `finSupport` is needed**: `probOutput_bind_eq_sum_finSupport` requires `[DecidableEq α]` and `[HasEvalFinset m]`.

4. **Forgetting `probOutput_eq_zero_of_not_mem_support`**: useful when restricting sums.

5. **`evalSPMF` on bare `query t`**: works directly when the expected type pins `query t` to a monadic form, since `query` resolves to `HasQuery.query`. Write `evalSPMF (query t : OracleComp spec _)` (or hand the result to a context that provides the same ascription). If you need the primitive `OracleQuery spec _` (e.g. for `OracleQuery.cont`), use `spec.query t` instead.
