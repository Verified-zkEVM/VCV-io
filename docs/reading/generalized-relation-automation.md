# Generalized relation automation in VCVio

Investigated on 2026-09-08 against VCVio
`bda0be2da973b1304e016589bb794b22ca299f45`, Lean `v4.33.1`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The experiments and production pilots accompany
this report. Dependency pins are unchanged.

## Findings and retained changes

The main opportunity is to make existing mathematical interfaces usable by generalized rewriting.
VCVio already registers expectation, event-probability, support-handler, query-slack, and unary-WP
monotonicity. Repeating that tagging pass would miss the remaining problems.

Two production pilots have current callers:

1. **Upper cost bounds.** Register `AddWriterT.pathwiseCostAtMost_mono` and
   `queryBoundedAboveBy_mono` with `gcongr`. Both tactics can now transport an inequality through
   these predicates using implication. Fischlin's search proof uses `grw` to weaken its unit and
   weighted early-return bounds and the cost of its weighted query. The unit-cost model bridge
   uses the same interface for its pure branch.
2. **Measure bind.** Add `Measure.bind_mono_right_of_forall`, with explicit `AEMeasurable`
   hypotheses and a pointwise continuation inequality. Register it for both `gcongr` and `grw`.
   `PFunctor.Resumption.outputMeasure_le_succ` now descends to the induction hypothesis using
   `gcongr`, without manually wrapping it in `Filter.Eventually.of_forall`.

The latter proof keeps its two measurability obligations and has the same number of tactic lines.
Its improvement is the direct pointwise continuation goal. Neither pilot changes the semantic
definitions or adds a tactic implementation. Only these three declarations enter the global
congruence registry. The new theorem lives below VCVio, in the existing Mathlib-facing measure
module. The two cost theorem signatures are unchanged.

Other promising registrations remain local to an experimental test module. Their value and missing
production justification are recorded below. A successful registration alone is insufficient reason
to enlarge a default tactic set.

A second caller search also removed a manual support case split from
`expectedCost_le_of_support_bound` using the existing support-aware WP rule. Three Fischlin
weakening applications only reconciled equal bounds; `simpa only` now handles them directly.
These improvements require no additional global registrations.

## Choosing a tactic

| Obligation | First choice | What to expect |
|---|---|---|
| Compare matching expressions through monotone operations | `gcongr`, optionally with a pattern or depth | Pointwise relational goals and explicit side conditions. |
| Replace a subexpression using an inequality, inclusion, or equivalence | `grw [h]` / `grewrite [h]` | A valid implication from the rewritten goal to the original; polarity matters. |
| Rewrite using a theorem whose intended relation is implication | `apply_rw [h]` | For example, event inclusion from `h : ∀ x, p x → q x`. |
| Close a comparison with a deliberately chosen list of facts | `rel [h₁, h₂]` | Finishing-only; it does not silently use every local hypothesis as a main-goal fact. |
| Apply a collection of monotonicity rules as proof search | `mono` | A separate `@[mono]` database, with different search and failure behavior. |
| Match corresponding pieces by equality | `congr!` / `congrm` / `congr(...)` | Equality obligations, even when the original relation is merely reflexive. |
| Rewrite a specific operand using a contextual equality lemma | `conv => apply_congr lemma` | Useful for support-restricted equality without changing the global simp-congruence database. |
| Establish a coupling, supply a cut relation, or rearrange games | `rvcstep` / `rvcgen` / `rel_conseq` | Keep witnesses and program-logic structure explicit. |
| Normalize structural equations or close symbolic facts | `simp` / `grind` | Their existing normal-form and fail-fast contract still applies. |
| Search through numeric bounds and positivity conditions | `bound` | A separate Aesop rule set; useful adjacent machinery, reviewed in source rather than promoted in this slice. |

Use explicit `import Mathlib.Tactic.GRewrite` for generalized rewriting; availability of
`gcongr` does not itself promise this syntax. The cost proof imports it as an implementation
dependency. The test modules use ordinary public imports, without `import all` or visibility
options.

The implementation of `mono` in this pin is a non-backtracking `apply_rules`/`solve_by_elim`
wrapper with reducible transparency and `exfalso` disabled. `mono` and `mono*` have the same
behavior here; its parsed `left`/`right`, `with`, and `using` options are unsupported. This makes
it a useful comparison, but does not justify mirroring the new registrations into another global
database. See the [pinned monotonicity implementation][mono-source].

## What a registration actually buys

The authoritative sources for this investigation are the pinned
[congruence implementation][gcongr-source], [rewrite engine][grw-source], and
[rewrite frontend][grw-elab-source], read alongside their `MathlibTest/Tactic` counterparts.

### Shape, lookup, and priorities

`gcongr` indexes by the relation's name, the expression's head constant, and its arity. For
ordinary registrations, differing arguments of the head must be free variables after the supported
reductions. A theorem about `expectedValue mx f` fits; a theorem about
`probEvent p (mx >>= f)` does not directly expose `f` as an argument of `probEvent`.

Premises relating varying arguments become recursive **main goals**. Universally quantified
variables and support assumptions in these premises are introduced; `gcongr with x hx` names them.
Other premises become **side goals**, such as measurability. Numeric priority is considered first;
within a priority, fewer varying arguments are preferred. VCVio's support-aware expectation rule
therefore retains its priority over the unrestricted pointwise fallback.

Main goals are checked against local facts, symmetry, reflexivity, and imported
`gcongr_forward` extensions. This is bounded forward reasoning, not arbitrary application of every
universally quantified hypothesis. Side goals use the extensible `gcongr_discharger`, including
imported `assumption`/`positivity` behavior. Neither mechanism is a general measurability prover.
`gcongr` may succeed while leaving goals; tests of closure must include `done`.

Implication registrations can use an existing theorem with its proof premise before the inequality
premise. The attribute finds a matching predicate hypothesis and may generate an auxiliary theorem
with reordered binders. Thus the cost lemmas need attributes, not reordered public signatures.

### Three attributes with different contracts

| Attribute | Contract |
|---|---|
| `@[gcongr]` | Checks correspondence between each varying argument pair and a suitable premise, so the rule can also construct a rewrite. |
| `@[gcongr only]` | Relaxes that correspondence check and excludes the rule from `grw`. It does not remove all conclusion-shape requirements. |
| `@[gcongr strict]` | Allows different head constants on the two sides, supporting such operations as transporting between strict and non-strict inequalities. It is not a request for more aggressive search. |

The two tactics share registered lemmas, but their engines differ. Default `grw` constructs
replacements during its own traversal; `nth_grw` and `grw +useKAbstract` use abstraction followed
by generalized congruence. Default equality/iff rewrite rules take the ordinary rewrite path.
Successful `gcongr` tests therefore do not substitute for `grw` tests.

The corpus checks the alternate `grw +useKAbstract` traversal on cost predicates. It also pins an
occurrence-selection boundary: `nth_grw 1 [h]` with `h : ∀ x, f x ≤ g x` fails when `f` occurs
as the unexpanded function argument of `expectedValue`. Supplying
`nth_grw 1 [expectedValue_mono mx h]` instead selects the complete expectation expression and
closes the tested sum comparison.

### Concrete boundaries found in the experiments

- **Support premises:** with `h : ∀ x ∈ support mx, f x ≤ g x`, `grw [h]` changes the
  expectation but leaves the rewrite theorem's support premise, even though support membership
  is available in the generated context. `grw [h]; assumption` finishes. Existing
  `gcongr with x hx; exact h x hx` is still a good interface. No global discharger was added.
- **Bind normalization:** retain `rw [probEvent_bind_eq_expectedValue, ...]` before descent.
  Neither the normal-form contract nor the existing negative bind test is relaxed. A new facade
  solely to make bind-shaped inequalities look indexable is unnecessary for these callers.
- **Raw unary WP:** explicitly `change wp mx f ≤ wp mx g` on a raw `Std.Do'.wp` goal.
  The ordinary-import test checks both the failed direct descent and the working facade.
- **Qualitative triples:** registering `relTriple_post_mono` succeeds but direct descent through
  the `RelTriple` implication still fails. Registration and runtime reduction of the abbreviations
  expose different heads. The existing `rel_conseq with R` works; a diagnostic test preserves the
  failure rather than adding another facade.
- **Equality congruence:** `expectedValue_congr_of_support` works as a local `gcongr` rule,
  but the same theorem is rejected by `@[congr]`: its support premise contains the unresolved
  fixed computation parameter. Explicit `apply_congr` works when the computation and function
  arguments are supplied. The test pins this rejection. `congr!` without a contextual rule asks
  for function equality, which loses the support restriction.
- **Almost everywhere:** `Measure.bind_mono_right` is rejected as a normal `gcongr` rule because
  its AE premise is not the required pointwise relation between the function arguments. A local
  `gcongr only` registration can close a goal when the AE fact is already supplied, but does not
  make it a generalized rewrite rule. The new pointwise companion preserves the original AE API.
- **Measurability:** a pointwise bound alone does not suffice for measure-bind rewriting. Kernel
  arguments provide measurability via their bundled proof. In the dependent resumption caller,
  `fun_prop` did not find the discrete-space proof, so the proof keeps
  `Measurable.of_discrete.aemeasurable` explicitly. There is no new measurability assumption on
  the resumption theorem.
- **Nested binds:** measurability of the outer continuation does not discharge measurability in
  each inner source. A rewrite under two binds leaves the two inner obligations even with
  `∀ x, AEMeasurable f (k x)` in context; explicit applications close them. The tests pin these
  residual goals, as well as rewriting a bind whose source is itself a bind.
- **Cost vectors and infinite bounds:** the cost rule works for `ι → ℕ` and `ℝ≥0∞`, in the same
  support-only monad context as scalar costs. `gcongr` exposes the function-order goal for a
  vector; `exact h` supplies its pointwise proof. `rel [show a ≤ ⊤ from le_top]` closes the
  infinite-bound implication without adding a finiteness hypothesis.

## Candidate ledger

Every row refers to current source or a compiled local experiment, not the historical counts in
the upstream-alignment survey.

| Candidate and relevant shape | Evidence / callers | Decision |
|---|---|---|
| `pathwiseCostAtMost_mono`: `w₁ ≤ w₂ → (PathwiseCostAtMost oa w₁ → PathwiseCostAtMost oa w₂)` | Weighted Fischlin query charge and early return; generic ordered additive costs, per-oracle vectors, infinite bounds, and both rewrite locations tested. | **Adopt attribute.** Existing statement uses `AddCommMonoid` and `PartialOrder`; do not claim only a preorder suffices for that registered theorem. |
| `queryBoundedAboveBy_mono`: `n₁ ≤ n₂ → (QueryBoundedAboveBy oa n₁ → QueryBoundedAboveBy oa n₂)` | Fischlin early return and cost-model pure branch; nested arithmetic, both rewrite traversals, wrong-polarity rejection, and generic support-only monads tested. | **Adopt attribute.** |
| `bind_mono_right_of_forall`: `AEMeasurable f μ → AEMeasurable g μ → (∀ x, f x ≤ g x) → μ.bind f ≤ μ.bind g` | Resumption observations; arbitrary measurable spaces, explicit side conditions, and kernels tested. | **Adopt helper and attribute.** Mathlib-facing follow-up candidate. |
| Existing `expectedValue_mono[_of_support]`, `probEvent_mono`, `wp_mono[_of_support]` | Pointwise/support-restricted rewriting, implication, subtraction, and hypotheses tested. | **Keep registrations; improve documentation.** |
| Existing `supportWhen_mono`, `expectedQuerySlack_mono` and its step rule | Already tagged; support-handler test uses an arbitrary oracle signature without probability classes. | **Keep.** Not missing registrations. |
| `GameEquiv.bind_congr`, `map_congr`, plus `IsTrans _ GameEquiv` | Local tests compose bind/map and rewrite nested equivalent games. Tags alone allow descent; `grw` also needs transitivity of the outer relation. | **Experimental.** Existing OTP callers need a coupling bijection; the current program-logic walkthrough already has short `rvcgen` proofs. Future composed-game proofs with supplied equivalences are a concrete use. |
| `expectedValue_congr_of_support` | Local equality descent works; direct theorem application already handles current callers. | **Experimental.** Promote when equality under a larger shared context removes repeated manual congruence. |
| `relTriple_post_mono` | Attribute accepted, facade descent fails; existing `rel_conseq` succeeds. | **Defer.** Address the abbreviation/indexing boundary only with a caller that needs compositional rewriting. |
| `MeasureProgramLogic.eRelWP_mono`, `CouplingPost.mono` | Local pointwise quantitative/qualitative postcondition tests pass. | **Experimental.** Future measure-native relational proofs can use them; current witness and bridge proofs do not become clearer merely by replacing a direct theorem call. |
| `Measure.bind_mono_right` with `gcongr only` | Local AE closing test passes; ordinary registration rejection is checked. | **Keep explicit API.** Do not suggest AE facts become pointwise facts. |
| Lower pathwise/unit-cost bounds | Local contravariant `grw` tests pass; no independent current callers of these weakening lemmas were found. | **Experimental.** Promote with a lower-cost proof caller. |
| `@[mono] queryBoundedAboveBy_mono` | Local `mono` closes a supplied bound/inequality example. | **Defer global tag.** Explicit generalized rewriting already serves retained callers. |
| New VCVio tactic or global `gcongr_forward`/discharger | No retained caller requires one. | **Reject for this slice.** Additional search would broaden behavior without demonstrated benefit. |

## Before and after at proof sites

Fischlin's weighted charge originally constructed an explicit weakening proof:

```lean
AddWriterT.pathwiseCostAtMost_mono
  (AddWriterT.pathwiseCostAtMost_addTell
    (m := m) (costFn ⟨pk, msg, comList, i, chal, resp⟩))
  (hcost _)
```

The retained proof rewrites the bound and then proves the exact charge:

```lean
by
  grw [← hcost ⟨pk, msg, comList, i, chal, resp⟩]
  exact AddWriterT.pathwiseCostAtMost_addTell _
```

The reverse arrow is deliberate: to establish an upper bound `w`, it suffices to establish the
smaller bound `costFn query`. Conversely, `grw [h] at hcost` weakens a supplied cost certificate.
The computation is fixed throughout.

For resumption observations, the old final step supplied the AE wrapper manually:

```lean
exact Measure.bind_mono_right
  Measurable.of_discrete.aemeasurable
  Measurable.of_discrete.aemeasurable
  (Filter.Eventually.of_forall fun direction => ih (next direction))
```

It now exposes the continuation comparison:

```lean
gcongr with direction
· exact Measurable.of_discrete.aemeasurable
· exact Measurable.of_discrete.aemeasurable
· exact ih (next direction)
```

Where measurability hypotheses are already in context, the test corpus closes the analogous goal
with `grw [h]`. Simple direct applications can still be shorter and faster; these additions are
compositional interfaces, not a prescription to rewrite every existing proof.

The cost-model support bound previously unfolded both weakest preconditions into infinite sums
and split on support membership. Its complete proof is now:

```lean
rw [expectedCost_eq_wp_costDist, ← wp_const (costDist oa cm) c]
gcongr with z hz
exact h z hz
```

This uses the existing `wp_mono_of_support` registration. In contrast, the signing proofs' final
continuation bounds differ only by `+ 0` and the enumeration-length equation. They now finish
with `simpa only [add_zero, hlen] using ...`, without a separate monotonicity proof.

The following counts cover the complete changed proof bodies, excluding declaration signatures,
the initial `:= by`, and blank lines. Attribute-only and assumption-scope edits do not change proof
bodies and are excluded.

| Proof | Before | After |
|---|---:|---:|
| Fischlin `fischlinSearchAuxWithUnitCost_queryBoundedAboveBy` | 46 | 45 |
| Fischlin `fischlinSearchAuxWithAddCost_pathwiseCostAtMost` | 69 | 66 |
| Fischlin `sign_usesAtMostRhoCardOmegaQueries` | 104 | 103 |
| Fischlin `sign_usesWeightedQueryCostAtMost` | 104 | 103 |
| Cost model `expectedCost_le_of_support_bound` | 6 | 3 |
| Cost model `IsPerIndexQueryBound.toWorstCaseCostBound_unit_sum` | 31 | 29 |
| Resumption `outputMeasure_le_succ` | 26 | 26 |

The caller search also covered Fiat–Shamir with abort, Fujisaki–Okamoto, replay forking, and
Diffie–Hellman reductions. Short direct theorem applications and proofs requiring substantial
algebra or case analysis were retained where generalized rewriting did not improve them. No
existing caller of `GameEquiv.bind_congr` or `GameEquiv.map_congr` was found outside their
defining module and the new experiments, so their proposed registrations remain local.

## Reproduction and validation

The ordinary-import corpus is
[`VCVioTest/Tactic/GeneralizedRelations.lean`](../../VCVioTest/Tactic/GeneralizedRelations.lean).
Local candidate registrations, rejection diagnostics, and alternative tactics are in
[`GeneralizedRelationsExperiments.lean`](../../VCVioTest/Tactic/GeneralizedRelationsExperiments.lean).
Both are included in the generated test umbrella. Their local attributes and instance do not
modify downstream defaults.

The expanded corpus contains 57 examples and two checked attribute-rejection diagnostics.
Terminal entries check closure; interactive congruence and rewrite entries pin exposed targets
or hypotheses. Dated gap pairs check the support, raw-WP, occurrence-selection, cost-vector,
measurability, and custom-relation boundaries. The nested game-equivalence example now closes
with one `grw [h, hfg, hkl]` call.

Run:

```sh
lake build VCVioTest.Tactic.GeneralizedRelationsExperiments
./scripts/validate.sh --lint --test --axioms
```

The original two `GCongr` modules, probability batteries, `GrindFailFast`, and
`LongChainPrograms` remain regression gates. No heartbeat limits, linter settings, exposure
baselines, or axiom allowances are increased. New failures do not get hidden by replacing a
terminal test with unrelated search.

To satisfy the touched-file PMF ratchet without introducing semantic aliases, the writer module's
two tail lemmas share one scoped `omit`, and Fischlin's adjacent expected-cost theorems share their
identical section assumptions. These are scope-only changes: explicit finite-distribution
identifiers decrease while theorem requirements and parameter ordering stay intact.

Validation completed successfully:

- `lake exe cache get` and the baseline `lake build` succeeded.
- `./scripts/validate.sh --lint --test --axioms` passed: proof builds, warning budgets,
  generated umbrellas, boundary checks, style and environment linters, the full test driver, and
  axiom sweep. The sweep covered 18,153 declarations in 567 proof modules, with no new axiom or
  `sorry` taint.
- The new test modules also passed an explicit `lint-style` invocation, since the style driver's
  `git ls-files` expansion does not include untracked additions before staging.
- Documentation path/coverage checks and generated-fragment checks passed after the guide edits.
- `scripts/check-pmf-boundary.sh --ratchet HEAD` passed for the complete working diff.
- Eight public signature checks across the writer and Fischlin assumption-scope edits matched the
  base revision, including the affected tail lemmas and expected-cost theorems.

### Elaboration measurements

Three fresh `lake env lean <file>` runs per module, using already-built imports, gave the following
wall times for the initial production pilots, before the additional cost-model and signing proof
simplifications. These include process startup and import loading. The unchanged notation module
is a control; differences of a few hundredths of a second are not evidence of an optimization.

| Module | Before, seconds (three runs) | Initial pilot, seconds (three runs) |
|---|---|---|
| `VCVioTest/LongChainPrograms` | 3.051, 2.955, 2.956 | 3.084, 2.917, 2.918 |
| `VCVioTest/GrindFailFast` | 7.225, 7.244, 7.281 | 7.142, 7.184, 7.163 |
| `VCVio/ProgramLogic/NotationCore` | 1.793, 1.791, 1.764 | 1.765, 1.758, 1.752 |
| `VCVio/OracleComp/QueryTracking/WriterCost` | 2.093, 2.080, 2.101 | 2.079, 2.086, 2.080 |
| `VCVio/CryptoFoundations/Fischlin/CostAccounting` | 1.779, 1.783, 1.794 | 1.762, 1.778, 1.771 |
| `VCVio/EvalDist/ResumptionMeasure` | 1.495, 1.500, 1.512 | 1.503, 1.501, 1.510 |

After the expanded caller search and full validation, three further runs with no concurrent
builds measured `CostModel` at 1.658, 1.666, 1.661 seconds for the base proof bodies and
1.667, 1.666, 1.666 for the final proofs. Final Fischlin cost accounting measured
1.770, 1.771, 1.777 seconds. These remain indistinguishable from ordinary run-to-run variation.

For a more focused comparison, minimal goal pairs using the test-corpus hypotheses were elaborated
with `Mathlib.Util.CountHeartbeats`, `set_option Elab.async false`, and `#count_heartbeats in`
around each declaration. Disabling asynchronous proof elaboration here is essential: measuring
only the command's scheduling work gives misleadingly identical before/after counts.

| Goal pair | Explicit / existing proof | Generalized rewrite | Heartbeats, before → after |
|---|---|---|---|
| Upper cost certificate from `ha` and `hab : a ≤ b` | `queryBoundedAboveBy_mono ha hab` | `grw [← hab]; exact ha` | 28 → 37 |
| Measure bind, measurable continuations and pointwise `h` | `bind_mono_right hf hg (Filter.Eventually.of_forall h)` | `grw [h]` | 56 → 108 |
| Expectation with support-restricted `h` | `gcongr with x hx; exact h x hx` | `grw [h]; assumption` | 94 → 68 |
| Two nested binds with game equivalences `h`, `hfg`, `hkl` | `GameEquiv.bind_congr (GameEquiv.bind_congr h hfg) hkl` | `grw [h, hfg, hkl]`, with the experimental local registrations and instance | 68 → 148 |

These are synchronous whole-declaration snapshots in user-facing heartbeat units, not permanent
thresholds. To repeat them, use the corresponding parameterized goals in the corpus and the two
proof bodies in the table; the nested game goal extends the single-bind rewrite example with its
second continuation. All were well below the default 200,000-heartbeat limit. Direct theorem
applications often cost less, as expected. The evidence supports adding a compositional interface
without a material module-level regression, not a claim that generalized rewriting is always faster.

## Follow-up work and upstream distinction

1. **First eligible caller:** when a proof composes existing `GameEquiv` facts under bind/map,
   promote the tested congruence registrations together with the transitivity instance. Compare
   against `rvcgen` and direct `GameEquiv.bind_congr` before choosing the proof interface.
2. **Measure-native relational development:** promote the local postcondition rules when a real
   quantitative/qualitative measure proof benefits. Measurable coupling families and gluing remain
   mathematical prerequisites for sequential rules; congruence cannot synthesize them.
3. **Mathlib-facing proposal:** the pointwise Giry-bind helper has a direct resumption caller and
   mirrors Mathlib's explicit-forall integral monotonicity rule. A future upstream proposal should
   include the ordinary registration rejection for the AE theorem and tests for both tactics.
4. **Diagnostics, not speculative search:** retain small reproducers for the qualitative-triple
   head mismatch and contextual congruence rejection. Before changing tactic internals, establish
   whether a generic upstream theorem shape or explicit normalization addresses the caller.

The rolling upstream [GCongr documentation][rolling-gcongr] was checked on 2026-09-08. It documents
`gconvert e`, which transports a proof to the target by generalized congruence and supports binder
patterns. This command is absent from VCVio's pinned `GCongr/Core.lean`; none of the experiments
or retained proofs use it. It is relevant to future consequence/weakening ergonomics, but its
presence in rolling documentation is not evidence that it is available in this build. Reevaluate
it at a coordinated toolchain/Mathlib upgrade rather than backporting a competing local tactic.

[gcongr-source]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/GCongr/Core.lean
[grw-source]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/GRewrite/Core.lean
[grw-elab-source]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/GRewrite/Elab.lean
[mono-source]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/Monotonicity/Basic.lean
[rolling-gcongr]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/GCongr/Core.html#Mathlib.Tactic.GCongr.gconvert
