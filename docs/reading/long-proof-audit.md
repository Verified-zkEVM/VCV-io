# Long proofs: automation, extraction, and mathematical structure

The largest immediate opportunity is **reusing semantic normalization**, followed by **factoring
state-transition invariants**. More generalized-congruence registrations help at comparison leaves,
but they do not account for most of the length of the largest proofs. Several long proofs already
contain short mathematical arguments surrounded by repeated descriptions of the same games.
Others, especially potential arguments and explicit coupling constructions, contain substantial
mathematics that should remain visible.

This audit examines the source at `fb2b3a960df430454596ac9ee0aaf7b1f934762b`, including the
cost/measure congruence changes. The ranked data is in [long-proof-audit.csv](long-proof-audit.csv).
The findings below distinguish compiled experiments from proposed extractions. Production Lean
files were not changed for the initial audit. The implementation results below are a separate
follow-up; the CSV and original case studies retain their baseline measurements.

## Implementation results — September 2026

The implementation follows the measure-first constraint. Native semantic proofs use `Measure`
and Giry composition; existing discrete interfaces have compatibility wrappers. Structural
cache/log proofs use no probability assumptions. This does not remove the library's complete
retiring probability surface or change the substantive coupling mathematics.

The work is split into the following review stages:

| Stage | Change | Review |
|---|---|---|
| Sampling foundations | Separate native semantics cores; measurable draw interchange and rotation | [#687](https://github.com/Verified-zkEVM/VCVio/pull/687) |
| Adaptive bounds | Cache/log coherence helpers and native measure inductions | [#690](https://github.com/Verified-zkEVM/VCVio/pull/690) |
| BR93 | Shared transcript experiment, observation identities, and event inclusion | [#693](https://github.com/Verified-zkEVM/VCVio/pull/693) |
| PRF tag/reader | Native table laws, composed lazy/eager bridges, and shared observations | [#694](https://github.com/Verified-zkEVM/VCVio/pull/694) |
| KEM–DEM | Probability-free games and shared native hybrid argument | [#695](https://github.com/Verified-zkEVM/VCVio/pull/695) |
| Stateful Fiat–Shamir | Shared structural outcome relation and pure invariant preservation | [Chain.lean](../../VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/Chain.lean) |

Using the same lexical body measurement as the initial audit:

| Existing proof body | Baseline lines | Implemented lines |
|---|---:|---:|
| PRF positive-slot case | 774 | 541 |
| PRF zero-slot case | 696 | 463 |
| PRF reader case | 664 | 606 |
| PRF headline composition | 262 | 167 |
| BR93 inversion-bound wrapper | 352 | 4 |
| KEM–DEM composition wrapper | 194 | 57 |
| Fiat–Shamir freshness/log step | 175 | 4 |
| Fiat–Shamir live/adversary-cache step | 118 | 4 |

These caller counts exclude extracted definitions, theorem signatures, and helper proofs.
They measure reduced repetition at the call sites, not elimination of the mathematical work.
For example, Fiat–Shamir now has a shared 61-line support-case proof and 39-/28-line pure
preservation proofs. KEM–DEM has a 31-line native composition argument in addition to its
shared game identities and Boolean measure algebra. BR93's short wrapper invokes a native
event-inclusion bound after separately proved transcript observations.

The remaining long PRF reader body still contains distinct acceptance and rejection arguments,
cache-column facts, and collision counting. Positive and zero tag slots likewise retain different
cell-identification arguments. The instrumented lazy/eager table induction is about the same
size after its measure migration (228 to 231 body lines): its benefit is explicit calibration and
reusable semantics. Further reductions there need additional domain lemmas, rather than more
generalized-congruence registrations. The native adaptive and online inductions retain the
potential argument while sharing cache/log updates (106 and 144 body lines respectively).

Validation includes the full build, environment and source linters, test libraries, smoke and
SLH-DSA tests, and the axiom sweep. Native-only import checks cover draw, table, and KEM–DEM
foundations. Transitive theorem-dependency checks cover the adaptive bounds, table core, and
pure Fiat–Shamir invariant updates. Sampling frontend types such as `SampleableType` still carry
compatibility certificates, so these checks deliberately distinguish the native foundation from
the frontend adapter. No new axioms or `sorry` debt were introduced.

The discrete rotation experiment below is historical. Production callers use
`evalDist_bind_bind_bind_rotate`; they do not use the prototype's discrete semantic proof.

## Scope and measurement

A source scan covered 560 Lean files under the seven default library directories and identified
6,196 named theorem/lemma bodies. It excluded dependencies, tests, dormant `Interop`, and proofs
embedded in definitions or instances. These are source-size measurements, not measurements of
human effort, elaboration time, or kernel proof-term size.

The scanner erases nested comments and strings while retaining line positions, finds declaration
boundaries, and locates the body assignment outside nested brackets. This matters: the largest
signatures contain long induction hypotheses and named arguments that must not be counted as the
proof. The ranking is a lexical census rather than a Lean parser export; the leading declarations
and the phase boundaries discussed below were also inspected directly.

“Lines” below means nonblank, noncomment body lines, including a standalone leading `by`. A line
containing a long term counts once. The CSV's tactic/`have`/`let` columns are token counts; in
particular, `let` includes repeated do-blocks inside local theorem statements, not just distinct
local definitions. The `debt` column detects explicit proof-hole tokens in a body and is not a
transitive axiom audit.

| Library | Named bodies found | Largest body | Bodies of at least 100 lines |
|---|---:|---:|---:|
| `Examples` | 516 | 774 | 24 |
| `VCVio` | 3,786 | 209 | 24 |
| `LatticeCrypto` | 406 | 134 | 3 |
| `ToMathlib` | 612 | 74 | 0 |
| `HashSig` | 816 | 73 | 0 |
| `Extern` | 60 | 28 | 0 |
| `VCVioWidgets` | 0 | — | 0 |

Only 51 scanned bodies reach 100 lines. The three largest total 2,134 lines, all in one direct
coupling development. This makes a focused pass more promising than a repository-wide tactic
replacement campaign. Short source proofs can still be difficult or depend on substantial admitted
results; this inventory is not a ranking of mathematical completeness.

## Compiled experiments

### Generalized congruence: a small, real win

In the final bad-event comparison of [`dcAux_tag_slotPositive`][positive-tail], six lines manually
descend through two weighted sums and an event implication. After the existing normalization,
these can become:

```lean
gcongr with gS gFine z hz_mem
intro _
```

The existing bad-flag preservation theorem still supplies the final fact. A temporary copy of the
complete source file compiled with this replacement. This removes four lines from a 774-line body;
it improves the comparison interface but leaves its dominant work intact.

### A small semantic helper: a much larger win

Both tag proofs contain local `hLHS_comm` and `hBAD_comm` facts. Each moves a nonce draw before
two independently sampled tables. Each local proof body contains **105 noncomment lines**,
mostly restating the large continuation at intermediate stages. A generic composition of the
existing [`evalSPMF_bind_bind_swap`][swap] law proves the required permutation in four lines:

```lean
theorem rotate_independent_draws {α β γ δ : Type}
    (ma : ProbComp α) (mb : ProbComp β) (mc : ProbComp γ)
    (f : α → β → γ → ProbComp δ) :
    𝒮[ma >>= fun a => mb >>= fun b => mc >>= fun c => f a b c] =
      𝒮[mc >>= fun c => ma >>= fun a => mb >>= fun b => f a b c] := by
  trans 𝒮[ma >>= fun a => mc >>= fun c => mb >>= fun b => f a b c]
  · rw [evalSPMF_bind, evalSPMF_bind]
    exact congrArg _ (funext fun a => evalSPMF_bind_bind_swap mb mc (f a))
  · exact evalSPMF_bind_bind_swap ma mc _
```

All four local proofs can then be `exact rotate_independent_draws _ _ _ _`. Temporary copies of
both complete modules compiled with these substitutions and the helper in scope.

| Body | Original | Prototype | Removed from caller |
|---|---:|---:|---:|
| `dcAux_tag_slotPositive` | 774 | 566 | 208 |
| `dcAux_tag_slotZero` | 696 | 488 | 208 |

The 416 removed caller lines exclude the shared helper's declaration and proof. These prototypes
retain the large statements of `hLHS_comm` and `hBAD_comm`; naming the continuation and proving
one result-polymorphic observation equation could reduce repetition further, but that additional
saving has not been measured.

This is a proof of reuse in the current compatibility layer. It does not require a new congruence
attribute. Production placement should reuse the existing probability/semantic equation API and
respect the retiring PMF/SPMF boundary; it should not introduce another semantic representation.
A direct `vcstep` trial on these raw `𝒮[…] = 𝒮[…]` goals failed because that is not a supported
entry shape. This does not rule out a probability-level or relational reformulation.

### Cache/log coherence: a verified extraction boundary

[`AdaptivePrefix`][adaptive] and [`OnlineBound`][online] both prove that, after a cache miss,
updating the cache and appending the response to the log preserves the correspondence from log
entries to cache entries. The same 15-line proof occurs in both. A helper with the following
interface compiled without probability or finiteness assumptions:

```lean
(cache : (ι →ₒ Y).QueryCache) (log : (ι →ₒ Y).QueryLog)
(t : ι) (value : Y) (hnone : cache t = none)
(hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2) :
∀ entry ∈ log ++ [⟨t, value⟩],
  (cache.cacheQuery t value) entry.1 = some entry.2
```

It needs only `[DecidableEq ι]`. Replacing each occurrence with one application compiled in
copies of both complete modules. That removes 28 caller lines before counting the shared helper.
The reverse cache-to-log correspondence and cache-domain size update are adjacent, similar
extraction candidates; they were inspected but not implemented in this experiment.

## What drives the longest proofs

### 1. Positive-slot tag coupling — 774 lines

[`dcAux_tag_slotPositive`][positive] has 58 `have` declarations. Its main phases are:

| Source phase | Noncomment lines | Work performed |
|---|---:|---|
| Setup, through line 204 | 43 | Consume the tag-query budget, construct the next session state, and identify the nonzero slot. |
| Lines 205–592 | 381 | Restate the success, comparison, and bad-event computations; move the nonce draw outside both table draws. |
| Lines 593–631 | 27 | Split the nonce budget and enter the disagreement bound. |
| Lines 632–976 | 322 | Handle cache miss/hit, marginalize table cells, preserve invariants, apply the induction hypothesis, and bridge the two slot updates. |

The standalone leading `by` accounts for the remaining line in the total.

The essential reasoning is why an update to slot zero on one side can be compared with an update
to the current nonzero slot on the other, and why a cached response makes the bad flag sufficient.
The existing [`singleTableHandler_cache_swap_eq`][swap-bridge] already packages the difficult
permutation of table cells. The strongest next step is to combine that existing bridge with shared
observation/marginalization lemmas, rather than expand it again.

**Recommendation:** take the verified draw-rotation extraction first. Then define the repeated
continuation once and establish its observation equation for arbitrary result projections. Keep
the positive-slot mathematical branch separate from the zero-slot branch: the cache symmetry and
independence obligations differ.

### 2. Zero-slot tag coupling — 696 lines

[`dcAux_tag_slotZero`][zero] has the same three observations and the same sampling-order
normalization. Its commutation phase alone contains 298 noncomment lines. The later cache split
applies the induction hypothesis with either the unchanged cache or a newly populated slot-zero
cell, while preserving the response invariant.

Here the tag-step outputs agree directly. Most additional proof work comes from threading the
unused fine table, moving samples, and restating the same projected runs. This is why the same
small helper removes 208 caller lines despite the distinct mathematical case.

**Recommendation:** share sampling and observation equations with the positive-slot proof;
extract the cache extension's invariant preservation next. A Boolean parameter that merges both
entire proofs would hide the useful distinction between their coupling arguments.

### 3. Reader step — 664 lines

[`dcAux_reader_step`][reader] contains 42 `have` declarations and 74 normalization tokens. It first
normalizes three observations, then samples/caches the slot-zero column before the remaining
computation. The first two phases account for 232 lines. Another 62 lines establish cache and
response invariants after extending the set of reader-touched nonces. The final acceptance split
occupies 369 lines.

The substantial argument is that the multiple-world reader bit becomes fixed once its column is
cached. If that bit is true, the induction hypothesis applies directly; if false, single-world
acceptance is a separate event charged to the reader error budget. This is more than monotonicity:
it chooses the coupling information and explains where the error comes from.

**Recommendation:** extract one column-caching observation theorem parameterized by the final
observable, plus a lemma giving the post-column invariant bundle. Then expose the two acceptance
cases as named probability bounds. `gcongr` can shorten the final integration of those bounds,
but it cannot supply the acceptance-disagreement argument. These extractions are proposed, not
compiled in this audit.

### 4. BR93 bad-event reduction — 352 lines

[`badEventProb_le_tdpAdvantage`][br93] spends **330 lines** in five local equalities normalizing the
bad-event and inverter experiments. Only 18 lines remain after those rewrites for the nested
probability comparison and the transcript argument.

The key mathematical fact is already extracted: `find?_inr_of_anyInr` converts a bad-event log
witness into a usable inversion query. Most remaining effort is exposing a shared logged run,
discarding irrelevant uniform-oracle log entries, relocating the challenge sample, and reconciling
nested writer/state projections.

**Recommendation:** introduce a shared challenge-and-transcript experiment and prove observation
lemmas for its bad flag and inverter output. The headline bound should then compare two predicates
on that same experiment. This is an observation-API refactor with a small security argument, not
a need for a stronger arithmetic or generalized-relation tactic. The existing logging/projection
lemmas should remain the implementation foundation.

### 5. Direct-coupling composition and eager tables — 262 / 228 lines

[`multipleIdeal_le_singleIdeal_add_bad_DC`][compose] mainly translates between representations:
lazy multiple-bad execution, eager tables, a slot-zero subtable, and a finer handler with extra
bookkeeping. Success and bad-event observations repeatedly traverse the same projection equations.
Its final application of the direct-coupling induction occupies only the end of the proof.

[`evalSPMF_simulateQ_multipleBadQueryImpl_run_eq_tableExtending`][eager] proves one of those bridges
by induction. Related multiple-ideal and single-ideal bridges in [`Table.lean`][table] have 151
and 146 lines. Their tag and reader branches repeatedly normalize state runs, reuse cache-step or
cache-column sampling lemmas, and reconcile output projections.

**Recommendation:** extract bridges for a joint output/state distribution, then obtain individual
observations by projection. Consider a shared lazy/eager simulation invariant only after those
observation equations are reusable. Do not create another induction principle merely to shorten
three callers; existing simulation and handler laws may already supply the required transport.
Generalized rewriting is useful after these semantic equalities are available.

### 6. Authentication collision step — 249 lines

[`probEvent_authRFQueryImpl_step_core`][forge] bounds the probability that a distinguished response
cell has a chosen value, plus a weighted probability that the cell remains unfilled. The tag branch
expands the same stateful computation separately for both events, splits on whether the sampled
nonce targets that cell, and then splits on cache hit/miss. The reader branch handles a sequence
of lookups and an untouched-cell case.

The reusable mathematical idea is a one-cell potential: discovering a fresh cell pays at most its
maximum point probability, while leaving it unfilled retains the potential. The current proof
expresses that idea as two separately expanded event probabilities.

**Recommendation:** investigate a single expected-value postcondition for this potential, with
one-query and lookup-sequence lemmas. This could also serve the 148-line response-bound induction
and the 194-line adversary collision proof. It is a meaningful lemma/API extraction; `gcongr`
alone would save only the sum and multiplication wrappers. The proposed potential reformulation
has not been compiled.

### 7. Adaptive-prefix and online-target bounds — 168 / 209 lines

The two proofs share an induction over remaining oracle syntax, cache-hit and cache-miss run
normalizations, cache/log consistency preservation, a fresh-response probability bound, and a
numeric potential recurrence. The online version additionally propagates `Good` and charges a
response hitting a target set determined by the **pre-query** log. Its recurrence and target bound
are not interchangeable with the simpler adaptive-prefix theorem. [Sources: adaptive][adaptive],
[online][online].

Most avoidable proof work is the repeated structural invariant transport. The tested cache/log
helper establishes a low-level extraction that can live with the existing cache/log handler API.
A small invariant bundle could subsequently group cache coverage, log consistency, and domain
size, with hit/miss preservation lemmas.

**Recommendation:** extract those structural facts first. Only then evaluate a common induction
parameterized by a potential and fresh-step charge. Preserve the online theorem's predictable
target condition: using targets computed from the future log would change the argument, not just
its presentation. Arithmetic `gcongr` improvements at the final recurrence are secondary.

### 8. KEM–DEM composition — 194 lines

[`ind_cpa_one_time_bias_advantage_compose_with_dem_le`][kemdem] contains four explicit games, a
coin-branch identity, and four reduction/game identities. The identities occupy 121 lines; the
final distance triangle and substitutions occupy 30.

The real reduction choices are replacing the encapsulated key on each side and arranging the
middle DEM challenge. Most proof maintenance comes from repeating evaluation-distributes-over-bind
steps, Boolean challenge splits, constant-draw removal, and sampling commutation. The final
triangle inequality is already straightforward.

**Recommendation:** name the real/random message games and extract the four observation identities.
A message-selection parameter can likely share the left/right KEM identities. Keep the public
losslessness and runtime-coherence assumptions explicit. Because this file uses the retiring
SPMF representation directly, coordinate the refactor with the semantic boundary rather than
exporting a second family of legacy game definitions. More `gcongr` tags have little direct value
until the game identities are available.

### 9. Stateful Fiat–Shamir invariant preservation — 175 lines

[`forkLoggedImpl_preserves_inv_step`][stateful] has 44 `have` declarations and 17 case-analysis
tokens. It separates forwarded randomness, random-oracle cache miss/hit, and signing. Within
those cases it repeatedly projects equalities out of nested state tuples, substitutes components,
and proves that updates preserve fresh-query agreement and the query-log invariant.

The file already has `forkLoggedImpl_sign_support`; this is a good model for a corresponding
random-oracle support interface. The companion live-adversary invariant step is another 118 lines
with related branch structure. Existing generic `StateT.PreservesInv` and `QueryImpl` composition
laws should be reused, not redeclared; the [duplication ledger][duplication] records that boundary.

**Recommendation:** first provide semantic support cases for the composed random-oracle handler,
then pure invariant-preservation lemmas for each resulting state update. The outer proof can
compose them with the existing structural invariant rules. These are propositions about states,
so inequality automation is not the missing ingredient.

### 10. Fischlin's potential induction — 155 lines

[`main_induction_gen`][fischlin] is closer to irreducible mathematical work. It distinguishes
forwarded queries, cache hits, fresh live-slot reveals, new-slot creation, and inert/dead-slot
updates. The reveal case invokes `Phi_extend_le` or `Phi_open_le`; the inert case proves that
previously revealed records force the appropriate dead-slot condition.

There is still removable presentation work: the reveal branch expands a uniform expectation to a
finite sum, distributes constant terms, and cancels the sampling cardinality. Existing
`expectedValue_add`, `expectedValue_const`, and the uniform WP/expectation equations suggest a
small affine-average lemma. The proof already uses `gcongr` in several places, including dead-set
monotonicity and budget weakening.

**Recommendation:** extract the finite-average calculation and, if useful elsewhere, the
record-disagreement-to-dead-slot fact. Keep the reveal/open/inert case structure explicit. A generic
potential induction framework is worth considering only with a second proof using the same
invariant transitions; simply moving this proof into a more parameterized theorem would not remove
its main reasoning.

### 11. Merkle extraction disagreement — 155 lines

[`fresh_extractedTarget_of_extractor_disagreement`][extraction] inducts down a leaf path. At each
internal node it either finds a fresh queried value immediately or uses cache/log agreement and
collision freedom to identify the extracted children. It then transfers the leaf/proof disagreement
to the selected child. The left and right cases repeat much of this argument with swapped child
positions and proof-head conventions.

**Recommendation:** extract the cache/log-to-children fact and the disagreement transfer for a
selected child. A direction-indexed view might share the mirrored branches, but only if it keeps
address and proof-vector types easy to use. The essential reasoning is structural witness
construction; congruence can handle equality transport after the witnesses are supplied.

### 12. ML-KEM encoding — 134 / 119 lines

[`byteDecode_byteEncode_of_bound`][encoding] has 33 `have` declarations, largely index bounds and
representation equalities. The argument itself is coefficientwise: coefficient bits survive
bit-to-byte-to-bit conversion, the block at `i * d + j` is the `j`th bit of coefficient `i`, and
reconstruction by `ofDigits` recovers the bounded coefficient. A specialized 12-bit roundtrip is
another 119 lines.

The file already has `bytesToBits_bitsToBytes_getElem`, `ofDigits_digitsAppend_two`, and digit
bounds. The missing convenience layer is between those local facts and the polynomial facade:
block-index quotient/remainder facts, a consistent array access interface, and a bounded coefficient
block reconstruction theorem.

**Recommendation:** factor a generic fixed-width block codec law, then instantiate it at the
polynomial and 12-bit formats. Preserve bit order, byte alignment, coefficient bounds, and the
`ZMod` conversion explicitly. This is a representation-API refactor; order automation is relevant
only to small bound side goals. A broad simplifier will not reconcile dependent array indices
without the right equations.

## Long proofs that should not drive a tactic campaign

The 118-line [`tsum_min_le_eRelWP`][coupling] constructs an explicit coupling: diagonal common mass
plus a normalized product of residual masses. It handles zero residual mass, proves both marginals,
constructs a distribution, and evaluates its diagonal objective. Those are substantive obligations.
A maximal-coupling construction would be a valuable reusable mathematical lemma, particularly at
the measure-facing boundary; adding a postcondition monotonicity rule would not construct this
witness. The existing finite-type optimizer in [`OptimalCoupling.lean`][optimal] has a different
interface and does not directly replace the arbitrary-result-type construction.

The 105-line [`le_discreteGaussianSum`][gaussian] proves a sum/integral comparison by splitting at
`floor μ`, bounding two monotone tails, and paying for the missing unit interval. Most of its
steps correspond to those mathematical obligations. Extract the integer-sum split or unimodal
sum/integral estimate if another caller needs it; do not hide the entire argument behind a tactic.
The 74-line [`renyiDiv_prob_bound`][renyi] similarly contains a Hölder factorization with essential
zero/infinite-mass and exponent side conditions; it already uses generalized congruence where
monotonicity is the appropriate step.

HashSig's longest named theorem, the 73-line [`slhdsaConcreteAlg_components`][hashsig], is mostly
naturality and deterministic-handler specialization, with separate keygen/sign/verify components.
It is already substantially organized around the `QueryHom` API. A generic algorithm-map law
could reduce repeated specialization, but this is lower priority than the several hundred repeated
lines in the direct-coupling examples. No theorem in the scanned `ToMathlib` or `HashSig` slice
reaches 100 lines; this says nothing about the length of definitions or the difficulty of missing
security results.

## Original suggested order of work

| Priority | Bounded change | Evidence / limit |
|---|---|---|
| 1 | Share independent-draw rotation in the two tag proofs; retain the small `gcongr` cleanup. | Four 105-line blocks replaced in compiled copies. Largest verified reduction, with no invariant redesign. |
| 2 | Extract cache/log hit/miss preservation and cache-domain coverage laws. | One miss-preservation helper compiled at two callers; adjacent duplicated obligations identified. |
| 3 | Name joint observations in BR93 and the PRF reader/composition proofs. | Most of their length is semantic normalization and projection transport; proposed savings need a caller prototype. |
| 4 | Extract KEM–DEM game identities and composed-handler support/invariant facts. | Repeated game evaluation and state decomposition have clear interfaces, but semantic assumptions must remain explicit. |
| 5 | Factor fixed-width codec reconstruction and selected mathematical lemmas. | Strong reuse candidates; the deeper coupling/potential arguments should be extracted as mathematics, not hidden by search. |

Judge an extraction by the repeated reasoning it removes across callers, the assumptions it keeps
visible, and how readily a later proof can use its statement. Merely reducing the longest theorem's
line count by moving the same large context into single-use helpers is a weaker result.

## Initial audit validation and reproducibility

The following temporary modules were checked using `lake env lean -DautoImplicit=false` against built repository
imports: the generic draw-rotation helper; the two complete tag modules using it; the complete
positive-slot module with the separate `gcongr` cleanup; the cache/log helper; and the complete
adaptive-prefix and online-bound modules using that helper. All these successful variants compiled
without new holes or increased options. The direct `vcstep` experiment failed on the raw semantic
equality entry shape and was not retained as a proposed replacement.

The source census and experimental module copies are local analysis artifacts under
`/tmp/vcvio-long-proof-census.*` and `/tmp/vcvio-long-proofs/`. The CSV preserves the top 60 rows at
the audited revision. No production refactor, new global attribute, or repository-wide performance
claim is implied by these experiments. This document and its data are the deliverables; the earlier
full validation of the production branch is separate from the targeted checks performed here.

[positive]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/Examples/PRFTagReader/DirectCoupling/TagSlotPositive.lean#L59
[positive-tail]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/Examples/PRFTagReader/DirectCoupling/TagSlotPositive.lean#L954
[zero]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/Examples/PRFTagReader/DirectCoupling/TagSlotZero.lean#L56
[reader]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/Examples/PRFTagReader/DirectCoupling/ReaderCase.lean#L56
[swap]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/VCVio/EvalDist/Monad/Basic.lean#L869
[swap-bridge]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/Examples/PRFTagReader/DirectCoupling/Swap.lean#L385
[adaptive]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/VCVio/OracleComp/QueryTracking/AdaptivePrefix.lean#L140
[online]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/VCVio/CryptoFoundations/MerkleTree/MultiExtractability/OnlineBound.lean#L90
[br93]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/Examples/BR93.lean#L465
[compose]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/Examples/PRFTagReader/DirectCoupling/Compose.lean#L357
[eager]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/Examples/PRFTagReader/MultipleToHybrid/EagerSetup.lean#L506
[table]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/Examples/PRFTagReader/Table.lean#L520
[forge]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/Examples/PRFTagReader/Collision/ForgeStep.lean#L399
[kemdem]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/VCVio/CryptoFoundations/KEMDEM.lean#L143
[stateful]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/Chain.lean#L790
[duplication]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/docs/reading/internal-duplication.md#L14
[fischlin]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/VCVio/CryptoFoundations/Fischlin/KnowledgeSoundness.lean#L1453
[extraction]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/VCVio/CryptoFoundations/MerkleTree/ExtractionKernel.lean#L255
[encoding]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/LatticeCrypto/MLKEM/Concrete/Encoding.lean#L303
[coupling]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/VCVio/ProgramLogic/Relational/Quantitative.lean#L952
[optimal]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/ToMathlib/ProbabilityTheory/OptimalCoupling.lean#L323
[gaussian]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/LatticeCrypto/DiscreteGaussian.lean#L216
[renyi]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/ToMathlib/Probability/ProbabilityMassFunction/RenyiDivergence.lean#L259
[hashsig]: https://github.com/Verified-zkEVM/VCVio/blob/fb2b3a960df430454596ac9ee0aaf7b1f934762b/HashSig/SLHDSA/RandomOracle.lean#L96
