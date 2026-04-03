# Query Runtime Follow-Ups

Temporary design/TODO note for the next wave after PR `#260`.

This note records the concrete follow-up surface we likely want, so we can resume the work
without re-deriving the conceptual split between:

- pathwise cost bounds,
- output-indexed cost descriptions (`CostsAs`),
- expected cost / expected query count.

## Current State

After `#260`, the generic `HasQuery` runtime/accounting layer now has:

- `QueryRuntime` as the explicit runtime bundle,
- pathwise query-cost bounds in
  [VCVio/OracleComp/QueryTracking/QueryRuntime.lean](../VCVio/OracleComp/QueryTracking/QueryRuntime.lean),
- readable theorem-facing notation such as `Queries[...]`, `QueryCost[...]`, and
  `ExpectedQueries[...]`,
- pathwise and expected query theorems for:
  - Fiat-Shamir,
  - T-transform,
  - Fischlin.

The older
[VCVio/OracleComp/QueryTracking/CostModel.lean](../VCVio/OracleComp/QueryTracking/CostModel.lean)
still provides the `OracleComp`-specific cost/expectation story. The main open question is how far
to unify that older layer with the generic `HasQuery`/`QueryRuntime` layer.

## Recommended Order

1. Weighted expected cost in `QueryRuntime`
2. A multi-oracle weighted example, likely `UTransform`
3. Expected-query bounds for aborting/search constructions
4. Bridge the `QueryRuntime` and `CostModel` stories
5. Fold the conceptual split into the permanent docs

## 1. Weighted Expected Cost

### Goal

Extend the current unit-cost `ExpectedQueries[...]` story to weighted expected cost.

The main user-facing gap is that we can currently say:

- `Queries[ oa in runtime ] = n`
- `Queries[ oa in runtime ] ≤ n`
- `ExpectedQueries[ oa in runtime ] ≤ n`

but we do not yet have the weighted expected analogue.

### Proposed Surface

Keep the current unit-cost notation, and add a weighted API first as definitions and theorems:

In
[VCVio/OracleComp/QueryTracking/QueryRuntime.lean](../VCVio/OracleComp/QueryTracking/QueryRuntime.lean):

```lean
noncomputable def HasQuery.expectedWeightedCost
    {ω : Type} [AddMonoid ω] [HasEvalSPMF m]
    (oa : Computation spec (AddWriterT ω m) α)
    (runtime : QueryRuntime spec m)
    (costFn : spec.Domain → ω)
    (val : ω → ENNReal) : ENNReal
```

and the bridge lemmas:

```lean
lemma HasQuery.expectedWeightedCost_le_of_usesCostAtMost ...
lemma HasQuery.expectedWeightedCost_ge_of_usesCostAtLeast ...
lemma HasQuery.expectedWeightedCost_eq_of_usesCostExactly ...
```

Then define the unit-cost theorem layer as specialization:

```lean
abbrev HasQuery.expectedQueries := ...
```

### Notation

The notation should probably come second, after the theorem layer settles.

The most likely stable notation is something like:

```lean
ExpectedQueryCost[ oa in runtime by costFn ; val ]
```

but this should only be added if the syntax remains pleasant in theorem statements. If the syntax
starts feeling too dense, a named def is preferable to a clever notation.

### Why This Matters

This gives the first fully generic way to say:

- “the expected number of hash queries is at most `q`,” and
- “the expected weighted runtime under cost model `costFn` is at most `B`,”

without requiring the construction itself to be written in concrete `OracleComp` syntax.

## 2. Multi-Oracle Weighted Example

### Candidate

The best next target is
[VCVio/CryptoFoundations/FujisakiOkamoto/UTransform.lean](../VCVio/CryptoFoundations/FujisakiOkamoto/UTransform.lean),
assuming it can be pushed into the same generic `HasQuery` style that `TTransform` now uses.

### Goal

Demonstrate that the framework handles:

- multiple oracle families,
- non-unit cost models,
- exact and upper-bound theorems in the same development.

### Proposed Slice

1. Generalize `UTransform` over `HasQuery` if it is still concrete.
2. Introduce a runtime and/or `costFn` that distinguishes query families.
3. Prove at least:
   - a unit-cost theorem,
   - a weighted theorem where different query families contribute differently.

### Theorem Shape

Depending on the final oracle spec, the public theorem layer should look like:

```lean
Queries[ (UTransform ...).encaps ... in runtime ] = 2
Queries[ (UTransform ...).decaps ... in runtime ] ≤ 2
```

and, more importantly, a weighted statement such as:

```lean
QueryCost[ (UTransform ...).encaps ... in runtime by costFn ] = w
```

or an expected weighted upper bound if the cost is branch-sensitive.

### Why This Matters

Right now the framework is strongest for “one oracle, one unit cost.” A multi-oracle weighted
example is the real test that the abstraction is not just a polished query counter.

## 3. Expected Bounds for Aborting/Search Constructions

### Candidate

[VCVio/CryptoFoundations/FiatShamirWithAbort.lean](../VCVio/CryptoFoundations/FiatShamirWithAbort.lean)

### Goal

Handle constructions where the number of oracle queries is not fixed, but still has:

- a pathwise upper bound,
- an expected upper bound,
- possibly later, a sharper expected bound from acceptance-probability lemmas.

### Minimum Useful Theorems

For verification:

```lean
Queries[ verify ... in runtime ] = 1
ExpectedQueries[ verify ... in runtime ] = 1
```

For signing:

```lean
Queries[ sign ... in runtime ] ≤ maxAttempts
ExpectedQueries[ sign ... in runtime ] ≤ maxAttempts
```

### Why This Matters

This is the first example where expectation genuinely adds information beyond worst-case query
bounds. It would show that the framework supports random stopping times, not just fixed-query
constructions.

## 4. Bridge to `CostModel`

### Goal

Make precise how the generic `QueryRuntime` expectation layer relates to the older
`OracleComp`-specific
[CostModel.lean](../VCVio/OracleComp/QueryTracking/CostModel.lean).

### Desired Result

When a construction is instantiated in the free/original oracle world, the two expected-cost
stories should agree.

Concretely, we want a theorem of the form:

```lean
HasQuery.expectedWeightedCost ... = CostModel.expectedCost ...
```

under the canonical free-runtime / free-semantics instantiation.

### Why This Matters

Without this bridge, the library risks growing two parallel cost stories:

- one for generic `HasQuery` constructions,
- one for concrete `OracleComp` computations.

That duplication is acceptable temporarily, but we should eventually prove they agree where both
apply.

## 5. Documentation Follow-Up

Once the API settles, the conceptual split should be written down permanently in:

- [docs/agents/oracle-comp.md](agents/oracle-comp.md)
- [docs/agents/probability.md](agents/probability.md)
- possibly a dedicated note if the cost layer keeps growing

The key explanation to preserve is:

- `CostsAs`: output determines cost,
- pathwise bounds: every execution path satisfies the bound,
- expected cost: expectation of the cost marginal.

That distinction is subtle enough that we should not rely on theorem names alone.

## Concrete Next PR Plan

If we want the smallest high-value next slice, it should be:

1. Add weighted expected cost to `QueryRuntime`
2. Add the weighted bridge lemmas from `UsesCost...`
3. Pick one multi-oracle example, ideally `UTransform`
4. Stop there before touching `FiatShamirWithAbort`

That gives a coherent next PR:

- one API extension,
- one compelling example,
- no need to solve the entire long-term complexity story in one go.
