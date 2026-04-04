# Query Tracking and Cost Semantics

This guide explains the query-tracking stack in `VCVio/OracleComp/QueryTracking/`.

The current design is intentionally **weighted-first**:

- `QueryCost[...]` and `ExpectedQueryCost[...]` are the primary notions.
- `Queries[...]` and `ExpectedQueries[...]` are the unit-cost specializations.

The stack is also intentionally split into:

- a generic `HasQuery` runtime layer
- a thin `OracleComp` facade
- a small `ToMathlib` probability layer for reusable tail-sum facts

## Main Files

| File | Role |
|------|------|
| `VCVio/OracleComp/QueryTracking/QueryRuntime.lean` | Generic query-cost accounting for `HasQuery` computations |
| `VCVio/OracleComp/QueryTracking/CostModel.lean` | `OracleComp`-specific facade over the generic semantics |
| `ToMathlib/Control/WriterT.lean` | Pathwise and output-indexed cost predicates for `AddWriterT` |
| `ToMathlib/Probability/ProbabilityMassFunction/TailSums.lean` | Generic PMF tail-sum identities used for expected runtime |

## Layering

### 1. `AddWriterT`: raw cost semantics

The semantic core is a writer monad whose log records cost.

At this level, the key notions are:

- `AddWriterT.PathwiseCostAtMost`
- `AddWriterT.PathwiseCostAtLeast`
- `Cost[ oa ] = w`
- `Cost[ oa ] ≤ w`
- `Cost[ oa ] ≥ w`

These are **pathwise** statements: they talk about every reachable execution path.

This file also defines the stronger, output-indexed notion:

- `AddWriterT.CostsAs oa f`

This means:

- the cost of `oa` is completely determined by its output
- there is a function `f` such that every reachable run producing `a` has cost `f a`

That is stronger than a pathwise bound. It is useful when exact cost is determined by the final
result, but it is not the default semantic notion.

### 2. `QueryRuntime`: generic `HasQuery` accounting

`QueryRuntime spec m` packages a concrete runtime for a generic `HasQuery spec m` world.

This layer interprets generic constructions in:

- the base monad `m`
- the instrumented monad `AddWriterT ω m`

and exposes the public API:

- exact weighted cost:
  `QueryCost[ oa in runtime by costFn ] = w`
- weighted upper/lower bounds:
  `QueryCost[ oa in runtime by costFn ] ≤ w`
  `QueryCost[ oa in runtime by costFn ] ≥ w`
- exact / bounded unit-cost query counting:
  `Queries[ oa in runtime ] = n`
  `Queries[ oa in runtime ] ≤ n`
  `Queries[ oa in runtime ] ≥ n`
- expected weighted cost:
  `ExpectedQueryCost[ oa in runtime by costFn via val ]`
- expected unit-cost query count:
  `ExpectedQueries[ oa in runtime ]`

The intended reading is:

- `QueryCost[...]` is the general notion
- `Queries[...]` means the same thing with `costFn := fun _ ↦ 1`

### 3. `CostModel`: `OracleComp` facade

`CostModel.lean` should be read as a free-`OracleComp` view of the same semantics, not as a
second independent cost semantics.

The important design point is:

- `QueryRuntime` and `AddWriterT` are the semantic core
- `CostModel` is now a thin facade for `OracleComp`-specific theorems and asymptotic packaging

Use `CostModel` when you want:

- the free-oracle viewpoint
- `OracleComp`-specific reductions
- the older asymptotic query-cost packaging

Use `QueryRuntime` when you want:

- a generic theorem over any `HasQuery` construction
- runtime-instantiated cryptographic constructions
- weighted expected cost and expected query count

### 4. `ToMathlib`: generic probability facts

Expected-cost proofs should avoid hard-coding query semantics when the real theorem is purely
probabilistic.

`ToMathlib/Probability/ProbabilityMassFunction/TailSums.lean` contains the generic discrete
tail-sum identities used by the query-runtime layer:

- `E[T] = ∑ Pr[i < T]`
- tail domination implies expectation domination

This keeps the query-runtime layer small and makes the stopping-time machinery more plausibly
upstreamable.

## Three Cost Notions

There are three distinct notions in the current API.

### Pathwise cost

Use this when the statement is about **all runs**.

Examples:

- encryption uses at most one query
- decryption uses at least zero queries
- signing uses at most `ρ * |Ω|` queries

This is the natural meaning of:

- `QueryCost[...] ≤ w`
- `Queries[...] ≤ n`

### Output-indexed cost

Use this when cost is determined by the final output.

Examples:

- a single Fiat-Shamir signing attempt queries exactly the returned commitment
- a verification procedure always makes a fixed number of queries determined by its output shape

This is expressed by:

- `UsesCostAs`
- `CostsAs`

and is mainly useful as a bridge to exact expected-cost formulas.

### Expected cost

Use this when cost is random and pathwise exact equalities are not the right public theorem.

Examples:

- Fischlin signing has expected query count at most `ρ * |Ω|`
- Fiat-Shamir-with-aborts signing has expected query count equal to a tail sum

This is expressed by:

- `ExpectedQueryCost[...]`
- `ExpectedQueries[...]`

## When To Prove Which Theorem

### Prove exact pathwise cost

Use an exact pathwise theorem when every run really has the same cost.

Examples:

- `FiatShamir.verify` uses exactly one query
- `TTransform.encrypt` uses exactly one query
- `Fischlin.verify` uses exactly `ρ` queries

### Prove `UsesCostAs`

Use `UsesCostAs` when cost is a function of the output, and you want an expectation theorem of the
form “expected cost is the expectation of `val ∘ f` over outputs.”

Example:

- one `FiatShamirWithAbort` signing attempt

Do **not** force this notion onto retry loops or search procedures whose cost is not determined by
the final output.

### Prove a pathwise upper bound

Use a pathwise upper bound when branching or retrying changes the cost across runs.

Examples:

- `TTransform.decrypt` uses at most one query
- `FiatShamirWithAbort.sign` uses at most `maxAttempts` queries
- Fischlin signing uses at most `ρ * |Ω|` queries

These are the right first theorems for search loops, aborting schemes, and stopping-time style
computations.

### Prove expectation via a bridge

After a pathwise bound or a `UsesCostAs` theorem is in place, derive expectation theorems using the
generic bridge lemmas in `QueryRuntime.lean`.

There are two main patterns:

- `UsesCostAs` gives an exact output-expectation formula
- pathwise bounds give expectation upper/lower bounds

For natural-valued costs, the tail-sum lemmas give sharper expectation theorems.

## Notation Guide

### Weighted cost

```lean
QueryCost[ oa in runtime by costFn ] = w
QueryCost[ oa in runtime by costFn ] ≤ w
QueryCost[ oa in runtime by costFn ] ≥ w
```

### Unit-cost query counting

```lean
Queries[ oa in runtime ] = n
Queries[ oa in runtime ] ≤ n
Queries[ oa in runtime ] ≥ n
```

These are just the weighted statements specialized to `fun _ ↦ 1`.

### Expected weighted cost

```lean
ExpectedQueryCost[ oa in runtime by costFn via val ]
```

The `val` parameter interprets the weighted cost in `ENNReal`. For unit-count expectations, use:

```lean
ExpectedQueries[ oa in runtime ]
```

## Worked Examples

### Fiat-Shamir

See `VCVio/CryptoFoundations/FiatShamir.lean`.

This is the clean “exact one query” example.

- signing and verification support exact unit-cost statements
- the single-query cost is also a good example of `UsesCostAs`

### Fischlin

See `VCVio/CryptoFoundations/Fischlin.lean`.

This is the first substantial bounded-cost example.

- verification uses exactly `ρ` queries
- signing uses at most `ρ * |Ω|`
- the weighted theorem layer generalizes the unit-cost one

This file is the best reference for:

- weighted pathwise upper bounds
- expected weighted cost from pathwise bounds

### T-transform and U-transform

See:

- `VCVio/CryptoFoundations/FujisakiOkamoto/TTransform.lean`
- `VCVio/CryptoFoundations/FujisakiOkamoto/UTransform.lean`

These illustrate:

- exact cost theorems for simple FO-style constructions
- upper bounds for branch-sensitive decryption
- weighted multi-query accounting

### Fiat-Shamir with aborts

See `VCVio/CryptoFoundations/FiatShamirWithAbort.lean`.

This is the main stopping-time example.

The key progression is:

1. one attempt has output-determined cost
2. the full retry loop has only a pathwise upper bound
3. expected query count is expressed by a tail sum
4. the tail sum is rewritten semantically in terms of abort-prefix probabilities
5. geometric upper bounds follow from bounds on the one-step abort probability

This is the main reference for:

- tail-sum expectation theorems
- stopping-time style query bounds

## Typeclass Hygiene

The query-tracking files now try to keep theorem signatures narrow.

Preferred pattern:

- put only genuinely shared assumptions in section variable blocks
- localize `HasEvalSet`, `HasEvalSPMF`, `HasEvalPMF`, and `LawfulMonad` to the smallest section or
  theorem that needs them
- if a proof needs extra decidability or classical choice, install it locally with `classical` or
  a local instance

Avoid:

- wide sections followed by repeated `omit ... in`
- theorem statements carrying large blocks of unused typeclass assumptions

## Implementation Pattern

When adding a new example or construction:

1. Prove the pathwise exact/bounded theorem first.
2. If cost is output-determined, add a `UsesCostAs` theorem.
3. Derive expected-cost theorems from those generic bridges.
4. If the cost is natural-valued and behaves like a stopping time, look for a tail-sum theorem
   rather than forcing a coarse worst-case expectation bound.

This keeps the theorem layer mathematically honest and makes the public API easier to read.
