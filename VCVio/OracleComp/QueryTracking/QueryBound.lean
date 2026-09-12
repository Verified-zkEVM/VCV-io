/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Bounding Queries Made by a Computation

This file defines a predicate `IsQueryBound oa budget canQuery cost` parameterized by:
- `B` — the budget type
- `budget : B` — the initial budget
- `canQuery : ι → B → Prop` — whether a query to oracle `t` is allowed under budget `b`
- `cost : ι → B → B` — how the budget is updated after a query to oracle `t`

The definition is structural via `OracleComp.construct`: `pure` satisfies any bound, and
`query t >>= mx` satisfies the bound when `canQuery t b` holds and each continuation
satisfies the bound with the updated budget `cost t b`.

The classical per-index and total query bounds are recovered by `IsPerIndexQueryBound`
and `IsTotalQueryBound`. `IsQueryBoundP` counts queries satisfying a predicate;
`AllQueriesSatisfy` constrains the allowed indices without counting queries.
-/
