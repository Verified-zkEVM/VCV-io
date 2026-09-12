/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Allowed-query predicates and adaptive response paths

A handler that returns false avoids the forbidden second query. The structural predicate must
nevertheless reject the program, since a true response reaches that query. The zero-budget bridge
must count forbidden indices, rather than the allowed first query.
-/

public section

namespace VCVioTest.QueryBounds

open OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery

abbrev flagSpec : OracleSpec Bool := fun _ => Bool

/-- Query the forbidden index only when the first answer is true. -/
def adaptive : OracleComp flagSpec Bool := do
  let answer ← liftM (flagSpec.query true)
  if answer then liftM (flagSpec.query false) else pure false

/-- All response paths are checked, including the path not taken by the handler below. -/
example : ¬ AllQueriesSatisfy adaptive (· = true) := by
  simp [adaptive, allQueriesSatisfy_query_bind_iff]

/-- With only the allowed query, the budget for its complement is zero. -/
example : IsQueryBoundP (liftM (flagSpec.query true) : OracleComp flagSpec Bool)
    (fun t => ¬ t = true) 0 := by
  rw [isQueryBoundP_zero_iff]
  simp

/-- This deterministic run avoids the forbidden branch and records the answer it received. -/
example :
    (simulateQ (QueryImpl.withLogging (m := Id)
      ((fun _ => false) : QueryImpl flagSpec Id)) adaptive).run.run =
    (false, ([⟨true, false⟩] : QueryLog flagSpec)) := by
  simp [adaptive, show Id.run false = false from rfl]

end VCVioTest.QueryBounds
