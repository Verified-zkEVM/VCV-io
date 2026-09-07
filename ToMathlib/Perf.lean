/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import Lean.Elab.InfoTree.Types
public import Std.Data.HashSet.Lemmas

/-!
# Performance Prototypes for Metaprograms

Explicit, side-effect-free alternatives for measuring shared metaprogram operations.
Importing this module does not install callbacks or change any linter, tactic, or instance.
The goal-difference operation preserves input order and multiplicity while indexing the
comparison list once. Its reference equation supports differential performance tests.
-/

public meta section

namespace ToMathlib.Perf

/-- Goals from `left` whose names do not occur in `right`, preserving order and duplicates. -/
def goalDifference (left right : List Lean.MVarId) : List Lean.MVarId :=
  let names := Std.HashSet.ofList (right.map (·.name))
  left.filter fun goal => !names.contains goal.name

/-- The indexed implementation agrees with a list-membership filter. -/
theorem goalDifference_eq (left right : List Lean.MVarId) :
    goalDifference left right =
      left.filter (fun goal => !(right.map (·.name)).contains goal.name) := by
  simp only [goalDifference, Std.HashSet.contains_ofList]

/-- Goals removed by a tactic, according to its before/after goal identifiers. -/
def goalsTargetedBy (info : Lean.Elab.TacticInfo) : List Lean.MVarId :=
  goalDifference info.goalsBefore info.goalsAfter

/-- Goals created by a tactic, according to its before/after goal identifiers. -/
def goalsCreatedBy (info : Lean.Elab.TacticInfo) : List Lean.MVarId :=
  goalDifference info.goalsAfter info.goalsBefore

end ToMathlib.Perf
