/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.TVDist
public meta import Mathlib.Tactic.Positivity.Core

/-!
# Positivity of monadic total variation distance

The `positivity` extension for `tvDist` uses its public nonnegativity theorem. It composes
with arithmetic extensions and does not assert strict positivity or distinguishability.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Meta.Positivity

/-- Monadic total variation distance is nonnegative. -/
@[positivity tvDist _ _]
def evalTVDist : PositivityExt where
  eval {u α} _ pα? e :=
    match pα? with | none => pure .none | some _ => do
    match u, α, e with
    | 0, ~q(ℝ), ~q(@tvDist $m $inst $β $mx $my) =>
        assertInstancesCommute
        return .nonnegative q(@tvDist_nonneg $m $inst $β $mx $my)
    | _, _, _ => throwError "not a monadic total variation distance"

end Mathlib.Meta.Positivity
