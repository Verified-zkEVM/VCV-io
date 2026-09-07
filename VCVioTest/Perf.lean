/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import ToMathlib.Perf

/-! # Regression Tests for Indexed Goal Differences -/

public meta section

open ToMathlib.Perf

private def goal (n : Nat) : Lean.MVarId := ⟨Lean.Name.num `goal n⟩

example : goalDifference [] [goal 1] = [] := by
  rw [goalDifference_eq]; simp [goal]

example : goalDifference [goal 1, goal 2] [] = [goal 1, goal 2] := by
  rw [goalDifference_eq]; simp [goal]

example : goalDifference [goal 1, goal 2] [goal 2, goal 1] = [] := by
  rw [goalDifference_eq]; simp [goal]

example : goalDifference [goal 3, goal 1, goal 3, goal 2] [goal 1, goal 1] =
    [goal 3, goal 3, goal 2] := by
  rw [goalDifference_eq]; simp [goal]

example : goalDifference [goal 1, goal 2] [goal 3, goal 4] = [goal 1, goal 2] := by
  rw [goalDifference_eq]; simp [goal]
