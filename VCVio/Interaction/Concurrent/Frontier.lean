/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Spec

/-!
# Frontiers and residual concurrent interaction

This file gives the primary scheduler-facing execution view of
`Interaction.Concurrent.Spec`.

The foundational concurrent syntax is structural:
sequential nodes plus binary `par`.
For execution, the important questions are instead:

* what events are currently enabled?
* and what residual interaction remains after choosing one of them?

Those questions are answered by:

* `Front S` — the type of currently enabled frontier events of `S`;
* `residual` — the residual concurrent spec after one frontier event.

The definition of `Front` is intentionally an **inductive family**, not a
recursive alias into `PEmpty` and `Sum`. This keeps the scheduler-facing API
close to the source syntax and preserves direct pattern matching and
definitional computation for `residual`.
-/

universe u

namespace Interaction
namespace Concurrent

/--
`Front S` is the type of currently enabled frontier events of the concurrent
spec `S`.

Reading by cases:

* `Front .done` has no constructors, since no further events are enabled;
* `Front (.node X rest)` is a chosen move `x : X`;
* `Front (.par left right)` is an event from the left or right concurrent
  component.

The inductive-family presentation keeps the scheduler-facing interface
definitionally close to the structural source syntax.
-/
inductive Front : Spec → Type (u + 1) where
  | /-- A frontier event of an atomic node is simply one chosen move. -/
    move {Moves : Type u} {rest : Moves → Spec} (x : Moves) :
      Front (.node Moves rest)
  | /-- Lift a frontier event from the left component of a parallel spec. -/
    left {left right : Spec} (event : Front left) : Front (.par left right)
  | /-- Lift a frontier event from the right component of a parallel spec. -/
    right {left right : Spec} (event : Front right) : Front (.par left right)

/--
`residual event` is the residual concurrent spec after performing one frontier
event `event`.

The equations are definitionally the expected ones:

* a move at an atomic node continues with that node's continuation;
* a left frontier event updates only the left component of a parallel node;
* a right frontier event updates only the right component.

This is the primary execution primitive for schedulers, adversaries, and traces.
-/
def residual : {S : Spec} → Front S → Spec
  | .done, event => nomatch event
  | .node _ rest, .move x => rest x
  | .par _ right, .left event => .par (residual event) right
  | .par left _, .right event => .par left (residual event)

/--
If a concurrent spec is not live, then its frontier type is empty.

This packages the structural fact that `Spec.isLive` exactly decides whether a
concurrent spec still exposes enabled frontier events.
-/
theorem isEmpty_of_not_live : {S : Spec} → S.isLive = false → Front S → False
  | .done, _, event => nomatch event
  | .node _ _, h, _ => by cases h
  | .par left right, h, event => by
      match hLeft : left.isLive with
      | true =>
          match hRight : right.isLive with
          | true => simp [Spec.isLive, hLeft, hRight] at h
          | false => simp [Spec.isLive, hLeft, hRight] at h
      | false =>
          match hRight : right.isLive with
          | true => simp [Spec.isLive, hLeft, hRight] at h
          | false =>
              let leftEmpty : Front left → False := isEmpty_of_not_live hLeft
              let rightEmpty : Front right → False := isEmpty_of_not_live hRight
              exact match event with
              | .left event => leftEmpty event
              | .right event => rightEmpty event

@[simp, grind =]
theorem residual_move {Moves : Type u} {rest : Moves → Spec} (x : Moves) :
    residual (Front.move (rest := rest) x) = rest x := rfl

@[simp, grind =]
theorem residual_left {left right : Spec} (event : Front left) :
    residual (Front.left (right := right) event) = .par (residual event) right := rfl

@[simp, grind =]
theorem residual_right {left right : Spec} (event : Front right) :
    residual (Front.right (left := left) event) = .par left (residual event) := rfl

end Concurrent
end Interaction
