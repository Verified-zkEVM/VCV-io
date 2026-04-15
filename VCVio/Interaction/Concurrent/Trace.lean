/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Frontier

/-!
# Structural frontier traces

This file defines finite traces of the **structural** concurrent source syntax.

For sequential `Interaction.Spec`, a `Transcript` records one complete root-to-
leaf play through a tree whose next move family is always unique.

For concurrent `Interaction.Concurrent.Spec`, there may be multiple currently
enabled frontier events at once. A `Trace S` therefore records one **finite
scheduler linearization**:

* choose one frontier event of `S`;
* continue with the residual spec after that event;
* repeat until reaching a quiescent residual with no enabled frontier events.

So `Trace` is the finite interleaving-level linearization object associated to
the structural tree frontend. The dynamic concurrent execution API now lives
over `Concurrent.Process` in `Concurrent/Execution`.

If a later true-concurrency layer adds independence or partial-order
semantics, those refinements should be layered over these structural
linearizations rather than replacing the basic tree frontend story here.
-/

universe u

namespace Interaction
namespace Concurrent

/--
`Trace S` is a finite structural linearization trace of the concurrent spec
`S`.

It records one scheduler-chosen linearization of frontier events, ending when
the residual concurrent spec becomes quiescent, meaning its frontier type is
empty.

This should be read as the concurrent analogue of a sequential transcript, but
with one crucial difference:
the constructors record **frontier choices** rather than the moves of a
single always-current node.
-/
inductive Trace : Spec → Type (u + 1) where
  | /-- A finished trace of a quiescent concurrent spec with no enabled
    frontier events. This covers not only `.done` itself, but also dead
    residual shapes such as `.par .done .done`. -/
    done {S : Spec} (h : Front S → False) : Trace S
  | /-- Extend a trace by one frontier event and a trace of the residual spec
    that remains after performing that event. -/
    step {S : Spec} (event : Front S) : Trace (residual event) → Trace S

namespace Trace

/--
Construct the finished trace of a concurrent spec that is known to be
quiescent.
-/
def doneOfNotLive {S : Spec} (h : S.isLive = false) : Trace S :=
  .done (isEmpty_of_not_live h)

/-- The number of frontier events in a finite concurrent trace. -/
def length : {S : Spec} → Trace S → Nat
  | _, .done _ => 0
  | _, .step _ tail => tail.length.succ

@[simp, grind =]
theorem length_done {S : Spec} (h : Front S → False) :
    length (Trace.done h) = 0 := rfl

@[simp, grind =]
theorem length_step {S : Spec} (event : Front S) (tail : Trace (residual event)) :
    length (Trace.step event tail) = tail.length.succ := rfl

/-- A `step` contributes exactly one additional frontier event to the trace
length. -/
theorem length_step_eq_add_one {S : Spec} (event : Front S)
    (tail : Trace (residual event)) :
    length (Trace.step event tail) = tail.length + 1 := rfl

end Trace
end Concurrent
end Interaction
