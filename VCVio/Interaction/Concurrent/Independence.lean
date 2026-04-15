/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Current

/-!
# Independence and commuting concurrent events

This file adds the first true-concurrency refinement to the structural
concurrent syntax.

The source syntax `Concurrent.Spec` and its frontier semantics still admit an
interleaving reading: when several frontier events are enabled, a scheduler may
pick one and continue with the residual spec.

To recover a more genuinely concurrent perspective, we also want to identify
frontier events that come from independent concurrent components and therefore
commute. This file does that in the most structural way possible.

Main definitions:

* `Independent event₁ event₂` says that two frontier events of the same
  concurrent spec arise from distinct concurrently live components;
* `afterLeft h` and `afterRight h` transport the other event across one chosen
  independent event;
* `diamond h` is the commuting residual law: independent events yield the same
  residual spec regardless of which one is scheduled first.

This is intentionally the minimal true-concurrency layer.
It does not yet quotient traces by independence, attach fairness assumptions,
or introduce richer partial-order objects such as pomsets or event structures.
-/

universe u

namespace Interaction
namespace Concurrent

/--
`Independent event₁ event₂` says that the frontier events `event₁` and
`event₂` of the same concurrent spec come from genuinely independent concurrent
components.

Reading by constructors:

* `left_right` and `right_left` express that one event comes from the left
  branch of a parallel spec and the other from the right branch;
* `left` and `right` propagate independence recursively inside the left or
  right concurrent component of a larger parallel spec.

There is intentionally no constructor for two events of the same atomic node:
different payload moves of one `node` are alternative choices, not independent
concurrent events.
-/
inductive Independent : {S : Spec} → Front S → Front S → Type (u + 1) where
  | /-- Frontier events from opposite sides of the same parallel node are
    independent. -/
    left_right {left right : Spec} (eventLeft : Front left) (eventRight : Front right) :
      Independent (Front.left (right := right) eventLeft) (Front.right (left := left) eventRight)
  | /-- Independence is symmetric across the two sides of a parallel node. -/
    right_left {left right : Spec} (eventRight : Front right) (eventLeft : Front left) :
      Independent (Front.right (left := left) eventRight) (Front.left (right := right) eventLeft)
  | /-- Independence inside a left concurrent component lifts to the whole
    parallel spec. -/
    left {left right : Spec} {event₁ event₂ : Front left}
      (h : Independent event₁ event₂) :
      Independent (Front.left (right := right) event₁) (Front.left (right := right) event₂)
  | /-- Independence inside a right concurrent component lifts to the whole
    parallel spec. -/
    right {left right : Spec} {event₁ event₂ : Front right}
      (h : Independent event₁ event₂) :
      Independent (Front.right (left := left) event₁) (Front.right (left := left) event₂)

namespace Independent

/--
Independence is symmetric.

If `event₁` is independent of `event₂`, then `event₂` is independent of
`event₁`.
-/
def symm {S : Spec} {event₁ event₂ : Front S} :
    Independent event₁ event₂ → Independent event₂ event₁
  | .left_right eventLeft eventRight => .right_left eventRight eventLeft
  | .right_left eventRight eventLeft => .left_right eventLeft eventRight
  | .left h => .left (symm h)
  | .right h => .right (symm h)

/--
`afterLeft h` is the residual form of the second event after first scheduling
the left-hand event of the independence witness `h`.

So if `h : Independent event₁ event₂`, then `afterLeft h` is an enabled
frontier event of the residual spec `residual event₁`.
-/
def afterLeft {S : Spec} {event₁ event₂ : Front S} :
    Independent event₁ event₂ → Front (residual event₁)
  | .left_right _ eventRight => .right eventRight
  | .right_left _ eventLeft => .left eventLeft
  | .left h => .left (afterLeft h)
  | .right h => .right (afterLeft h)

/--
`afterRight h` is the residual form of the first event after first scheduling
the right-hand event of the independence witness `h`.

So if `h : Independent event₁ event₂`, then `afterRight h` is an enabled
frontier event of the residual spec `residual event₂`.
-/
def afterRight {S : Spec} {event₁ event₂ : Front S} :
    Independent event₁ event₂ → Front (residual event₂)
  | .left_right eventLeft _ => .left eventLeft
  | .right_left eventRight _ => .right eventRight
  | .left h => .left (afterRight h)
  | .right h => .right (afterRight h)

/--
Independent frontier events commute at the level of residual concurrent specs.

If `event₁` and `event₂` are independent, then performing `event₁` first and
then the transported `event₂` yields the same residual spec as performing
`event₂` first and then the transported `event₁`.
-/
theorem diamond :
    {S : Spec} → {event₁ event₂ : Front S} →
      (h : Independent event₁ event₂) →
      residual (afterLeft h) = residual (afterRight h)
  | .par _ _, .left _, .right _, .left_right _ _ => rfl
  | .par _ _, .right _, .left _, .right_left _ _ => rfl
  | .par _ rightSpec, .left _event₁, .left _event₂, .left h =>
      by
        simpa [afterLeft, afterRight, residual] using
          congrArg (fun s => Spec.par s rightSpec) (diamond h)
  | .par leftSpec _, .right _event₁, .right _event₂, .right h =>
      by
        simpa [afterLeft, afterRight, residual] using
          congrArg (fun s => Spec.par leftSpec s) (diamond h)

end Independent
end Concurrent
end Interaction
