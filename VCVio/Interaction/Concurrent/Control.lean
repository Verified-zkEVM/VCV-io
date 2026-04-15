/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Profile

/-!
# Scheduler and control ownership for concurrent interaction

This file adds an explicit control layer on top of the concurrent source syntax.

The key distinction is:

* at an atomic `node`, some party controls the **payload move** itself;
* at a parallel `par left right`, some party may control the **scheduling
  choice** of which currently live side fires next.

So a full frontier event may be controlled by several parties in sequence:
a scheduler may first choose a live branch of `par`, and then a downstream node
owner may choose the payload move of the selected atomic node.

The purpose of this file is to represent that control structure directly and
definitionally.

Main definitions:

* `Control Party S` — structural control metadata for the concurrent spec `S`;
* `Control.residual` — transport control metadata across one scheduled frontier
  event;
* `Control.isLive` — whether a control tree still exposes enabled frontier
  events;
* `Control.scheduler?` — the party who currently has a genuine scheduling
  choice between two live concurrent components, if any;
* `Control.current?` — the party who currently controls the next decision,
  whether that is a scheduler choice or an atomic payload choice;
* `Control.controllers` — the full control path of a concrete frontier event.

This is intentionally a control/ownership layer only.
It does **not** yet prescribe how those parties compute their choices or how
local endpoint programs should be assembled from that ownership data.
-/

universe u

namespace Interaction
namespace Concurrent

/--
`Control Party S` records who controls the next decision at each structural
position of the concurrent spec `S`.

Constructors mirror the concurrent syntax:

* `done` — there are no further decisions to control;
* `node owner cont` — at an atomic node, `owner` controls the move payload, and
  `cont x` records the residual control tree after choosing `x`;
* `par scheduler left right` — at a parallel node, `scheduler` controls the
  choice between the two concurrently live components `left` and `right`.

This is not a local-view or observation object. It records only control.
-/
inductive Control (Party : Type u) : Spec → Type (u + 1) where
  | /-- Control tree for a terminated concurrent spec. -/
    done : Control Party .done
  | /-- Control tree for an atomic node: `owner` controls the move payload,
    and the continuation records residual control after that move. -/
    node {Moves : Type u} {rest : Moves → Spec}
      (owner : Party)
      (cont : (x : Moves) → Control Party (rest x)) :
      Control Party (.node Moves rest)
  | /-- Control tree for a parallel spec: `scheduler` controls the choice of
    which live side fires next while both sides remain live. -/
    par {left right : Spec}
      (scheduler : Party)
      (leftControl : Control Party left)
      (rightControl : Control Party right) :
      Control Party (.par left right)

namespace Control

/--
`residual control event` is the control tree remaining after scheduling the
frontier event `event`.

This mirrors the residual concurrent spec structurally:
* atomic node control follows the chosen payload branch;
* parallel control updates only the side from which the event came.
-/
def residual {Party : Type u} :
    {S : Spec} → Control Party S → (event : Front S) → Control Party (Concurrent.residual event)
  | .done, .done, event => nomatch event
  | .node _ _, .node _ cont, .move x => cont x
  | .par _ _, .par scheduler leftControl rightControl, .left event =>
      .par scheduler (residual leftControl event) rightControl
  | .par _ _, .par scheduler leftControl rightControl, .right event =>
      .par scheduler leftControl (residual rightControl event)

/--
`isLive control` decides whether the control tree `control` still exposes any
enabled frontier event.

This is the control-side analogue of asking whether the indexed frontier type is
empty:
* `done` is not live;
* an atomic node is live;
* a parallel control tree is live iff either side is live.
-/
def isLive {Party : Type u} : {S : Spec} → Control Party S → Bool
  | .done, .done => false
  | .node _ _, .node _ _ => true
  | .par _ _, .par _ leftControl rightControl => leftControl.isLive || rightControl.isLive

/--
`scheduler? control` returns the party who currently has a genuine **scheduling
choice** between two live concurrent components.

This returns:
* `some scheduler` at a `par` node exactly when both sides are live;
* `none` otherwise.

So this records *frontier scheduling ownership*, not payload ownership.
-/
def scheduler? {Party : Type u} : {S : Spec} → Control Party S → Option Party
  | .done, .done => none
  | .node _ _, .node _ _ => none
  | .par _ _, .par scheduler leftControl rightControl =>
      match leftControl.isLive, rightControl.isLive with
      | true, true => some scheduler
      | _, _ => none

/--
`current? control` returns the party who currently controls the **next**
decision.

This may be:
* a scheduler at a `par` node when both sides are live;
* otherwise, the controlling party of the unique live side;
* or the owner of an atomic node.

So `current?` collapses scheduler choice and payload choice into the one party
who is currently in control of progress.
-/
def current? {Party : Type u} : {S : Spec} → Control Party S → Option Party
  | .done, .done => none
  | .node _ _, .node owner _ => some owner
  | .par _ _, .par scheduler leftControl rightControl =>
      match leftControl.isLive, rightControl.isLive with
      | true, true => some scheduler
      | true, false => current? leftControl
      | false, true => current? rightControl
      | false, false => none

/--
`controllers control event` is the full control path of the concrete frontier
event `event`.

For an atomic node, this is the singleton list containing the node owner.
For a parallel node:
* if the opposite side is also live, the scheduler is prepended;
* if the chosen side is the only live side, the scheduler does not appear,
  because there is no genuine scheduling choice to make.

This distinction matters after residual steps such as `.par .done right`,
where control should immediately collapse to the right subtree rather than
crediting a vacuous scheduler choice.
-/
def controllers {Party : Type u} :
    {S : Spec} → Control Party S → (event : Front S) → List Party
  | .done, .done, event => nomatch event
  | .node _ _, .node owner _, .move _ => [owner]
  | .par _ _, .par scheduler leftControl rightControl, .left event =>
      match rightControl.isLive with
      | true => scheduler :: controllers leftControl event
      | false => controllers leftControl event
  | .par _ _, .par scheduler leftControl rightControl, .right event =>
      match leftControl.isLive with
      | true => scheduler :: controllers rightControl event
      | false => controllers rightControl event

@[simp, grind =]
theorem isLive_done {Party : Type u} :
    isLive (Party := Party) Control.done = false := rfl

@[simp, grind =]
theorem isLive_node {Party : Type u} {Moves : Type u} {rest : Moves → Spec}
    (owner : Party) (cont : (x : Moves) → Control Party (rest x)) :
    isLive (Control.node owner cont) = true := rfl

@[simp, grind =]
theorem scheduler?_node {Party : Type u} {Moves : Type u} {rest : Moves → Spec}
    (owner : Party) (cont : (x : Moves) → Control Party (rest x)) :
    scheduler? (Control.node owner cont) = none := rfl

@[simp, grind =]
theorem current?_node {Party : Type u} {Moves : Type u} {rest : Moves → Spec}
    (owner : Party) (cont : (x : Moves) → Control Party (rest x)) :
    current? (Control.node owner cont) = some owner := rfl

@[simp, grind =]
theorem controllers_move {Party : Type u} {Moves : Type u} {rest : Moves → Spec}
    (owner : Party) (cont : (x : Moves) → Control Party (rest x)) (x : Moves) :
    controllers (Control.node owner cont) (.move x) = [owner] := rfl

end Control
end Concurrent
end Interaction
