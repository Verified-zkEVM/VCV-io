/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Control

/-!
# Current local views of concurrent frontier events

This file combines the two structural concurrent layers:

* `Concurrent.Control`, which records who currently controls scheduling and
  payload choices;
* `Concurrent.Profile`, which records what each party can locally observe from
  concrete frontier events.

From those ingredients, it computes the **current local view** of the next
frontier event for a fixed party.

This is the key conceptual bridge:

* if the fixed party currently controls the next decision, its current local
  view is `active`;
* otherwise, its current local view is the observation view induced by the
  current frontier profile.

At a `par` node, this means:
* when both sides are live, the scheduler's local view is `active` on the full
  frontier event type `Front S`;
* when only one side remains live, control collapses to that side's own current
  controller and local view.

So this file gives the first true "who chooses what next, and what does everyone
else learn?" interface for the concurrent layer.
-/

universe u

namespace Interaction
namespace Concurrent
namespace Current

/-- The party currently controlling the next decision in the concurrent control
tree. This is just `Control.current?`, re-exported here because the present
module treats `Control` and `Profile` together as the current-step interface. -/
abbrev controller? {Party : Type u} {S : Spec} (control : Control Party S) : Option Party :=
  Control.current? control

/-- The party currently controlling a genuine scheduling choice between two live
concurrent components, when such a choice exists. This is just
`Control.scheduler?`, re-exported here for the combined current-step interface. -/
abbrev scheduler? {Party : Type u} {S : Spec} (control : Control Party S) : Option Party :=
  Control.scheduler? control

/--
If a concurrent control tree is not live, then its frontier type is empty.

This packages the fact that `Control.isLive` is the control-side decision
procedure for whether a concurrent spec still exposes any enabled frontier
event.
-/
private theorem frontIsEmptyOfNotLive {Party : Type u} :
    {S : Spec} → (control : Control Party S) → control.isLive = false → IsEmpty (Front S)
  | .done, .done, _ => ⟨fun event => nomatch event⟩
  | .node _ _, .node _ _, h => by cases h
  | .par _ _, .par _ leftControl rightControl, h => by
      match hLeft : leftControl.isLive with
      | true =>
          match hRight : rightControl.isLive with
          | true => simp [Control.isLive, hLeft, hRight] at h
          | false => simp [Control.isLive, hLeft, hRight] at h
      | false =>
          match hRight : rightControl.isLive with
          | true => simp [Control.isLive, hLeft, hRight] at h
          | false =>
              let leftEmpty : IsEmpty (Front _) := frontIsEmptyOfNotLive leftControl hLeft
              let rightEmpty : IsEmpty (Front _) := frontIsEmptyOfNotLive rightControl hRight
              exact ⟨fun
                | .left event => leftEmpty.false event
                | .right event => rightEmpty.false event⟩

/--
Lift a local view on the left frontier into the full frontier of a parallel
spec whose right side is known to have no enabled events.

This preserves the meaning of the local view while avoiding a spurious right
branch tag in the observation when the right side is dead.
-/
private def liftLeftView {left right : Spec} (rightEmpty : IsEmpty (Front right)) :
    Multiparty.LocalView (Front left) → Multiparty.LocalView (Front (.par left right))
  | .active => .active
  | .observe => .observe
  | .hidden => .hidden
  | .quotient Obs toObs =>
      .quotient Obs (fun
        | .left event => toObs event
        | .right event => False.elim (rightEmpty.false event))

/--
Lift a local view on the right frontier into the full frontier of a parallel
spec whose left side is known to have no enabled events.

This preserves the meaning of the local view while avoiding a spurious left
branch tag in the observation when the left side is dead.
-/
private def liftRightView {left right : Spec} (leftEmpty : IsEmpty (Front left)) :
    Multiparty.LocalView (Front right) → Multiparty.LocalView (Front (.par left right))
  | .active => .active
  | .observe => .observe
  | .hidden => .hidden
  | .quotient Obs toObs =>
      .quotient Obs (fun
        | .left event => False.elim (leftEmpty.false event)
        | .right event => toObs event)

/--
`view me control profile` is the current local view of the next frontier event
for the fixed party `me`.

It is computed from both control and observation structure:

* at an atomic node, the owner recorded by `control` gets `active`, while every
  other party gets the frontier observation induced by `profile`;
* at a parallel node with two live sides, the scheduler recorded by `control`
  gets `active` on the full frontier event type, while every other party gets
  the profile-induced frontier observation;
* at a parallel node with exactly one live side, control collapses to that
  side's current local view and is then lifted back to the full frontier type
  without introducing a spurious branch tag from the dead side;
* at `done`, everyone is `hidden`.

This is the fundamental current-step local interface for the concurrent layer.
-/
def view {Party : Type u} [DecidableEq Party] (me : Party) :
    {S : Spec} → Control Party S → Profile Party S → Multiparty.LocalView (Front S)
  | .done, .done, .done => .hidden
  | .node _ _, .node owner _, profile =>
      if me = owner then .active else Profile.frontierView me profile
  | .par left right, .par scheduler leftControl rightControl,
      profile@(.par leftProfile rightProfile) =>
      match hLeft : leftControl.isLive with
      | true =>
          match hRight : rightControl.isLive with
          | true =>
              if me = scheduler then .active else Profile.frontierView me profile
          | false =>
              let rightEmpty : IsEmpty (Front right) := frontIsEmptyOfNotLive rightControl hRight
              liftLeftView rightEmpty (view me leftControl leftProfile)
      | false =>
          match rightControl.isLive with
          | true =>
              let leftEmpty : IsEmpty (Front left) := frontIsEmptyOfNotLive leftControl hLeft
              liftRightView leftEmpty (view me rightControl rightProfile)
          | false => .hidden

/--
`ObsType me control profile` is the type of the current local observation
available to the fixed party `me` for the next frontier event.

This is just the observation type of `Current.view me control profile`.
-/
abbrev ObsType {Party : Type u} [DecidableEq Party] (me : Party)
    {S : Spec} (control : Control Party S) (profile : Profile Party S) : Type (u + 1) :=
  (view me control profile).ObsType

/--
`observe me control profile event` is the current local observation exposed to
the fixed party `me` by the concrete frontier event `event`.

If `me` is currently the active controller, this returns the full frontier event
itself. Otherwise, it returns the profile-induced observation of that frontier
event.
-/
def observe {Party : Type u} [DecidableEq Party] (me : Party) :
    {S : Spec} → (control : Control Party S) → (profile : Profile Party S) →
      (event : Front S) → ObsType me control profile
  | _, control, profile, event => (view me control profile).obsOf event

/--
`residualView me control profile event` is the current local view of the fixed
party `me` after scheduling the frontier event `event`.

This is defined by first transporting both control and profile through the
event, then recomputing the current local view of the residual concurrent
interaction.
-/
def residualView {Party : Type u} [DecidableEq Party] (me : Party) :
    {S : Spec} → (control : Control Party S) → (profile : Profile Party S) →
      (event : Front S) → Multiparty.LocalView (Front (Concurrent.residual event))
  | _, control, profile, event =>
      view me (Control.residual control event) (Profile.residual profile event)

end Current
end Concurrent
end Interaction
