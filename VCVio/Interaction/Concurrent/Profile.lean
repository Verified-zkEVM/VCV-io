/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Trace
import VCVio.Interaction.Multiparty.Core

/-!
# Per-party observation profiles for concurrent interaction

This file adds the first multiparty-facing layer on top of the minimal
concurrent core.

The concurrent source syntax says only which residual subprotocols are live.
To speak about distributed or adversarial semantics, we also need to describe
what each party can observe when a frontier event is scheduled.

The design here stays structural and continuation-based:

* `Profile Party S` recursively attaches a `Multiparty.LocalView` to every
  atomic node of the concurrent spec `S`;
* `Profile.residual` transports such a profile across one scheduled frontier
  event;
* `Profile.ObsType me profile` computes the type of observations available to
  a fixed party `me` for the *current* frontier of `profile`;
* `Profile.observe me profile event` computes the actual observation exposed by
  a concrete frontier event `event`;
* `Profile.frontierView me profile` packages the whole current frontier as a
  single `Multiparty.LocalView`.

This is intentionally only an observation/profile layer.
It does **not** yet introduce:

* a full concurrent local endpoint semantics;
* explicit scheduler ownership;
* fairness conditions;
* or true-concurrency refinements.

Those later layers can build on this structural profile API.
-/

universe u

namespace Interaction
namespace Concurrent

/--
`Profile Party S` is a structural per-party local-view assignment for the
concurrent spec `S`.

Constructors mirror the concurrent syntax itself:

* `done` — no further metadata is needed for a terminated concurrent spec;
* `node views cont` — for an atomic node, each party is assigned a local view
  of the move type, together with continuation profiles for each residual
  branch;
* `par leftProfile rightProfile` — a parallel spec carries one profile for each
  concurrently live component.

This is the concurrent analogue of decorating every node of a sequential spec,
but phrased directly over the structural concurrent syntax.
-/
inductive Profile (Party : Type u) : Spec → Type (u + 1) where
  | /-- Profile of a terminated concurrent spec. -/
    done : Profile Party .done
  | /-- Profile of an atomic node: each party gets a local view of the move
    type, and the continuation records residual profiles for each chosen move. -/
    node {Moves : Type u} {rest : Moves → Spec}
      (views : Party → Multiparty.LocalView Moves)
      (cont : (x : Moves) → Profile Party (rest x)) :
      Profile Party (.node Moves rest)
  | /-- Profile of a parallel concurrent spec. -/
    par {left right : Spec}
      (leftProfile : Profile Party left)
      (rightProfile : Profile Party right) :
      Profile Party (.par left right)

namespace Profile

/--
`residual profile event` is the profile that remains after scheduling the
frontier event `event`.

This mirrors `Concurrent.residual` structurally:
* at an atomic node, follow the continuation profile for the chosen move;
* at a parallel node, update only the side from which the event came.
-/
def residual {Party : Type u} :
    {S : Spec} → Profile Party S → (event : Front S) → Profile Party (Concurrent.residual event)
  | .done, .done, event => nomatch event
  | .node _ _, .node _ cont, .move x => cont x
  | .par _ _, .par leftProfile rightProfile, .left event =>
      .par (residual leftProfile event) rightProfile
  | .par _ _, .par leftProfile rightProfile, .right event =>
      .par leftProfile (residual rightProfile event)

/--
`ObsType me profile` is the type of observations available to the fixed party
`me` at the *current* frontier of `profile`.

At an atomic node, this is exactly the observation type of `me`'s local view at
that node.
At a parallel node, current observations are a sum: a scheduled frontier event
comes from the left or the right component, and the observation records which
side fired together with the observation from that side.
-/
def ObsType {Party : Type u} (me : Party) :
    {S : Spec} → Profile Party S → Type u
  | .done, .done => PUnit
  | .node _ _, .node views _ => (views me).ObsType
  | .par _ _, .par leftProfile rightProfile =>
      Sum (ObsType me leftProfile) (ObsType me rightProfile)

/--
`observe me profile event` is the concrete observation exposed to the fixed
party `me` by the scheduled frontier event `event`.

This is computed structurally:
* at an atomic node, use the underlying `Multiparty.LocalView.obsOf`;
* at a parallel node, tag observations by whether the event came from the left
  or right concurrent component.
-/
def observe {Party : Type u} (me : Party) :
    {S : Spec} → (profile : Profile Party S) → (event : Front S) → ObsType me profile
  | .done, .done, event => nomatch event
  | .node _ _, .node views _, .move x => (views me).obsOf x
  | .par _ _, .par leftProfile _, .left event => .inl (observe me leftProfile event)
  | .par _ _, .par _ rightProfile, .right event => .inr (observe me rightProfile event)

/--
`frontierView me profile` packages the entire current frontier of `profile`
into a single `Multiparty.LocalView`.

This is useful when one wants to treat the current scheduled frontier event as a
single global move:
* atomic nodes reuse the party's underlying atomic local view, with `active`
  collapsing to `observe` because the scheduled frontier event itself is already
  fixed;
* parallel nodes expose a quotient view whose observations are exactly
  `ObsType me profile`.

So `frontierView` is an observation-level concurrent local view, not yet a full
local process semantics for the participant.
-/
def frontierView {Party : Type u} (me : Party) :
    {S : Spec} → (profile : Profile Party S) → Multiparty.LocalView (Front S)
  | .done, .done => .hidden
  | .node _ _, .node views _ =>
      match views me with
      | .active => .observe
      | .observe => .observe
      | .hidden => .hidden
      | .quotient Obs toObs =>
          .quotient (PLift Obs) (fun
            | .move x => ⟨toObs x⟩)
  | .par _ _, profile => .quotient (PLift (ObsType me profile)) (fun e => ⟨observe me profile e⟩)

end Profile
end Concurrent
end Interaction
