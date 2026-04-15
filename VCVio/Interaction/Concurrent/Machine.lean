/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Process
import ToMathlib.Control.Coalgebra

/-!
# State-indexed concurrent machines

This file provides the flat, transition-system presentation of the concurrent
interaction framework.

The semantic center of the library is `Concurrent.Process`: a residual process
state exposes one sequential interaction step, and completing that step yields
the next residual state. That continuation-based view is convenient when the
shape of the current interaction matters.

Many protocol designers, however, start from a more operational picture:

* there is an explicit global state `σ`,
* a family `Enabled σ` of events that may happen next, and
* a function describing the successor state after such an event.

`Machine` packages exactly that presentation. It is intentionally small, and
then layered enrichments add stable event labels, fairness tickets, and system
predicates. The key bridge is `Machine.toProcess`, which interprets each
enabled event set as a one-node sequential step and thereby embeds machine
semantics into the general `Concurrent.Process` core.

This is the natural frontend for transition-system style models, including
state-heavy distributed and cryptographic protocol semantics.
-/

universe u v

namespace Interaction
namespace Concurrent

/--
`Machine` is the minimal state-indexed presentation of a concurrent system.

At any residual state `σ`, the type `Enabled σ` describes the events that may
occur next, and `step σ e` records the successor state produced by choosing the
enabled event `e`.

This record intentionally contains only dynamics. Event labels, fairness
tickets, controller ownership, local views, and verification predicates are all
added in separate layers so that the core transition semantics stays small and
reusable.
-/
structure Machine where
  State : Type v
  Enabled : State → Type u
  step : (σ : State) → Enabled σ → State

namespace Machine

/-- The step functor for `Machine`: at a state, the machine exposes an event type `E`
together with a successor-state function `E → S`. -/
def StepFun : Type v → Type (max (u + 1) v) := fun S => Σ (E : Type u), (E → S)

instance : Functor Machine.StepFun.{u, v} where
  map f := fun ⟨E, g⟩ => ⟨E, f ∘ g⟩

instance : LawfulFunctor Machine.StepFun.{u, v} where
  id_map := fun ⟨_, _⟩ => rfl
  comp_map := fun _ _ ⟨_, _⟩ => rfl
  map_const := rfl

/-- Every `Machine` is an F-coalgebra for `Machine.StepFun`. -/
instance (m : Machine.{u, v}) : Coalg Machine.StepFun m.State :=
  ⟨fun σ => ⟨m.Enabled σ, m.step σ⟩⟩

/--
`EventMap` assigns a stable external label to each enabled machine event.

These labels are the observable step descriptions that one typically wants to
preserve under refinement, compare across runs, or expose in user-facing trace
statements.
-/
abbrev EventMap (machine : Machine) (Event : Type u) :=
  (σ : machine.State) → machine.Enabled σ → Event

/--
`Tickets` assigns a stable obligation identifier to each enabled machine event.

Unlike the raw event itself, a ticket is meant to persist across different
representations of the same scheduling obligation, so later fairness and
liveness layers quantify over tickets rather than over the concrete event type
of one particular state.
-/
abbrev Tickets (machine : Machine) (Ticket : Type u) :=
  (σ : machine.State) → machine.Enabled σ → Ticket

/--
`Machine.Labeled` packages a machine together with its chosen event-label map.

This is the smallest bundle that supports statements about observable event
traces without committing to fairness or safety metadata.
-/
structure Labeled where
  toMachine : Machine
  Event : Type u
  event : toMachine.EventMap Event

/--
`Machine.Ticketed` packages a machine together with stable tickets for its
enabled events.

This is the machine-side entry point for fairness and liveness statements.
-/
structure Ticketed where
  toMachine : Machine
  Ticket : Type u
  ticket : toMachine.Tickets Ticket

/--
`Machine.System` augments a machine by the standard verification predicates
used throughout VCVio: initial states, ambient assumptions, safety, and
invariants.

These predicates are orthogonal to the step relation itself, so they are kept
out of `Machine` and bundled only when one wants verification-oriented
statements about the machine.
-/
structure System extends Machine where
  init : State → Prop
  assumptions : State → Prop := fun _ => True
  safe : State → Prop := fun _ => True
  inv : State → Prop := fun _ => True

/--
Compile a flat state-indexed machine into the continuation-based
`Concurrent.Process` core.

At each machine state `σ`, the current enabled event type `Enabled σ` is turned
into a one-node sequential interaction step. The supplied `semantics` equips
that node with controller and local-view information, so the result is not just
an operational embedding of the state transition relation, but a full process
step inside the richer interaction semantics.

`Machine.toProcess` is therefore the canonical bridge from transition-system
models to the more general process-centered concurrent layer.
-/
def toProcess {Party : Type u} (machine : Machine)
    (semantics : (σ : machine.State) → NodeSemantics Party (machine.Enabled σ)) :
    Process Party where
  Proc := machine.State
  step σ :=
    { spec := .node (machine.Enabled σ) (fun _ => .done)
      semantics := ⟨semantics σ, fun _ => PUnit.unit⟩
      next := fun
        | ⟨event, _⟩ => machine.step σ event }

/--
Lift `Machine.toProcess` from bare dynamics to the verification-oriented
`Process.System` layer by reusing the same initial, assumption, safety, and
invariant predicates.
-/
def System.toProcess {Party : Type u} (system : Machine.System)
    (semantics : (σ : system.State) → NodeSemantics Party (system.Enabled σ)) :
    Process.System Party where
  toProcess := system.toMachine.toProcess semantics
  init := system.init
  assumptions := system.assumptions
  safe := system.safe
  inv := system.inv

end Machine
end Concurrent
end Interaction
