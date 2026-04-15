/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Execution

/-!
# Executable step policies for dynamic concurrent processes

This file adds a lightweight policy layer on top of finite executions of
`Concurrent.ProcessOver`.

The point of a policy here is operational rather than semantic in the liveness
sense: it describes which concrete step transcripts are allowed to occur in a
finite execution. So this layer is useful for expressing scheduler rules,
authorization filters, event allowlists, or ticket filters that can be checked
step by step.

The closed-world `Process` API is recovered as a specialization of these
generic definitions.
-/

universe u v w w₂ w₃

namespace Interaction
namespace Concurrent
namespace ProcessOver

/--
`StepPolicy process` is an executable constraint on one complete process step.

A policy sees:

* the current residual process state `p`;
* the concrete sequential transcript `tr` chosen for the current step protocol
  `process.step p`.

It returns `true` when that step is allowed and `false` when it is forbidden.
-/
abbrev StepPolicy
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver Γ) :=
  {p : process.Proc} → (process.step p).spec.Transcript → Bool

namespace StepPolicy

/-- The permissive policy that allows every step transcript. -/
def top
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ} : StepPolicy process :=
  fun _ => true

/-- Conjunction of two step policies. A step is allowed exactly when both
component policies allow it. -/
def inter
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (left right : StepPolicy process) : StepPolicy process :=
  fun tr => left tr && right tr

/--
`byController resolve allow` constrains only the current controlling party of
the concrete step transcript, after projecting the generic context into
`StepContext`.
-/
def byController
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    (allow : Party → Bool) : StepPolicy process :=
  fun {p} tr =>
    match ((process.step p).mapContext resolve).currentController? tr with
    | some controller => allow controller
    | none => true

/--
`byPath resolve allow` constrains the full controller path of the concrete step
transcript, after projecting the generic context into `StepContext`.
-/
def byPath
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    (allow : List Party → Bool) : StepPolicy process :=
  fun {p} tr => allow (((process.step p).mapContext resolve).controllerPath tr)

/--
`byEvent eventMap allow` constrains the stable event label induced by the
transcript-level event map `eventMap`.
-/
def byEvent
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    (allow : Event → Bool) : StepPolicy process :=
  fun {p} tr => allow (eventMap p tr)

/--
`byTicket ticketMap allow` constrains the stable ticket attached to each step
transcript by `ticketMap`.
-/
def byTicket
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    (allow : Ticket → Bool) : StepPolicy process :=
  fun {p} tr => allow (ticketMap p tr)

end StepPolicy

namespace Trace

/--
`respects policy trace` checks whether every step of the finite process
execution `trace` satisfies the executable step policy `policy`.
-/
def respects
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (policy : StepPolicy process) :
    {p : process.Proc} → Trace process p → Bool
  | _, .done _ => true
  | _, .step tr tail => policy tr && respects policy tail

@[simp, grind =]
theorem respects_top
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {p : process.Proc} (trace : Trace process p) :
    respects StepPolicy.top trace = true := by
  induction trace with
  | done h => rfl
  | step tr tail ih =>
      simp [Trace.respects, StepPolicy.top, ih]

end Trace

end ProcessOver

namespace Process

/-- The closed-world specialization of `ProcessOver.StepPolicy`. -/
abbrev StepPolicy {Party : Type u} (process : Process Party) :=
  ProcessOver.StepPolicy process

namespace StepPolicy

/-- The permissive closed-world step policy. -/
abbrev top {Party : Type u} {process : Process Party} : StepPolicy process :=
  ProcessOver.StepPolicy.top

/-- Conjunction of closed-world step policies. -/
abbrev inter {Party : Type u} {process : Process Party}
    (left right : StepPolicy process) : StepPolicy process :=
  ProcessOver.StepPolicy.inter left right

/--
`byController allow` constrains only the current controlling party of the
concrete closed-world step transcript.
-/
abbrev byController {Party : Type u} {process : Process Party}
    (allow : Party → Bool) : StepPolicy process :=
  ProcessOver.StepPolicy.byController
    (resolve := Interaction.Spec.Node.ContextHom.id (StepContext Party))
    allow

/--
`byPath allow` constrains the full controller path of the concrete closed-world
step transcript.
-/
abbrev byPath {Party : Type u} {process : Process Party}
    (allow : List Party → Bool) : StepPolicy process :=
  ProcessOver.StepPolicy.byPath
    (resolve := Interaction.Spec.Node.ContextHom.id (StepContext Party))
    allow

/--
`byEvent eventMap allow` constrains the stable event label induced by the
transcript-level event map `eventMap`.
-/
abbrev byEvent {Party : Type u} {process : Process Party}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    (allow : Event → Bool) : StepPolicy process :=
  ProcessOver.StepPolicy.byEvent eventMap allow

/--
`byTicket ticketMap allow` constrains the stable ticket attached to each
closed-world step transcript by `ticketMap`.
-/
abbrev byTicket {Party : Type u} {process : Process Party}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    (allow : Ticket → Bool) : StepPolicy process :=
  ProcessOver.StepPolicy.byTicket ticketMap allow

end StepPolicy

namespace Trace

/--
`respects policy trace` checks whether every step of the finite closed-world
process execution `trace` satisfies the executable step policy `policy`.
-/
abbrev respects {Party : Type u} {process : Process Party}
    (policy : StepPolicy process) :
    {p : process.Proc} → Trace process p → Bool :=
  ProcessOver.Trace.respects policy

@[simp, grind =]
theorem respects_top {Party : Type u} {process : Process Party}
    {p : process.Proc} (trace : Trace process p) :
    respects StepPolicy.top trace = true :=
  ProcessOver.Trace.respects_top trace

end Trace

end Process
end Concurrent
end Interaction
