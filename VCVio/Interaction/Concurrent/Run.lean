/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Execution

/-!
# Finite prefixes and infinite runs of dynamic concurrent processes

This file extends finite executions in the two directions needed for semantic
reasoning about ongoing concurrent behavior.

* `ProcessOver.Prefix` is the right notion of a finite initial segment of an
  execution. Unlike `ProcessOver.Trace`, it may stop at any residual process
  state, not only at a quiescent one.
* `ProcessOver.Run` is an infinite execution, represented by the residual
  process state at each time index together with the complete transcript chosen
  for the corresponding process step.

The closed-world `Process` API is recovered as a specialization of these
generic definitions.
-/

universe u v w w₂ w₃

namespace Interaction
namespace Concurrent
namespace ProcessOver

/--
`Prefix process p n` is a finite prefix of length `n` of an execution starting
from the residual process state `p`.

Unlike `ProcessOver.Trace`, a `Prefix` may stop at any residual state. This
makes it the correct finite prefix object for later infinite-run semantics.

Each `step` constructor records one complete sequential transcript of the
current process step and then continues with a shorter prefix of the induced
residual state.
-/
inductive Prefix
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver Γ) :
    process.Proc → Nat → Sort _ where
  | /-- The empty execution prefix. -/
    nil {p : process.Proc} : Prefix process p 0
  | /-- Extend a finite prefix by one complete process step transcript. -/
    step {p : process.Proc} {n : Nat}
      (tr : (process.step p).spec.Transcript) :
      Prefix process ((process.step p).next tr) n →
      Prefix process p n.succ

namespace Prefix

/--
The sequence of current controlling parties exposed by a finite prefix after
projecting the generic context into `StepContext`.
-/
def currentControllers
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party)) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List (Option Party)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      ((process.step p).mapContext resolve).currentController? tr :: currentControllers resolve tail

/--
The sequence of full controller paths exposed by a finite prefix after
projecting the generic context into `StepContext`.
-/
def controllerPaths
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party)) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List (List Party)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      ((process.step p).mapContext resolve).controllerPath tr :: controllerPaths resolve tail

/-- The stable event labels attached to the executed steps of a finite prefix. -/
def events
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List Event
  | _, _, .nil => []
  | p, _, .step tr tail =>
      eventMap p tr :: events eventMap tail

/-- The stable tickets attached to the executed steps of a finite prefix. -/
def tickets
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List Ticket
  | _, _, .nil => []
  | p, _, .step tr tail =>
      ticketMap p tr :: tickets ticketMap tail

/--
Forget the quiescence proof of a finite `Trace` and keep only its executed
prefix.
-/
def ofTrace
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ} :
    {p : process.Proc} → (trace : Trace process p) → Prefix process p trace.length
  | _, .done _ => .nil
  | _, .step tr tail => .step tr (ofTrace tail)

@[simp, grind =]
theorem currentControllers_nil
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    {p : process.Proc} :
    currentControllers resolve (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem controllerPaths_nil
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    {p : process.Proc} :
    controllerPaths resolve (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem events_nil
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    {p : process.Proc} :
    events eventMap (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem tickets_nil
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    {p : process.Proc} :
    tickets ticketMap (.nil : Prefix process p 0) = [] := rfl

end Prefix

/--
`Run process` is an infinite execution of the dynamic process `process`.

It is represented by:

* `state n`, the residual process state after `n` complete process steps;
* `transcript n`, the concrete transcript chosen for step `n`;
* `next_state`, which states that the residual state stream follows the
  process continuation exactly.

This is a continuation-based infinite semantics: the run does not introduce a
new operational state space of its own. It simply records how the residual
process state evolves when one complete process step is chosen at each time.
-/
structure Run
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver Γ) where
  state : Nat → process.Proc
  transcript : (n : Nat) → (process.step (state n)).spec.Transcript
  next_state : ∀ n, state n.succ = (process.step (state n)).next (transcript n)

namespace Run

/-- The initial residual process state of a run. -/
def initial
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (run : Run process) : process.Proc :=
  run.state 0

/--
The first complete process-step transcript of the run.
-/
def head
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (run : Run process) : (process.step run.initial).spec.Transcript :=
  run.transcript 0

/--
The tail of a run after its first process step.
-/
def tail
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (run : Run process) :
    Run process where
  state n := run.state n.succ
  transcript n := run.transcript n.succ
  next_state n := run.next_state n.succ

/--
The initial state of `run.tail` is exactly the residual state obtained by
executing `run.head`.
-/
theorem tail_initial
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (run : Run process) :
    run.tail.initial = (process.step run.initial).next run.head :=
  run.next_state 0

/--
`take run n` is the length-`n` finite execution prefix of the infinite run
`run`.
-/
def take
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (run : Run process) : (n : Nat) → Prefix process run.initial n
  | 0 => .nil
  | n + 1 =>
      .step run.head (run.tail_initial ▸ run.tail.take n)

/--
The current controlling party of step `n` of a run, if any, after projecting
the generic context into `StepContext`.
-/
def currentController?
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    (run : Run process) (n : Nat) : Option Party :=
  ((process.step (run.state n)).mapContext resolve).currentController? (run.transcript n)

/-- The current controlling parties exposed along the first `n` executed steps
of the run `run`. -/
def currentControllersUpTo
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    (run : Run process) : Nat → List (Option Party)
  | 0 => []
  | n + 1 => run.currentController? resolve 0 :: run.tail.currentControllersUpTo resolve n

/--
The full controller path recorded by step `n` of a run after projecting the
generic context into `StepContext`.
-/
def controllerPath
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    (run : Run process) (n : Nat) : List Party :=
  ((process.step (run.state n)).mapContext resolve).controllerPath (run.transcript n)

/-- The full controller paths exposed along the first `n` executed steps of the
run `run`. -/
def controllerPathsUpTo
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    (run : Run process) : Nat → List (List Party)
  | 0 => []
  | n + 1 => run.controllerPath resolve 0 :: run.tail.controllerPathsUpTo resolve n

/-- The stable event label attached to step `n` of a run. -/
def event
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    (run : Run process) (n : Nat) : Event :=
  eventMap (run.state n) (run.transcript n)

/-- The stable event labels attached to the first `n` executed steps of the run
`run`. -/
def eventsUpTo
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    (run : Run process) : Nat → List Event
  | 0 => []
  | n + 1 => run.event eventMap 0 :: run.tail.eventsUpTo eventMap n

/-- The stable ticket attached to step `n` of a run. -/
def ticket
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    (run : Run process) (n : Nat) : Ticket :=
  ticketMap (run.state n) (run.transcript n)

/-- The stable tickets attached to the first `n` executed steps of the run
`run`. -/
def ticketsUpTo
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    (run : Run process) : Nat → List Ticket
  | 0 => []
  | n + 1 => run.ticket ticketMap 0 :: run.tail.ticketsUpTo ticketMap n

/--
`RelUpTo rel left right n` states that the first `n` executed steps of the
runs `left` and `right` match step-by-step according to `rel`.
-/
def RelUpTo
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver Γ}
    {right : ProcessOver Δ}
    (rel : ProcessOver.TranscriptRel left right)
    (leftRun : Run left) (rightRun : Run right) : Nat → Prop
  | 0 => True
  | n + 1 =>
      rel (leftRun.transcript 0) (rightRun.transcript 0) ∧
        RelUpTo rel leftRun.tail rightRun.tail n

/--
`Rel rel left right` states that every finite prefix of the runs `left` and
`right` matches according to `rel`.
-/
def Rel
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver Γ}
    {right : ProcessOver Δ}
    (rel : ProcessOver.TranscriptRel left right)
    (leftRun : Run left) (rightRun : Run right) : Prop :=
  ∀ n, RelUpTo rel leftRun rightRun n

/-- Pointwise step matching implies prefix matching of the first `n` steps. -/
theorem relUpTo_of_pointwise
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver Γ}
    {right : ProcessOver Δ}
    (rel : ProcessOver.TranscriptRel left right)
    (leftRun : Run left) (rightRun : Run right)
    (hrel : ∀ n, rel (leftRun.transcript n) (rightRun.transcript n)) :
    ∀ n, RelUpTo rel leftRun rightRun n := by
  intro n
  induction n generalizing leftRun rightRun with
  | zero =>
      trivial
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · exact hrel 0
      · exact ih leftRun.tail rightRun.tail (fun k => hrel k.succ)

/-- Pointwise step matching implies full run matching. -/
theorem rel_of_pointwise
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {left : ProcessOver Γ}
    {right : ProcessOver Δ}
    (rel : ProcessOver.TranscriptRel left right)
    (leftRun : Run left) (rightRun : Run right)
    (hrel : ∀ n, rel (leftRun.transcript n) (rightRun.transcript n)) :
    Rel rel leftRun rightRun :=
  relUpTo_of_pointwise rel leftRun rightRun hrel

@[simp, grind =]
theorem take_zero
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (run : Run process) :
    run.take 0 = Prefix.nil := rfl

@[simp, grind =]
theorem take_succ
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (run : Run process) (n : Nat) :
    run.take (n + 1) =
      Prefix.step run.head (run.tail_initial ▸ run.tail.take n) := rfl

@[simp, grind =]
theorem currentControllersUpTo_zero
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    (run : Run process) :
    run.currentControllersUpTo resolve 0 = [] := rfl

@[simp, grind =]
theorem controllerPathsUpTo_zero
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    (run : Run process) :
    run.controllerPathsUpTo resolve 0 = [] := rfl

@[simp, grind =]
theorem eventsUpTo_zero
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    (run : Run process) :
    run.eventsUpTo eventMap 0 = [] := rfl

@[simp, grind =]
theorem ticketsUpTo_zero
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    (run : Run process) :
    run.ticketsUpTo ticketMap 0 = [] := rfl

@[simp, grind =]
theorem currentControllersUpTo_succ
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    (run : Run process) (n : Nat) :
    run.currentControllersUpTo resolve (n + 1) =
      run.currentController? resolve 0 :: run.tail.currentControllersUpTo resolve n := rfl

@[simp, grind =]
theorem controllerPathsUpTo_succ
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Party : Type u}
    {process : ProcessOver Γ}
    (resolve : Interaction.Spec.Node.ContextHom Γ (StepContext Party))
    (run : Run process) (n : Nat) :
    run.controllerPathsUpTo resolve (n + 1) =
      run.controllerPath resolve 0 :: run.tail.controllerPathsUpTo resolve n := rfl

@[simp, grind =]
theorem eventsUpTo_succ
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Event : Type w₃}
    (eventMap : process.EventMap Event)
    (run : Run process) (n : Nat) :
    run.eventsUpTo eventMap (n + 1) =
      run.event eventMap 0 :: run.tail.eventsUpTo eventMap n := rfl

@[simp, grind =]
theorem ticketsUpTo_succ
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket)
    (run : Run process) (n : Nat) :
    run.ticketsUpTo ticketMap (n + 1) =
      run.ticket ticketMap 0 :: run.tail.ticketsUpTo ticketMap n := rfl

end Run

end ProcessOver

namespace Process

/-- The closed-world specialization of `ProcessOver.Prefix`. -/
abbrev Prefix {Party : Type u} (process : Process Party) :=
  ProcessOver.Prefix process

namespace Prefix

/-- The sequence of current controlling parties exposed by a finite closed-world
prefix. -/
def currentControllers {Party : Type u} {process : Process Party} :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List (Option Party)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      (process.step p).currentController? tr :: currentControllers tail

/-- The sequence of full controller paths exposed by a finite closed-world
prefix. -/
def controllerPaths {Party : Type u} {process : Process Party} :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List (List Party)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      (process.step p).controllerPath tr :: controllerPaths tail

/-- The stable event labels attached to the executed steps of a finite
closed-world prefix. -/
abbrev events {Party : Type u} {process : Process Party} {Event : Type w₃}
    (eventMap : process.EventMap Event) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List Event :=
  ProcessOver.Prefix.events eventMap

/-- The stable tickets attached to the executed steps of a finite closed-world
prefix. -/
abbrev tickets {Party : Type u} {process : Process Party} {Ticket : Type w₃}
    (ticketMap : process.Tickets Ticket) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List Ticket :=
  ProcessOver.Prefix.tickets ticketMap

/-- Forget the quiescence proof of a finite closed-world trace and keep only
its executed prefix. -/
abbrev ofTrace {Party : Type u} {process : Process Party} :
    {p : process.Proc} → (trace : Trace process p) → Prefix process p trace.length :=
  ProcessOver.Prefix.ofTrace

@[simp, grind =]
theorem currentControllers_nil {Party : Type u} {process : Process Party}
    {p : process.Proc} :
    currentControllers (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem controllerPaths_nil {Party : Type u} {process : Process Party}
    {p : process.Proc} :
    controllerPaths (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem events_nil {Party : Type u} {process : Process Party}
    {Event : Type w₃} (eventMap : process.EventMap Event)
    {p : process.Proc} :
    events eventMap (.nil : Prefix process p 0) = [] :=
  ProcessOver.Prefix.events_nil eventMap

@[simp, grind =]
theorem tickets_nil {Party : Type u} {process : Process Party}
    {Ticket : Type w₃} (ticketMap : process.Tickets Ticket)
    {p : process.Proc} :
    tickets ticketMap (.nil : Prefix process p 0) = [] :=
  ProcessOver.Prefix.tickets_nil ticketMap

end Prefix

/-- The closed-world specialization of `ProcessOver.Run`. -/
abbrev Run {Party : Type u} (process : Process Party) :=
  ProcessOver.Run process

namespace Run

/-- The initial residual process state of a closed-world run. -/
abbrev initial {Party : Type u} {process : Process Party}
    (run : Run process) : process.Proc :=
  ProcessOver.Run.initial run

/-- The first complete process-step transcript of a closed-world run. -/
abbrev head {Party : Type u} {process : Process Party}
    (run : Run process) : (process.step run.initial).spec.Transcript :=
  ProcessOver.Run.head run

/-- The tail of a closed-world run after its first process step. -/
abbrev tail {Party : Type u} {process : Process Party}
    (run : Run process) :
    Run process :=
  ProcessOver.Run.tail run

theorem tail_initial {Party : Type u} {process : Process Party}
    (run : Run process) :
    run.tail.initial = (process.step run.initial).next run.head :=
  ProcessOver.Run.tail_initial run

/-- The length-`n` finite prefix of a closed-world run. -/
abbrev take {Party : Type u} {process : Process Party}
    (run : Run process) : (n : Nat) → Prefix process run.initial n :=
  ProcessOver.Run.take run

/-- The current controlling party of step `n` of a closed-world run, if any. -/
def currentController? {Party : Type u} {process : Process Party}
    (run : Run process) (n : Nat) : Option Party :=
  (process.step (run.state n)).currentController? (run.transcript n)

/-- The current controlling parties exposed along the first `n` executed steps
of a closed-world run. -/
def currentControllersUpTo {Party : Type u} {process : Process Party}
    (run : Run process) : Nat → List (Option Party)
  | 0 => []
  | n + 1 => run.currentController? 0 :: run.tail.currentControllersUpTo n

/-- The full controller path recorded by step `n` of a closed-world run. -/
def controllerPath {Party : Type u} {process : Process Party}
    (run : Run process) (n : Nat) : List Party :=
  (process.step (run.state n)).controllerPath (run.transcript n)

/-- The full controller paths exposed along the first `n` executed steps of a
closed-world run. -/
def controllerPathsUpTo {Party : Type u} {process : Process Party}
    (run : Run process) : Nat → List (List Party)
  | 0 => []
  | n + 1 => run.controllerPath 0 :: run.tail.controllerPathsUpTo n

/-- The stable event label attached to step `n` of a closed-world run. -/
abbrev event {Party : Type u} {process : Process Party}
    {Event : Type w₃} (eventMap : process.EventMap Event)
    (run : Run process) (n : Nat) : Event :=
  ProcessOver.Run.event eventMap run n

/-- The stable event labels attached to the first `n` executed steps of a
closed-world run. -/
abbrev eventsUpTo {Party : Type u} {process : Process Party}
    {Event : Type w₃} (eventMap : process.EventMap Event)
    (run : Run process) : Nat → List Event :=
  ProcessOver.Run.eventsUpTo eventMap run

/-- The stable ticket attached to step `n` of a closed-world run. -/
abbrev ticket {Party : Type u} {process : Process Party}
    {Ticket : Type w₃} (ticketMap : process.Tickets Ticket)
    (run : Run process) (n : Nat) : Ticket :=
  ProcessOver.Run.ticket ticketMap run n

/-- The stable tickets attached to the first `n` executed steps of a
closed-world run. -/
abbrev ticketsUpTo {Party : Type u} {process : Process Party}
    {Ticket : Type w₃} (ticketMap : process.Tickets Ticket)
    (run : Run process) : Nat → List Ticket :=
  ProcessOver.Run.ticketsUpTo ticketMap run

@[simp, grind =]
theorem take_zero {Party : Type u} {process : Process Party}
    (run : Run process) :
    run.take 0 = ProcessOver.Prefix.nil :=
  ProcessOver.Run.take_zero run

@[simp, grind =]
theorem take_succ {Party : Type u} {process : Process Party}
    (run : Run process) (n : Nat) :
    run.take (n + 1) =
      ProcessOver.Prefix.step run.head (run.tail_initial ▸ run.tail.take n) :=
  ProcessOver.Run.take_succ run n

@[simp, grind =]
theorem currentControllersUpTo_zero {Party : Type u} {process : Process Party}
    (run : Run process) :
    run.currentControllersUpTo 0 = [] := rfl

@[simp, grind =]
theorem controllerPathsUpTo_zero {Party : Type u} {process : Process Party}
    (run : Run process) :
    run.controllerPathsUpTo 0 = [] := rfl

@[simp, grind =]
theorem eventsUpTo_zero {Party : Type u} {process : Process Party}
    {Event : Type w₃} (eventMap : process.EventMap Event)
    (run : Run process) :
    run.eventsUpTo eventMap 0 = [] :=
  ProcessOver.Run.eventsUpTo_zero eventMap run

@[simp, grind =]
theorem ticketsUpTo_zero {Party : Type u} {process : Process Party}
    {Ticket : Type w₃} (ticketMap : process.Tickets Ticket)
    (run : Run process) :
    run.ticketsUpTo ticketMap 0 = [] :=
  ProcessOver.Run.ticketsUpTo_zero ticketMap run

@[simp, grind =]
theorem currentControllersUpTo_succ {Party : Type u} {process : Process Party}
    (run : Run process) (n : Nat) :
    run.currentControllersUpTo (n + 1) =
      run.currentController? 0 :: run.tail.currentControllersUpTo n := rfl

@[simp, grind =]
theorem controllerPathsUpTo_succ {Party : Type u} {process : Process Party}
    (run : Run process) (n : Nat) :
    run.controllerPathsUpTo (n + 1) =
      run.controllerPath 0 :: run.tail.controllerPathsUpTo n := rfl

@[simp, grind =]
theorem eventsUpTo_succ {Party : Type u} {process : Process Party}
    {Event : Type w₃} (eventMap : process.EventMap Event)
    (run : Run process) (n : Nat) :
    run.eventsUpTo eventMap (n + 1) =
      run.event eventMap 0 :: run.tail.eventsUpTo eventMap n :=
  ProcessOver.Run.eventsUpTo_succ eventMap run n

@[simp, grind =]
theorem ticketsUpTo_succ {Party : Type u} {process : Process Party}
    {Ticket : Type w₃} (ticketMap : process.Tickets Ticket)
    (run : Run process) (n : Nat) :
    run.ticketsUpTo ticketMap (n + 1) =
      run.ticket ticketMap 0 :: run.tail.ticketsUpTo ticketMap n :=
  ProcessOver.Run.ticketsUpTo_succ ticketMap run n

end Run

end Process
end Concurrent
end Interaction
