/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Bisimulation

/-!
# Common concurrent equivalence notions

This file packages the bisimulation-based equivalence notions that are most
useful in practice.

The underlying `Refinement.Bisimulation` API is intentionally general: it can
talk about any step relation whatsoever. For actual protocol work, however, one
usually wants a smaller family of standard questions:

* do the two systems expose the same controller at each step?
* do they expose the same full controller path?
* do they produce the same external event trace?
* do they preserve the same fairness tickets?
* does a chosen party observe the same thing in both systems?

This file packages exactly those questions as named equivalence notions and
records the immediate preservation lemmas for finite run prefixes.
-/

universe u v w

namespace Interaction
namespace Concurrent
namespace Equivalence

/--
`Controller left right` means that `left` and `right` are bisimilar while
preserving the current controlling party chosen at each executed step.
-/
abbrev Controller {Party : Type u}
    (left right : Process.System Party) :=
  Refinement.Bisimulation left right
    Observation.Process.TranscriptRel.byController
    (Observation.Process.TranscriptRel.byController
      (left := right.toProcess) (right := left.toProcess))

/--
`ControllerPath left right` means that `left` and `right` are bisimilar while
preserving the full controller path of each executed step.
-/
abbrev ControllerPath {Party : Type u}
    (left right : Process.System Party) :=
  Refinement.Bisimulation left right
    Observation.Process.TranscriptRel.byPath
    (Observation.Process.TranscriptRel.byPath
      (left := right.toProcess) (right := left.toProcess))

/--
`Trace left right eventLeft eventRight` means that `left` and `right` are
bisimilar while preserving the stable external event label attached to each
complete step transcript.
-/
abbrev Trace {Party : Type u} {Event : Type w}
    (left right : Process.System Party)
    (eventLeft : left.toProcess.EventMap Event)
    (eventRight : right.toProcess.EventMap Event) :=
  Refinement.Bisimulation left right
    (Observation.Process.TranscriptRel.byEvent eventLeft eventRight)
    (Observation.Process.TranscriptRel.byEvent
      (left := right.toProcess) (right := left.toProcess) eventRight eventLeft)

/--
`Ticket left right ticketLeft ticketRight` means that `left` and `right` are
bisimilar while preserving the stable tickets attached to complete step
transcripts.
-/
abbrev Ticket {Party : Type u} {TicketTy : Type w}
    (left right : Process.System Party)
    (ticketLeft : left.toProcess.Tickets TicketTy)
    (ticketRight : right.toProcess.Tickets TicketTy) :=
  Refinement.Bisimulation left right
    (Observation.Process.TranscriptRel.byTicket ticketLeft ticketRight)
    (Observation.Process.TranscriptRel.byTicket
      (left := right.toProcess) (right := left.toProcess) ticketRight ticketLeft)

/--
`Observation me left right` means that `left` and `right` are bisimilar while
preserving the packed local observations exposed to the fixed party `me` at
every executed step.
-/
abbrev Observation {Party : Type u} [DecidableEq Party]
    (me : Party)
    (left right : Process.System Party) :=
  Refinement.Bisimulation left right
    (Observation.Process.TranscriptRel.byObservation me)
    (Observation.Process.TranscriptRel.byObservation
      (left := right.toProcess) (right := left.toProcess) me)

namespace Controller

/--
Along the forward direction of a controller equivalence, the current controller
sequence of every finite run prefix is preserved.
-/
theorem currentControllersUpTo_eq {Party : Type u}
    {left right : Process.System Party}
    (equiv : Controller left right)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Process.Run.currentControllersUpTo run n =
      Process.Run.currentControllersUpTo (equiv.forth.mapRun run hrel) n :=
  equiv.forth.currentControllersUpTo_mapRun run hrel n

end Controller

namespace ControllerPath

/--
Along the forward direction of a controller-path equivalence, the full
controller-path sequence of every finite run prefix is preserved.
-/
theorem controllerPathsUpTo_eq {Party : Type u}
    {left right : Process.System Party}
    (equiv : ControllerPath left right)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Process.Run.controllerPathsUpTo run n =
      Process.Run.controllerPathsUpTo (equiv.forth.mapRun run hrel) n :=
  equiv.forth.controllerPathsUpTo_mapRun run hrel n

end ControllerPath

namespace Trace

/--
Along the forward direction of a trace equivalence, the stable event trace of
every finite run prefix is preserved.
-/
theorem eventsUpTo_eq {Party : Type u} {Event : Type w}
    {left right : Process.System Party}
    {eventLeft : left.toProcess.EventMap Event}
    {eventRight : right.toProcess.EventMap Event}
    (equiv : Trace left right eventLeft eventRight)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Process.Run.eventsUpTo eventLeft run n =
      Process.Run.eventsUpTo eventRight (equiv.forth.mapRun run hrel) n :=
  equiv.forth.eventsUpTo_mapRun run hrel n

end Trace

namespace Ticket

/--
Along the forward direction of a ticket equivalence, the stable ticket
sequence of every finite run prefix is preserved.
-/
theorem ticketsUpTo_eq {Party : Type u} {TicketTy : Type w}
    {left right : Process.System Party}
    {ticketLeft : left.toProcess.Tickets TicketTy}
    {ticketRight : right.toProcess.Tickets TicketTy}
    (equiv : Ticket left right ticketLeft ticketRight)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Process.Run.ticketsUpTo ticketLeft run n =
      Process.Run.ticketsUpTo ticketRight (equiv.forth.mapRun run hrel) n :=
  equiv.forth.ticketsUpTo_mapRun run hrel n

end Ticket

namespace Observation

/--
Along the forward direction of an observational equivalence, the packed local
observations of the chosen party are preserved on every finite run prefix.
-/
theorem observationsUpTo_eq {Party : Type u} [DecidableEq Party]
    (me : Party)
    {left right : Process.System Party}
    (equiv : Observation me left right)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Observation.Process.Run.observationsUpTo me run n =
      Observation.Process.Run.observationsUpTo me (equiv.forth.mapRun run hrel) n :=
  equiv.forth.observationsUpTo_mapRun me run hrel n

end Observation

end Equivalence
end Concurrent
end Interaction
