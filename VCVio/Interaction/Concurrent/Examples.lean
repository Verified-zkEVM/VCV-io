/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Execution
import VCVio.Interaction.Concurrent.Equivalence
import VCVio.Interaction.Concurrent.Fairness
import VCVio.Interaction.Concurrent.Interleaving
import VCVio.Interaction.Concurrent.Independence
import VCVio.Interaction.Concurrent.Liveness
import VCVio.Interaction.Concurrent.Observation
import VCVio.Interaction.Concurrent.Policy
import VCVio.Interaction.Concurrent.Refinement
import VCVio.Interaction.Concurrent.Run
import VCVio.Interaction.Concurrent.Tree

/-!
# Concurrent interaction examples

This file gives small definitional examples for the current concurrent layer.

The examples are intentionally focused on:

* binary structural parallelism;
* frontier events and residuals;
* per-party observation profiles over concurrently live components.
* scheduler ownership versus atomic payload ownership;
* the combined current local view of the next frontier event.
* process executions, controller paths, and observed local traces.
* interleaving equivalence under commuting independent steps.
* executable scheduler and controller policies over finite traces.

They are meant to exercise the current expressivity surface before later layers
such as fairness or richer execution semantics are added.
-/

universe u

namespace Interaction
namespace Concurrent
namespace Examples

/-- Three parties for the toy concurrent examples: two honest parties and a
network adversary. -/
inductive Party where
  | alice
  | bob
  | adv

deriving instance DecidableEq for Party

/-- One atomic message-delivery step whose payload is a pair of a public header
and a private payload bit. -/
def delivery : Spec :=
  .node (Nat × Bool) (fun _ => .done)

/-- A profile where Alice originates the payload, Bob sees the whole message,
and the adversary sees only the public header. -/
def deliveryProfile : Profile Party delivery :=
  .node (fun
      | .alice => .active
      | .bob => .observe
      | .adv => .quotient Nat Prod.fst)
    (fun _ => .done)

example : Profile.ObsType Party.alice deliveryProfile = (Nat × Bool) := rfl

example : Profile.ObsType Party.bob deliveryProfile = (Nat × Bool) := rfl

example : Profile.ObsType Party.adv deliveryProfile = Nat := rfl

example :
    Profile.observe Party.adv deliveryProfile (.move (3, true)) = (3 : Nat) := rfl

/-- A second atomic node that only Bob fully observes, while the adversary
learns nothing. -/
def ack : Spec :=
  .node Bool (fun _ => .done)

/-- Local observations for the acknowledgement node. -/
def ackProfile : Profile Party ack :=
  .node (fun
      | .alice => .hidden
      | .bob => .observe
      | .adv => .hidden)
    (fun _ => .done)

/-- A concurrent system where delivery and acknowledgement are both live. -/
def inFlight : Spec :=
  .par delivery ack

/-- The corresponding concurrent observation profile. -/
def inFlightProfile : Profile Party inFlight :=
  .par deliveryProfile ackProfile

/-- Control ownership for the delivery step: Alice chooses the payload. -/
def deliveryControl : Control Party delivery :=
  .node .alice (fun _ => .done)

/-- Control ownership for the acknowledgement step: Bob chooses the bit. -/
def ackControl : Control Party ack :=
  .node .bob (fun _ => .done)

/-- The adversary controls scheduling between the two concurrently live
subsystems, while Alice and Bob still control their respective atomic nodes. -/
def inFlightControl : Control Party inFlight :=
  .par .adv deliveryControl ackControl

example :
    Profile.ObsType Party.adv inFlightProfile = Sum Nat PUnit := rfl

example :
    Profile.ObsType Party.bob inFlightProfile = Sum (Nat × Bool) Bool := rfl

example :
    Profile.observe Party.adv inFlightProfile (.left (.move (5, false))) =
      (Sum.inl (α := Nat) (β := PUnit) 5) := rfl

example :
    Profile.observe Party.adv inFlightProfile (.right (.move true)) = Sum.inr PUnit.unit := rfl

example :
    Profile.residual inFlightProfile (.left (.move (7, true))) = .par .done ackProfile := rfl

example :
    Profile.residual inFlightProfile (.right (.move false)) = .par deliveryProfile .done := rfl

example : Control.scheduler? inFlightControl = some .adv := rfl

example : Control.current? inFlightControl = some .adv := rfl

example :
    Control.controllers inFlightControl (.left (.move (5, false))) = [.adv, .alice] := rfl

example :
    Control.controllers inFlightControl (.right (.move true)) = [.adv, .bob] := rfl

def afterDelivery : Control Party (.par .done ack) :=
  Control.residual inFlightControl (.left (.move (7, true)))

example : Control.scheduler? afterDelivery = none := rfl

example : Control.current? afterDelivery = some .bob := rfl

example : Control.controllers afterDelivery (.right (.move false)) = [.bob] := rfl

example : Current.controller? inFlightControl = some .adv := rfl

example : Current.scheduler? inFlightControl = some .adv := rfl

example :
    Current.view Party.adv inFlightControl inFlightProfile = Multiparty.LocalView.active := by
  rfl

example :
    Current.observe Party.adv inFlightControl inFlightProfile
      (Front.left (.move (5, false))) =
      (Front.left (.move (5, false))) := rfl

example :
    Current.observe Party.alice inFlightControl inFlightProfile (.left (.move (5, false))) =
      (show PLift (Sum (Nat × Bool) PUnit) from ⟨Sum.inl (5, false)⟩) := rfl

example :
    Current.observe Party.bob inFlightControl inFlightProfile (.right (.move true)) =
      (show PLift (Sum (Nat × Bool) Bool) from ⟨Sum.inr true⟩) := rfl

def afterDeliveryProfile : Profile Party (.par .done ack) :=
  Profile.residual inFlightProfile (.left (.move (7, true)))

example : Current.controller? afterDelivery = some .bob := rfl

example : Current.scheduler? afterDelivery = none := rfl

example :
    Current.view Party.bob afterDelivery afterDeliveryProfile = Multiparty.LocalView.active := by
  rfl

example :
    Current.view Party.adv afterDelivery afterDeliveryProfile = Multiparty.LocalView.hidden := by
  rfl

example :
    Current.observe Party.adv afterDelivery afterDeliveryProfile (.right (.move false)) =
      PUnit.unit := rfl

/-- A concrete structural trace where the adversary schedules delivery first and the
remaining acknowledgement second. -/
def deliveryThenAck : Trace inFlight :=
  .step (.left (.move (7, true)))
    (.step (.right (.move false)) (Trace.doneOfNotLive rfl))

/-- The dynamic process compiled from the structural tree frontend. -/
def inFlightProcess : Process Party :=
  Tree.toProcess (Party := Party)

/-- The packaged initial structural state of the in-flight system. -/
def inFlightState : Tree.State Party :=
  Tree.init inFlightControl inFlightProfile

/-- The process execution induced by `deliveryThenAck`. -/
def deliveryThenAckExec :
    Process.Trace inFlightProcess inFlightState :=
  Tree.ofLinearization inFlightControl inFlightProfile deliveryThenAck

example :
    Process.Trace.currentControllers deliveryThenAckExec = [some .adv, some .bob] := rfl

example :
    Process.Trace.controllerPaths deliveryThenAckExec = [[.adv, .alice], [.bob]] := rfl

example :
    (Step.observe Party.adv inFlightState.currentStep
      (inFlightState.transcriptOfEvent (.left (.move (7, true))))).length = 1 := rfl

def afterDeliveryState : Tree.State Party :=
  Tree.init afterDelivery afterDeliveryProfile

example :
    (Step.observe Party.alice inFlightState.currentStep
      (inFlightState.transcriptOfEvent (.left (.move (7, true))))).length = 1 := rfl

example :
    ((Step.observe Party.bob afterDeliveryState.currentStep
      (afterDeliveryState.transcriptOfEvent (.right (.move false)))).length = 1) := rfl

example :
    (Process.ObservedTrace.ofTrace Party.bob inFlightProcess deliveryThenAckExec).length =
      2 := rfl

/-- A concrete structural trace where the adversary schedules the acknowledgement before
the delivery event. -/
def ackThenDelivery : Trace inFlight :=
  .step (.right (.move true))
    (.step (.left (.move (9, false))) (Trace.doneOfNotLive rfl))

def afterAck : Control Party (.par delivery .done) :=
  Control.residual inFlightControl (.right (.move true))

def afterAckProfile : Profile Party (.par delivery .done) :=
  Profile.residual inFlightProfile (.right (.move true))

/-- The process execution induced by `ackThenDelivery`. -/
def ackThenDeliveryExec :
    Process.Trace inFlightProcess inFlightState :=
  Tree.ofLinearization inFlightControl inFlightProfile ackThenDelivery

example :
    Process.Trace.currentControllers ackThenDeliveryExec = [some .adv, some .alice] := rfl

example :
    Process.Trace.controllerPaths ackThenDeliveryExec = [[.adv, .bob], [.alice]] := rfl

example :
    ((Step.observe Party.adv inFlightState.currentStep
      (inFlightState.transcriptOfEvent (.right (.move true)))).length = 1) := rfl

def afterAckState : Tree.State Party :=
  Tree.init afterAck afterAckProfile

example :
    (Step.observe Party.adv afterAckState.currentStep
      (afterAckState.transcriptOfEvent (.left (.move (9, false))))).length = 1 := rfl

def deliveryEvent : Front inFlight :=
  .left (.move (4, true))

def ackEvent : Front inFlight :=
  .right (.move false)

def leftThenRight : Trace inFlight :=
  .step deliveryEvent
    (.step (Independent.afterLeft (Independent.left_right (.move (4, true)) (.move false)))
      (Trace.doneOfNotLive rfl))

def rightThenLeft : Trace inFlight :=
  .step ackEvent
    (.step (Independent.afterRight (Independent.left_right (.move (4, true)) (.move false)))
      (Trace.doneOfNotLive rfl))

example : Trace.Equiv leftThenRight rightThenLeft :=
  .swap (Independent.left_right (.move (4, true)) (.move false)) (Trace.doneOfNotLive rfl)

example :
    Trace.Equiv.length_eq
      (.swap (Independent.left_right (.move (4, true)) (.move false)) (Trace.doneOfNotLive rfl) :
        Trace.Equiv leftThenRight rightThenLeft) = rfl := rfl

/-- When both sides of a live `par` are available, prefer the left branch. -/
def preferLeft : Process.StepPolicy inFlightProcess :=
  fun {p} tr =>
    match p with
    | ⟨.par _ _, .par _ leftControl rightControl, _⟩ =>
        match tr with
        | ⟨event, _⟩ =>
            match leftControl.isLive, rightControl.isLive, event with
            | true, true, .left _ => true
            | true, true, .right _ => false
            | _, _, _ => true
    | _ => true

/-- When both sides of a live `par` are available, prefer the right branch. -/
def preferRight : Process.StepPolicy inFlightProcess :=
  fun {p} tr =>
    match p with
    | ⟨.par _ _, .par _ leftControl rightControl, _⟩ =>
        match tr with
        | ⟨event, _⟩ =>
            match leftControl.isLive, rightControl.isLive, event with
            | true, true, .left _ => false
            | true, true, .right _ => true
            | _, _, _ => true
    | _ => true

example : Process.Trace.respects preferLeft deliveryThenAckExec = true := rfl

example : Process.Trace.respects preferLeft ackThenDeliveryExec = false := rfl

example : Process.Trace.respects preferRight ackThenDeliveryExec = true := rfl

example : Process.Trace.respects preferRight deliveryThenAckExec = false := rfl

example :
    Process.Trace.respects (Process.StepPolicy.byController (fun | .adv => true | _ => false))
      deliveryThenAckExec = false := rfl

example :
    Process.Trace.respects (Process.StepPolicy.byController (fun | .bob => false | _ => true))
      deliveryThenAckExec = false := rfl

example :
    Process.Trace.respects (Process.StepPolicy.byController (fun | .bob => false | _ => true))
      ackThenDeliveryExec = true := rfl

/-- A three-way concurrent system used to illustrate recursive independence
inside one branch of a larger parallel spec. -/
def threeWay : Spec :=
  .par delivery (.par ack ack)

example :
    Independent
      (Front.left (right := ack) (.move (4, true)) : Front inFlight)
      (Front.right (left := delivery) (.move false)) :=
  .left_right (.move (4, true)) (.move false)

example :
    Independent.afterLeft
      (Independent.left_right
        (left := delivery) (right := ack) (.move (4, true)) (.move false)) =
      Front.right (.move false) := rfl

example :
    Independent.afterRight
      (Independent.left_right
        (left := delivery) (right := ack) (.move (4, true)) (.move false)) =
      Front.left (.move (4, true)) := rfl

example :
    Independent.diamond
      (Independent.left_right
        (left := delivery) (right := ack) (.move (4, true)) (.move false)) = rfl := rfl

example :
    Independent
      (Front.right (left := delivery) (Front.left (.move true)) : Front threeWay)
      (Front.right (left := delivery) (Front.right (.move false))) :=
  .right (.left_right (.move true) (.move false))

example :
    Independent.diamond
      (.right
        (Independent.left_right
          (left := ack) (right := ack) (.move true) (.move false)) :
        Independent
          (Front.right (left := delivery) (Front.left (.move true)) : Front threeWay)
          (Front.right (left := delivery) (Front.right (.move false)))) = rfl := rfl

section PhaseOneExamples

/-- Node semantics for a tiny looping process:
the adversary actively chooses the boolean step, Bob observes it, and Alice is
hidden from it. -/
def loopNode : NodeSemantics Party Bool where
  controllers := fun _ => [.adv]
  views
    | .adv => .active
    | .bob => .observe
    | .alice => .hidden

/-- A tiny one-state looping process used to exercise runs, tickets, fairness,
and refinement. -/
def loopProcess : Process Party :=
  { Proc := PUnit
    step := fun _ =>
      { spec := .node Bool (fun _ => .done)
        semantics := ⟨loopNode, fun _ => PUnit.unit⟩
        next := fun _ => PUnit.unit } }

/-- A ticketed view of `loopProcess` using the chosen boolean as the stable
ticket. -/
def loopTicketed : Process.Ticketed Party where
  toProcess := loopProcess
  Ticket := Bool
  ticket := fun _ tr =>
    match tr with
    | ⟨b, _⟩ => b

/-- A simple always-true infinite run of `loopProcess`. -/
def trueRun : Process.Run loopProcess where
  state _ := PUnit.unit
  transcript _ := ⟨true, PUnit.unit⟩
  next_state _ := rfl

example : Process.Run.initial trueRun = PUnit.unit := rfl

example :
    Process.Run.ticketsUpTo loopTicketed.ticket trueRun 3 = [true, true, true] := by
  simp only [ProcessOver.Run.ticketsUpTo_succ, ProcessOver.Run.ticketsUpTo_zero,
    ProcessOver.Run.ticket, ProcessOver.Run.tail, loopTicketed, trueRun]

example :
    (Observation.Process.Run.observationsUpTo Party.adv trueRun 2).length = 2 := rfl

example :
    (Observation.Process.Run.observationsUpTo Party.bob trueRun 2).length = 2 := rfl

example :
    Process.Ticketed.firedAt loopTicketed trueRun true 5 := by
  simp [ProcessOver.Ticketed.firedAt, loopTicketed, trueRun]

example :
    Process.Ticketed.enabledAt loopTicketed trueRun true 7 := by
  refine ⟨by
    change Interaction.Spec.Transcript (.node Bool fun _ => .done)
    exact ⟨true, PUnit.unit⟩, ?_⟩
  simp [loopTicketed]

example :
    Process.Ticketed.WeakFairOn loopTicketed trueRun true := by
  intro _ N
  refine ⟨N, Nat.le_refl _, ?_⟩
  simp [ProcessOver.Ticketed.firedAt, loopTicketed, trueRun]

example :
    Process.Ticketed.StrongFairOn loopTicketed trueRun true := by
  intro _ N
  refine ⟨N, Nat.le_refl _, ?_⟩
  simp [ProcessOver.Ticketed.firedAt, loopTicketed, trueRun]

/-- A trivial system wrapper around `loopProcess`. -/
def loopSystem : Process.System Party where
  toProcess := loopProcess
  init _ := True
  assumptions _ := True
  safe _ := True
  inv _ := True

/-- The identity simulation on `loopSystem`, preserving the boolean ticket. -/
def loopSim :
    Refinement.ForwardSimulation loopSystem loopSystem
      (Observation.Process.TranscriptRel.byTicket
        loopTicketed.ticket loopTicketed.ticket) where
  stateRel _ _ := True
  init p hp := ⟨p, hp, trivial⟩
  assumptions _ _ := trivial
  step _
    | ⟨b, tail⟩ => ⟨⟨b, tail⟩, rfl, trivial⟩
  safe _ _ := trivial

/-- The specification-side run obtained by matching `trueRun` through
`loopSim`. -/
noncomputable def loopMappedRun : Process.Run loopSystem.toProcess :=
  loopSim.mapRun (pSpec := PUnit.unit) trueRun trivial

/-- The identity simulation on `loopSystem`, preserving Bob's local
observations. -/
def loopObsSimBob :
    Refinement.ForwardSimulation loopSystem loopSystem
      (Observation.Process.TranscriptRel.byObservation Party.bob) where
  stateRel _ _ := True
  init p hp := ⟨p, hp, trivial⟩
  assumptions _ _ := trivial
  step _
    | ⟨b, tail⟩ => ⟨⟨b, tail⟩, rfl, trivial⟩
  safe _ _ := trivial

/-- The specification-side run obtained by matching `trueRun` through
`loopObsSimBob`. -/
noncomputable def loopObsMappedRunBob : Process.Run loopSystem.toProcess :=
  loopObsSimBob.mapRun (pSpec := PUnit.unit) trueRun trivial

/-- The identity ticket bisimulation on `loopSystem`. -/
def loopTicketBisim :
    Refinement.Bisimulation loopSystem loopSystem
      (Observation.Process.TranscriptRel.byTicket
        loopTicketed.ticket loopTicketed.ticket)
      (Observation.Process.TranscriptRel.byTicket
        loopTicketed.ticket loopTicketed.ticket) where
  forth := loopSim
  back := loopSim

/-- The identity observational bisimulation on `loopSystem` for Bob. -/
def loopObsBisimBob :
    Refinement.Bisimulation loopSystem loopSystem
      (Observation.Process.TranscriptRel.byObservation Party.bob)
      (Observation.Process.TranscriptRel.byObservation Party.bob) where
  forth := loopObsSimBob
  back := loopObsSimBob

example : loopMappedRun.state 4 = PUnit.unit := rfl

example :
    Observation.Process.TranscriptRel.byTicket loopTicketed.ticket loopTicketed.ticket
      (trueRun.transcript 3) (loopMappedRun.transcript 3) := by
  exact loopSim.match_mapRun (pSpec := PUnit.unit) trueRun trivial 3

example : Process.System.Safe loopSystem loopMappedRun := by
  intro _
  trivial

example :
    Process.System.Satisfies loopSystem (fun _ => True) (Process.System.Safe loopSystem) := by
  intro run _ _ _ n
  trivial

example :
    Process.System.Satisfies loopSystem (fun _ => True) (Process.System.Safe loopSystem) := by
  apply loopSim.safe_of_satisfies (fairImpl := fun _ => True) (fairSpec := fun _ => True)
  · intro _ _ _
    trivial
  · intro run _ _ _ n
    trivial

example :
    Process.Run.ticketsUpTo loopTicketed.ticket trueRun 4 =
      Process.Run.ticketsUpTo loopTicketed.ticket loopMappedRun 4 := by
  exact loopSim.ticketsUpTo_mapRun (pSpec := PUnit.unit) trueRun trivial 4

example :
    Observation.Process.Run.observationsUpTo Party.bob trueRun 3 =
      Observation.Process.Run.observationsUpTo Party.bob loopObsMappedRunBob 3 := by
  exact loopObsSimBob.observationsUpTo_mapRun Party.bob
    (pSpec := PUnit.unit) trueRun trivial 3

example :
    Observation.Process.Run.Rel
      (Observation.Process.TranscriptRel.byTicket loopTicketed.ticket loopTicketed.ticket)
      trueRun loopMappedRun := by
  exact Observation.Process.Run.rel_of_pointwise
    (Observation.Process.TranscriptRel.byTicket loopTicketed.ticket loopTicketed.ticket)
    trueRun loopMappedRun
    (loopSim.match_mapRun (pSpec := PUnit.unit) trueRun trivial)

example :
    Process.Run.ticketsUpTo loopTicketed.ticket trueRun 5 =
      Process.Run.ticketsUpTo loopTicketed.ticket
        (loopTicketBisim.forth.mapRun trueRun (pSpec := PUnit.unit) trivial) 5 := by
  exact Equivalence.Ticket.ticketsUpTo_eq loopTicketBisim trueRun
    (pRight := PUnit.unit) trivial 5

example :
    Observation.Process.Run.observationsUpTo Party.bob trueRun 4 =
      Observation.Process.Run.observationsUpTo Party.bob
        (loopObsBisimBob.forth.mapRun trueRun (pSpec := PUnit.unit) trivial) 4 := by
  exact Equivalence.Observation.observationsUpTo_eq Party.bob loopObsBisimBob
    trueRun (pRight := PUnit.unit) trivial 4

example :
    Process.System.Satisfies loopSystem (fun _ => True) (Process.System.Safe loopSystem) := by
  exact
    (Refinement.Bisimulation.safe_iff_of_satisfies loopTicketBisim
      (fairLeft := fun _ => True) (fairRight := fun _ => True)
      (hfairLeft := by
        intro _ _ _ _
        trivial)
      (hfairRight := by
        intro _ _ _ _
        trivial)).mp
      (by
        intro run _ _ _ n
        trivial)

end PhaseOneExamples

end Examples
end Concurrent
end Interaction
