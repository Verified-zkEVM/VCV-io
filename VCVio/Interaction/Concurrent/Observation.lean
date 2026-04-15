/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Run

/-!
# Observation equivalence for concurrent processes

This file packages the notion of "what a party can tell apart" from concrete
executions of a concurrent process.

The process semantics keeps the exact dependent type of each local observation,
which is ideal when reasoning inside one fixed execution. But comparison across
different executions, processes, or refinement layers needs a uniform carrier.
The solution adopted here is to pack each local observation together with its
type and then compare executions through these packed observations.

The resulting API provides:

* packed local observations for one sequential step;
* per-step observation summaries for finite traces, finite prefixes, and runs;
* generic transcript relations saying when two executions match; and
* reusable lemmas showing that controller, event, ticket, and observation data
  are preserved when those transcript relations hold.

This is the comparison layer later used by refinement and equivalence results.
-/

universe u v w

namespace Interaction
namespace Concurrent
namespace Observation

/--
`PackedObs` is a locally observed value packaged together with its observation
type.

This is the simplest uniform carrier for local observations whose precise type
may vary from one visited node to the next.
-/
structure PackedObs : Type (w + 1) where
  α : Type w
  val : α

namespace Step
namespace Observed

/--
Forget the dependent indices of an observed sequential transcript and keep only
the concrete packed sequence of observations that was exposed locally.

This is the uniform, comparison-friendly summary of what one party learned from
one complete sequential step transcript.
-/
def toList {Party : Type u} [DecidableEq Party] {me : Party} :
    {spec : Interaction.Spec.{w}} →
      {semantics : Interaction.Spec.Decoration (StepContext Party) spec} →
      {tr : Interaction.Spec.Transcript spec} →
      Interaction.Concurrent.Step.Observed me semantics tr →
      List PackedObs
  | .done, _, _, .done => []
  | .node _ _, _, _, .step obs rest =>
      ⟨_, obs⟩ :: toList rest

end Observed

/--
`obsList me step tr` is the packed sequence of local observations available to
the fixed party `me` while the sequential process step `step` executes along
the transcript `tr`.

This forgets the exact dependent observation types but keeps their concrete
values in order, which makes it the basic comparison object for one process
step.
-/
def obsList {Party : Type u} [DecidableEq Party] (me : Party)
    {P : Type v} (step : Interaction.Concurrent.Step Party P)
    (tr : Interaction.Spec.Transcript step.spec) : List PackedObs :=
  Observed.toList (Interaction.Concurrent.Step.observe me step tr)

end Step

namespace Process
namespace Trace

/--
The per-step packed local observations exposed along a finite complete process
trace.

Each list element corresponds to one executed process step and stores the local
observations that `me` obtained during that step.
-/
def observations {Party : Type u} [DecidableEq Party]
    {process : Process Party} (me : Party) :
    {p : process.Proc} → Process.Trace process p → List (List PackedObs)
  | _, .done _ => []
  | p, .step tr tail =>
      Step.obsList me (process.step p) tr :: observations me tail

end Trace

namespace Prefix

/--
The per-step packed local observations exposed along a finite process prefix.

This is the prefix-level analogue of `Trace.observations`.
-/
def observations {Party : Type u} [DecidableEq Party]
    {process : Process Party} (me : Party) :
    {p : process.Proc} → {n : Nat} → Process.Prefix process p n →
      List (List PackedObs)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      Step.obsList me (process.step p) tr :: observations me tail

/--
`Rel rel left right` states that the two finite prefixes `left` and `right`
match step-by-step according to the transcript relation `rel`.

The length index forces the two prefixes to have the same number of executed
steps.

So `Prefix.Rel` is the generic finite-horizon comparison interface: the caller
chooses what it means for one process step of `left` to match one process step
of `right`, and `Rel` lifts that choice to whole finite prefixes.
-/
def Rel {Party : Type u}
    {left right : Process Party}
    (rel :
      {pL : left.Proc} → {pR : right.Proc} →
        (left.step pL).spec.Transcript →
        (right.step pR).spec.Transcript →
        Prop) :
    {pL : left.Proc} → {pR : right.Proc} → {n : Nat} →
      Process.Prefix left pL n → Process.Prefix right pR n → Prop
  | _, _, _, .nil, .nil => True
  | _, _, _, .step trL tailL, .step trR tailR =>
      rel trL trR ∧ Rel rel tailL tailR

/-- Transporting both prefixes along equal start states does not change their
matching relation. -/
theorem rel_cast {Party : Type u}
    {left right : Process Party}
    (rel :
      {pL : left.Proc} → {pR : right.Proc} →
        (left.step pL).spec.Transcript →
        (right.step pR).spec.Transcript →
        Prop)
    {pL pL' : left.Proc} {pR pR' : right.Proc} {n : Nat}
    (hL : pL = pL') (hR : pR = pR')
    (leftPrefix : Process.Prefix left pL n)
    (rightPrefix : Process.Prefix right pR n) :
    Rel rel
      (cast (by cases hL; rfl) leftPrefix)
      (cast (by cases hR; rfl) rightPrefix) ↔
      Rel rel leftPrefix rightPrefix := by
  cases hL
  cases hR
  rfl

end Prefix

/--
`TranscriptRel left right` is a cross-process relation on one complete process
step transcript of `left` and one complete process step transcript of `right`.

This is the basic matching interface used later by refinement, equivalence, and
observation-preservation theorems.
-/
abbrev TranscriptRel {Party : Type u}
    (left right : Process Party) :=
  {pL : left.Proc} → {pR : right.Proc} →
    (left.step pL).spec.Transcript →
    (right.step pR).spec.Transcript →
    Prop

namespace TranscriptRel

/--
The permissive transcript relation that accepts every pair of transcripts.
-/
def top {Party : Type u} {left right : Process Party} :
    TranscriptRel left right :=
  fun _ _ => True

/--
Conjunction of transcript relations.

This is useful when one refinement should preserve several observational
features at once.
-/
def inter {Party : Type u} {left right : Process Party}
    (first second : TranscriptRel left right) :
    TranscriptRel left right :=
  fun trL trR => first trL trR ∧ second trL trR

/--
Match two transcripts by equality of their current controlling parties.
-/
def byController {Party : Type u} {left right : Process Party} :
    TranscriptRel left right :=
  fun {pL} {pR} trL trR =>
    (left.step pL).currentController? trL = (right.step pR).currentController? trR

/--
Match two transcripts by equality of their full controller paths.
-/
def byPath {Party : Type u} {left right : Process Party} :
    TranscriptRel left right :=
  fun {pL} {pR} trL trR =>
    (left.step pL).controllerPath trL = (right.step pR).controllerPath trR

/--
Match two transcripts by equality of stable external event labels.
-/
def byEvent {Party : Type u} {left right : Process Party}
    {Event : Type w}
    (eventL : left.EventMap Event) (eventR : right.EventMap Event) :
    TranscriptRel left right :=
  fun {pL} {pR} trL trR =>
    eventL pL trL = eventR pR trR

/--
Match two transcripts by equality of stable tickets.
-/
def byTicket {Party : Type u} {left right : Process Party}
    {Ticket : Type w}
    (ticketL : left.Tickets Ticket) (ticketR : right.Tickets Ticket) :
    TranscriptRel left right :=
  fun {pL} {pR} trL trR =>
    ticketL pL trL = ticketR pR trR

/-- Match two transcripts by equality of the packed local observations exposed
to one fixed party.

This is the relation that identifies executions that are observationally
indistinguishable to `me` at the step level.
-/
def byObservation {Party : Type u} [DecidableEq Party]
    {left right : Process Party} (me : Party) :
    TranscriptRel left right :=
  fun {pL} {pR} trL trR =>
    let obsL : List PackedObs := Step.obsList me (left.step pL) trL
    let obsR : List PackedObs := Step.obsList me (right.step pR) trR
    obsL = obsR

end TranscriptRel

namespace Prefix

/-- Matching by current controller equality preserves the extracted controller
sequence of finite prefixes. -/
theorem currentControllers_eq_of_relByController {Party : Type u}
    {left right : Process Party}
    {pL : left.Proc} {pR : right.Proc} {n : Nat}
    {leftPrefix : Process.Prefix left pL n}
    {rightPrefix : Process.Prefix right pR n}
    (hrel : Rel TranscriptRel.byController leftPrefix rightPrefix) :
    Process.Prefix.currentControllers leftPrefix =
      Process.Prefix.currentControllers rightPrefix := by
  revert pR rightPrefix
  induction leftPrefix with
  | nil =>
      intro pR rightPrefix
      cases rightPrefix
      intro _
      rfl
  | step trL tailL ih =>
      intro pR rightPrefix
      cases rightPrefix with
      | step trR tailR =>
          intro hrel
          rcases hrel with ⟨hHead, hTail⟩
          have hTail' : Rel TranscriptRel.byController tailL tailR := by
            simpa using hTail
          have hHead' :
              (left.step _).currentController? trL = (right.step _).currentController? trR := by
            simpa [TranscriptRel.byController] using hHead
          change (left.step _).currentController? trL ::
              Process.Prefix.currentControllers tailL =
            (right.step _).currentController? trR ::
              Process.Prefix.currentControllers tailR
          simp [hHead', ih hTail']

/-- Matching by controller-path equality preserves the extracted controller
path sequence of finite prefixes. -/
theorem controllerPaths_eq_of_relByPath {Party : Type u}
    {left right : Process Party}
    {pL : left.Proc} {pR : right.Proc} {n : Nat}
    {leftPrefix : Process.Prefix left pL n}
    {rightPrefix : Process.Prefix right pR n}
    (hrel : Rel TranscriptRel.byPath leftPrefix rightPrefix) :
    Process.Prefix.controllerPaths leftPrefix =
      Process.Prefix.controllerPaths rightPrefix := by
  revert pR rightPrefix
  induction leftPrefix with
  | nil =>
      intro pR rightPrefix
      cases rightPrefix
      intro _
      rfl
  | step trL tailL ih =>
      intro pR rightPrefix
      cases rightPrefix with
      | step trR tailR =>
          intro hrel
          rcases hrel with ⟨hHead, hTail⟩
          have hTail' : Rel TranscriptRel.byPath tailL tailR := by
            simpa using hTail
          have hHead' :
              (left.step _).controllerPath trL = (right.step _).controllerPath trR := by
            simpa [TranscriptRel.byPath] using hHead
          change (left.step _).controllerPath trL ::
              Process.Prefix.controllerPaths tailL =
            (right.step _).controllerPath trR ::
              Process.Prefix.controllerPaths tailR
          simp [hHead', ih hTail']

/-- Matching by stable event equality preserves the extracted event sequence of
finite prefixes. -/
theorem events_eq_of_relByEvent {Party : Type u}
    {left right : Process Party} {Event : Type w}
    (eventL : left.EventMap Event) (eventR : right.EventMap Event)
    {pL : left.Proc} {pR : right.Proc} {n : Nat}
    {leftPrefix : Process.Prefix left pL n}
    {rightPrefix : Process.Prefix right pR n}
    (hrel : Rel (TranscriptRel.byEvent eventL eventR) leftPrefix rightPrefix) :
    Process.Prefix.events eventL leftPrefix =
      Process.Prefix.events eventR rightPrefix := by
  revert pR rightPrefix
  induction leftPrefix with
  | nil =>
      intro pR rightPrefix
      cases rightPrefix
      intro _
      rfl
  | step trL tailL ih =>
      intro pR rightPrefix
      cases rightPrefix with
      | step trR tailR =>
          intro hrel
          rcases hrel with ⟨hHead, hTail⟩
          have hTail' : Rel (TranscriptRel.byEvent eventL eventR) tailL tailR := by
            simpa using hTail
          have hHead' : eventL _ trL = eventR _ trR := by
            simpa [TranscriptRel.byEvent] using hHead
          change eventL _ trL :: Process.Prefix.events eventL tailL =
            eventR _ trR :: Process.Prefix.events eventR tailR
          simp [hHead', ih hTail']

/-- Matching by stable ticket equality preserves the extracted ticket sequence
of finite prefixes. -/
theorem tickets_eq_of_relByTicket {Party : Type u}
    {left right : Process Party} {Ticket : Type w}
    (ticketL : left.Tickets Ticket) (ticketR : right.Tickets Ticket)
    {pL : left.Proc} {pR : right.Proc} {n : Nat}
    {leftPrefix : Process.Prefix left pL n}
    {rightPrefix : Process.Prefix right pR n}
    (hrel : Rel (TranscriptRel.byTicket ticketL ticketR) leftPrefix rightPrefix) :
    Process.Prefix.tickets ticketL leftPrefix =
      Process.Prefix.tickets ticketR rightPrefix := by
  revert pR rightPrefix
  induction leftPrefix with
  | nil =>
      intro pR rightPrefix
      cases rightPrefix
      intro _
      rfl
  | step trL tailL ih =>
      intro pR rightPrefix
      cases rightPrefix with
      | step trR tailR =>
          intro hrel
          rcases hrel with ⟨hHead, hTail⟩
          have hTail' : Rel (TranscriptRel.byTicket ticketL ticketR) tailL tailR := by
            simpa using hTail
          have hHead' : ticketL _ trL = ticketR _ trR := by
            simpa [TranscriptRel.byTicket] using hHead
          change ticketL _ trL :: Process.Prefix.tickets ticketL tailL =
            ticketR _ trR :: Process.Prefix.tickets ticketR tailR
          simp [hHead', ih hTail']

/-- Matching by local observation equality preserves the packed observation
sequence of finite prefixes for the chosen party. -/
theorem observations_eq_of_relByObservation {Party : Type u} [DecidableEq Party]
    (me : Party)
    {left right : Process Party}
    {pL : left.Proc} {pR : right.Proc} {n : Nat}
    {leftPrefix : Process.Prefix left pL n}
    {rightPrefix : Process.Prefix right pR n}
    (hrel : Rel (TranscriptRel.byObservation me) leftPrefix rightPrefix) :
    observations me leftPrefix = observations me rightPrefix := by
  revert pR rightPrefix
  induction leftPrefix with
  | nil =>
      intro pR rightPrefix
      cases rightPrefix
      intro _
      rfl
  | step trL tailL ih =>
      intro pR rightPrefix
      cases rightPrefix with
      | step trR tailR =>
          intro hrel
          rcases hrel with ⟨hHead, hTail⟩
          have hTail' : Rel (TranscriptRel.byObservation me) tailL tailR := by
            simpa using hTail
          have hHead' :
              Step.obsList me (left.step _) trL = Step.obsList me (right.step _) trR := by
            simpa [TranscriptRel.byObservation] using hHead
          change Step.obsList me (left.step _) trL :: observations me tailL =
            Step.obsList me (right.step _) trR :: observations me tailR
          simp [hHead', ih hTail']

end Prefix

namespace Run

/--
The per-step packed local observations exposed along the first `n` steps of the
run `run`.

This is the infinite-run analogue of `Prefix.observations`, truncated to the
first `n` steps.
-/
def observationsUpTo {Party : Type u} [DecidableEq Party]
    {process : Process Party} (me : Party)
    (run : Process.Run process) : Nat → List (List PackedObs)
  | 0 => []
  | n + 1 =>
      Step.obsList me (process.step (run.state 0)) (run.transcript 0) ::
        observationsUpTo me run.tail n

/--
`RelUpTo rel left right n` states that the first `n` executed steps of the
runs `left` and `right` match step-by-step according to `rel`.

This is the finite-prefix comparison predicate for runs.
-/
def RelUpTo {Party : Type u}
    {left right : Process Party}
    (rel : TranscriptRel left right)
    (leftRun : Process.Run left) (rightRun : Process.Run right) : Nat → Prop
  | 0 => True
  | n + 1 =>
      rel (leftRun.transcript 0) (rightRun.transcript 0) ∧
        RelUpTo rel leftRun.tail rightRun.tail n

/--
`Rel rel left right` states that every finite prefix of the runs `left` and
`right` matches according to `rel`.

So two runs are related when they remain indistinguishable at every finite
horizon under the chosen step-matching criterion.
-/
def Rel {Party : Type u}
    {left right : Process Party}
    (rel : TranscriptRel left right)
    (leftRun : Process.Run left) (rightRun : Process.Run right) : Prop :=
  ∀ n, RelUpTo rel leftRun rightRun n

/-- Pointwise transcript matching implies prefix matching of the first `n`
steps. -/
theorem relUpTo_of_pointwise {Party : Type u}
    {left right : Process Party}
    (rel : TranscriptRel left right)
    (leftRun : Process.Run left) (rightRun : Process.Run right)
    (hrel : ∀ n, rel (leftRun.transcript n) (rightRun.transcript n)) :
    ∀ n, RelUpTo rel leftRun rightRun n := by
  intro n
  induction n generalizing leftRun rightRun with
  | zero =>
      trivial
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · exact hrel 0
      · exact ih leftRun.tail rightRun.tail
          (by
            intro k
            simpa [Process.Run.tail] using hrel k.succ)

/-- Pointwise transcript matching implies full run matching. -/
theorem rel_of_pointwise {Party : Type u}
    {left right : Process Party}
    (rel : TranscriptRel left right)
    (leftRun : Process.Run left) (rightRun : Process.Run right)
    (hrel : ∀ n, rel (leftRun.transcript n) (rightRun.transcript n)) :
    Rel rel leftRun rightRun :=
  relUpTo_of_pointwise rel leftRun rightRun hrel

/-- Matching by current controller equality preserves the extracted controller
sequence of the first `n` run steps. -/
theorem currentControllersUpTo_eq_of_relUpTo_byController {Party : Type u}
    {left right : Process Party}
    (leftRun : Process.Run left) (rightRun : Process.Run right) {n : Nat}
    (hrel : RelUpTo TranscriptRel.byController leftRun rightRun n) :
    leftRun.currentControllersUpTo n = rightRun.currentControllersUpTo n := by
  induction n generalizing leftRun rightRun with
  | zero => rfl
  | succ n ih =>
      rcases hrel with ⟨hHead, hTail⟩
      have hHead' : leftRun.currentController? 0 = rightRun.currentController? 0 := by
        simpa [TranscriptRel.byController, Process.Run.currentController?] using hHead
      change leftRun.currentController? 0 :: leftRun.tail.currentControllersUpTo n =
        rightRun.currentController? 0 :: rightRun.tail.currentControllersUpTo n
      rw [hHead', ih leftRun.tail rightRun.tail hTail]

/-- Matching by controller-path equality preserves the extracted controller-path
sequence of the first `n` run steps. -/
theorem controllerPathsUpTo_eq_of_relUpTo_byPath {Party : Type u}
    {left right : Process Party}
    (leftRun : Process.Run left) (rightRun : Process.Run right) {n : Nat}
    (hrel : RelUpTo TranscriptRel.byPath leftRun rightRun n) :
    leftRun.controllerPathsUpTo n = rightRun.controllerPathsUpTo n := by
  induction n generalizing leftRun rightRun with
  | zero => rfl
  | succ n ih =>
      rcases hrel with ⟨hHead, hTail⟩
      have hHead' : leftRun.controllerPath 0 = rightRun.controllerPath 0 := by
        simpa [TranscriptRel.byPath, Process.Run.controllerPath] using hHead
      change leftRun.controllerPath 0 :: leftRun.tail.controllerPathsUpTo n =
        rightRun.controllerPath 0 :: rightRun.tail.controllerPathsUpTo n
      rw [hHead', ih leftRun.tail rightRun.tail hTail]

/-- Matching by stable event equality preserves the extracted event sequence of
the first `n` run steps. -/
theorem eventsUpTo_eq_of_relUpTo_byEvent {Party : Type u}
    {left right : Process Party} {Event : Type w}
    (eventL : left.EventMap Event) (eventR : right.EventMap Event)
    (leftRun : Process.Run left) (rightRun : Process.Run right) {n : Nat}
    (hrel : RelUpTo (TranscriptRel.byEvent eventL eventR) leftRun rightRun n) :
    leftRun.eventsUpTo eventL n = rightRun.eventsUpTo eventR n := by
  induction n generalizing leftRun rightRun with
  | zero => rfl
  | succ n ih =>
      rcases hrel with ⟨hHead, hTail⟩
      have hHead' : leftRun.event eventL 0 = rightRun.event eventR 0 := by
        simpa [TranscriptRel.byEvent, Process.Run.event] using hHead
      change leftRun.event eventL 0 :: leftRun.tail.eventsUpTo eventL n =
        rightRun.event eventR 0 :: rightRun.tail.eventsUpTo eventR n
      rw [hHead', ih leftRun.tail rightRun.tail hTail]

/-- Matching by stable ticket equality preserves the extracted ticket sequence
of the first `n` run steps. -/
theorem ticketsUpTo_eq_of_relUpTo_byTicket {Party : Type u}
    {left right : Process Party} {Ticket : Type w}
    (ticketL : left.Tickets Ticket) (ticketR : right.Tickets Ticket)
    (leftRun : Process.Run left) (rightRun : Process.Run right) {n : Nat}
    (hrel : RelUpTo (TranscriptRel.byTicket ticketL ticketR) leftRun rightRun n) :
    leftRun.ticketsUpTo ticketL n = rightRun.ticketsUpTo ticketR n := by
  induction n generalizing leftRun rightRun with
  | zero => rfl
  | succ n ih =>
      rcases hrel with ⟨hHead, hTail⟩
      have hHead' : leftRun.ticket ticketL 0 = rightRun.ticket ticketR 0 := by
        simpa [TranscriptRel.byTicket, Process.Run.ticket] using hHead
      change leftRun.ticket ticketL 0 :: leftRun.tail.ticketsUpTo ticketL n =
        rightRun.ticket ticketR 0 :: rightRun.tail.ticketsUpTo ticketR n
      rw [hHead', ih leftRun.tail rightRun.tail hTail]

/-- Matching by local observation equality preserves the packed observation
sequence of the first `n` run steps for the chosen party. -/
theorem observationsUpTo_eq_of_relUpTo_byObservation {Party : Type u}
    [DecidableEq Party] (me : Party)
    {left right : Process Party}
    (leftRun : Process.Run left) (rightRun : Process.Run right) {n : Nat}
    (hrel : RelUpTo (TranscriptRel.byObservation me) leftRun rightRun n) :
    observationsUpTo me leftRun n = observationsUpTo me rightRun n := by
  induction n generalizing leftRun rightRun with
  | zero => rfl
  | succ n ih =>
      rcases hrel with ⟨hHead, hTail⟩
      have hHead' :
          Step.obsList me (left.step (leftRun.state 0)) (leftRun.transcript 0) =
            Step.obsList me (right.step (rightRun.state 0)) (rightRun.transcript 0) := by
        simpa [TranscriptRel.byObservation] using hHead
      change
        Step.obsList me (left.step (leftRun.state 0)) (leftRun.transcript 0) ::
            observationsUpTo me leftRun.tail n =
          Step.obsList me (right.step (rightRun.state 0)) (rightRun.transcript 0) ::
            observationsUpTo me rightRun.tail n
      rw [hHead', ih leftRun.tail rightRun.tail hTail]

end Run

end Process
end Observation
end Concurrent
end Interaction
