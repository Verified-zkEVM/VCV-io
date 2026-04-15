/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Liveness
import VCVio.Interaction.Concurrent.Observation

/-!
# Forward refinement for dynamic concurrent processes

This file introduces the first process-level refinement notion for the dynamic
concurrent core.

The central object is `ForwardSimulation` between two `Process.System`s. It
captures the usual implementation/specification picture:

* implementation and specification states are related by a simulation
  invariant;
* every admissible implementation start state can be matched by some
  specification start state;
* every concrete implementation step can be simulated by a specification step;
* the simulation may additionally insist that the two steps agree on events,
  tickets, controller data, or local observations; and
* safety obligations may be transferred from the specification side back to the
  implementation side.

This gives a reusable refinement layer that is independent of any particular
concurrent frontend and rich enough to support observational reasoning, not
just state-reachability arguments.
-/

universe u v w w₂ w₃

namespace Interaction
namespace Concurrent
namespace Refinement

/--
`ForwardSimulation impl spec matchStep` is a forward simulation from the
implementation system `impl` to the specification system `spec`.

The meaning is:

* every initial implementation state is related to some initial specification
  state;
* assumptions are preserved from implementation to specification;
* every implementation step transcript can be matched by some specification
  step transcript satisfying `matchStep`;
* related safe specification states imply safe implementation states.

This is intentionally phrased over the dynamic `Process.System` core rather
than any particular concurrent frontend.

The parameter `matchStep` determines what behavioral information the
simulation preserves at each step. Choosing different transcript relations
recovers event-preserving, ticket-preserving, controller-preserving, or
observation-preserving refinements.
-/
structure ForwardSimulation
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    (impl : ProcessOver.System Γ)
    (spec : ProcessOver.System Δ)
    (matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess :=
        ProcessOver.TranscriptRel.top) where
  stateRel : impl.Proc → spec.Proc → Prop
  init :
    ∀ pImpl, impl.init pImpl →
      ∃ pSpec, spec.init pSpec ∧ stateRel pImpl pSpec
  assumptions :
    ∀ {pImpl pSpec}, stateRel pImpl pSpec →
      impl.assumptions pImpl → spec.assumptions pSpec
  step :
    ∀ {pImpl pSpec}, stateRel pImpl pSpec →
      ∀ trImpl : (impl.step pImpl).spec.Transcript,
        ∃ trSpec : (spec.step pSpec).spec.Transcript,
          matchStep trImpl trSpec ∧
            stateRel ((impl.step pImpl).next trImpl) ((spec.step pSpec).next trSpec)
  safe :
    ∀ {pImpl pSpec}, stateRel pImpl pSpec →
      spec.safe pSpec → impl.safe pImpl

namespace ForwardSimulation

/--
Choose the matching specification transcript for one implementation transcript.

This is the specification-side step selected by the simulation for the given
implementation step.
-/
noncomputable def matchTranscript
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    {pImpl pSpec : _}
    (hrel : sim.stateRel pImpl pSpec)
    (trImpl : (impl.step pImpl).spec.Transcript) :
    (spec.step pSpec).spec.Transcript :=
  Classical.choose (sim.step hrel trImpl)

/--
The chosen matching transcript satisfies `matchStep` and preserves the state
relation to the next residual states.
-/
theorem matchTranscript_spec
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    {pImpl pSpec : _}
    (hrel : sim.stateRel pImpl pSpec)
    (trImpl : (impl.step pImpl).spec.Transcript) :
    matchStep trImpl (sim.matchTranscript hrel trImpl) ∧
      sim.stateRel ((impl.step pImpl).next trImpl)
        ((spec.step pSpec).next (sim.matchTranscript hrel trImpl)) :=
  Classical.choose_spec (sim.step hrel trImpl)

/--
`matchedState sim run hrel n` is the specification-side state reached after
matching the first `n` steps of the implementation run `run`, starting from an
initial related specification state witnessed by `hrel`.

This is the fundamental state-transport construction behind run-level
refinement: it recursively follows the implementation run while using the
simulation to pick matching specification transcripts.
-/
noncomputable def matchedState
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : ProcessOver.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) :
    (n : Nat) → {qSpec : spec.Proc // sim.stateRel (run.state n) qSpec}
  | 0 => ⟨pSpec, by simpa [ProcessOver.Run.initial] using hrel⟩
  | n + 1 =>
      let prev := sim.matchedState run hrel n
      let trSpec := sim.matchTranscript prev.2 (run.transcript n)
      let hspec := sim.matchTranscript_spec prev.2 (run.transcript n)
      ⟨(spec.step prev.1).next trSpec, by
        dsimp [trSpec]
        rw [run.next_state n]
        exact hspec.2⟩

/--
The specification transcript chosen to match the `n`th implementation step of
the run `run`, relative to the initial related specification state witnessed by
`hrel`.

This is the stepwise witness used to build the whole matched specification run.
-/
noncomputable def matchedTranscript
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : ProcessOver.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec)
    (n : Nat) :
    (spec.step (sim.matchedState run hrel n).1).spec.Transcript :=
  sim.matchTranscript (sim.matchedState run hrel n).2 (run.transcript n)

/--
`mapRun sim run hrel` is the specification run obtained by recursively matching
every step of the implementation run `run`, starting from an initial related
specification state witnessed by `hrel`.

So `mapRun` turns a forward simulation into an execution-level translation from
implementation runs to matching specification runs.
-/
noncomputable def mapRun
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : ProcessOver.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) :
    ProcessOver.Run spec.toProcess where
  state n := (sim.matchedState run hrel n).1
  transcript n := sim.matchedTranscript run hrel n
  next_state _ := rfl

/--
At every step index `n`, the mapped specification run remains related to the
implementation run by `stateRel`.
-/
theorem stateRel_mapRun
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : ProcessOver.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) :
    ∀ n, sim.stateRel (run.state n) ((sim.mapRun run hrel).state n)
  | n => (sim.matchedState run hrel n).2

/--
At every step index `n`, the mapped specification transcript matches the
implementation transcript by `matchStep`.

This is the run-level form of the step-matching guarantee.
-/
theorem match_mapRun
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : ProcessOver.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) :
    ∀ n,
      matchStep (run.transcript n) ((sim.mapRun run hrel).transcript n)
  | n => (sim.matchTranscript_spec (sim.matchedState run hrel n).2 (run.transcript n)).1

/--
If every state along the mapped specification run is safe, then every state
along the implementation run is safe.

This is the basic safety-transport principle of forward simulation.
-/
theorem safe_of_mapRun
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : ProcessOver.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec)
    (hsafe :
      ∀ n, spec.safe ((sim.mapRun run hrel).state n)) :
    ∀ n, impl.safe (run.state n)
  | n => sim.safe (sim.stateRel_mapRun run hrel n) (hsafe n)

/--
If an implementation run is admissible, then its mapped specification run is
also admissible.

So ambient assumptions are preserved along the run translation induced by the
simulation.
-/
theorem admissible_mapRun
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : ProcessOver.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec)
    (hadm : ProcessOver.System.Admissible impl run) :
    ProcessOver.System.Admissible spec (sim.mapRun run hrel) :=
  fun n => sim.assumptions (sim.stateRel_mapRun run hrel n) (hadm n)

/-- The first `n` steps of the mapped specification run match the first `n`
implementation steps according to `matchStep`. -/
theorem prefixRel_mapRun
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : ProcessOver.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) :
    ∀ n, ProcessOver.Run.RelUpTo matchStep run (sim.mapRun run hrel) n :=
  ProcessOver.Run.relUpTo_of_pointwise matchStep run (sim.mapRun run hrel)
    (sim.match_mapRun run hrel)

/-- The mapped specification run matches the implementation run at every finite
prefix according to `matchStep`. -/
theorem runRel_mapRun
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : ProcessOver.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) :
    ProcessOver.Run.Rel matchStep run (sim.mapRun run hrel) :=
  ProcessOver.Run.rel_of_pointwise matchStep run (sim.mapRun run hrel)
    (sim.match_mapRun run hrel)

/-- A controller-preserving simulation preserves the current controller sequence
of every finite run prefix. -/
theorem currentControllersUpTo_mapRun {Party : Type u}
    {impl spec : Process.System Party}
    (sim : ForwardSimulation impl spec Observation.Process.TranscriptRel.byController)
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) (n : Nat) :
    Process.Run.currentControllersUpTo run n =
      Process.Run.currentControllersUpTo (sim.mapRun run hrel) n :=
  Observation.Process.Run.currentControllersUpTo_eq_of_relUpTo_byController
    run (sim.mapRun run hrel)
    (Observation.Process.Run.relUpTo_of_pointwise
      Observation.Process.TranscriptRel.byController
      run (sim.mapRun run hrel) (sim.match_mapRun run hrel) n)

/-- A controller-path-preserving simulation preserves the controller-path
sequence of every finite run prefix. -/
theorem controllerPathsUpTo_mapRun {Party : Type u}
    {impl spec : Process.System Party}
    (sim : ForwardSimulation impl spec Observation.Process.TranscriptRel.byPath)
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) (n : Nat) :
    Process.Run.controllerPathsUpTo run n =
      Process.Run.controllerPathsUpTo (sim.mapRun run hrel) n :=
  Observation.Process.Run.controllerPathsUpTo_eq_of_relUpTo_byPath
    run (sim.mapRun run hrel)
    (Observation.Process.Run.relUpTo_of_pointwise
      Observation.Process.TranscriptRel.byPath
      run (sim.mapRun run hrel) (sim.match_mapRun run hrel) n)

/-- An event-preserving simulation preserves the stable event sequence of every
finite run prefix. -/
theorem eventsUpTo_mapRun {Party : Type u}
    {impl spec : Process.System Party} {Event : Type w}
    {eventImpl : impl.toProcess.EventMap Event}
    {eventSpec : spec.toProcess.EventMap Event}
    (sim : ForwardSimulation impl spec
      (Observation.Process.TranscriptRel.byEvent eventImpl eventSpec))
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) (n : Nat) :
    Process.Run.eventsUpTo eventImpl run n =
      Process.Run.eventsUpTo eventSpec (sim.mapRun run hrel) n :=
  Observation.Process.Run.eventsUpTo_eq_of_relUpTo_byEvent
    eventImpl eventSpec run (sim.mapRun run hrel)
    (Observation.Process.Run.relUpTo_of_pointwise
      (Observation.Process.TranscriptRel.byEvent eventImpl eventSpec)
      run (sim.mapRun run hrel) (sim.match_mapRun run hrel) n)

/-- A ticket-preserving simulation preserves the stable ticket sequence of every
finite run prefix. -/
theorem ticketsUpTo_mapRun {Party : Type u}
    {impl spec : Process.System Party} {Ticket : Type w}
    {ticketImpl : impl.toProcess.Tickets Ticket}
    {ticketSpec : spec.toProcess.Tickets Ticket}
    (sim : ForwardSimulation impl spec
      (Observation.Process.TranscriptRel.byTicket ticketImpl ticketSpec))
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) (n : Nat) :
    Process.Run.ticketsUpTo ticketImpl run n =
      Process.Run.ticketsUpTo ticketSpec (sim.mapRun run hrel) n :=
  Observation.Process.Run.ticketsUpTo_eq_of_relUpTo_byTicket
    ticketImpl ticketSpec run (sim.mapRun run hrel)
    (Observation.Process.Run.relUpTo_of_pointwise
      (Observation.Process.TranscriptRel.byTicket ticketImpl ticketSpec)
      run (sim.mapRun run hrel) (sim.match_mapRun run hrel) n)

/-- An observation-preserving simulation preserves one party's packed
observations of every finite run prefix. -/
theorem observationsUpTo_mapRun {Party : Type u} [DecidableEq Party]
    (me : Party)
    {impl spec : Process.System Party}
    (sim : ForwardSimulation impl spec
      (Observation.Process.TranscriptRel.byObservation me))
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) (n : Nat) :
    Observation.Process.Run.observationsUpTo me run n =
      Observation.Process.Run.observationsUpTo me (sim.mapRun run hrel) n :=
  Observation.Process.Run.observationsUpTo_eq_of_relUpTo_byObservation
    me run (sim.mapRun run hrel)
    (Observation.Process.Run.relUpTo_of_pointwise
      (Observation.Process.TranscriptRel.byObservation me)
      run (sim.mapRun run hrel) (sim.match_mapRun run hrel) n)

/--
If the specification system satisfies safety under some fairness assumption,
then the implementation system also satisfies safety under any implementation
fairness assumption that transfers along the simulation.

This is the top-level preservation theorem: once fairness is known to transfer,
forward simulation lets one discharge implementation-side safety obligations by
proving them on the specification side.
-/
theorem safe_of_satisfies
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {Δ : Interaction.Spec.Node.Context.{w, w₃}}
    {impl : ProcessOver.System Γ} {spec : ProcessOver.System Δ}
    {matchStep :
      ProcessOver.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (fairImpl : ProcessOver.Run.Pred impl.toProcess)
    (fairSpec : ProcessOver.Run.Pred spec.toProcess)
    (hfair :
      ∀ (run : ProcessOver.Run impl.toProcess) {pSpec : spec.Proc},
        (hrel : sim.stateRel run.initial pSpec) →
          fairImpl run → fairSpec (sim.mapRun run hrel))
    (hspec : ProcessOver.System.Satisfies spec fairSpec (ProcessOver.System.Safe spec)) :
    ProcessOver.System.Satisfies impl fairImpl (ProcessOver.System.Safe impl) := by
  intro run hInit hAdm hFair
  rcases sim.init run.initial hInit with ⟨pSpec, hInitSpec, hrel⟩
  have hAdmSpec : ProcessOver.System.Admissible spec (sim.mapRun run hrel) :=
    sim.admissible_mapRun run hrel hAdm
  have hSafeSpec : ProcessOver.System.Safe spec (sim.mapRun run hrel) :=
    hspec (sim.mapRun run hrel) hInitSpec hAdmSpec (hfair run hrel hFair)
  exact sim.safe_of_mapRun run hrel hSafeSpec

end ForwardSimulation

end Refinement
end Concurrent
end Interaction
