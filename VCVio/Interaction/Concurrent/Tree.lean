/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Current
import VCVio.Interaction.Concurrent.Execution

/-!
# Structural-tree frontend for dynamic processes

This file turns the structural concurrent syntax into a frontend for the
dynamic `Concurrent.Process` core.

The present frontend keeps one important design choice from the original
structural execution story: one process step corresponds to exactly one
scheduled structural frontier event. The dynamic process step therefore uses a
single move type `Front S`, but its node semantics record:

* the full controller path `Control.controllers control event` associated to
  each chosen frontier event `event`; and
* the current local view `Current.view me control profile` of that same
  frontier event for each party `me`.

So the structural tree language remains an important source language, but the
dynamic process core is now the semantic center.
-/

universe u

namespace Interaction
namespace Concurrent
namespace Tree

/--
`State Party` is one structural concurrent residual state packaged together
with its control tree and observation profile.

This is the exact structural data needed to view the current tree as one state
of a dynamic `Concurrent.Process`.
-/
structure State (Party : Type u) where
  spec : Concurrent.Spec
  control : Control Party spec
  profile : Profile Party spec

namespace State

/--
`currentStep st` is the one-step process view of the structural residual state
`st`.

Its move type is the current structural frontier `Front st.spec`. The
controller-path contribution of each move is exactly
`Control.controllers st.control`, and the local view of that move is exactly
`Current.view me st.control st.profile`.
-/
def currentStep {Party : Type u} [DecidableEq Party] (st : State Party) :
    Step Party (State Party) :=
  { spec := .node (Front st.spec) (fun _ => .done)
    semantics :=
      ⟨{ controllers := Control.controllers st.control
         views := fun me => Current.view me st.control st.profile },
        fun _ => PUnit.unit⟩
    next := fun
      | ⟨event, _⟩ =>
          { spec := residual event
            control := Control.residual st.control event
            profile := Profile.residual st.profile event } }

/--
`eventOfTranscript st tr` forgets the trivial `done` tail of the process step
transcript and recovers the scheduled structural frontier event.
-/
def eventOfTranscript {Party : Type u} [DecidableEq Party] (st : State Party) :
    Interaction.Spec.Transcript st.currentStep.spec → Front st.spec
  | ⟨event, _⟩ => event

/--
`transcriptOfEvent st event` re-expresses a structural frontier event as the
corresponding one-step process transcript.
-/
def transcriptOfEvent {Party : Type u} [DecidableEq Party] (st : State Party) :
    Front st.spec → Interaction.Spec.Transcript st.currentStep.spec
  | event => ⟨event, PUnit.unit⟩

end State

/--
`toProcess` compiles the structural concurrent-tree frontend into the dynamic
`Concurrent.Process` core.

Each process state is one packaged structural residual state, and each process
step is the current frontier interaction produced by `State.currentStep`.
-/
def toProcess {Party : Type u} [DecidableEq Party] : Process Party where
  Proc := State Party
  step := State.currentStep

/-- Package one structural residual state as the initial state of the tree
frontend process. -/
def init {Party : Type u} {spec : Concurrent.Spec}
    (control : Control Party spec) (profile : Profile Party spec) : State Party :=
  { spec := spec, control := control, profile := profile }

/--
`ofLinearization control profile trace` converts a structural frontier trace
into the corresponding dynamic process execution trace of `Tree.toProcess`.
-/
def ofLinearization {Party : Type u} [DecidableEq Party] :
    {spec : Concurrent.Spec} →
      (control : Control Party spec) →
      (profile : Profile Party spec) →
      Concurrent.Trace spec →
      Process.Trace (toProcess (Party := Party)) (init control profile)
  | _, control, profile, .done h =>
      .done (fun tr => h ((init control profile).eventOfTranscript tr))
  | _, control, profile, .step event tail =>
      .step
        ((init control profile).transcriptOfEvent event)
        (ofLinearization (Control.residual control event) (Profile.residual profile event) tail)

end Tree
end Concurrent
end Interaction
