/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Fairness

/-!
# Safety and liveness predicates over concurrent runs

This file packages the semantic notions of safety and liveness that sit on top
of runs and fairness.

The goal is deliberately modest and foundational. Rather than introducing a
full temporal-logic syntax, the file defines:

* run predicates and state predicates;
* the basic temporal lifts of a state predicate along a run;
* admissibility, safety, and initiality for `ProcessOver.System`; and
* what it means for a system to satisfy a run property under a chosen fairness
  assumption.

The closed-world `Process` API is recovered as a specialization of these
generic definitions.
-/

universe u v w w₂

namespace Interaction
namespace Concurrent

namespace ProcessOver
namespace Run

/-- `Pred process` is the type of semantic properties of whole runs of
`process`. -/
abbrev Pred
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver Γ) :=
  ProcessOver.Run process → Prop

/-- `StatePred process` is the type of predicates on residual process
states. -/
abbrev StatePred
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver Γ) :=
  process.Proc → Prop

/-- `AlwaysState P run` means that the state predicate `P` holds at every state
of the run `run`. -/
def AlwaysState
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (P : StatePred process) (run : ProcessOver.Run process) : Prop :=
  ∀ n, P (run.state n)

/--
`EventuallyState P run` means that the run eventually reaches a state
satisfying `P`.
-/
def EventuallyState
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (P : StatePred process) (run : ProcessOver.Run process) : Prop :=
  ∃ n, P (run.state n)

/-- `InfinitelyOftenState P run` means that `P` holds at arbitrarily late
states of `run`. -/
def InfinitelyOftenState
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    (P : StatePred process) (run : ProcessOver.Run process) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ P (run.state n)

/-- Monotonicity of `AlwaysState`. -/
theorem alwaysState_mono
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : ProcessOver.Run process}, AlwaysState P run → AlwaysState Q run := by
  intro run hP n
  exact himp _ (hP n)

/-- Monotonicity of `EventuallyState`. -/
theorem eventuallyState_mono
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : ProcessOver.Run process}, EventuallyState P run → EventuallyState Q run := by
  rintro run ⟨n, hP⟩
  exact ⟨n, himp _ hP⟩

/-- Monotonicity of `InfinitelyOftenState`. -/
theorem infinitelyOftenState_mono
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    {process : ProcessOver Γ}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : ProcessOver.Run process},
      InfinitelyOftenState P run → InfinitelyOftenState Q run := by
  intro run hP N
  rcases hP N with ⟨n, hn, hPn⟩
  exact ⟨n, hn, himp _ hPn⟩

end Run

namespace System

/-- A run of `system` is admissible when the ambient assumptions hold at every
state along the run. -/
def Admissible
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (system : ProcessOver.System Γ)
    (run : ProcessOver.Run system.toProcess) : Prop :=
  ProcessOver.Run.AlwaysState system.assumptions run

/-- A run of `system` is safe when the safety predicate holds at every state
along the run. -/
def Safe
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (system : ProcessOver.System Γ)
    (run : ProcessOver.Run system.toProcess) : Prop :=
  ProcessOver.Run.AlwaysState system.safe run

/-- A run starts from an initial state when its first residual process state
satisfies `system.init`. -/
def Initial
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (system : ProcessOver.System Γ)
    (run : ProcessOver.Run system.toProcess) : Prop :=
  system.init run.initial

/--
`Satisfies system fairness property` means:
every initial admissible run of `system` that satisfies the fairness
assumption `fairness` also satisfies the run property `property`.
-/
def Satisfies
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (system : ProcessOver.System Γ)
    (fairness property : ProcessOver.Run.Pred system.toProcess) : Prop :=
  ∀ run : ProcessOver.Run system.toProcess,
    Initial system run →
      Admissible system run →
        fairness run →
          property run

/--
If a run is safe and every safe state satisfies `P`, then `P` holds at every
state along the run.
-/
theorem alwaysState_of_safe
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (system : ProcessOver.System Γ)
    {P : ProcessOver.Run.StatePred system.toProcess}
    (himp : ∀ p, system.safe p → P p) :
    ∀ {run : ProcessOver.Run system.toProcess},
      Safe system run → ProcessOver.Run.AlwaysState P run := by
  intro run hsafe n
  exact himp _ (hsafe n)

end System

end ProcessOver

namespace Process
namespace Run

/-- The closed-world specialization of `ProcessOver.Run.Pred`. -/
abbrev Pred {Party : Type u} (process : Process Party) :=
  ProcessOver.Run.Pred process

/-- The closed-world specialization of `ProcessOver.Run.StatePred`. -/
abbrev StatePred {Party : Type u} (process : Process Party) :=
  ProcessOver.Run.StatePred process

/-- `AlwaysState` for closed-world runs. -/
abbrev AlwaysState {Party : Type u} {process : Process Party}
    (P : StatePred process) (run : Process.Run process) : Prop :=
  ProcessOver.Run.AlwaysState P run

/-- `EventuallyState` for closed-world runs. -/
abbrev EventuallyState {Party : Type u} {process : Process Party}
    (P : StatePred process) (run : Process.Run process) : Prop :=
  ProcessOver.Run.EventuallyState P run

/-- `InfinitelyOftenState` for closed-world runs. -/
abbrev InfinitelyOftenState {Party : Type u} {process : Process Party}
    (P : StatePred process) (run : Process.Run process) : Prop :=
  ProcessOver.Run.InfinitelyOftenState P run

theorem alwaysState_mono {Party : Type u} {process : Process Party}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : Process.Run process}, AlwaysState P run → AlwaysState Q run :=
  ProcessOver.Run.alwaysState_mono himp

theorem eventuallyState_mono {Party : Type u} {process : Process Party}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : Process.Run process}, EventuallyState P run → EventuallyState Q run :=
  ProcessOver.Run.eventuallyState_mono himp

theorem infinitelyOftenState_mono {Party : Type u} {process : Process Party}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : Process.Run process},
      InfinitelyOftenState P run → InfinitelyOftenState Q run :=
  ProcessOver.Run.infinitelyOftenState_mono himp

end Run

namespace System

/-- The closed-world specialization of run admissibility. -/
abbrev Admissible {Party : Type u} (system : Process.System Party)
    (run : Process.Run system.toProcess) : Prop :=
  ProcessOver.System.Admissible system run

/-- The closed-world specialization of run safety. -/
abbrev Safe {Party : Type u} (system : Process.System Party)
    (run : Process.Run system.toProcess) : Prop :=
  ProcessOver.System.Safe system run

/-- The closed-world specialization of initiality. -/
abbrev Initial {Party : Type u} (system : Process.System Party)
    (run : Process.Run system.toProcess) : Prop :=
  ProcessOver.System.Initial system run

/-- The closed-world specialization of semantic satisfaction under fairness. -/
abbrev Satisfies {Party : Type u} (system : Process.System Party)
    (fairness property : Process.Run.Pred system.toProcess) : Prop :=
  ProcessOver.System.Satisfies system fairness property

theorem alwaysState_of_safe {Party : Type u} (system : Process.System Party)
    {P : Process.Run.StatePred system.toProcess}
    (himp : ∀ p, system.safe p → P p) :
    ∀ {run : Process.Run system.toProcess},
      Safe system run → Process.Run.AlwaysState P run :=
  ProcessOver.System.alwaysState_of_safe system himp

end System

end Process

end Concurrent
end Interaction
