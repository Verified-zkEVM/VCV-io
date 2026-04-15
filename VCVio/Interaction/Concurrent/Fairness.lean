/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Run

/-!
# Fairness of dynamic concurrent runs

This file adds the first fairness layer on top of `Concurrent.ProcessOver.Run`.

The key design choice is that fairness is phrased in terms of stable
`Tickets`, not raw frontier events. This matters because the concrete event
type available at one residual process state need not even be comparable with
the event type at a later state, while a ticket is meant to name the same
scheduling obligation across time and across different presentations of the
same protocol.

The closed-world `Process` API is recovered as a specialization of these
generic definitions.
-/

universe u v w w₂ w₃

namespace Interaction
namespace Concurrent

namespace ProcessOver
namespace Run

/-- `Always P` means that the temporal property `P` holds at every time
index. -/
def Always (P : Nat → Prop) : Prop := ∀ n, P n

/-- `Eventually P` means that `P` holds at some time index. -/
def Eventually (P : Nat → Prop) : Prop := ∃ n, P n

/-- `EventuallyAlways P` means that from some time onward, `P` keeps holding
forever. -/
def EventuallyAlways (P : Nat → Prop) : Prop :=
  ∃ N, ∀ n, N ≤ n → P n

/-- `InfinitelyOften P` means that `P` holds at arbitrarily late time
indices. -/
def InfinitelyOften (P : Nat → Prop) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ P n

theorem always_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    Always P → Always Q := by
  intro hP n
  exact himp n (hP n)

theorem eventually_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    Eventually P → Eventually Q := by
  rintro ⟨n, hP⟩
  exact ⟨n, himp n hP⟩

theorem eventuallyAlways_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    EventuallyAlways P → EventuallyAlways Q := by
  rintro ⟨N, hP⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact himp n (hP n hn)

theorem infinitelyOften_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    InfinitelyOften P → InfinitelyOften Q := by
  intro hP N
  rcases hP N with ⟨n, hn, hPn⟩
  exact ⟨n, hn, himp n hPn⟩

end Run

namespace Ticketed

/--
`enabledAt ticketed run ticket n` means that at time `n`, there exists some
complete transcript of the current process step whose stable ticket is
`ticket`.
-/
def enabledAt
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (ticketed : ProcessOver.Ticketed Γ)
    (run : ProcessOver.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) (n : Nat) : Prop :=
  ∃ tr : (ticketed.toProcess.step (run.state n)).spec.Transcript,
    ticketed.ticket (run.state n) tr = ticket

/--
`firedAt ticketed run ticket n` means that the actual transcript chosen by the
run at time `n` has stable ticket `ticket`.
-/
def firedAt
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (ticketed : ProcessOver.Ticketed Γ)
    (run : ProcessOver.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) (n : Nat) : Prop :=
  ticketed.ticket (run.state n) (run.transcript n) = ticket

/--
Weak fairness for one ticket:
if the ticket is continuously enabled from some point onward, then it fires
infinitely often.
-/
def WeakFairOn
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (ticketed : ProcessOver.Ticketed Γ)
    (run : ProcessOver.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) : Prop :=
  ProcessOver.Run.EventuallyAlways (enabledAt ticketed run ticket) →
    ProcessOver.Run.InfinitelyOften (firedAt ticketed run ticket)

/--
Strong fairness for one ticket:
if the ticket is enabled infinitely often, then it is fired infinitely often.
-/
def StrongFairOn
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (ticketed : ProcessOver.Ticketed Γ)
    (run : ProcessOver.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) : Prop :=
  ProcessOver.Run.InfinitelyOften (enabledAt ticketed run ticket) →
    ProcessOver.Run.InfinitelyOften (firedAt ticketed run ticket)

/-- A run is weakly fair when every ticket is weakly fair. -/
def WeakFair
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (ticketed : ProcessOver.Ticketed Γ)
    (run : ProcessOver.Run ticketed.toProcess) : Prop :=
  ∀ ticket, WeakFairOn ticketed run ticket

/-- A run is strongly fair when every ticket is strongly fair. -/
def StrongFair
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (ticketed : ProcessOver.Ticketed Γ)
    (run : ProcessOver.Run ticketed.toProcess) : Prop :=
  ∀ ticket, StrongFairOn ticketed run ticket

/--
The actually fired ticket at time `n` is always enabled at time `n`.
-/
theorem fired_implies_enabled
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (ticketed : ProcessOver.Ticketed Γ)
    (run : ProcessOver.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) (n : Nat) :
    firedAt ticketed run ticket n → enabledAt ticketed run ticket n := by
  intro hfired
  exact ⟨run.transcript n, hfired⟩

end Ticketed
end ProcessOver

namespace Process
namespace Run

/-- The closed-world specialization of `Always`. -/
abbrev Always := ProcessOver.Run.Always

/-- The closed-world specialization of `Eventually`. -/
abbrev Eventually := ProcessOver.Run.Eventually

/-- The closed-world specialization of `EventuallyAlways`. -/
abbrev EventuallyAlways := ProcessOver.Run.EventuallyAlways

/-- The closed-world specialization of `InfinitelyOften`. -/
abbrev InfinitelyOften := ProcessOver.Run.InfinitelyOften

theorem always_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    Always P → Always Q :=
  ProcessOver.Run.always_mono himp

theorem eventually_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    Eventually P → Eventually Q :=
  ProcessOver.Run.eventually_mono himp

theorem eventuallyAlways_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    EventuallyAlways P → EventuallyAlways Q :=
  ProcessOver.Run.eventuallyAlways_mono himp

theorem infinitelyOften_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    InfinitelyOften P → InfinitelyOften Q :=
  ProcessOver.Run.infinitelyOften_mono himp

end Run

namespace Ticketed

/-- The closed-world specialization of `enabledAt`. -/
abbrev enabledAt {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) (n : Nat) : Prop :=
  ProcessOver.Ticketed.enabledAt ticketed run ticket n

/-- The closed-world specialization of `firedAt`. -/
abbrev firedAt {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) (n : Nat) : Prop :=
  ProcessOver.Ticketed.firedAt ticketed run ticket n

/-- The closed-world specialization of weak fairness for one ticket. -/
abbrev WeakFairOn {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) : Prop :=
  ProcessOver.Ticketed.WeakFairOn ticketed run ticket

/-- The closed-world specialization of strong fairness for one ticket. -/
abbrev StrongFairOn {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) : Prop :=
  ProcessOver.Ticketed.StrongFairOn ticketed run ticket

/-- The closed-world specialization of weak fairness. -/
abbrev WeakFair {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess) : Prop :=
  ProcessOver.Ticketed.WeakFair ticketed run

/-- The closed-world specialization of strong fairness. -/
abbrev StrongFair {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess) : Prop :=
  ProcessOver.Ticketed.StrongFair ticketed run

theorem fired_implies_enabled {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) (n : Nat) :
    firedAt ticketed run ticket n → enabledAt ticketed run ticket n :=
  ProcessOver.Ticketed.fired_implies_enabled ticketed run ticket n

end Ticketed
end Process

end Concurrent
end Interaction
