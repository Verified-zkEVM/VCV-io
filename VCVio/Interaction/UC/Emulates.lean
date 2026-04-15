/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.OpenTheory

/-!
# Contextual emulation and UC security

This file defines the core judgments for Universally Composable (UC) security
at the abstract `OpenTheory` level.

## Main definitions

* `Emulates T real ideal ObsEq` says that the open system `real` *emulates*
  `ideal` in theory `T` whenever, for every valid plug (context), the
  resulting closed systems are observationally equivalent.

* `UCSecure T protocol ideal ObsEq SimSpace simulate` is the existential
  simulator variant: there exists a simulator that transforms any context so
  that the closed ideal system (with the simulated context) is observationally
  equivalent to the closed real system.

## Basic properties

* `Emulates.refl` and `Emulates.trans` follow immediately from the
  corresponding properties of the observation relation `ObsEq`.

* `Emulates.map_invariance` shows that adapting both sides of an emulation
  along the same boundary morphism preserves the emulation (requires a
  lawful theory).

* `Emulates.plug_invariance` shows that plugging both sides of an emulation
  with the same additional context preserves the emulation (requires a
  lawful theory).

## UC composition theorems

* `Emulates.par_compose`: parallel composition preserves emulation.
* `Emulates.wire_compose`: wired composition preserves emulation.
* `Emulates.plug_compose`: both protocol and environment emulation
  compose to yield observational equivalence of the closed systems.

These rely on structural factorization lemmas
(`close_par_left`, `close_par_right`, `close_wire_left`,
`close_wire_right`, `plug_comm`) that capture monoidal coherence
identities, derived from the `CompactClosed` axioms.
-/

universe u

namespace Interaction
namespace UC

variable {T : OpenTheory.{u}}

/--
`Emulates T real ideal ObsEq` asserts that `real` contextually emulates
`ideal` in the open-composition theory `T`.

For every plug `K : T.Plug Δ`, the closed compositions `T.close real K`
and `T.close ideal K` are related by `ObsEq`.

This is the definitional core of UC security: no environment can
distinguish `real` from `ideal`.
-/
structure Emulates
    {Δ : PortBoundary}
    (real ideal : T.Obj Δ)
    (ObsEq : T.Closed → T.Closed → Prop) : Prop where
  compare : ∀ K : T.Plug Δ, ObsEq (T.close real K) (T.close ideal K)

namespace Emulates

/--
Every open system emulates itself, provided the observation relation is
reflexive.
-/
theorem refl
    {Δ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    (hRefl : ∀ c, ObsEq c c)
    (W : T.Obj Δ) :
    Emulates W W ObsEq :=
  ⟨fun _ => hRefl _⟩

/--
Emulation composes transitively, provided the observation relation is
transitive.
-/
theorem trans
    {Δ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    (hTrans : ∀ a b c, ObsEq a b → ObsEq b c → ObsEq a c)
    {W₁ W₂ W₃ : T.Obj Δ}
    (h₁₂ : Emulates W₁ W₂ ObsEq)
    (h₂₃ : Emulates W₂ W₃ ObsEq) :
    Emulates W₁ W₃ ObsEq :=
  ⟨fun K => hTrans _ _ _ (h₁₂.compare K) (h₂₃.compare K)⟩

/--
Adapting both sides of an emulation along the same boundary morphism
preserves the emulation, provided the theory has lawful `map` and `plug`.

The key identity used is `plug (map f W) K = plug W (map (swap f) K)`,
which is the `map_plug` naturality law.
-/
theorem map_invariance
    [OpenTheory.IsLawfulPlug T]
    {Δ₁ Δ₂ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    (f : PortBoundary.Hom Δ₁ Δ₂)
    {real ideal : T.Obj Δ₁}
    (h : Emulates real ideal ObsEq) :
    Emulates (T.map f real) (T.map f ideal) ObsEq :=
  ⟨fun K => by
    simp only [OpenTheory.close,
      OpenTheory.map_plug f real K, OpenTheory.map_plug f ideal K]
    exact h.compare _⟩

/--
Plugging both sides of an emulation with the same additional context
preserves the emulation.

If `real` emulates `ideal` and we close both against the same plug `K`,
the resulting closed systems are still observationally equivalent. This is
immediate from the definition.
-/
theorem plug_invariance
    {Δ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    {real ideal : T.Obj Δ}
    (h : Emulates real ideal ObsEq)
    (K : T.Plug Δ) :
    ObsEq (T.close real K) (T.close ideal K) :=
  h.compare K

end Emulates

-- ============================================================================
-- § Structural factorization of `close` under composition
-- ============================================================================

section Factorization

variable [OpenTheory.CompactClosed T]

/-- The effective plug for the left component of a parallel composition.

Given `W₂ : T.Obj Δ₂` and `K : T.Plug (tensor Δ₁ Δ₂)`, wire them
together through the `Δ₂` boundary to obtain a plug for `Δ₁` alone. -/
def OpenTheory.parContextLeft
    {Δ₁ Δ₂ : PortBoundary} (W₂ : T.Obj Δ₂)
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.Plug Δ₁ :=
  T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁))
    (T.wire
      (Γ := PortBoundary.swap Δ₂)
      (Δ₂ := PortBoundary.empty)
      K
      (T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm W₂))

/-- The effective plug for the right component of a parallel composition.

Given `W₁ : T.Obj Δ₁` and `K : T.Plug (tensor Δ₁ Δ₂)`, wire them
together through the `Δ₁` boundary to obtain a plug for `Δ₂` alone. -/
def OpenTheory.parContextRight
    {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁)
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.Plug Δ₂ :=
  T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₂))
    (T.wire
      (Γ := PortBoundary.swap Δ₁)
      (Δ₂ := PortBoundary.empty)
      (T.mapEquiv
        (PortBoundary.Equiv.tensorComm
          (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂))
        K)
      (T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight Δ₁).symm W₁))

/-- Closing a parallel composition factors through the left component.

This captures the string-diagram identity: plugging `par W₁ W₂` against
`K` is the same as plugging `W₁` against the residual context formed by
wiring `W₂` into `K`. -/
theorem OpenTheory.close_par_left
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.close (T.par W₁ W₂) K = T.close W₁ (T.parContextLeft W₂ K) :=
  OpenTheory.plug_par_left W₁ W₂ K

/-- Closing a parallel composition factors through the right component. -/
theorem OpenTheory.close_par_right
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.close (T.par W₁ W₂) K = T.close W₂ (T.parContextRight W₁ K) := by
  simp only [OpenTheory.close]
  rw [← OpenTheory.par_comm W₂ W₁, OpenTheory.map_plug, OpenTheory.plug_par_left]
  unfold parContextRight
  simp only [OpenTheory.mapEquiv]
  congr 3

/-- The effective plug for the left factor of a wiring.

Given `W₂ : T.Obj (tensor (swap Γ) Δ₂)` and
`K : T.Plug (tensor Δ₁ Δ₂)`, wire them together through the `Δ₂`
boundary to obtain a plug for `tensor Δ₁ Γ`. -/
def OpenTheory.wireContextLeft
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.Plug (PortBoundary.tensor Δ₁ Γ) :=
  T.wire
    (Δ₁ := PortBoundary.swap Δ₁)
    (Γ := PortBoundary.swap Δ₂)
    (Δ₂ := PortBoundary.swap Γ)
    K
    (T.mapEquiv
      (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂)
      W₂)

/-- The effective plug for the right factor of a wiring.

Given `W₁ : T.Obj (tensor Δ₁ Γ)` and `K : T.Plug (tensor Δ₁ Δ₂)`,
wire them together through the `Δ₁` boundary to obtain a plug for
`tensor (swap Γ) Δ₂`. -/
def OpenTheory.wireContextRight
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.Plug (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) :=
  T.mapEquiv
    (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₂) Γ)
    (T.wire
      (Δ₁ := PortBoundary.swap Δ₂)
      (Γ := PortBoundary.swap Δ₁)
      (Δ₂ := Γ)
      (T.mapEquiv
        (PortBoundary.Equiv.tensorComm
          (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂))
        K)
      W₁)

/-- Closing a wired composition factors through the left component. -/
theorem OpenTheory.close_wire_left
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.close (T.wire W₁ W₂) K =
      T.close W₁ (T.wireContextLeft W₂ K) :=
  OpenTheory.plug_wire_left W₁ W₂ K

/-- Closing a wired composition factors through the right component. -/
theorem OpenTheory.close_wire_right
    {Δ₁ Γ Δ₂ : PortBoundary}
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.close (T.wire W₁ W₂) K =
      T.close W₂ (T.wireContextRight W₁ K) := by
  simp only [OpenTheory.close]
  rw [OpenTheory.wire_comm, OpenTheory.map_plug, OpenTheory.plug_wire_left,
    OpenTheory.map_plug]
  unfold wireContextRight
  simp only [OpenTheory.mapEquiv]
  congr 1
  congr 1
  rw [← OpenTheory.map_comp]
  erw [PortBoundary.Equiv.tensorComm_comp_tensorComm Δ₁ Γ, OpenTheory.map_id]
  rfl

/-- `plug` is symmetric: the protocol and context roles are interchangeable.

This follows from `plug_eq_wire` plus commutativity of `wire` via
`par_comm`. -/
theorem OpenTheory.plug_comm
    {Δ : PortBoundary}
    (W : T.Obj Δ) (K : T.Obj (PortBoundary.swap Δ)) :
    T.plug W K = T.plug K W := by
  rw [OpenTheory.plug_eq_wire W K, OpenTheory.plug_eq_wire K W,
    OpenTheory.wire_comm]
  congr 1
  simp only [OpenTheory.mapEquiv]
  rw [← OpenTheory.map_comp, ← OpenTheory.map_comp]
  have hcomm : (PortBoundary.Equiv.tensorComm
      PortBoundary.empty PortBoundary.empty).toHom =
      PortBoundary.Hom.id _ := by
    apply PortBoundary.Hom.ext <;>
      exact PFunctor.Chart.ext _ _
        (fun a => PEmpty.elim (Sum.elim id id a))
        (fun a => PEmpty.elim (Sum.elim id id a))
  rw [hcomm, OpenTheory.map_id]
  congr 1 <;> congr 1 <;> apply PortBoundary.Hom.ext
  all_goals
    exact PFunctor.Chart.ext _ _
      (fun a => by
        first
        | cases a with
          | inl x => first | exact PEmpty.elim x | rfl
          | inr x => first | exact PEmpty.elim x | rfl
        | rfl)
      (fun a => by
        first
        | cases a with
          | inl x => first | exact PEmpty.elim x | rfl
          | inr x => first | exact PEmpty.elim x | rfl
        | rfl)

end Factorization

-- ============================================================================
-- § UC composition theorems
-- ============================================================================

namespace Emulates

variable [OpenTheory.CompactClosed T]

/-- Replacing the left component of a parallel composition preserves
emulation, with the right component and environment held fixed. -/
theorem par_left
    {Δ₁ Δ₂ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    {real₁ ideal₁ : T.Obj Δ₁}
    (h₁ : Emulates real₁ ideal₁ ObsEq)
    (W₂ : T.Obj Δ₂) :
    Emulates (T.par real₁ W₂) (T.par ideal₁ W₂) ObsEq :=
  ⟨fun K => by
    rw [OpenTheory.close_par_left real₁ W₂ K,
        OpenTheory.close_par_left ideal₁ W₂ K]
    exact h₁.compare _⟩

/-- Replacing the right component of a parallel composition preserves
emulation, with the left component and environment held fixed. -/
theorem par_right
    {Δ₁ Δ₂ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    (W₁ : T.Obj Δ₁)
    {real₂ ideal₂ : T.Obj Δ₂}
    (h₂ : Emulates real₂ ideal₂ ObsEq) :
    Emulates (T.par W₁ real₂) (T.par W₁ ideal₂) ObsEq :=
  ⟨fun K => by
    rw [OpenTheory.close_par_right W₁ real₂ K,
        OpenTheory.close_par_right W₁ ideal₂ K]
    exact h₂.compare _⟩

/-- **UC composition theorem for `par`**: if each component emulates its
ideal, then their parallel composition emulates the parallel composition
of ideals.

The proof uses a hybrid argument through `T.par ideal₁ real₂`, with
each step reducing to emulation of a single component via
`close_par_left` / `close_par_right`. -/
theorem par_compose
    {Δ₁ Δ₂ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    (hTrans : ∀ a b c, ObsEq a b → ObsEq b c → ObsEq a c)
    {real₁ ideal₁ : T.Obj Δ₁} {real₂ ideal₂ : T.Obj Δ₂}
    (h₁ : Emulates real₁ ideal₁ ObsEq)
    (h₂ : Emulates real₂ ideal₂ ObsEq) :
    Emulates (T.par real₁ real₂) (T.par ideal₁ ideal₂) ObsEq :=
  Emulates.trans hTrans (par_left h₁ real₂) (par_right ideal₁ h₂)

/-- Replacing the left factor of a wiring preserves emulation. -/
theorem wire_left
    {Δ₁ Γ Δ₂ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    {real₁ ideal₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    (h₁ : Emulates real₁ ideal₁ ObsEq)
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    Emulates (T.wire real₁ W₂) (T.wire ideal₁ W₂) ObsEq :=
  ⟨fun K => by
    rw [OpenTheory.close_wire_left real₁ W₂ K,
        OpenTheory.close_wire_left ideal₁ W₂ K]
    exact h₁.compare _⟩

/-- Replacing the right factor of a wiring preserves emulation. -/
theorem wire_right
    {Δ₁ Γ Δ₂ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    {real₂ ideal₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₂ : Emulates real₂ ideal₂ ObsEq) :
    Emulates (T.wire W₁ real₂) (T.wire W₁ ideal₂) ObsEq :=
  ⟨fun K => by
    rw [OpenTheory.close_wire_right W₁ real₂ K,
        OpenTheory.close_wire_right W₁ ideal₂ K]
    exact h₂.compare _⟩

/-- **UC composition theorem for `wire`**: if each factor emulates its
ideal, then their wired composition emulates the wired ideal. -/
theorem wire_compose
    {Δ₁ Γ Δ₂ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    (hTrans : ∀ a b c, ObsEq a b → ObsEq b c → ObsEq a c)
    {real₁ ideal₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    {real₂ ideal₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₁ : Emulates real₁ ideal₁ ObsEq)
    (h₂ : Emulates real₂ ideal₂ ObsEq) :
    Emulates (T.wire real₁ real₂) (T.wire ideal₁ ideal₂) ObsEq :=
  Emulates.trans hTrans (wire_left h₁ real₂) (wire_right ideal₁ h₂)

/-- Replacing the plug (environment) while keeping the protocol fixed
preserves observational equivalence, using `plug_comm` to swap
the protocol/environment roles. -/
theorem plug_right
    {Δ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    (W : T.Obj Δ)
    {K₁ K₂ : T.Obj (PortBoundary.swap Δ)}
    (hK : Emulates K₁ K₂ ObsEq) :
    ObsEq (T.close W K₁) (T.close W K₂) := by
  simp only [OpenTheory.close, OpenTheory.plug_comm W K₁,
    OpenTheory.plug_comm W K₂]
  exact hK.compare W

/-- **UC composition theorem for `plug`**: if the protocol emulates its
ideal and the environment emulates its ideal, then the closed real-world
execution is observationally equivalent to the closed ideal-world
execution.

The proof uses a hybrid through `T.close ideal K_real`:
step 1 is `plug_invariance` (same environment, different protocol) and
step 2 is `plug_right` (same protocol, different environment). -/
theorem plug_compose
    {Δ : PortBoundary}
    {ObsEq : T.Closed → T.Closed → Prop}
    (hTrans : ∀ a b c, ObsEq a b → ObsEq b c → ObsEq a c)
    {real ideal : T.Obj Δ}
    {K_real K_ideal : T.Obj (PortBoundary.swap Δ)}
    (hProt : Emulates real ideal ObsEq)
    (hEnv : Emulates K_real K_ideal ObsEq) :
    ObsEq (T.close real K_real) (T.close ideal K_ideal) :=
  hTrans _ _ _
    (hProt.plug_invariance K_real)
    (plug_right ideal hEnv)

end Emulates

/--
`UCSecure T protocol ideal ObsEq SimSpace simulate` is the UC security
statement with an existential simulator.

There exists a simulator parameter `s : SimSpace` such that for every
context `K`, the closed real-world execution `T.close protocol K` is
observationally equivalent to the closed ideal-world execution
`T.close ideal (simulate s K)`.

The simulator `simulate s` transforms the context rather than the ideal
functionality, following the standard UC convention: the simulator acts as
a wrapper around the honest context to make the ideal world look like the
real world.
-/
def UCSecure
    {Δ : PortBoundary}
    (protocol ideal : T.Obj Δ)
    (ObsEq : T.Closed → T.Closed → Prop)
    (SimSpace : Type*) (simulate : SimSpace → T.Plug Δ → T.Plug Δ) : Prop :=
  ∃ s : SimSpace, ∀ K : T.Plug Δ,
    ObsEq (T.close protocol K) (T.close ideal (simulate s K))

/--
Emulation implies UC security with the trivial (identity) simulator.
-/
theorem Emulates.toUCSecure
    {Δ : PortBoundary}
    {protocol ideal : T.Obj Δ}
    {ObsEq : T.Closed → T.Closed → Prop}
    (h : Emulates protocol ideal ObsEq) :
    UCSecure protocol ideal ObsEq PUnit (fun _ K => K) :=
  ⟨⟨⟩, h.compare⟩

/--
UC security with identity simulation recovers emulation.
-/
theorem UCSecure.toEmulates_id
    {Δ : PortBoundary}
    {protocol ideal : T.Obj Δ}
    {ObsEq : T.Closed → T.Closed → Prop}
    (hSec : UCSecure protocol ideal ObsEq PUnit (fun _ K => K)) :
    Emulates protocol ideal ObsEq :=
  let ⟨_, h⟩ := hSec; ⟨h⟩

end UC
end Interaction
