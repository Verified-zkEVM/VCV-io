/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.Interaction.UC.OpenTheory

/-!
# Contextual emulation and UC security

This file defines the core judgments for Universally Composable (UC) security
at the abstract `OpenTheory` level.

## Main definitions

* `Observation T` bundles a binary relation on closed systems together with a
  proof that it is an equivalence relation. UC judgments are parameterized
  uniformly over `Observation T` so that reflexivity, symmetry, and
  transitivity are always available without per-call hypotheses.

* `Emulates real ideal Obs` says that the open system `real` *emulates*
  `ideal` whenever, for every valid plug (context), the resulting closed
  systems are related by `Obs.rel`.

* `UCSecure protocol ideal Obs SimSpace simulate` is the existential simulator
  variant: there exists a simulator that transforms any context so that the
  closed ideal system (with the simulated context) is `Obs.rel`-related to
  the closed real system.

The canonical `Observation.eq T` instantiates the framework with perfect
syntactic equality on closed systems; downstream layers (e.g. open process
isos, asymptotic computational indistinguishability) supply their own
`Observation` constructors.

## Basic properties

* `Emulates.refl` and `Emulates.trans` are immediate consequences of the
  bundled `Equivalence` proof in `Observation`.

* `Emulates.map_invariance` shows that adapting both sides of an emulation
  along the same boundary morphism preserves the emulation (requires a
  lawful theory).

* `Emulates.plug_invariance` shows that plugging both sides of an emulation
  with the same additional context preserves the emulation.

## UC composition theorems

* `Emulates.par_compose`: parallel composition preserves emulation.
* `Emulates.wire_compose`: wired composition preserves emulation.
* `Emulates.plug_compose`: both protocol and environment emulation
  compose to yield observational equivalence of the closed systems.

These rely on structural factorization lemmas
(`close_par_left`, `close_par_right`, `close_wire_left`,
`close_wire_right`, `plug_comm`) that capture monoidal coherence
identities, derived from the `CompactClosed` axioms.

## Design note: why `Observation` requires a full `Equivalence`

Bundling the equivalence proof into `Observation` lets every UC theorem
quantify over a single parameter `Obs : Observation T` rather than threading
a relation plus separate `hRefl`/`hTrans`/`hSymm` hypotheses. The cost is
that observation relations which are *not* equivalences (e.g. the fixed-`ε`
computational distinguishability relation
`fun c₁ c₂ => distAdvantage (sem c₁) (sem c₂) ≤ ε`, which fails transitivity
because the triangle inequality only gives `2ε`) cannot be packaged as
`Observation T`. The intended bridge from computational security to abstract
`Emulates` therefore lives at the asymptotic level (where negligible
distance is closed under sums and is a genuine equivalence), not at the
fixed-`ε` level.
-/

universe u

namespace Interaction
namespace UC

variable {T : OpenTheory.{u}}

/--
`Observation T` bundles a binary relation on the closed systems of an open
theory `T` together with a proof that it is an equivalence relation.

This is the parameter slot through which different security flavors
(perfect, statistical, asymptotic computational) plug into the abstract UC
judgments `Emulates` and `UCSecure`.
-/
structure Observation (T : OpenTheory.{u}) where
  /-- The underlying binary relation on closed systems. -/
  rel : T.Closed → T.Closed → Prop
  /-- The relation is an equivalence (reflexive, symmetric, transitive). -/
  equiv : Equivalence rel

namespace Observation

/-- Perfect syntactic equality on closed systems is an observation relation. -/
def eq (T : OpenTheory.{u}) : Observation T where
  rel := Eq
  equiv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

@[simp]
theorem eq_rel {T : OpenTheory.{u}} {c₁ c₂ : T.Closed} :
    (Observation.eq T).rel c₁ c₂ ↔ c₁ = c₂ := Iff.rfl

end Observation

/--
`Emulates real ideal Obs` asserts that `real` contextually emulates
`ideal` in the open-composition theory `T`, judged by the observation
relation `Obs : Observation T`.

For every plug `K : T.Plug Δ`, the closed compositions `T.close real K`
and `T.close ideal K` are related by `Obs.rel`.

This is the definitional core of UC security: no environment can
distinguish `real` from `ideal` under the chosen observation.
-/
structure Emulates
    {Δ : PortBoundary}
    (real ideal : T.Obj Δ)
    (Obs : Observation T) : Prop where
  compare : ∀ K : T.Plug Δ, Obs.rel (T.close real K) (T.close ideal K)

namespace Emulates

/-- Every open system emulates itself. -/
theorem refl
    {Δ : PortBoundary}
    (Obs : Observation T)
    (W : T.Obj Δ) :
    Emulates W W Obs :=
  ⟨fun _ => Obs.equiv.refl _⟩

/-- Emulation is symmetric. -/
theorem symm
    {Δ : PortBoundary}
    {Obs : Observation T}
    {W₁ W₂ : T.Obj Δ}
    (h : Emulates W₁ W₂ Obs) :
    Emulates W₂ W₁ Obs :=
  ⟨fun K => Obs.equiv.symm (h.compare K)⟩

/-- Emulation composes transitively. -/
theorem trans
    {Δ : PortBoundary}
    {Obs : Observation T}
    {W₁ W₂ W₃ : T.Obj Δ}
    (h₁₂ : Emulates W₁ W₂ Obs)
    (h₂₃ : Emulates W₂ W₃ Obs) :
    Emulates W₁ W₃ Obs :=
  ⟨fun K => Obs.equiv.trans (h₁₂.compare K) (h₂₃.compare K)⟩

/--
Adapting both sides of an emulation along the same boundary morphism
preserves the emulation, provided the theory has lawful `map` and `plug`.

The key identity used is `plug (map f W) K = plug W (map (swap f) K)`,
which is the `map_plug` naturality law.
-/
theorem map_invariance
    [OpenTheory.IsLawfulPlug T]
    {Δ₁ Δ₂ : PortBoundary}
    {Obs : Observation T}
    (f : PortBoundary.Hom Δ₁ Δ₂)
    {real ideal : T.Obj Δ₁}
    (h : Emulates real ideal Obs) :
    Emulates (T.map f real) (T.map f ideal) Obs :=
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
    {Obs : Observation T}
    {real ideal : T.Obj Δ}
    (h : Emulates real ideal Obs)
    (K : T.Plug Δ) :
    Obs.rel (T.close real K) (T.close ideal K) :=
  h.compare K

end Emulates

/-! ## Structural factorization of `close` under composition -/

section Factorization

variable [OpenTheory.HasPlugWireFactor T]

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

/-! ## UC composition theorems -/

namespace Emulates

variable [OpenTheory.HasPlugWireFactor T]

/-- Replacing the left component of a parallel composition preserves
emulation, with the right component and environment held fixed. -/
theorem par_left
    {Δ₁ Δ₂ : PortBoundary}
    {Obs : Observation T}
    {real₁ ideal₁ : T.Obj Δ₁}
    (h₁ : Emulates real₁ ideal₁ Obs)
    (W₂ : T.Obj Δ₂) :
    Emulates (T.par real₁ W₂) (T.par ideal₁ W₂) Obs :=
  ⟨fun K => by
    rw [OpenTheory.close_par_left real₁ W₂ K,
        OpenTheory.close_par_left ideal₁ W₂ K]
    exact h₁.compare _⟩

/-- Replacing the right component of a parallel composition preserves
emulation, with the left component and environment held fixed. -/
theorem par_right
    {Δ₁ Δ₂ : PortBoundary}
    {Obs : Observation T}
    (W₁ : T.Obj Δ₁)
    {real₂ ideal₂ : T.Obj Δ₂}
    (h₂ : Emulates real₂ ideal₂ Obs) :
    Emulates (T.par W₁ real₂) (T.par W₁ ideal₂) Obs :=
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
    {Obs : Observation T}
    {real₁ ideal₁ : T.Obj Δ₁} {real₂ ideal₂ : T.Obj Δ₂}
    (h₁ : Emulates real₁ ideal₁ Obs)
    (h₂ : Emulates real₂ ideal₂ Obs) :
    Emulates (T.par real₁ real₂) (T.par ideal₁ ideal₂) Obs :=
  Emulates.trans (par_left h₁ real₂) (par_right ideal₁ h₂)

/-- Replacing the left factor of a wiring preserves emulation. -/
theorem wire_left
    {Δ₁ Γ Δ₂ : PortBoundary}
    {Obs : Observation T}
    {real₁ ideal₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    (h₁ : Emulates real₁ ideal₁ Obs)
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    Emulates (T.wire real₁ W₂) (T.wire ideal₁ W₂) Obs :=
  ⟨fun K => by
    rw [OpenTheory.close_wire_left real₁ W₂ K,
        OpenTheory.close_wire_left ideal₁ W₂ K]
    exact h₁.compare _⟩

/-- Replacing the right factor of a wiring preserves emulation. -/
theorem wire_right
    {Δ₁ Γ Δ₂ : PortBoundary}
    {Obs : Observation T}
    (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    {real₂ ideal₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₂ : Emulates real₂ ideal₂ Obs) :
    Emulates (T.wire W₁ real₂) (T.wire W₁ ideal₂) Obs :=
  ⟨fun K => by
    rw [OpenTheory.close_wire_right W₁ real₂ K,
        OpenTheory.close_wire_right W₁ ideal₂ K]
    exact h₂.compare _⟩

/-- **UC composition theorem for `wire`**: if each factor emulates its
ideal, then their wired composition emulates the wired ideal. -/
theorem wire_compose
    {Δ₁ Γ Δ₂ : PortBoundary}
    {Obs : Observation T}
    {real₁ ideal₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    {real₂ ideal₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₁ : Emulates real₁ ideal₁ Obs)
    (h₂ : Emulates real₂ ideal₂ Obs) :
    Emulates (T.wire real₁ real₂) (T.wire ideal₁ ideal₂) Obs :=
  Emulates.trans (wire_left h₁ real₂) (wire_right ideal₁ h₂)

/-- Replacing the plug (environment) while keeping the protocol fixed
preserves observational equivalence, using `plug_comm` to swap
the protocol/environment roles. -/
theorem plug_right
    {Δ : PortBoundary}
    {Obs : Observation T}
    (W : T.Obj Δ)
    {K₁ K₂ : T.Obj (PortBoundary.swap Δ)}
    (hK : Emulates K₁ K₂ Obs) :
    Obs.rel (T.close W K₁) (T.close W K₂) := by
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
    {Obs : Observation T}
    {real ideal : T.Obj Δ}
    {K_real K_ideal : T.Obj (PortBoundary.swap Δ)}
    (hProt : Emulates real ideal Obs)
    (hEnv : Emulates K_real K_ideal Obs) :
    Obs.rel (T.close real K_real) (T.close ideal K_ideal) :=
  Obs.equiv.trans
    (hProt.plug_invariance K_real)
    (plug_right ideal hEnv)

end Emulates

/--
`UCSecure protocol ideal Obs SimSpace simulate` is the UC security statement
with an existential simulator.

There exists a simulator parameter `s : SimSpace` such that for every
context `K`, the closed real-world execution `T.close protocol K` is
related (under `Obs.rel`) to the closed ideal-world execution
`T.close ideal (simulate s K)`.

The simulator `simulate s` transforms the context rather than the ideal
functionality, following the standard UC convention: the simulator acts as
a wrapper around the honest context to make the ideal world look like the
real world.
-/
def UCSecure
    {Δ : PortBoundary}
    (protocol ideal : T.Obj Δ)
    (Obs : Observation T)
    (SimSpace : Type*) (simulate : SimSpace → T.Plug Δ → T.Plug Δ) : Prop :=
  ∃ s : SimSpace, ∀ K : T.Plug Δ,
    Obs.rel (T.close protocol K) (T.close ideal (simulate s K))

/--
Emulation implies UC security with the trivial (identity) simulator.
-/
theorem Emulates.toUCSecure
    {Δ : PortBoundary}
    {protocol ideal : T.Obj Δ}
    {Obs : Observation T}
    (h : Emulates protocol ideal Obs) :
    UCSecure protocol ideal Obs PUnit (fun _ K => K) :=
  ⟨⟨⟩, h.compare⟩

/--
UC security with identity simulation recovers emulation.
-/
theorem UCSecure.toEmulates_id
    {Δ : PortBoundary}
    {protocol ideal : T.Obj Δ}
    {Obs : Observation T}
    (hSec : UCSecure protocol ideal Obs PUnit (fun _ K => K)) :
    Emulates protocol ideal Obs :=
  let ⟨_, h⟩ := hSec; ⟨h⟩

end UC
end Interaction
