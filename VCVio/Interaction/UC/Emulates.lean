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
