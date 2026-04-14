/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.OpenProcess
import VCVio.Interaction.UC.OpenTheory

/-!
# Concrete `OpenTheory` model backed by `OpenProcess`

This file provides the first concrete realization of `UC.OpenTheory`
using actual open processes (`OpenProcess Party Δ`).

## Implemented operations

* `map` adapts boundary actions along a `PortBoundary.Hom`, with a proven
  `IsLawfulMap` instance (functoriality).

* `par` places two open processes side by side using binary-choice
  interleaving: a scheduling node chooses left or right, then runs the
  selected subprocess's step protocol. Emitted packets are injected into
  the appropriate summand of the tensor output interface.

* `wire` connects a shared internal boundary between two processes.
  Packets on the shared boundary are filtered out (deferred to runtime
  routing), while packets on the remaining external boundaries are
  preserved.

* `plug` closes an open system against a matching context by
  internalizing all boundary traffic.
-/

universe u v w

namespace Interaction
namespace UC

open Concurrent

section Model

variable (Party : Type u)

/-- The hidden scheduler node shared by `par`, `wire`, and `plug`. -/
private def schedulerNode (Δ : PortBoundary) :
    OpenNodeSemantics Party Δ (ULift.{w} Bool) where
  controllers := fun _ => []
  views := fun _ => .hidden
  boundary := .internal Δ _

/--
The concrete open-composition theory backed by `OpenProcess`.

* `Obj Δ` is `OpenProcess Party Δ`, the boundary-indexed family of open
  concurrent processes.
* `map` adapts boundary actions along a `PortBoundary.Hom`.
* `par`, `wire`, and `plug` all use `ProcessOver.interleave` with the
  appropriate context morphisms.
-/
def openTheory : OpenTheory.{max (v + 1) u (w + 1)} where
  Obj Δ := OpenProcess.{u, v, w} Party Δ
  map φ p := p.mapBoundary φ
  par {Δ₁} {Δ₂} p₁ p₂ :=
    p₁.interleave p₂
      (OpenStepContext.inlTensor Party Δ₁ Δ₂)
      (OpenStepContext.inrTensor Party Δ₁ Δ₂)
      (schedulerNode Party (PortBoundary.tensor Δ₁ Δ₂))
  wire {Δ₁} {Γ} {Δ₂} p₁ p₂ :=
    p₁.interleave p₂
      (OpenStepContext.wireLeft Party Δ₁ Γ Δ₂)
      (OpenStepContext.wireRight Party Δ₁ Γ Δ₂)
      (schedulerNode Party (PortBoundary.tensor Δ₁ Δ₂))
  plug {Δ} p k :=
    p.interleave k
      (OpenStepContext.close Party Δ)
      (OpenStepContext.close Party (PortBoundary.swap Δ))
      (schedulerNode Party PortBoundary.empty)

instance : OpenTheory.IsLawfulMap (openTheory.{u, v, w} Party) where
  map_id {Δ} W := by
    change W.mapBoundary (PortBoundary.Hom.id Δ) = W
    simp only [OpenProcess.mapBoundary]
    rw [OpenStepContext.map_id]
    cases W with | mk Proc step =>
    simp only [ProcessOver.mapContext, StepOver.mapContext]
    congr 1; funext p
    exact congrArg₂ (StepOver.mk _)
      (Interaction.Spec.Decoration.map_id _ _) rfl
  map_comp {Δ₁} {Δ₂} {Δ₃} g f W := by
    change W.mapBoundary (PortBoundary.Hom.comp g f) =
      (W.mapBoundary f).mapBoundary g
    simp only [OpenProcess.mapBoundary]
    rw [← OpenStepContext.map_comp]
    cases W with | mk Proc step =>
    simp only [ProcessOver.mapContext, StepOver.mapContext]
    congr 1; funext p
    exact congrArg₂ (StepOver.mk _)
      (Interaction.Spec.Decoration.map_comp _ _ _ _).symm rfl

end Model

end UC
end Interaction
