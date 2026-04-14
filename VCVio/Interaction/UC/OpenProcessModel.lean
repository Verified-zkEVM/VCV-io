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

The key operation is `map`, which adapts an open process's exposed boundary
along a `PortBoundary.Hom` by transforming every node's boundary action via
`BoundaryAction.mapBoundary`. This is fully implemented and satisfies
`IsLawfulMap` (functoriality).

The remaining operations (`par`, `wire`, `plug`) are structurally typed but
their step functions are deferred (`sorry`). These operations involve process
interleaving and boundary-traffic routing whose exact semantics belong partly
in the runtime/execution layer. Their definitions here establish the type-level
interface and will be fleshed out once the runtime layer is in place.

This file validates that the `OpenTheory` algebra is realizable by actual
processes, not just the free syntax model in `OpenSyntax.lean`.
-/

universe u v w

namespace Interaction
namespace UC

open Concurrent

section Model

variable (Party : Type u)

/--
The concrete open-composition theory backed by `OpenProcess`.

* `Obj Δ` is `OpenProcess Party Δ`, the boundary-indexed family of open
  concurrent processes.
* `map` adapts boundary actions along a `PortBoundary.Hom`.
* `par` places two open processes side by side (step function deferred).
* `wire` connects a shared internal boundary (step function deferred).
* `plug` closes against a matching context (step function deferred).
-/
def openTheory : OpenTheory.{max (v + 1) u (w + 1)} where
  Obj Δ := OpenProcess.{u, v, w} Party Δ
  map φ p := p.mapBoundary φ
  par {Δ₁} {Δ₂} p₁ p₂ := {
    Proc := p₁.Proc × p₂.Proc
    step := sorry
  }
  wire {Δ₁} {_Γ} {Δ₂} p₁ p₂ := {
    Proc := p₁.Proc × p₂.Proc
    step := sorry
  }
  plug p k := {
    Proc := p.Proc × k.Proc
    step := sorry
  }

instance : OpenTheory.IsLawfulMap (openTheory.{u, v, w} Party) where
  map_id {Δ} W := by
    change W.mapBoundary (PortBoundary.Hom.id Δ) = W
    simp only [OpenProcess.mapBoundary]
    rw [openStepContextMap_id]
    cases W with | mk Proc step =>
    simp only [ProcessOver.mapContext, StepOver.mapContext]
    congr 1; funext p
    exact congrArg₂ (StepOver.mk _)
      (Interaction.Spec.Decoration.map_id _ _) rfl
  map_comp {Δ₁} {Δ₂} {Δ₃} g f W := by
    change W.mapBoundary (PortBoundary.Hom.comp g f) =
      (W.mapBoundary f).mapBoundary g
    simp only [OpenProcess.mapBoundary]
    rw [← openStepContextMap_comp]
    cases W with | mk Proc step =>
    simp only [ProcessOver.mapContext, StepOver.mapContext]
    congr 1; funext p
    exact congrArg₂ (StepOver.mk _)
      (Interaction.Spec.Decoration.map_comp _ _ _ _).symm rfl

end Model

end UC
end Interaction
