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

The remaining operations (`wire`, `plug`) are structurally typed but their
step functions are deferred (`sorry`). These require boundary-traffic routing
whose exact semantics belong in the runtime/execution layer.
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
* `par` places two open processes side by side with binary-choice
  interleaving: a scheduling node selects left or right, then runs
  the selected subprocess's step protocol.
* `wire` connects a shared internal boundary (step function deferred).
* `plug` closes against a matching context (step function deferred).
-/
def openTheory : OpenTheory.{max (v + 1) u (w + 1)} where
  Obj Δ := OpenProcess.{u, v, w} Party Δ
  map φ p := p.mapBoundary φ
  par {Δ₁} {Δ₂} p₁ p₂ := {
    Proc := p₁.Proc × p₂.Proc
    step := fun (s₁, s₂) =>
      let step₁ := p₁.step s₁
      let step₂ := p₂.step s₂
      let schedulerNode : OpenNodeSemantics Party
          (PortBoundary.tensor Δ₁ Δ₂) (ULift.{v} Bool) :=
        { controllers := fun _ => []
          views := fun _ => .hidden
          boundary := .internal _ _ }
      { spec := .node (ULift.{v} Bool) fun
          | ⟨true⟩ => step₁.spec
          | ⟨false⟩ => step₂.spec
        semantics :=
          ⟨schedulerNode, fun
            | ⟨true⟩ => Interaction.Spec.Decoration.map
                (openStepContextInlTensor Party Δ₁ Δ₂)
                step₁.spec step₁.semantics
            | ⟨false⟩ => Interaction.Spec.Decoration.map
                (openStepContextInrTensor Party Δ₁ Δ₂)
                step₂.spec step₂.semantics⟩
        next := fun
          | ⟨⟨true⟩, tr⟩ => (step₁.next tr, s₂)
          | ⟨⟨false⟩, tr⟩ => (s₁, step₂.next tr) }
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
