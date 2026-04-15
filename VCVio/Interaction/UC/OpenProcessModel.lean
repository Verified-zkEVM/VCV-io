/-
Copyright (c) 2026 Quang Dao. All rights reserved.
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

private theorem schedulerNode_mapBoundary
    {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂) :
    (schedulerNode.{u, w} Party Δ₁).mapBoundary φ =
      schedulerNode Party Δ₂ := by
  simp [schedulerNode, OpenNodeSemantics.mapBoundary, BoundaryAction.mapBoundary,
    BoundaryAction.internal]

instance : OpenTheory.IsLawfulPar (openTheory.{u, v, w} Party) where
  map_par {Δ₁} {Δ₁'} {Δ₂} {Δ₂'} f₁ f₂ W₁ W₂ := by
    change OpenProcess.mapBoundary (PortBoundary.Hom.tensor f₁ f₂)
        (W₁.interleave W₂ _ _ _) =
      (OpenProcess.mapBoundary f₁ W₁).interleave
        (OpenProcess.mapBoundary f₂ W₂) _ _ _
    simp only [OpenProcess.mapBoundary]
    rw [ProcessOver.mapContext_interleave, ProcessOver.interleave_mapContext]
    congr 1
    · exact OpenStepContext.map_tensor_comp_inlTensor Party f₁ f₂
    · exact OpenStepContext.map_tensor_comp_inrTensor Party f₁ f₂

instance : OpenTheory.IsLawfulWire (openTheory.{u, v, w} Party) where
  map_wire {Δ₁} {Δ₁'} {Γ} {Δ₂} {Δ₂'} f₁ f₂ W₁ W₂ := by
    change OpenProcess.mapBoundary (PortBoundary.Hom.tensor f₁ f₂)
        (W₁.interleave W₂ _ _ _) =
      (OpenProcess.mapBoundary
        (PortBoundary.Hom.tensor f₁ (PortBoundary.Hom.id Γ)) W₁).interleave
        (OpenProcess.mapBoundary (PortBoundary.Hom.tensor
          (PortBoundary.Hom.id (PortBoundary.swap Γ)) f₂) W₂) _ _ _
    simp only [OpenProcess.mapBoundary]
    rw [ProcessOver.mapContext_interleave, ProcessOver.interleave_mapContext]
    congr 1
    · exact OpenStepContext.map_tensor_comp_wireLeft Party f₁ f₂
    · exact OpenStepContext.map_tensor_comp_wireRight Party f₁ f₂

instance : OpenTheory.IsLawfulPlug (openTheory.{u, v, w} Party) where
  map_plug {Δ₁} {Δ₂} f W K := by
    change (OpenProcess.mapBoundary f W).interleave K _ _ _ =
      W.interleave (OpenProcess.mapBoundary (PortBoundary.Hom.swap f) K) _ _ _
    simp only [OpenProcess.mapBoundary]
    rw [ProcessOver.interleave_mapContext_left, ProcessOver.interleave_mapContext_right]
    congr 1

instance : OpenTheory.IsLawful (openTheory.{u, v, w} Party) where

-- ============================================================================
-- § Monoidal and compact closed laws up to bisimilarity
-- ============================================================================

/-- Parallel composition of open processes is associative up to bisimilarity:
reassociating the internal scheduler nesting does not change the observable
boundary behavior. -/
theorem openTheory_par_assoc_iso
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w} Party Δ₁)
    (W₂ : OpenProcess.{u, v, w} Party Δ₂)
    (W₃ : OpenProcess.{u, v, w} Party Δ₃) :
    OpenProcessIso
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom
        ((openTheory Party).par ((openTheory Party).par W₁ W₂) W₃))
      ((openTheory Party).par W₁ ((openTheory Party).par W₂ W₃)) := by
  simp only [openTheory]
  refine ⟨fun ⟨⟨s₁, s₂⟩, s₃⟩ ⟨s₁', ⟨s₂', s₃'⟩⟩ => s₁ = s₁' ∧ s₂ = s₂' ∧ s₃ = s₃',
    fun ⟨⟨s₁, s₂⟩, s₃⟩ => ⟨⟨s₁, ⟨s₂, s₃⟩⟩, rfl, rfl, rfl⟩,
    fun ⟨s₁, ⟨s₂, s₃⟩⟩ => ⟨⟨⟨s₁, s₂⟩, s₃⟩, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  all_goals intro ⟨⟨s₁, s₂⟩, s₃⟩ ⟨s₁', ⟨s₂', s₃'⟩⟩ ⟨h1, h2, h3⟩
  all_goals subst h1; subst h2; subst h3
  · intro ⟨⟨b⟩, rest⟩ _
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true => exact .inl ⟨⟨⟨true⟩, rest'⟩, rfl, rfl, rfl⟩
      | false => exact .inl ⟨⟨⟨false⟩, ⟨⟨true⟩, rest'⟩⟩, rfl, rfl, rfl⟩
    | false => exact .inl ⟨⟨⟨false⟩, ⟨⟨false⟩, rest⟩⟩, rfl, rfl, rfl⟩
  · intro ⟨⟨b⟩, rest⟩ hvisible
    rw [isSilentStep_mapBoundary_iff] at hvisible
    match b with
    | true =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine ⟨⟨⟨true⟩, rest'⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
        simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
          Spec.Decoration.map] at h
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
        all_goals intro X ons
        all_goals simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]
      | false =>
        refine ⟨⟨⟨false⟩, ⟨⟨true⟩, rest'⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
        simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
          Spec.Decoration.map] at h
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))⟩
        all_goals intro X ons
        · simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]
    | false =>
      refine ⟨⟨⟨false⟩, ⟨⟨false⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
        Spec.Decoration.map] at h
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
      all_goals intro X ons
      all_goals simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]
  · intro ⟨⟨b⟩, rest⟩ _
    match b with
    | true => exact .inl ⟨⟨⟨true⟩, ⟨⟨true⟩, rest⟩⟩, rfl, rfl, rfl⟩
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true => exact .inl ⟨⟨⟨true⟩, ⟨⟨false⟩, rest'⟩⟩, rfl, rfl, rfl⟩
      | false => exact .inl ⟨⟨⟨false⟩, rest'⟩, rfl, rfl, rfl⟩
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      refine ⟨⟨⟨true⟩, ⟨⟨true⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      rw [isSilentStep_mapBoundary_iff] at h
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
        Spec.Decoration.map] at h
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
      all_goals intro X ons
      all_goals simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]
    | false =>
      obtain ⟨⟨b'⟩, rest'⟩ := rest
      match b' with
      | true =>
        refine ⟨⟨⟨true⟩, ⟨⟨false⟩, rest'⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        rw [isSilentStep_mapBoundary_iff] at h
        simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
        simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
          Spec.Decoration.map] at h
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp
              ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2)))⟩
        all_goals intro X ons
        · simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]
      | false =>
        refine ⟨⟨⟨false⟩, rest'⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
        rw [isSilentStep_mapBoundary_iff] at h
        simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
        simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
          Spec.Decoration.map] at h
        refine ⟨rfl, rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mpr
            ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
        all_goals intro X ons
        all_goals simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]

/-- Parallel composition of open processes is commutative up to bisimilarity. -/
theorem openTheory_par_comm_iso
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w} Party Δ₁)
    (W₂ : OpenProcess.{u, v, w} Party Δ₂) :
    OpenProcessIso
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom
        ((openTheory Party).par W₁ W₂))
      ((openTheory Party).par W₂ W₁) := by
  simp only [openTheory]
  refine ⟨fun ⟨s₁, s₂⟩ ⟨s₂', s₁'⟩ => s₁ = s₁' ∧ s₂ = s₂',
    fun ⟨s₁, s₂⟩ => ⟨⟨s₂, s₁⟩, rfl, rfl⟩,
    fun ⟨s₂, s₁⟩ => ⟨⟨s₁, s₂⟩, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  all_goals intro ⟨s₁, s₂⟩ ⟨s₂', s₁'⟩ ⟨h1, h2⟩
  all_goals subst h1; subst h2
  · intro ⟨⟨b⟩, rest⟩ _
    match b with
    | true => exact .inl ⟨⟨⟨false⟩, rest⟩, rfl, rfl⟩
    | false => exact .inl ⟨⟨⟨true⟩, rest⟩, rfl, rfl⟩
  · intro ⟨⟨b⟩, rest⟩ hvisible
    rw [isSilentStep_mapBoundary_iff] at hvisible
    match b with
    | true =>
      refine ⟨⟨⟨false⟩, rest⟩, fun h => hvisible ?_, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration]
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration] at h
      exact ⟨rfl, (isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]) _ _).mpr
        ((isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]) _ _).mp h.2)⟩
    | false =>
      refine ⟨⟨⟨true⟩, rest⟩, fun h => hvisible ?_, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration]
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration] at h
      exact ⟨rfl, (isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]) _ _).mpr
        ((isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]) _ _).mp h.2)⟩
  · intro ⟨⟨b⟩, rest⟩ _
    match b with
    | true => exact .inl ⟨⟨⟨false⟩, rest⟩, rfl, rfl⟩
    | false => exact .inl ⟨⟨⟨true⟩, rest⟩, rfl, rfl⟩
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      refine ⟨⟨⟨false⟩, rest⟩, fun h => hvisible ?_, rfl, rfl⟩
      rw [isSilentStep_mapBoundary_iff] at h
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration]
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration] at h
      exact ⟨rfl, (isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]) _ _).mpr
        ((isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]) _ _).mp h.2)⟩
    | false =>
      refine ⟨⟨⟨true⟩, rest⟩, fun h => hvisible ?_, rfl, rfl⟩
      rw [isSilentStep_mapBoundary_iff] at h
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration]
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration] at h
      exact ⟨rfl, (isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]) _ _).mpr
        ((isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]) _ _).mp h.2)⟩

/-- The unit for parallel composition is the trivial process with no boundary
and `PUnit` state. -/
def openTheory_unit : OpenProcess.{u, v, w} Party PortBoundary.empty where
  Proc := PUnit
  step := fun _ =>
    { spec := .done
      semantics := ⟨⟩
      next := fun _ => PUnit.unit }

/-- The monoidal unit is a left identity for parallel composition up to
bisimilarity. -/
theorem openTheory_par_leftUnit_iso
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w} Party Δ) :
    OpenProcessIso
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom
        ((openTheory Party).par (openTheory_unit Party) W))
      W := by
  simp only [openTheory, openTheory_unit]
  refine ⟨fun s₁ s₂ => s₁.2 = s₂, fun ⟨_, s⟩ => ⟨s, rfl⟩,
    fun s => ⟨⟨⟨⟩, s⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  all_goals intro ⟨_, s⟩ s₂ heq
  all_goals subst heq
  · intro ⟨⟨b⟩, rest⟩ _
    match b with
    | true => exact .inr rfl
    | false => exact .inl ⟨rest, rfl⟩
  · intro ⟨⟨b⟩, rest⟩ hvisible
    rw [isSilentStep_mapBoundary_iff] at hvisible
    match b with
    | true =>
      exact absurd (by simp [IsSilentStep, ProcessOver.interleave,
        IsSilentDecoration, Spec.Decoration.map, schedulerNode,
        BoundaryAction.internal]) hvisible
    | false =>
      refine ⟨rest, fun h => hvisible ?_, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr h⟩
      intro X ons
      simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]
  · intro tr₂ _
    exact .inl ⟨⟨⟨false⟩, tr₂⟩, rfl⟩
  · intro tr₂ hvisible
    refine ⟨⟨⟨false⟩, tr₂⟩, fun h => hvisible ?_, rfl⟩
    rw [isSilentStep_mapBoundary_iff] at h
    simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
      Spec.Decoration.map] at h
    refine (isSilentDecoration_iff_map _ ?_ _ _).mp h.2
    intro X ons
    simp [OpenStepContext.inrTensor, BoundaryAction.embedInrTensor]

/-- The monoidal unit is a right identity for parallel composition up to
bisimilarity. -/
theorem openTheory_par_rightUnit_iso
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w} Party Δ) :
    OpenProcessIso
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyRight Δ).toHom
        ((openTheory Party).par W (openTheory_unit Party)))
      W := by
  simp only [openTheory, openTheory_unit]
  refine ⟨fun s₁ s₂ => s₁.1 = s₂, fun ⟨s, _⟩ => ⟨s, rfl⟩,
    fun s => ⟨⟨s, ⟨⟩⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  all_goals intro ⟨s, _⟩ s₂ heq
  all_goals subst heq
  · intro ⟨⟨b⟩, rest⟩ _
    match b with
    | true => exact .inl ⟨rest, rfl⟩
    | false => exact .inr rfl
  · intro ⟨⟨b⟩, rest⟩ hvisible
    rw [isSilentStep_mapBoundary_iff] at hvisible
    match b with
    | true =>
      refine ⟨rest, fun h => hvisible ?_, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr h⟩
      intro X ons
      simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]
    | false =>
      exact absurd (by simp [IsSilentStep, ProcessOver.interleave,
        IsSilentDecoration, Spec.Decoration.map, schedulerNode,
        BoundaryAction.internal]) hvisible
  · intro tr₂ _
    exact .inl ⟨⟨⟨true⟩, tr₂⟩, rfl⟩
  · intro tr₂ hvisible
    refine ⟨⟨⟨true⟩, tr₂⟩, fun h => hvisible ?_, rfl⟩
    rw [isSilentStep_mapBoundary_iff] at h
    simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
      Spec.Decoration.map] at h
    refine (isSilentDecoration_iff_map _ ?_ _ _).mp h.2
    intro X ons
    simp [OpenStepContext.inlTensor, BoundaryAction.embedInlTensor]

/-- The identity wire (coevaluation) on boundary `Γ`: relays messages
bidirectionally between `swap Γ` and `Γ`. -/
def openTheory_idWire (Γ : PortBoundary) :
    OpenProcess.{u, v, w} Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Γ) where
  Proc := PUnit
  step := fun _ =>
    { spec := .done
      semantics := ⟨⟩
      next := fun _ => PUnit.unit }

/-- Left zig-zag: wiring the identity wire on the left is a no-op up to
bisimilarity. -/
theorem openTheory_wire_idWire_iso
    (Γ : PortBoundary)
    {Δ₂ : PortBoundary}
    (W₂ : OpenProcess.{u, v, w} Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    OpenProcessIso
      ((openTheory Party).wire (openTheory_idWire Party Γ) W₂)
      W₂ := by
  simp only [openTheory, openTheory_idWire]
  refine ⟨fun s₁ s₂ => s₁.2 = s₂, fun ⟨_, s⟩ => ⟨s, rfl⟩,
    fun s => ⟨⟨⟨⟩, s⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  all_goals intro ⟨_, s⟩ s₂ heq
  all_goals subst heq
  · intro ⟨⟨b⟩, rest⟩ _
    match b with
    | true => exact .inr rfl
    | false => exact .inl ⟨rest, rfl⟩
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      exact absurd (by simp [IsSilentStep, ProcessOver.interleave,
        IsSilentDecoration, Spec.Decoration.map, schedulerNode,
        BoundaryAction.internal]) hvisible
    | false =>
      refine ⟨rest, fun h => hvisible ?_, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr h⟩
      intro X ons
      simp [OpenStepContext.wireRight, BoundaryAction.wireRight]
  · intro tr₂ _
    exact .inl ⟨⟨⟨false⟩, tr₂⟩, rfl⟩
  · intro tr₂ hvisible
    refine ⟨⟨⟨false⟩, tr₂⟩, fun h => hvisible ?_, rfl⟩
    simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
      Spec.Decoration.map] at h
    refine (isSilentDecoration_iff_map _ ?_ _ _).mp h.2
    intro X ons
    simp [OpenStepContext.wireRight, BoundaryAction.wireRight]

/-- Right zig-zag: wiring the identity wire on the right is a no-op up to
bisimilarity. -/
theorem openTheory_wire_idWire_right_iso
    (Γ : PortBoundary)
    {Δ₁ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w} Party
      (PortBoundary.tensor Δ₁ Γ)) :
    OpenProcessIso
      ((openTheory Party).wire W₁ (openTheory_idWire Party Γ))
      W₁ := by
  simp only [openTheory, openTheory_idWire]
  refine ⟨fun s₁ s₂ => s₁.1 = s₂, fun ⟨s, _⟩ => ⟨s, rfl⟩,
    fun s => ⟨⟨s, ⟨⟩⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  all_goals intro ⟨s, _⟩ s₂ heq
  all_goals subst heq
  · intro ⟨⟨b⟩, rest⟩ _
    match b with
    | true => exact .inl ⟨rest, rfl⟩
    | false => exact .inr rfl
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      refine ⟨rest, fun h => hvisible ?_, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr h⟩
      intro X ons
      simp [OpenStepContext.wireLeft, BoundaryAction.wireLeft]
    | false =>
      exact absurd (by simp [IsSilentStep, ProcessOver.interleave,
        IsSilentDecoration, Spec.Decoration.map, schedulerNode,
        BoundaryAction.internal]) hvisible
  · intro tr₂ _
    exact .inl ⟨⟨⟨true⟩, tr₂⟩, rfl⟩
  · intro tr₂ hvisible
    refine ⟨⟨⟨true⟩, tr₂⟩, fun h => hvisible ?_, rfl⟩
    simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
      Spec.Decoration.map] at h
    refine (isSilentDecoration_iff_map _ ?_ _ _).mp h.2
    intro X ons
    simp [OpenStepContext.wireLeft, BoundaryAction.wireLeft]

/-- `plug` is derivable from `wire` plus boundary reshaping, up to
bisimilarity. -/
theorem openTheory_plug_eq_wire_iso
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w} Party Δ)
    (K : OpenProcess.{u, v, w} Party (PortBoundary.swap Δ)) :
    OpenProcessIso
      ((openTheory Party).plug W K)
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
        ((openTheory Party).wire
          (OpenProcess.mapBoundary
            (PortBoundary.Equiv.tensorEmptyLeft Δ).symm.toHom W)
          (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorEmptyRight
              (PortBoundary.swap Δ)).symm.toHom K))) := by
  simp only [openTheory]
  refine ⟨fun s₁ s₂ => s₁ = s₂,
    fun s => ⟨s, rfl⟩, fun s => ⟨s, rfl⟩, ?_, ?_, ?_, ?_⟩
  all_goals intro s₁ s₂ heq
  all_goals subst heq
  · intro ⟨⟨b⟩, rest⟩ _
    match b with
    | true => exact .inl ⟨⟨⟨true⟩, rest⟩, rfl⟩
    | false => exact .inl ⟨⟨⟨false⟩, rest⟩, rfl⟩
  · intro ⟨⟨b⟩, rest⟩ hvisible
    match b with
    | true =>
      refine ⟨⟨⟨true⟩, rest⟩, fun h => hvisible ?_, rfl⟩
      rw [isSilentStep_mapBoundary_iff] at h
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
      · intro X ons; simp [OpenStepContext.close, BoundaryAction.closed]
      · intro X ons
        simp [OpenStepContext.map, OpenNodeSemantics.mapBoundary, BoundaryAction.mapBoundary]
      · intro X ons; simp [OpenStepContext.wireLeft, BoundaryAction.wireLeft]
    | false =>
      refine ⟨⟨⟨false⟩, rest⟩, fun h => hvisible ?_, rfl⟩
      rw [isSilentStep_mapBoundary_iff] at h
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
      · intro X ons; simp [OpenStepContext.close, BoundaryAction.closed]
      · intro X ons
        simp [OpenStepContext.map, OpenNodeSemantics.mapBoundary, BoundaryAction.mapBoundary]
      · intro X ons; simp [OpenStepContext.wireRight, BoundaryAction.wireRight]
  · intro ⟨⟨b⟩, rest⟩ _
    match b with
    | true => exact .inl ⟨⟨⟨true⟩, rest⟩, rfl⟩
    | false => exact .inl ⟨⟨⟨false⟩, rest⟩, rfl⟩
  · intro ⟨⟨b⟩, rest⟩ hvisible
    rw [isSilentStep_mapBoundary_iff] at hvisible
    match b with
    | true =>
      refine ⟨⟨⟨true⟩, rest⟩, fun h => hvisible ?_, rfl⟩
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
      · intro X ons; simp [OpenStepContext.wireLeft, BoundaryAction.wireLeft]
      · intro X ons
        simp [OpenStepContext.map, OpenNodeSemantics.mapBoundary, BoundaryAction.mapBoundary]
      · intro X ons; simp [OpenStepContext.close, BoundaryAction.closed]
    | false =>
      refine ⟨⟨⟨false⟩, rest⟩, fun h => hvisible ?_, rfl⟩
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
      · intro X ons; simp [OpenStepContext.wireRight, BoundaryAction.wireRight]
      · intro X ons
        simp [OpenStepContext.map, OpenNodeSemantics.mapBoundary, BoundaryAction.mapBoundary]
      · intro X ons; simp [OpenStepContext.close, BoundaryAction.closed]

/-- The monoidal unit equals the coevaluation at the trivial boundary,
up to bisimilarity. -/
theorem openTheory_unit_eq_iso :
    OpenProcessIso
      (openTheory_unit.{u, v, w} Party)
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
        (openTheory_idWire Party PortBoundary.empty)) :=
  ⟨fun _ _ => True, fun _ => ⟨PUnit.unit, trivial⟩, fun _ => ⟨PUnit.unit, trivial⟩,
    fun _ _ _ _ _ => .inl ⟨PUnit.unit, trivial⟩,
    fun _ _ _ _ hns => absurd trivial hns,
    fun _ _ _ _ _ => .inl ⟨PUnit.unit, trivial⟩,
    fun _ _ _ _ hns => absurd trivial hns⟩

end Model

end UC
end Interaction
