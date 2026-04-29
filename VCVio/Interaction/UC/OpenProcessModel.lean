/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.Interaction.UC.OpenProcess
import VCVio.Interaction.UC.OpenTheory

/-!
# Concrete `OpenTheory` model backed by `OpenProcess m`

This file provides the first concrete realization of `UC.OpenTheory`
using actual open processes (`OpenProcess m Party Δ`), i.e., processes
that carry a per-step nodewise-monadic sampler in the intermediate monad
`m`.

## Implemented operations

* `map` adapts boundary actions along a `PortBoundary.Hom`, with a proven
  `IsLawfulMap` instance (functoriality). The per-step sampler is left
  unchanged; only the boundary-action decoration is pushed forward.

* `par` places two open processes side by side using binary-choice
  interleaving: a scheduling node chooses left or right, then runs the
  selected subprocess's step protocol. Emitted packets are injected into
  the appropriate summand of the tensor output interface. The scheduler
  move is resolved by the theory's shared `schedulerSampler : m (ULift
  Bool)`; per-branch samplers are assembled via
  `Spec.Sampler.interleave`.

* `wire` connects a shared internal boundary between two processes.
  Packets on the shared boundary are filtered out (deferred to runtime
  routing), while packets on the remaining external boundaries are
  preserved. Samplers are threaded the same way as for `par`.

* `plug` closes an open system against a matching context by
  internalizing all boundary traffic. Samplers are again threaded via
  the scheduler-interleaving pattern.
-/

universe u v w w'

namespace Interaction
namespace UC

open Concurrent

section Model

variable (Party : Type u)
variable (m : Type w → Type w')
variable (schedulerSampler : m (ULift.{w, 0} Bool))

/-- The hidden scheduler node shared by `par`, `wire`, and `plug`. -/
private def schedulerNode (Δ : PortBoundary) :
    OpenNodeProfile.{u, w} Party Δ (ULift.{w, 0} Bool) where
  controllers := fun _ => []
  views := fun _ => .hidden
  boundary := .internal Δ _

/--
The concrete open-composition theory backed by `OpenProcess m`.

* `Obj Δ` is `OpenProcess m Party Δ`, the boundary-indexed family of
  open concurrent processes carrying per-step `m`-samplers.
* `map` adapts boundary actions along a `PortBoundary.Hom`, preserving
  samplers verbatim.
* `par`, `wire`, and `plug` all use `OpenProcess.interleave` with the
  appropriate context morphisms and thread the shared `schedulerSampler`
  through `Spec.Sampler.interleave`.
-/
def openTheory : OpenTheory where
  Obj Δ := OpenProcess.{u, v, w, w'} m Party Δ
  map φ p := p.mapBoundary φ
  par {Δ₁} {Δ₂} p₁ p₂ :=
    p₁.interleave p₂
      (OpenNodeContext.inlTensor Party Δ₁ Δ₂)
      (OpenNodeContext.inrTensor Party Δ₁ Δ₂)
      (schedulerNode Party (PortBoundary.tensor Δ₁ Δ₂))
      schedulerSampler
  wire {Δ₁} {Γ} {Δ₂} p₁ p₂ :=
    p₁.interleave p₂
      (OpenNodeContext.wireLeft Party Δ₁ Γ Δ₂)
      (OpenNodeContext.wireRight Party Δ₁ Γ Δ₂)
      (schedulerNode Party (PortBoundary.tensor Δ₁ Δ₂))
      schedulerSampler
  plug {Δ} p k :=
    p.interleave k
      (OpenNodeContext.close Party Δ)
      (OpenNodeContext.close Party (PortBoundary.swap Δ))
      (schedulerNode Party PortBoundary.empty)
      schedulerSampler

instance lawfulMap_openTheory :
    OpenTheory.IsLawfulMap (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  map_id {Δ} W := by
    change W.mapBoundary (PortBoundary.Hom.id Δ) = W
    simp only [OpenProcess.mapBoundary]
    rw [OpenNodeContext.map_id]
    cases W with | mk Proc step stepSampler =>
    congr 1
    funext s
    simp only [StepOver.mapContext]
    exact congrArg₂ (StepOver.mk _)
      (Interaction.Spec.Decoration.map_id _ _) rfl
  map_comp {Δ₁} {Δ₂} {Δ₃} g f W := by
    change W.mapBoundary (PortBoundary.Hom.comp g f) =
      (W.mapBoundary f).mapBoundary g
    simp only [OpenProcess.mapBoundary]
    rw [← OpenNodeContext.map_comp]
    cases W with | mk Proc step stepSampler =>
    congr 1
    funext s
    simp only [StepOver.mapContext]
    exact congrArg₂ (StepOver.mk _)
      (Interaction.Spec.Decoration.map_comp _ _ _ _).symm rfl

/-- Extensionality for `OpenProcess` when both sides share the same
residual state type `Proc` definitionally, the `step` fields are equal
as functions, and the `stepSampler` fields are HEq (which reduces to
literal equality once `step` agrees). -/
private theorem OpenProcess.ext_of_step_eq
    {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}
    {Proc : Type v}
    {step₁ step₂ : Proc → StepOver (OpenNodeContext.{u, w} Party Δ) Proc}
    {stepSampler₁ : ∀ s, Spec.Sampler.{w, w'} m (step₁ s).spec}
    {stepSampler₂ : ∀ s, Spec.Sampler.{w, w'} m (step₂ s).spec}
    (hstep : step₁ = step₂)
    (hsampler : HEq stepSampler₁ stepSampler₂) :
    (OpenProcess.mk Proc step₁ stepSampler₁ :
      OpenProcess.{u, v, w, w'} m Party Δ) =
      OpenProcess.mk Proc step₂ stepSampler₂ := by
  subst hstep
  cases hsampler
  rfl

/-- Derive step equality (as a function) from a `ProcessOver` equality,
when both ProcessOvers have the same `.Proc` type definitionally. -/
private theorem heq_step_of_processOver_eq.{v₀, w₀, w₂}
    {Γ : Interaction.Spec.Node.Context.{w₀, w₂}}
    {P₁ P₂ : Concurrent.ProcessOver.{v₀, w₀, w₂} Γ}
    (h : P₁ = P₂) :
    HEq P₁.step P₂.step :=
  h ▸ HEq.rfl

instance lawfulPar_openTheory :
    OpenTheory.IsLawfulPar (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  __ := lawfulMap_openTheory Party m schedulerSampler
  map_par {Δ₁} {Δ₁'} {Δ₂} {Δ₂'} f₁ f₂ W₁ W₂ := by
    change OpenProcess.mapBoundary (PortBoundary.Hom.tensor f₁ f₂)
        (W₁.interleave W₂ _ _ _ schedulerSampler) =
      (OpenProcess.mapBoundary f₁ W₁).interleave
        (OpenProcess.mapBoundary f₂ W₂) _ _ _ schedulerSampler
    -- The structural content lives at the `ProcessOver` layer: pushing a
    -- tensor-boundary map across `interleave` matches mapping each side
    -- first, using `map_tensor_comp_inlTensor`/`inrTensor` on the
    -- injections. The scheduler argument closes definitionally because
    -- boundary-mapping a purely internal node preserves the `.internal`
    -- tag (the trace-monoid unit `1` is fixed by `PFunctor.Trace.mapChart`).
    have hproc :
        (W₁.toProcess.interleave W₂.toProcess
            (OpenNodeContext.inlTensor Party Δ₁ Δ₂)
            (OpenNodeContext.inrTensor Party Δ₁ Δ₂)
            (schedulerNode Party (PortBoundary.tensor Δ₁ Δ₂))).mapContext
              (OpenNodeContext.map Party (PortBoundary.Hom.tensor f₁ f₂)) =
          (W₁.toProcess.mapContext (OpenNodeContext.map Party f₁)).interleave
            (W₂.toProcess.mapContext (OpenNodeContext.map Party f₂))
            (OpenNodeContext.inlTensor Party Δ₁' Δ₂')
            (OpenNodeContext.inrTensor Party Δ₁' Δ₂')
            (schedulerNode Party (PortBoundary.tensor Δ₁' Δ₂')) := by
      rw [ProcessOver.mapContext_interleave, ProcessOver.interleave_mapContext,
        OpenNodeContext.map_tensor_comp_inlTensor,
        OpenNodeContext.map_tensor_comp_inrTensor]
      congr 1
    -- Lift to the `OpenProcess` equality: `Proc` is `Proc₁ × Proc₂` on
    -- both sides; `step` is the `.step` of each side of `hproc` (defeq);
    -- `stepSampler` is `Sampler.interleave schedulerSampler ...`, same
    -- term on both sides (since `mapBoundary` preserves `stepSampler`).
    cases W₁ with | mk Proc₁ step₁ stepSampler₁ =>
    cases W₂ with | mk Proc₂ step₂ stepSampler₂ =>
    simp only [OpenProcess.mapBoundary, OpenProcess.interleave]
    exact OpenProcess.ext_of_step_eq
      (eq_of_heq (heq_step_of_processOver_eq hproc)) HEq.rfl

instance lawfulWire_openTheory :
    OpenTheory.IsLawfulWire (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  __ := lawfulMap_openTheory Party m schedulerSampler
  map_wire {Δ₁} {Δ₁'} {Γ} {Δ₂} {Δ₂'} f₁ f₂ W₁ W₂ := by
    change OpenProcess.mapBoundary (PortBoundary.Hom.tensor f₁ f₂)
        (W₁.interleave W₂ _ _ _ schedulerSampler) =
      (OpenProcess.mapBoundary
        (PortBoundary.Hom.tensor f₁ (PortBoundary.Hom.id Γ)) W₁).interleave
        (OpenProcess.mapBoundary (PortBoundary.Hom.tensor
          (PortBoundary.Hom.id (PortBoundary.swap Γ)) f₂) W₂) _ _ _
        schedulerSampler
    -- Same pattern as `map_par`, with the wire injections carrying the
    -- shared boundary `Γ` as a fixed axis: `map_tensor_comp_wireLeft`
    -- transports `f₁` past the left injection, and `map_tensor_comp_wireRight`
    -- transports `f₂` past the right injection.
    have hproc :
        (W₁.toProcess.interleave W₂.toProcess
            (OpenNodeContext.wireLeft Party Δ₁ Γ Δ₂)
            (OpenNodeContext.wireRight Party Δ₁ Γ Δ₂)
            (schedulerNode Party (PortBoundary.tensor Δ₁ Δ₂))).mapContext
              (OpenNodeContext.map Party (PortBoundary.Hom.tensor f₁ f₂)) =
          (W₁.toProcess.mapContext
              (OpenNodeContext.map Party
                (PortBoundary.Hom.tensor f₁ (PortBoundary.Hom.id Γ)))).interleave
            (W₂.toProcess.mapContext
              (OpenNodeContext.map Party
                (PortBoundary.Hom.tensor
                  (PortBoundary.Hom.id (PortBoundary.swap Γ)) f₂)))
            (OpenNodeContext.wireLeft Party Δ₁' Γ Δ₂')
            (OpenNodeContext.wireRight Party Δ₁' Γ Δ₂')
            (schedulerNode Party (PortBoundary.tensor Δ₁' Δ₂')) := by
      rw [ProcessOver.mapContext_interleave, ProcessOver.interleave_mapContext,
        OpenNodeContext.map_tensor_comp_wireLeft,
        OpenNodeContext.map_tensor_comp_wireRight]
      congr 1
    cases W₁ with | mk Proc₁ step₁ stepSampler₁ =>
    cases W₂ with | mk Proc₂ step₂ stepSampler₂ =>
    simp only [OpenProcess.mapBoundary, OpenProcess.interleave]
    exact OpenProcess.ext_of_step_eq
      (eq_of_heq (heq_step_of_processOver_eq hproc)) HEq.rfl

instance lawfulPlug_openTheory :
    OpenTheory.IsLawfulPlug (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  __ := lawfulMap_openTheory Party m schedulerSampler
  map_plug {Δ₁} {Δ₂} f W K := by
    change (OpenProcess.mapBoundary f W).interleave K _ _ _ schedulerSampler =
      W.interleave (OpenProcess.mapBoundary (PortBoundary.Hom.swap f) K) _ _ _
        schedulerSampler
    -- Only one side is boundary-mapped on each inequation: on the LHS, `W`
    -- carries `map Party f`, absorbed by `close Party Δ₂` via `close_comp_map`;
    -- on the RHS, `K` carries `map Party (swap f)`, absorbed by
    -- `close Party (swap Δ₁)` via the same lemma applied to `swap f`.
    have hproc :
        (W.toProcess.mapContext (OpenNodeContext.map Party f)).interleave K.toProcess
            (OpenNodeContext.close Party Δ₂)
            (OpenNodeContext.close Party (PortBoundary.swap Δ₂))
            (schedulerNode Party PortBoundary.empty) =
          W.toProcess.interleave
            (K.toProcess.mapContext
              (OpenNodeContext.map Party (PortBoundary.Hom.swap f)))
            (OpenNodeContext.close Party Δ₁)
            (OpenNodeContext.close Party (PortBoundary.swap Δ₁))
            (schedulerNode Party PortBoundary.empty) := by
      rw [ProcessOver.interleave_mapContext_left,
        ProcessOver.interleave_mapContext_right,
        OpenNodeContext.close_comp_map, OpenNodeContext.close_comp_map]
    cases W with | mk ProcW stepW stepSamplerW =>
    cases K with | mk ProcK stepK stepSamplerK =>
    simp only [OpenProcess.mapBoundary, OpenProcess.interleave]
    exact OpenProcess.ext_of_step_eq
      (eq_of_heq (heq_step_of_processOver_eq hproc)) HEq.rfl

instance : OpenTheory.IsLawful (openTheory.{u, v, w, w'} Party m schedulerSampler) where

/-! ## Monoidal and compact closed laws up to bisimilarity -/

/-- Parallel composition of open processes is associative up to bisimilarity:
reassociating the internal scheduler nesting does not change the observable
boundary behavior. -/
theorem openTheory_par_assoc_iso
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (W₃ : OpenProcess.{u, v, w, w'} m Party Δ₃) :
    OpenProcessIso
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom
        ((openTheory Party m schedulerSampler).par
          ((openTheory Party m schedulerSampler).par W₁ W₂) W₃))
      ((openTheory Party m schedulerSampler).par W₁
        ((openTheory Party m schedulerSampler).par W₂ W₃)) := by
  simp only [openTheory, OpenProcess.interleave]
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
        all_goals simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
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
        · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
    | false =>
      refine ⟨⟨⟨false⟩, ⟨⟨false⟩, rest⟩⟩, fun h => hvisible ?_, rfl, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration, Spec.Decoration.map]
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
        Spec.Decoration.map] at h
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2.2))⟩
      all_goals intro X ons
      all_goals simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
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
      all_goals simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
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
        · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
        · simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
        · simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
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
        all_goals simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]

/-- Parallel composition of open processes is commutative up to bisimilarity. -/
theorem openTheory_par_comm_iso
    {Δ₁ Δ₂ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (W₂ : OpenProcess.{u, v, w, w'} m Party Δ₂) :
    OpenProcessIso
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom
        ((openTheory Party m schedulerSampler).par W₁ W₂))
      ((openTheory Party m schedulerSampler).par W₂ W₁) := by
  simp only [openTheory, OpenProcess.interleave]
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
          simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]) _ _).mpr
        ((isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]) _ _).mp h.2)⟩
    | false =>
      refine ⟨⟨⟨true⟩, rest⟩, fun h => hvisible ?_, rfl, rfl⟩
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration]
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration] at h
      exact ⟨rfl, (isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]) _ _).mpr
        ((isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]) _ _).mp h.2)⟩
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
          simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]) _ _).mpr
        ((isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]) _ _).mp h.2)⟩
    | false =>
      refine ⟨⟨⟨true⟩, rest⟩, fun h => hvisible ?_, rfl, rfl⟩
      rw [isSilentStep_mapBoundary_iff] at h
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration]
      simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration] at h
      exact ⟨rfl, (isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]) _ _).mpr
        ((isSilentDecoration_iff_map _ (fun X ons => by
          simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]) _ _).mp h.2)⟩

/-- The unit for parallel composition is the trivial process with no boundary
and `PUnit` state. The sampler is the trivial `Decoration.done` sampler. -/
def openTheory_unit : OpenProcess.{u, v, w, w'} m Party PortBoundary.empty where
  Proc := PUnit
  step := fun _ =>
    { spec := .done
      semantics := ⟨⟩
      next := fun _ => PUnit.unit }
  stepSampler := fun _ => ⟨⟩

/-- The monoidal unit is a left identity for parallel composition up to
bisimilarity. -/
theorem openTheory_par_leftUnit_iso
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w, w'} m Party Δ) :
    OpenProcessIso
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom
        ((openTheory Party m schedulerSampler).par
          (openTheory_unit Party m) W))
      W := by
  simp only [openTheory, openTheory_unit, OpenProcess.interleave]
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
      simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]
  · intro tr₂ _
    exact .inl ⟨⟨⟨false⟩, tr₂⟩, rfl⟩
  · intro tr₂ hvisible
    refine ⟨⟨⟨false⟩, tr₂⟩, fun h => hvisible ?_, rfl⟩
    rw [isSilentStep_mapBoundary_iff] at h
    simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
      Spec.Decoration.map] at h
    refine (isSilentDecoration_iff_map _ ?_ _ _).mp h.2
    intro X ons
    simp [OpenNodeContext.inrTensor, BoundaryAction.embedInrTensor]

/-- The monoidal unit is a right identity for parallel composition up to
bisimilarity. -/
theorem openTheory_par_rightUnit_iso
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w, w'} m Party Δ) :
    OpenProcessIso
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyRight Δ).toHom
        ((openTheory Party m schedulerSampler).par W
          (openTheory_unit Party m)))
      W := by
  simp only [openTheory, openTheory_unit, OpenProcess.interleave]
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
      simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]
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
    simp [OpenNodeContext.inlTensor, BoundaryAction.embedInlTensor]

/-- The identity wire (coevaluation) on boundary `Γ`: relays messages
bidirectionally between `swap Γ` and `Γ`. -/
def openTheory_idWire (Γ : PortBoundary) :
    OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Γ) where
  Proc := PUnit
  step := fun _ =>
    { spec := .done
      semantics := ⟨⟩
      next := fun _ => PUnit.unit }
  stepSampler := fun _ => ⟨⟩

/-- Left zig-zag: wiring the identity wire on the left is a no-op up to
bisimilarity. -/
theorem openTheory_wire_idWire_iso
    (Γ : PortBoundary)
    {Δ₂ : PortBoundary}
    (W₂ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    OpenProcessIso
      ((openTheory Party m schedulerSampler).wire
        (openTheory_idWire Party m Γ) W₂)
      W₂ := by
  simp only [openTheory, openTheory_idWire, OpenProcess.interleave]
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
      simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
  · intro tr₂ _
    exact .inl ⟨⟨⟨false⟩, tr₂⟩, rfl⟩
  · intro tr₂ hvisible
    refine ⟨⟨⟨false⟩, tr₂⟩, fun h => hvisible ?_, rfl⟩
    simp only [IsSilentStep, ProcessOver.interleave, IsSilentDecoration,
      Spec.Decoration.map] at h
    refine (isSilentDecoration_iff_map _ ?_ _ _).mp h.2
    intro X ons
    simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]

/-- Right zig-zag: wiring the identity wire on the right is a no-op up to
bisimilarity. -/
theorem openTheory_wire_idWire_right_iso
    (Γ : PortBoundary)
    {Δ₁ : PortBoundary}
    (W₁ : OpenProcess.{u, v, w, w'} m Party
      (PortBoundary.tensor Δ₁ Γ)) :
    OpenProcessIso
      ((openTheory Party m schedulerSampler).wire W₁
        (openTheory_idWire Party m Γ))
      W₁ := by
  simp only [openTheory, openTheory_idWire, OpenProcess.interleave]
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
      simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
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
    simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]

/-- `plug` is derivable from `wire` plus boundary reshaping, up to
bisimilarity. -/
theorem openTheory_plug_eq_wire_iso
    {Δ : PortBoundary}
    (W : OpenProcess.{u, v, w, w'} m Party Δ)
    (K : OpenProcess.{u, v, w, w'} m Party (PortBoundary.swap Δ)) :
    OpenProcessIso
      ((openTheory Party m schedulerSampler).plug W K)
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
        ((openTheory Party m schedulerSampler).wire
          (OpenProcess.mapBoundary
            (PortBoundary.Equiv.tensorEmptyLeft Δ).symm.toHom W)
          (OpenProcess.mapBoundary
              (PortBoundary.Equiv.tensorEmptyRight
              (PortBoundary.swap Δ)).symm.toHom K))) := by
  simp only [openTheory, OpenProcess.interleave]
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
      · intro X ons; simp [OpenNodeContext.close, BoundaryAction.closed]
      · intro X ons
        simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · intro X ons; simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
    | false =>
      refine ⟨⟨⟨false⟩, rest⟩, fun h => hvisible ?_, rfl⟩
      rw [isSilentStep_mapBoundary_iff] at h
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mp
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
      · intro X ons; simp [OpenNodeContext.close, BoundaryAction.closed]
      · intro X ons
        simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · intro X ons; simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
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
      · intro X ons; simp [OpenNodeContext.wireLeft, BoundaryAction.wireLeft]
      · intro X ons
        simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · intro X ons; simp [OpenNodeContext.close, BoundaryAction.closed]
    | false =>
      refine ⟨⟨⟨false⟩, rest⟩, fun h => hvisible ?_, rfl⟩
      refine ⟨rfl, (isSilentDecoration_iff_map _ ?_ _ _).mpr
        ((isSilentDecoration_iff_map _ ?_ _ _).mpr
          ((isSilentDecoration_iff_map _ ?_ _ _).mp h.2))⟩
      · intro X ons; simp [OpenNodeContext.wireRight, BoundaryAction.wireRight]
      · intro X ons
        simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]
      · intro X ons; simp [OpenNodeContext.close, BoundaryAction.closed]

/-- The monoidal unit equals the coevaluation at the trivial boundary,
up to bisimilarity. -/
theorem openTheory_unit_eq_iso :
    OpenProcessIso
      (openTheory_unit.{u, v, w, w'} Party m)
      (OpenProcess.mapBoundary
        (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
        (openTheory_idWire Party m PortBoundary.empty)) :=
  ⟨fun _ _ => True, fun _ => ⟨PUnit.unit, trivial⟩, fun _ => ⟨PUnit.unit, trivial⟩,
    fun _ _ _ _ _ => .inl ⟨PUnit.unit, trivial⟩,
    fun _ _ _ _ hns => absurd trivial hns,
    fun _ _ _ _ _ => .inl ⟨PUnit.unit, trivial⟩,
    fun _ _ _ _ hns => absurd trivial hns⟩

end Model

end UC
end Interaction
