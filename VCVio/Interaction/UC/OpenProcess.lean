/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Concurrent.Process
import VCVio.Interaction.UC.Interface

/-!
# Open concurrent processes with boundary traffic

This file defines the semantic bridge between the closed-world concurrent
process core (`ProcessOver`, `StepOver`) and the open-world layer needed for
UC-style composition.

The key idea is simple: a closed concurrent step already records controller
paths and local views at each node. An **open** concurrent step additionally
records how each node may receive traffic from, or emit traffic to, an
external boundary.

The design follows the layered approach from the UC design notes:

* `BoundaryAction Δ X` records, at one protocol node with move space `X`,
  whether the node is externally activated and what outbound packets the
  chosen move contributes.
* `OpenNodeSemantics Party Δ X` extends the existing `NodeSemantics Party X`
  by one `BoundaryAction` field.
* `OpenStepContext Party Δ` is the resulting realized node context.
* `OpenProcess Party Δ` specializes `ProcessOver` to that open context.

The closed-world layer is recovered by the canonical forgetful projection
`openStepContextForget`, which drops the boundary action and retains only
the `NodeSemantics`. This means every `OpenProcess` can be viewed as a plain
closed `Process` by `ProcessOver.mapContext`.

Boundary actions are structurally mappable along `PortBoundary.Hom` via
`BoundaryAction.mapBoundary`. The `isActivated` flag is invariant under
boundary adaptation (only `emit` transforms), which ensures functoriality.
The query-level decoding of how input messages determine node moves belongs
in the runtime/execution layer, not the structural boundary action.
-/

universe u v w

namespace Interaction
namespace UC

open Concurrent

/--
`BoundaryAction Δ X` records the boundary traffic associated with one
protocol node whose move space is `X`, against an open boundary `Δ`.

Fields:

* `isActivated` flags whether this node is driven by external boundary
  input (`true`) or by the internal protocol dynamics (`false`).
* `emit` maps each chosen move to the list of outbound packets it
  contributes on `Δ.Out`.

The activation flag is a structural marker. The query-level information
about *how* an input message determines the node's move belongs in the
runtime/execution layer: charts (used by `PortBoundary.Hom`) can map
packets but cannot map queries, so the structural boundary action records
only the fact of activation, not the decoding.

The `emit` field records only the protocol's own direct output. Runtime-level
concerns (buffering, duplication, scheduling, delivery) belong in a separate
`Runtime` layer and are not encoded here.
-/
structure BoundaryAction (Δ : PortBoundary) (X : Type w) where
  isActivated : Bool := false
  emit : X → List (Interface.Packet Δ.Out) := fun _ => []

namespace BoundaryAction

/--
A purely internal node: not externally activated and no outbound packets.
-/
def internal (Δ : PortBoundary) (X : Type w) : BoundaryAction Δ X where
  isActivated := false
  emit := fun _ => []

/--
A boundary-activated node that emits no outbound packets.
-/
def activated (Δ : PortBoundary) (X : Type w) : BoundaryAction Δ X where
  isActivated := true

/--
An internally driven node that emits outbound packets.
-/
def outputOnly {Δ : PortBoundary} {X : Type w}
    (e : X → List (Interface.Packet Δ.Out)) : BoundaryAction Δ X where
  emit := e

/--
Transform a boundary action along a boundary adaptation.

The activation flag is preserved (it does not depend on the boundary
presentation). The emitted packets are translated forward along
`φ.onOut`.
-/
def mapBoundary {Δ₁ Δ₂ : PortBoundary} {X : Type w}
    (φ : PortBoundary.Hom Δ₁ Δ₂) (b : BoundaryAction Δ₁ X) :
    BoundaryAction Δ₂ X where
  isActivated := b.isActivated
  emit x := (b.emit x).map (Interface.Hom.mapPacket φ.onOut)

@[simp]
theorem mapBoundary_id {Δ : PortBoundary} {X : Type w}
    (b : BoundaryAction Δ X) :
    mapBoundary (PortBoundary.Hom.id Δ) b = b := by
  simp [mapBoundary, PortBoundary.Hom.id, Interface.Hom.mapPacket_id]

@[simp]
theorem mapBoundary_comp {Δ₁ Δ₂ Δ₃ : PortBoundary} {X : Type w}
    (g : PortBoundary.Hom Δ₂ Δ₃) (f : PortBoundary.Hom Δ₁ Δ₂)
    (b : BoundaryAction Δ₁ X) :
    mapBoundary g (mapBoundary f b) =
      mapBoundary (PortBoundary.Hom.comp g f) b := by
  simp [mapBoundary, PortBoundary.Hom.comp, List.map_map,
    Interface.Hom.mapPacket_comp]

/--
Embed a boundary action on the left factor into the tensor boundary.

Emitted packets are injected into the left summand of the combined output
interface. The activation flag is preserved.
-/
def embedInlTensor {Δ₁ : PortBoundary} (Δ₂ : PortBoundary) {X : Type w}
    (b : BoundaryAction Δ₁ X) :
    BoundaryAction (PortBoundary.tensor Δ₁ Δ₂) X where
  isActivated := b.isActivated
  emit x := (b.emit x).map (Interface.Hom.mapPacket (Interface.Hom.inl Δ₁.Out Δ₂.Out))

/--
Embed a boundary action on the right factor into the tensor boundary.

Emitted packets are injected into the right summand of the combined output
interface. The activation flag is preserved.
-/
def embedInrTensor (Δ₁ : PortBoundary) {Δ₂ : PortBoundary} {X : Type w}
    (b : BoundaryAction Δ₂ X) :
    BoundaryAction (PortBoundary.tensor Δ₁ Δ₂) X where
  isActivated := b.isActivated
  emit x := (b.emit x).map (Interface.Hom.mapPacket (Interface.Hom.inr Δ₁.Out Δ₂.Out))

/--
Transform a boundary action on `tensor Δ₁ Γ` into one on `tensor Δ₁ Δ₂`
by keeping only the left-summand (Δ₁) packets and re-injecting them
into the left summand of the combined output. Right-summand (Γ) packets
are dropped (they become internal traffic handled by the runtime).
-/
def wireLeft {Δ₁ Γ : PortBoundary} (Δ₂ : PortBoundary) {X : Type w}
    (b : BoundaryAction (PortBoundary.tensor Δ₁ Γ) X) :
    BoundaryAction (PortBoundary.tensor Δ₁ Δ₂) X where
  isActivated := b.isActivated
  emit x := (b.emit x).filterMap fun
    | ⟨Sum.inl a₁, m⟩ => some ⟨Sum.inl a₁, m⟩
    | ⟨Sum.inr _, _⟩ => none

/--
Transform a boundary action on `tensor (swap Γ) Δ₂` into one on
`tensor Δ₁ Δ₂` by keeping only the right-summand (Δ₂) packets and
re-injecting them into the right summand of the combined output.
Left-summand (swap Γ) packets are dropped (internal traffic).
-/
def wireRight (Δ₁ : PortBoundary) {Γ Δ₂ : PortBoundary} {X : Type w}
    (b : BoundaryAction (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) X) :
    BoundaryAction (PortBoundary.tensor Δ₁ Δ₂) X where
  isActivated := b.isActivated
  emit x := (b.emit x).filterMap fun
    | ⟨Sum.inl _, _⟩ => none
    | ⟨Sum.inr a₂, m⟩ => some ⟨Sum.inr a₂, m⟩

/--
Close a boundary action by dropping all external traffic.

The result lives on `PortBoundary.empty` and has no activation or emission.
This is used by `plug` to internalize all boundary interactions.
-/
def closed {Δ : PortBoundary} {X : Type w}
    (_b : BoundaryAction Δ X) :
    BoundaryAction PortBoundary.empty X :=
  .internal PortBoundary.empty X

end BoundaryAction

/--
`OpenNodeSemantics Party Δ X` extends `NodeSemantics Party X` with one
`BoundaryAction Δ X` recording the node's interaction with an external
boundary.

This is the per-node data that distinguishes an open process from a closed
one: the closed part (`controllers`, `views`) describes internal control and
observation, while `boundary` describes the node's interface with the outside
world.
-/
structure OpenNodeSemantics (Party : Type u) (Δ : PortBoundary) (X : Type w)
    extends NodeSemantics Party X where
  boundary : BoundaryAction Δ X := .internal Δ X

namespace OpenNodeSemantics

/--
Build an `OpenNodeSemantics` from a closed `NodeSemantics` by marking the node
as purely internal (no boundary traffic).
-/
def ofClosed {Party : Type u} {Δ : PortBoundary} {X : Type w}
    (ns : NodeSemantics Party X) : OpenNodeSemantics Party Δ X where
  toNodeSemantics := ns

/--
Transform the boundary action of an open node semantics along a boundary
adaptation, preserving the closed-world node semantics.
-/
def mapBoundary {Party : Type u} {Δ₁ Δ₂ : PortBoundary} {X : Type w}
    (φ : PortBoundary.Hom Δ₁ Δ₂) (ons : OpenNodeSemantics Party Δ₁ X) :
    OpenNodeSemantics Party Δ₂ X where
  toNodeSemantics := ons.toNodeSemantics
  boundary := ons.boundary.mapBoundary φ

@[simp]
theorem mapBoundary_id {Party : Type u} {Δ : PortBoundary} {X : Type w}
    (ons : OpenNodeSemantics Party Δ X) :
    mapBoundary (PortBoundary.Hom.id Δ) ons = ons := by
  cases ons; simp [mapBoundary, BoundaryAction.mapBoundary_id]

@[simp]
theorem mapBoundary_comp {Party : Type u}
    {Δ₁ Δ₂ Δ₃ : PortBoundary} {X : Type w}
    (g : PortBoundary.Hom Δ₂ Δ₃) (f : PortBoundary.Hom Δ₁ Δ₂)
    (ons : OpenNodeSemantics Party Δ₁ X) :
    mapBoundary g (mapBoundary f ons) =
      mapBoundary (PortBoundary.Hom.comp g f) ons := by
  cases ons; simp [mapBoundary, BoundaryAction.mapBoundary_comp]

end OpenNodeSemantics

/--
The open-world node context for processes with boundary `Δ`.

At a node with move space `X`, the context value is
`OpenNodeSemantics Party Δ X`: the usual controller-path and local-view data,
plus a `BoundaryAction` describing the node's external traffic.
-/
abbrev OpenStepContext (Party : Type u) (Δ : PortBoundary) :=
  fun (X : Type w) => OpenNodeSemantics Party Δ X

/--
The forgetful map from the open-world context to the closed-world context.

This drops the `BoundaryAction` and retains only the `NodeSemantics`
(controllers and local views).
-/
def openStepContextForget (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenStepContext Party Δ : Spec.Node.Context.{w})
      (StepContext Party) :=
  fun _ ons => ons.toNodeSemantics

/--
The embedding from the closed-world context into the open-world context.

This marks every node as purely internal (no boundary traffic).
-/
def openStepContextEmbed (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.ContextHom
      (StepContext Party)
      (OpenStepContext Party Δ : Spec.Node.Context.{w}) :=
  fun _ ns => .ofClosed ns

/--
The context hom induced by a boundary adaptation.

This transforms every node's boundary action along `φ` while preserving
the closed-world node semantics.
-/
def openStepContextMap (Party : Type u) {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂) :
    Spec.Node.ContextHom
      (OpenStepContext Party Δ₁ : Spec.Node.Context.{w})
      (OpenStepContext Party Δ₂ : Spec.Node.Context.{w}) :=
  fun _ ons => ons.mapBoundary φ

@[simp]
theorem openStepContextMap_id (Party : Type u) (Δ : PortBoundary) :
    openStepContextMap.{u, w} Party (PortBoundary.Hom.id Δ) =
      Spec.Node.ContextHom.id _ := by
  funext X ons; simp [openStepContextMap, Spec.Node.ContextHom.id]

theorem openStepContextMap_comp (Party : Type u)
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (g : PortBoundary.Hom Δ₂ Δ₃) (f : PortBoundary.Hom Δ₁ Δ₂) :
    Spec.Node.ContextHom.comp
      (openStepContextMap.{u, w} Party g) (openStepContextMap Party f) =
      openStepContextMap Party (PortBoundary.Hom.comp g f) := by
  funext X ons; simp [openStepContextMap, Spec.Node.ContextHom.comp,
    OpenNodeSemantics.mapBoundary_comp]

/--
Embed the left factor's open-world context into the tensor boundary context.

This injects emitted packets into the left summand of the combined output
interface while preserving the closed-world node semantics.
-/
def openStepContextInlTensor (Party : Type u)
    (Δ₁ : PortBoundary) (Δ₂ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenStepContext Party Δ₁ : Spec.Node.Context.{w})
      (OpenStepContext Party (PortBoundary.tensor Δ₁ Δ₂) : Spec.Node.Context.{w}) :=
  fun _ ons => {
    toNodeSemantics := ons.toNodeSemantics
    boundary := ons.boundary.embedInlTensor Δ₂
  }

/--
Embed the right factor's open-world context into the tensor boundary context.

This injects emitted packets into the right summand of the combined output
interface while preserving the closed-world node semantics.
-/
def openStepContextInrTensor (Party : Type u)
    (Δ₁ : PortBoundary) (Δ₂ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenStepContext Party Δ₂ : Spec.Node.Context.{w})
      (OpenStepContext Party (PortBoundary.tensor Δ₁ Δ₂) : Spec.Node.Context.{w}) :=
  fun _ ons => {
    toNodeSemantics := ons.toNodeSemantics
    boundary := ons.boundary.embedInrTensor Δ₁
  }

/--
Wire the left factor: transform `OpenStepContext Party (tensor Δ₁ Γ)` into
`OpenStepContext Party (tensor Δ₁ Δ₂)` by filtering out internal (Γ) packets
and keeping only external (Δ₁) packets.
-/
def openStepContextWireLeft (Party : Type u)
    (Δ₁ Γ Δ₂ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenStepContext Party (PortBoundary.tensor Δ₁ Γ) : Spec.Node.Context.{w})
      (OpenStepContext Party (PortBoundary.tensor Δ₁ Δ₂) : Spec.Node.Context.{w}) :=
  fun _ ons => {
    toNodeSemantics := ons.toNodeSemantics
    boundary := ons.boundary.wireLeft Δ₂
  }

/--
Wire the right factor: transform
`OpenStepContext Party (tensor (swap Γ) Δ₂)` into
`OpenStepContext Party (tensor Δ₁ Δ₂)` by filtering out internal
(swap Γ) packets and keeping only external (Δ₂) packets.
-/
def openStepContextWireRight (Party : Type u)
    (Δ₁ Γ Δ₂ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenStepContext Party (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) :
        Spec.Node.Context.{w})
      (OpenStepContext Party (PortBoundary.tensor Δ₁ Δ₂) : Spec.Node.Context.{w}) :=
  fun _ ons => {
    toNodeSemantics := ons.toNodeSemantics
    boundary := ons.boundary.wireRight Δ₁
  }

/--
Close the boundary: transform `OpenStepContext Party Δ` into
`OpenStepContext Party empty` by dropping all boundary traffic.
Used by `plug` to internalize all external interactions.
-/
def openStepContextClose (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenStepContext Party Δ : Spec.Node.Context.{w})
      (OpenStepContext Party PortBoundary.empty : Spec.Node.Context.{w}) :=
  fun _ ons => {
    toNodeSemantics := ons.toNodeSemantics
    boundary := ons.boundary.closed
  }

/--
The open-world specialization of `StepOver`.

Here the node context carries `OpenNodeSemantics Party Δ`, so every node
records both the usual controller/view data and its boundary traffic against
`Δ`.
-/
abbrev OpenStep (Party : Type u) (Δ : PortBoundary) (P : Type v) :=
  StepOver (OpenStepContext Party Δ : Spec.Node.Context.{w}) P

/--
The open-world specialization of `ProcessOver`.

An `OpenProcess Party Δ` is a continuation-based process whose steps are
decorated by `OpenNodeSemantics Party Δ`. It exposes the directed boundary
`Δ` to an external context.

The closed-world `Process Party` is recovered by
`ProcessOver.mapContext (openStepContextForget Party Δ)`.
-/
abbrev OpenProcess (Party : Type u) (Δ : PortBoundary) :=
  ProcessOver (OpenStepContext Party Δ : Spec.Node.Context.{w})

namespace OpenProcess

/--
Forget the boundary layer and view an open process as a plain closed-world
process.

This is the canonical projection: it drops all `BoundaryAction` data from
every node while preserving the process structure, controller paths, and
local views.
-/
def toClosed {Party : Type u} {Δ : PortBoundary}
    (op : OpenProcess.{u, v, w} Party Δ) : Process Party :=
  op.mapContext (openStepContextForget Party Δ)

/--
Embed a closed-world process as an open process with no boundary traffic.

Every node is marked as purely internal: `isActivated = false` and `emit`
produces no packets.
-/
def ofClosed {Party : Type u} {Δ : PortBoundary}
    (p : Process.{u, v, w} Party) : OpenProcess Party Δ :=
  p.mapContext (openStepContextEmbed Party Δ)

/--
Adapt the exposed boundary of an open process along a structural boundary
morphism.

This transforms every node's boundary action along `φ` (translating emitted
packets, preserving activation flags) while leaving the process structure
and closed-world node semantics unchanged.
-/
def mapBoundary {Party : Type u} {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂) (op : OpenProcess.{u, v, w} Party Δ₁) :
    OpenProcess Party Δ₂ :=
  op.mapContext (openStepContextMap Party φ)

end OpenProcess

/--
`OpenProcess.System` augments an open process by the standard verification
predicates used throughout VCVio.
-/
abbrev OpenProcess.System (Party : Type u) (Δ : PortBoundary) :=
  ProcessOver.System (OpenStepContext Party Δ : Spec.Node.Context.{w})

end UC
end Interaction
