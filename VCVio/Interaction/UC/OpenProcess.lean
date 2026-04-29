/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import ToMathlib.PFunctor.Trace
import VCVio.Interaction.Basic.Sampler
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
* `OpenNodeProfile Party Δ X` extends the existing `NodeProfile Party X`
  by one `BoundaryAction` field.
* `OpenNodeContext Party Δ` is the resulting realized node context.
* `OpenProcess Party Δ` specializes `ProcessOver` to that open context.

The closed-world layer is recovered by the canonical forgetful projection
`OpenNodeContext.forget`, which drops the boundary action and retains only
the `NodeProfile`. This means every `OpenProcess` can be viewed as a plain
closed `Process` by `ProcessOver.mapContext`.

Boundary actions are structurally mappable along `PortBoundary.Hom` via
`BoundaryAction.mapBoundary`. The `isActivated` flag is invariant under
boundary adaptation (only `emit` transforms), which ensures functoriality.
The query-level decoding of how input messages determine node moves belongs
in the runtime/execution layer, not the structural boundary action.

The `emit` field is presented as a `PFunctor.Trace Δ.Out X` (the free-monoid
trace on `Δ.Out`-events indexed by the node's move space `X`). This makes the
structural boundary operations land directly in the generic `Trace` API:
`mapBoundary` is `Trace.mapChart` on the output chart, and `wireLeft` /
`wireRight` are `Trace.mapPartial` on the appropriate sum projections. The
empty-emission default is the trace-monoid unit `1`, which is definitionally
the constant-`[]` trace.
-/

universe u v w w'

namespace Interaction
namespace UC

open Concurrent

/--
`BoundaryAction Δ X` records the boundary traffic associated with one
protocol node whose move space is `X`, against an open boundary `Δ`.

Fields:

* `isActivated` flags whether this node is driven by external boundary
  input (`true`) or by the internal protocol dynamics (`false`).
* `emit` is the `PFunctor.Trace Δ.Out X` recording, for each chosen move
  `x : X`, the finite ordered list of outbound packets contributed on
  `Δ.Out`. The default is the monoid unit `1`, which is definitionally
  the constant-`[]` trace.

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
  emit : PFunctor.Trace Δ.Out X := 1

namespace BoundaryAction

/--
A purely internal node: not externally activated and no outbound packets.
-/
def internal (Δ : PortBoundary) (X : Type w) : BoundaryAction Δ X where
  isActivated := false
  emit := 1

/--
A boundary-activated node that emits no outbound packets.
-/
def activated (Δ : PortBoundary) (X : Type w) : BoundaryAction Δ X where
  isActivated := true

/--
An internally driven node that emits outbound packets.
-/
def outputOnly {Δ : PortBoundary} {X : Type w}
    (e : PFunctor.Trace Δ.Out X) : BoundaryAction Δ X where
  emit := e

/--
Transform a boundary action along a boundary adaptation.

The activation flag is preserved (it does not depend on the boundary
presentation). The emitted-trace is pushed forward along the output chart
`φ.onOut` via `PFunctor.Trace.mapChart`.
-/
def mapBoundary {Δ₁ Δ₂ : PortBoundary} {X : Type w}
    (φ : PortBoundary.Hom Δ₁ Δ₂) (b : BoundaryAction Δ₁ X) :
    BoundaryAction Δ₂ X where
  isActivated := b.isActivated
  emit := PFunctor.Trace.mapChart φ.onOut b.emit

@[simp]
theorem mapBoundary_id {Δ : PortBoundary} {X : Type w}
    (b : BoundaryAction Δ X) :
    mapBoundary (PortBoundary.Hom.id Δ) b = b := by
  simp [mapBoundary, PortBoundary.Hom.id, Interface.Hom.id]

@[simp]
theorem mapBoundary_comp {Δ₁ Δ₂ Δ₃ : PortBoundary} {X : Type w}
    (g : PortBoundary.Hom Δ₂ Δ₃) (f : PortBoundary.Hom Δ₁ Δ₂)
    (b : BoundaryAction Δ₁ X) :
    mapBoundary g (mapBoundary f b) =
      mapBoundary (PortBoundary.Hom.comp g f) b := by
  simp [mapBoundary, PortBoundary.Hom.comp, Interface.Hom.comp,
    PFunctor.Trace.mapChart_comp]

/--
Embed a boundary action on the left factor into the tensor boundary.

The trace is pushed forward along the left-injection chart
`Interface.Hom.inl Δ₁.Out Δ₂.Out` via `PFunctor.Trace.mapChart`. The
activation flag is preserved.
-/
def embedInlTensor {Δ₁ : PortBoundary} (Δ₂ : PortBoundary) {X : Type w}
    (b : BoundaryAction Δ₁ X) :
    BoundaryAction (PortBoundary.tensor Δ₁ Δ₂) X where
  isActivated := b.isActivated
  emit := PFunctor.Trace.mapChart (Interface.Hom.inl Δ₁.Out Δ₂.Out) b.emit

/--
Embed a boundary action on the right factor into the tensor boundary.

The trace is pushed forward along the right-injection chart
`Interface.Hom.inr Δ₁.Out Δ₂.Out` via `PFunctor.Trace.mapChart`. The
activation flag is preserved.
-/
def embedInrTensor (Δ₁ : PortBoundary) {Δ₂ : PortBoundary} {X : Type w}
    (b : BoundaryAction Δ₂ X) :
    BoundaryAction (PortBoundary.tensor Δ₁ Δ₂) X where
  isActivated := b.isActivated
  emit := PFunctor.Trace.mapChart (Interface.Hom.inr Δ₁.Out Δ₂.Out) b.emit

/--
Transform a boundary action on `tensor Δ₁ Γ` into one on `tensor Δ₁ Δ₂`
by keeping only the left-summand (Δ₁) packets and re-injecting them
into the left summand of the combined output. Right-summand (Γ) packets
are dropped (they become internal traffic handled by the runtime).

Implemented as `PFunctor.Trace.mapPartial` on the appropriate index-level
partial map.
-/
def wireLeft {Δ₁ Γ : PortBoundary} (Δ₂ : PortBoundary) {X : Type w}
    (b : BoundaryAction (PortBoundary.tensor Δ₁ Γ) X) :
    BoundaryAction (PortBoundary.tensor Δ₁ Δ₂) X where
  isActivated := b.isActivated
  emit := PFunctor.Trace.mapPartial
    (P := (PortBoundary.tensor Δ₁ Γ).Out)
    (Q := (PortBoundary.tensor Δ₁ Δ₂).Out)
    (fun
      | ⟨Sum.inl a₁, m⟩ => some ⟨Sum.inl a₁, m⟩
      | ⟨Sum.inr _, _⟩ => none) b.emit

/--
Transform a boundary action on `tensor (swap Γ) Δ₂` into one on
`tensor Δ₁ Δ₂` by keeping only the right-summand (Δ₂) packets and
re-injecting them into the right summand of the combined output.
Left-summand (swap Γ) packets are dropped (internal traffic).

Implemented as `PFunctor.Trace.mapPartial` on the appropriate index-level
partial map.
-/
def wireRight (Δ₁ : PortBoundary) {Γ Δ₂ : PortBoundary} {X : Type w}
    (b : BoundaryAction (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) X) :
    BoundaryAction (PortBoundary.tensor Δ₁ Δ₂) X where
  isActivated := b.isActivated
  emit := PFunctor.Trace.mapPartial
    (P := (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂).Out)
    (Q := (PortBoundary.tensor Δ₁ Δ₂).Out)
    (fun
      | ⟨Sum.inl _, _⟩ => none
      | ⟨Sum.inr a₂, m⟩ => some ⟨Sum.inr a₂, m⟩) b.emit

/--
Close a boundary action by dropping all external traffic.

The result lives on `PortBoundary.empty` and has no activation or emission.
This is used by `plug` to internalize all boundary interactions. The
emitted-trace is the monoid unit `1`, which is definitionally the constant-`[]`
trace.
-/
def closed {Δ : PortBoundary} {X : Type w}
    (b : BoundaryAction Δ X) :
    BoundaryAction PortBoundary.empty X where
  isActivated := b.isActivated
  emit := 1

@[simp]
theorem mapBoundary_embedInlTensor
    {Δ₁ Δ₁' : PortBoundary} {Δ₂ Δ₂' : PortBoundary} {X : Type w}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁') (f₂ : PortBoundary.Hom Δ₂ Δ₂')
    (b : BoundaryAction Δ₁ X) :
    (b.embedInlTensor Δ₂).mapBoundary (PortBoundary.Hom.tensor f₁ f₂) =
      (b.mapBoundary f₁).embedInlTensor Δ₂' := by
  simp only [mapBoundary, embedInlTensor, PortBoundary.Hom.tensor]
  congr 1
  rw [← PFunctor.Trace.mapChart_comp, ← PFunctor.Trace.mapChart_comp]
  exact congrArg (PFunctor.Trace.mapChart · b.emit)
    (Interface.Hom.comp_sum_inl f₁.onOut f₂.onOut)

@[simp]
theorem mapBoundary_embedInrTensor
    {Δ₁ Δ₁' : PortBoundary} {Δ₂ Δ₂' : PortBoundary} {X : Type w}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁') (f₂ : PortBoundary.Hom Δ₂ Δ₂')
    (b : BoundaryAction Δ₂ X) :
    (b.embedInrTensor Δ₁).mapBoundary (PortBoundary.Hom.tensor f₁ f₂) =
      (b.mapBoundary f₂).embedInrTensor Δ₁' := by
  simp only [mapBoundary, embedInrTensor, PortBoundary.Hom.tensor]
  congr 1
  rw [← PFunctor.Trace.mapChart_comp, ← PFunctor.Trace.mapChart_comp]
  exact congrArg (PFunctor.Trace.mapChart · b.emit)
    (Interface.Hom.comp_sum_inr f₁.onOut f₂.onOut)

@[simp]
theorem closed_mapBoundary
    {Δ₁ Δ₂ : PortBoundary} {X : Type w}
    (φ : PortBoundary.Hom Δ₁ Δ₂)
    (b : BoundaryAction Δ₁ X) :
    (b.mapBoundary φ).closed = b.closed := rfl

@[simp]
theorem mapBoundary_wireLeft
    {Δ₁ Δ₁' Γ : PortBoundary} {Δ₂ Δ₂' : PortBoundary} {X : Type w}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁') (f₂ : PortBoundary.Hom Δ₂ Δ₂')
    (b : BoundaryAction (PortBoundary.tensor Δ₁ Γ) X) :
    (b.wireLeft Δ₂).mapBoundary (PortBoundary.Hom.tensor f₁ f₂) =
      (b.mapBoundary
        (PortBoundary.Hom.tensor f₁ (PortBoundary.Hom.id Γ))).wireLeft Δ₂' := by
  simp only [wireLeft, mapBoundary, PortBoundary.Hom.tensor, PortBoundary.Hom.id]
  congr 1
  funext x
  simp only [PFunctor.Trace.mapChart_apply, PFunctor.Trace.mapPartial_apply,
    List.filterMap_filterMap]
  congr 1
  funext ⟨pkt_port, pkt_msg⟩
  cases pkt_port <;> rfl

@[simp]
theorem mapBoundary_wireRight
    {Δ₁ Δ₁' : PortBoundary} {Γ Δ₂ Δ₂' : PortBoundary} {X : Type w}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁') (f₂ : PortBoundary.Hom Δ₂ Δ₂')
    (b : BoundaryAction (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) X) :
    (b.wireRight Δ₁).mapBoundary (PortBoundary.Hom.tensor f₁ f₂) =
      (b.mapBoundary
        (PortBoundary.Hom.tensor
          (PortBoundary.Hom.id (PortBoundary.swap Γ)) f₂)).wireRight Δ₁' := by
  simp only [wireRight, mapBoundary, PortBoundary.Hom.tensor, PortBoundary.Hom.id]
  congr 1
  funext x
  simp only [PFunctor.Trace.mapChart_apply, PFunctor.Trace.mapPartial_apply,
    List.filterMap_filterMap]
  congr 1
  funext ⟨pkt_port, pkt_msg⟩
  cases pkt_port <;> rfl

end BoundaryAction

/--
`OpenNodeProfile Party Δ X` extends `NodeProfile Party X` with one
`BoundaryAction Δ X` recording the node's interaction with an external
boundary.

This is the per-node data that distinguishes an open process from a closed
one: the closed part (`controllers`, `views`) describes internal control and
observation, while `boundary` describes the node's interface with the outside
world.
-/
structure OpenNodeProfile (Party : Type u) (Δ : PortBoundary) (X : Type w)
    extends NodeProfile Party X where
  boundary : BoundaryAction Δ X := .internal Δ X

namespace OpenNodeProfile

/--
Build an `OpenNodeProfile` from a closed `NodeProfile` by marking the node
as purely internal (no boundary traffic).
-/
def ofClosed {Party : Type u} {Δ : PortBoundary} {X : Type w}
    (ns : NodeProfile Party X) : OpenNodeProfile Party Δ X where
  toNodeProfile := ns

/--
Transform the boundary action of an open node profile along a boundary
adaptation, preserving the closed-world node profile.
-/
def mapBoundary {Party : Type u} {Δ₁ Δ₂ : PortBoundary} {X : Type w}
    (φ : PortBoundary.Hom Δ₁ Δ₂) (ons : OpenNodeProfile Party Δ₁ X) :
    OpenNodeProfile Party Δ₂ X where
  toNodeProfile := ons.toNodeProfile
  boundary := ons.boundary.mapBoundary φ

@[simp]
theorem mapBoundary_id {Party : Type u} {Δ : PortBoundary} {X : Type w}
    (ons : OpenNodeProfile Party Δ X) :
    mapBoundary (PortBoundary.Hom.id Δ) ons = ons := by
  cases ons; simp [mapBoundary, BoundaryAction.mapBoundary_id]

@[simp]
theorem mapBoundary_comp {Party : Type u}
    {Δ₁ Δ₂ Δ₃ : PortBoundary} {X : Type w}
    (g : PortBoundary.Hom Δ₂ Δ₃) (f : PortBoundary.Hom Δ₁ Δ₂)
    (ons : OpenNodeProfile Party Δ₁ X) :
    mapBoundary g (mapBoundary f ons) =
      mapBoundary (PortBoundary.Hom.comp g f) ons := by
  cases ons; simp [mapBoundary, BoundaryAction.mapBoundary_comp]

end OpenNodeProfile

/--
The open-world node context for processes with boundary `Δ`.

At a node with move space `X`, the context value is
`OpenNodeProfile Party Δ X`: the usual controller-path and local-view data,
plus a `BoundaryAction` describing the node's external traffic.

## Polynomial reading

`OpenNodeContext Party Δ` is, up to the named-field-vs-pair identification
exhibited by `OpenNodeContext.equivProductView`, the non-dependent context
product

```
Spec.Node.Context.prod (StepContext Party) (fun X => BoundaryAction Δ X)
```

That is, the open node context is the polynomial product of the closed
`StepContext Party` and the boundary-action context `fun X => BoundaryAction Δ X`,
with both factors carried independently at each move space `X`. The
hand-rolled context-homs below (`forget`, `embed`, `map`, `inlTensor`,
`inrTensor`, `wireLeft`, `wireRight`, `close`) are concrete instances of
the universal projection / pairing maps for this product, specialized to
the particular boundary-action transformations they perform. The structure
form `OpenNodeProfile extends NodeProfile` is preserved as the working
API because it gives clean `{ toNodeProfile := ..., boundary := ... }`
construction sites and definitional projections used pervasively below.
-/
abbrev OpenNodeContext (Party : Type u) (Δ : PortBoundary) :=
  fun (X : Type w) => OpenNodeProfile Party Δ X

namespace OpenNodeContext

/-! ### Polynomial-product bridge

Exhibit `OpenNodeContext Party Δ` as the non-dependent polynomial product
of the closed `StepContext Party` and the boundary-action context, and
prove that the bridge is a definitional isomorphism (round trips reduce
to `rfl` by `Prod.mk.eta` and structure eta). The product view lets one
phrase universal-property arguments without repeatedly pattern-matching
on `OpenNodeProfile` literals; the structural API below is the working
form. -/

/-- The polynomial-product view of `OpenNodeContext`. Lives in the same
universes as `OpenNodeContext Party Δ` itself: the first universe is the
move-space universe `w`, and the second is whatever Lean infers for
`NodeProfile Party X × BoundaryAction Δ X`. -/
abbrev productView (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.Context.{w} :=
  Spec.Node.Context.prod (StepContext Party)
    (fun X : Type w => BoundaryAction Δ X)

/--
Forward direction of the polynomial-product bridge: read off the
`(NodeProfile, BoundaryAction)` pair from an `OpenNodeProfile`. -/
def toProductView (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenNodeContext Party Δ : Spec.Node.Context.{w})
      (productView.{u, w} Party Δ) :=
  fun _ ons => (ons.toNodeProfile, ons.boundary)

/--
Inverse direction of the polynomial-product bridge: reassemble an
`OpenNodeProfile` from a `(NodeProfile, BoundaryAction)` pair. -/
def ofProductView (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.ContextHom
      (productView.{u, w} Party Δ)
      (OpenNodeContext Party Δ : Spec.Node.Context.{w}) :=
  fun _ p => { toNodeProfile := p.1, boundary := p.2 }

@[simp]
theorem toProductView_ofProductView (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.ContextHom.comp
        (toProductView.{u, w} Party Δ) (ofProductView Party Δ) =
      Spec.Node.ContextHom.id (productView Party Δ) := by
  funext X p
  cases p
  rfl

@[simp]
theorem ofProductView_toProductView (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.ContextHom.comp
        (ofProductView.{u, w} Party Δ) (toProductView Party Δ) =
      Spec.Node.ContextHom.id (OpenNodeContext Party Δ) := by
  funext X ons
  cases ons
  simp [Spec.Node.ContextHom.comp, Spec.Node.ContextHom.id,
    toProductView, ofProductView]

/--
The forgetful map from the open-world context to the closed-world context.

This drops the `BoundaryAction` and retains only the `NodeProfile`
(controllers and local views).
-/
def forget (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenNodeContext Party Δ : Spec.Node.Context.{w})
      (StepContext Party) :=
  fun _ ons => ons.toNodeProfile

/--
The embedding from the closed-world context into the open-world context.

This marks every node as purely internal (no boundary traffic).
-/
def embed (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.ContextHom
      (StepContext Party)
      (OpenNodeContext Party Δ : Spec.Node.Context.{w}) :=
  fun _ ns => .ofClosed ns

/--
The context hom induced by a boundary adaptation.

This transforms every node's boundary action along `φ` while preserving
the closed-world node semantics.
-/
def map (Party : Type u) {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂) :
    Spec.Node.ContextHom
      (OpenNodeContext Party Δ₁ : Spec.Node.Context.{w})
      (OpenNodeContext Party Δ₂ : Spec.Node.Context.{w}) :=
  fun _ ons => ons.mapBoundary φ

@[simp]
theorem map_id (Party : Type u) (Δ : PortBoundary) :
    OpenNodeContext.map.{u, w} Party (PortBoundary.Hom.id Δ) =
      Spec.Node.ContextHom.id _ := by
  funext X ons; simp [map, Spec.Node.ContextHom.id]

theorem map_comp (Party : Type u)
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (g : PortBoundary.Hom Δ₂ Δ₃) (f : PortBoundary.Hom Δ₁ Δ₂) :
    Spec.Node.ContextHom.comp
      (OpenNodeContext.map.{u, w} Party g) (OpenNodeContext.map Party f) =
      OpenNodeContext.map Party (PortBoundary.Hom.comp g f) := by
  funext X ons; simp [map, Spec.Node.ContextHom.comp,
    OpenNodeProfile.mapBoundary_comp]

/--
Embed the left factor's open-world context into the tensor boundary context.

This injects emitted packets into the left summand of the combined output
interface while preserving the closed-world node semantics.
-/
def inlTensor (Party : Type u)
    (Δ₁ : PortBoundary) (Δ₂ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenNodeContext Party Δ₁ : Spec.Node.Context.{w})
      (OpenNodeContext Party (PortBoundary.tensor Δ₁ Δ₂) : Spec.Node.Context.{w}) :=
  fun _ ons => {
    toNodeProfile := ons.toNodeProfile
    boundary := ons.boundary.embedInlTensor Δ₂
  }

/--
Embed the right factor's open-world context into the tensor boundary context.

This injects emitted packets into the right summand of the combined output
interface while preserving the closed-world node semantics.
-/
def inrTensor (Party : Type u)
    (Δ₁ : PortBoundary) (Δ₂ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenNodeContext Party Δ₂ : Spec.Node.Context.{w})
      (OpenNodeContext Party (PortBoundary.tensor Δ₁ Δ₂) : Spec.Node.Context.{w}) :=
  fun _ ons => {
    toNodeProfile := ons.toNodeProfile
    boundary := ons.boundary.embedInrTensor Δ₁
  }

/--
Wire the left factor: transform `OpenNodeContext Party (tensor Δ₁ Γ)` into
`OpenNodeContext Party (tensor Δ₁ Δ₂)` by filtering out internal (Γ) packets
and keeping only external (Δ₁) packets.
-/
def wireLeft (Party : Type u)
    (Δ₁ Γ Δ₂ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenNodeContext Party (PortBoundary.tensor Δ₁ Γ) : Spec.Node.Context.{w})
      (OpenNodeContext Party (PortBoundary.tensor Δ₁ Δ₂) : Spec.Node.Context.{w}) :=
  fun _ ons => {
    toNodeProfile := ons.toNodeProfile
    boundary := ons.boundary.wireLeft Δ₂
  }

/--
Wire the right factor: transform
`OpenNodeContext Party (tensor (swap Γ) Δ₂)` into
`OpenNodeContext Party (tensor Δ₁ Δ₂)` by filtering out internal
(swap Γ) packets and keeping only external (Δ₂) packets.
-/
def wireRight (Party : Type u)
    (Δ₁ Γ Δ₂ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenNodeContext Party (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) :
        Spec.Node.Context.{w})
      (OpenNodeContext Party (PortBoundary.tensor Δ₁ Δ₂) : Spec.Node.Context.{w}) :=
  fun _ ons => {
    toNodeProfile := ons.toNodeProfile
    boundary := ons.boundary.wireRight Δ₁
  }

/--
Close the boundary: transform `OpenNodeContext Party Δ` into
`OpenNodeContext Party empty` by dropping all boundary traffic.
Used by `plug` to internalize all external interactions.
-/
def close (Party : Type u) (Δ : PortBoundary) :
    Spec.Node.ContextHom
      (OpenNodeContext Party Δ : Spec.Node.Context.{w})
      (OpenNodeContext Party PortBoundary.empty : Spec.Node.Context.{w}) :=
  fun _ ons => {
    toNodeProfile := ons.toNodeProfile
    boundary := ons.boundary.closed
  }

theorem map_tensor_comp_inlTensor (Party : Type u)
    {Δ₁ Δ₁' Δ₂ Δ₂' : PortBoundary}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁') (f₂ : PortBoundary.Hom Δ₂ Δ₂') :
    Spec.Node.ContextHom.comp
      (map.{u, w} Party (PortBoundary.Hom.tensor f₁ f₂))
      (inlTensor Party Δ₁ Δ₂) =
    Spec.Node.ContextHom.comp
      (inlTensor Party Δ₁' Δ₂')
      (map Party f₁) := by
  funext X ons
  simp [map, inlTensor, Spec.Node.ContextHom.comp,
    OpenNodeProfile.mapBoundary]

theorem map_tensor_comp_inrTensor (Party : Type u)
    {Δ₁ Δ₁' Δ₂ Δ₂' : PortBoundary}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁') (f₂ : PortBoundary.Hom Δ₂ Δ₂') :
    Spec.Node.ContextHom.comp
      (map.{u, w} Party (PortBoundary.Hom.tensor f₁ f₂))
      (inrTensor Party Δ₁ Δ₂) =
    Spec.Node.ContextHom.comp
      (inrTensor Party Δ₁' Δ₂')
      (map Party f₂) := by
  funext X ons
  simp [map, inrTensor, Spec.Node.ContextHom.comp,
    OpenNodeProfile.mapBoundary]

theorem close_comp_map (Party : Type u)
    {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂) :
    Spec.Node.ContextHom.comp
      (close.{u, w} Party Δ₂)
      (map Party φ) =
    close Party Δ₁ := by
  funext X ons
  simp [close, map, Spec.Node.ContextHom.comp,
    OpenNodeProfile.mapBoundary, BoundaryAction.closed, BoundaryAction.mapBoundary]

theorem map_tensor_comp_wireLeft (Party : Type u)
    {Δ₁ Δ₁' Γ Δ₂ Δ₂' : PortBoundary}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁') (f₂ : PortBoundary.Hom Δ₂ Δ₂') :
    Spec.Node.ContextHom.comp
      (map.{u, w} Party (PortBoundary.Hom.tensor f₁ f₂))
      (wireLeft Party Δ₁ Γ Δ₂) =
    Spec.Node.ContextHom.comp
      (wireLeft Party Δ₁' Γ Δ₂')
      (map Party (PortBoundary.Hom.tensor f₁ (PortBoundary.Hom.id Γ))) := by
  funext X ons
  simp [map, wireLeft, Spec.Node.ContextHom.comp,
    OpenNodeProfile.mapBoundary]

theorem map_tensor_comp_wireRight (Party : Type u)
    {Δ₁ Δ₁' Γ Δ₂ Δ₂' : PortBoundary}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁') (f₂ : PortBoundary.Hom Δ₂ Δ₂') :
    Spec.Node.ContextHom.comp
      (map.{u, w} Party (PortBoundary.Hom.tensor f₁ f₂))
      (wireRight Party Δ₁ Γ Δ₂) =
    Spec.Node.ContextHom.comp
      (wireRight Party Δ₁' Γ Δ₂')
      (map Party (PortBoundary.Hom.tensor
        (PortBoundary.Hom.id (PortBoundary.swap Γ)) f₂)) := by
  funext X ons
  simp [map, wireRight, Spec.Node.ContextHom.comp,
    OpenNodeProfile.mapBoundary]

/-! #### Existing context-homs as polynomial-product operations

The following identities exhibit the hand-rolled `OpenNodeContext`
context-homs above as concrete instances of the universal projections,
pairing maps, and product maps for the polynomial product `productView`.
They are documentation rather than a refactor: the named API forms remain
the working surface, and the equalities below let one switch between the
two presentations on demand. -/

/-- `forget` is the first projection of the polynomial product, postcomposed
with the bridge `toProductView`. -/
theorem forget_eq_prodFst_comp_toProductView
    (Party : Type u) (Δ : PortBoundary) :
    forget.{u, w} Party Δ =
      Spec.Node.ContextHom.comp
        (Spec.Node.Context.prodFst (StepContext Party)
          (fun X : Type w => BoundaryAction Δ X))
        (toProductView Party Δ) := rfl

/-- `embed` is the pairing of the identity on `StepContext` with the
constant `internal` boundary action, transported back along the bridge. -/
theorem embed_eq_ofProductView_comp_prodPair
    (Party : Type u) (Δ : PortBoundary) :
    embed.{u, w} Party Δ =
      Spec.Node.ContextHom.comp
        (ofProductView Party Δ)
        (Spec.Node.Context.prodPair
          (Spec.Node.ContextHom.id (StepContext Party))
          (fun X _ => BoundaryAction.internal Δ X)) := rfl

/-- `map φ` factors as the polynomial-product map of the identity on
`StepContext` and the boundary-action transport
`fun X => BoundaryAction.mapBoundary φ`. -/
theorem map_eq_ofProductView_comp_prodMap_comp_toProductView
    (Party : Type u) {Δ₁ Δ₂ : PortBoundary} (φ : PortBoundary.Hom Δ₁ Δ₂) :
    map.{u, w} Party φ =
      Spec.Node.ContextHom.comp
        (Spec.Node.ContextHom.comp
          (ofProductView Party Δ₂)
          (Spec.Node.Context.prodMap
            (Spec.Node.ContextHom.id (StepContext Party))
            (fun X (b : BoundaryAction Δ₁ X) => b.mapBoundary φ)))
        (toProductView Party Δ₁) := rfl

end OpenNodeContext

/--
The open-world specialization of `StepOver`.

Here the node context carries `OpenNodeProfile Party Δ`, so every node
records both the usual controller/view data and its boundary traffic against
`Δ`.
-/
abbrev OpenStep (Party : Type u) (Δ : PortBoundary) (P : Type v) :=
  StepOver (OpenNodeContext Party Δ : Spec.Node.Context.{0}) P

/--
An `m`-parametric open concurrent process exposing boundary `Δ`.

`OpenProcess m Party Δ` bundles:

* `Proc` — the residual state space of the process;
* `step` — for each state, the protocol step observed by the open world
  (move-tree `spec`, node-local semantics, and continuation `next`);
* `stepSampler` — a per-state `Spec.Sampler m (step s).spec` resolving
  each move of the step protocol in the intermediate monad `m`.

Each state of an open process carries its own nodewise-monadic
sampler as first-class data. `openTheory m` compositionally assembles
the per-step samplers of composite processes through `par`, `wire`,
and `plug` via `Spec.Sampler.interleave`, and the runtime layer
(`processSemantics`, `processSemanticsAsync`) reads the sampler off
the process rather than taking it as a separate argument.

## Universe conventions

The spec / move-type universe is pinned at `0` because `m : Type → Type`
only operates on `Type` and the `Sampler m spec` abbrev therefore
requires `spec : Spec.{0}`. The `Party` universe `u` and the state
universe `v` remain free.

## Recovering the structural layer

`op.toProcess : ProcessOver ...` projects onto the underlying
`ProcessOver`, feeding the structural lemmas in `Concurrent/Process.lean`
and the bisimulation infrastructure below.
-/
structure OpenProcess
    (m : Type w → Type w')
    (Party : Type u) (Δ : PortBoundary) where
  /-- Residual state space of the process. -/
  Proc : Type v
  /-- Protocol step observed at state `s`. -/
  step : Proc → StepOver (OpenNodeContext.{u, w} Party Δ) Proc
  /-- Per-state nodewise-monadic sampler that resolves each move of the step
  protocol in the intermediate monad `m`. -/
  stepSampler : ∀ s, Spec.Sampler.{w, w'} m (step s).spec

namespace OpenProcess

/-- Structural projection onto the underlying `ProcessOver`, dropping
the per-state sampler. The closed-world `ProcessOver` lemmas from
`Concurrent/Process.lean` apply through this projection. -/
@[reducible]
def toProcess {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}
    (op : OpenProcess.{u, v, w, w'} m Party Δ) :
    ProcessOver (OpenNodeContext.{u, w} Party Δ) where
  Proc := op.Proc
  step := op.step

/--
Forget the boundary layer and view an open process as a plain closed-world
process.

This is the canonical projection: it drops all `BoundaryAction` data from
every node while preserving the process structure, controller paths, and
local views. The sampler is also discarded, so the result is a bare
`ProcessOver` over the closed-world context.
-/
def toClosed {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}
    (op : OpenProcess.{u, v, w, w'} m Party Δ) : Process.{u, v, w} Party :=
  op.toProcess.mapContext (OpenNodeContext.forget.{u, w} Party Δ)

/--
Embed a closed-world process as an open process with no boundary traffic,
using a user-supplied per-state sampler.

Every node is marked as purely internal: `isActivated = false` and `emit`
produces no packets. The caller must supply the nodewise sampler because
the closed-world process carries no monadic information.
-/
def ofClosed {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}
    (p : Process.{u, v, w} Party)
    (sampler : ∀ s, Spec.Sampler.{w, w'} m (p.step s).spec) :
    OpenProcess.{u, v, w, w'} m Party Δ where
  Proc := (p.mapContext (OpenNodeContext.embed.{u, w} Party Δ)).Proc
  step := (p.mapContext (OpenNodeContext.embed.{u, w} Party Δ)).step
  stepSampler := sampler

/--
Adapt the exposed boundary of an open process along a structural boundary
morphism.

This transforms every node's boundary action along `φ` (translating emitted
packets, preserving activation flags) while leaving the process structure,
closed-world node semantics, and per-step samplers unchanged. The sampler
carries over verbatim because `StepOver.mapContext` preserves `step.spec`.
-/
def mapBoundary {m : Type w → Type w'} {Party : Type u} {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂) (op : OpenProcess.{u, v, w, w'} m Party Δ₁) :
    OpenProcess.{u, v, w, w'} m Party Δ₂ where
  Proc := op.Proc
  step := fun s => (op.step s).mapContext (OpenNodeContext.map.{u, w} Party φ)
  stepSampler := op.stepSampler

/--
Binary-choice interleaving of two open processes, targeting a common
boundary `Δ` via structural injections `f₁`, `f₂` and a scheduling node
context `schedulerCtx : OpenNodeContext Party Δ (ULift Bool)`.

Structure on `Proc` and `step` is delegated to the underlying
`Concurrent.ProcessOver.interleave`; the per-state sampler is assembled
by `Spec.Sampler.interleave`, which threads the scheduler sampler
`schedulerSampler : m (ULift Bool)` above the per-branch samplers so that
the resulting step carries a well-typed nodewise-monadic sampler.

This is the single ingredient shared by `openTheory.par`, `openTheory.wire`,
and `openTheory.plug`: those operations differ only in which injection
pair `f₁`, `f₂` they supply.
-/
def interleave {m : Type w → Type w'} {Party : Type u} {Δ₁ Δ₂ Δ : PortBoundary}
    (p₁ : OpenProcess.{u, v, w, w'} m Party Δ₁)
    (p₂ : OpenProcess.{u, v, w, w'} m Party Δ₂)
    (f₁ : Spec.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ))
    (f₂ : Spec.Node.ContextHom
      (OpenNodeContext.{u, w} Party Δ₂)
      (OpenNodeContext.{u, w} Party Δ))
    (schedulerCtx : OpenNodeContext.{u, w} Party Δ (ULift.{w, 0} Bool))
    (schedulerSampler : m (ULift.{w, 0} Bool)) :
    OpenProcess.{u, v, w, w'} m Party Δ where
  Proc := p₁.Proc × p₂.Proc
  step := (p₁.toProcess.interleave p₂.toProcess f₁ f₂ schedulerCtx).step
  stepSampler := fun (s₁, s₂) =>
    Spec.Sampler.interleave schedulerSampler
      (p₁.stepSampler s₁) (p₂.stepSampler s₂)

end OpenProcess

/--
`OpenProcess.System` augments an open process by the standard verification
predicates used throughout VCVio. The verification predicates are about
the structural `ProcessOver` layer, so `OpenProcess.System` is monad- and
sampler-agnostic and refers to the underlying `ProcessOver.System`.
-/
abbrev OpenProcess.System (Party : Type u) (Δ : PortBoundary) :=
  ProcessOver.System (OpenNodeContext.{u, w} Party Δ)

/-! ## Silent steps and weak bisimulation -/

/-- A transcript path through a decorated open-process spec is **silent** when
every visited node is not externally activated (`isActivated = false`).
Checking only `isActivated` (rather than also requiring `emit x = []`)
ensures the predicate is invariant under *all* context morphisms, including
`wireLeft` / `wireRight` which filter shared-boundary packets via
`List.filterMap`. -/
def IsSilentDecoration {Party : Type u} {Δ : PortBoundary} :
    {spec : Interaction.Spec.{w}} →
    Interaction.Spec.Decoration (OpenNodeContext.{u, w} Party Δ) spec →
    spec.Transcript → Prop
  | .done, _, _ => True
  | .node _ _, ⟨ons, drest⟩, ⟨x, tr⟩ =>
      ons.boundary.isActivated = false ∧ IsSilentDecoration (drest x) tr

/-- A complete step of an open process is **silent** when every node along
the chosen transcript path has boundary-internal semantics. -/
def IsSilentStep {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}
    (p : OpenProcess.{u, v, w, w'} m Party Δ) (s : p.Proc)
    (tr : (p.step s).spec.Transcript) : Prop :=
  IsSilentDecoration (p.step s).semantics tr

/-- `IsSilentDecoration` is invariant under context morphisms that preserve
`isActivated`. All morphisms in the open-process framework (including
`mapBoundary`, `embedInlTensor`, `embedInrTensor`, `wireLeft`, `wireRight`,
and `closed`) preserve `isActivated`. -/
theorem isSilentDecoration_iff_map {Party : Type u} {Δ₁ Δ₂ : PortBoundary}
    (f : Spec.Node.ContextHom (OpenNodeContext.{u, w} Party Δ₁)
      (OpenNodeContext.{u, w} Party Δ₂))
    (hAct : ∀ (X : Type w) (ons : OpenNodeContext Party Δ₁ X),
      (f X ons).boundary.isActivated = ons.boundary.isActivated) :
    {spec : Spec.{w}} → (d : Spec.Decoration (OpenNodeContext Party Δ₁) spec) →
    (tr : spec.Transcript) →
    IsSilentDecoration (Spec.Decoration.map f spec d) tr ↔ IsSilentDecoration d tr
  | .done, _, _ => Iff.rfl
  | .node _ _, ⟨ons, drest⟩, ⟨x, tr⟩ => by
    simp only [IsSilentDecoration, Spec.Decoration.map]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [hAct] at h1,
        (isSilentDecoration_iff_map f hAct (drest x) tr).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [hAct],
        (isSilentDecoration_iff_map f hAct (drest x) tr).mpr h2⟩

/-- `IsSilentStep` is invariant under `OpenProcess.mapBoundary`: remapping
the boundary does not change which transcripts are silent, because all
boundary maps preserve `isActivated`. -/
theorem isSilentStep_mapBoundary_iff {m : Type w → Type w'}
    {Party : Type u} {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂)
    (p : OpenProcess.{u, v, w, w'} m Party Δ₁) (s : p.Proc)
    (tr : (p.step s).spec.Transcript) :
    IsSilentStep (p.mapBoundary φ) s tr ↔ IsSilentStep p s tr := by
  apply isSilentDecoration_iff_map
  intro X ons
  simp [OpenNodeContext.map, OpenNodeProfile.mapBoundary, BoundaryAction.mapBoundary]

/-! ## OpenProcessIso: weak bisimulation equivalence for open processes -/

/--
Two open processes with the same boundary are **weakly bisimilar** when there
exists a relation on their state types satisfying:

1. **Totality / surjectivity**: every state on each side has a related partner.
2. **Silent forward/backward**: a silent step can either be matched by some step
   on the other side (maintaining the relation), or absorbed (the other side
   stays put and the relation is maintained with the successor).
3. **Visible forward/backward**: a visible (non-silent) step must be matched by
   a visible step on the other side that preserves the relation.

This is the appropriate equality notion for `openTheory` monoidal laws,
where the internal scheduler structure differs (e.g., left-nested vs.
right-nested interleaving) but the observable boundary traffic is the same.
The scheduler nodes introduced by `ProcessOver.interleave` are always silent,
so they can be absorbed by the weak bisimulation.
-/
def OpenProcessIso {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}
    (p₁ p₂ : OpenProcess.{u, v, w, w'} m Party Δ) : Prop :=
  ∃ (rel : p₁.Proc → p₂.Proc → Prop),
    (∀ s₁, ∃ s₂, rel s₁ s₂) ∧
    (∀ s₂, ∃ s₁, rel s₁ s₂) ∧
    (∀ s₁ s₂, rel s₁ s₂ →
      ∀ tr₁ : (p₁.step s₁).spec.Transcript, IsSilentStep p₁ s₁ tr₁ →
        (∃ tr₂ : (p₂.step s₂).spec.Transcript,
          rel ((p₁.step s₁).next tr₁) ((p₂.step s₂).next tr₂)) ∨
        rel ((p₁.step s₁).next tr₁) s₂) ∧
    (∀ s₁ s₂, rel s₁ s₂ →
      ∀ tr₁ : (p₁.step s₁).spec.Transcript, ¬ IsSilentStep p₁ s₁ tr₁ →
        ∃ tr₂ : (p₂.step s₂).spec.Transcript, ¬ IsSilentStep p₂ s₂ tr₂ ∧
          rel ((p₁.step s₁).next tr₁) ((p₂.step s₂).next tr₂)) ∧
    (∀ s₁ s₂, rel s₁ s₂ →
      ∀ tr₂ : (p₂.step s₂).spec.Transcript, IsSilentStep p₂ s₂ tr₂ →
        (∃ tr₁ : (p₁.step s₁).spec.Transcript,
          rel ((p₁.step s₁).next tr₁) ((p₂.step s₂).next tr₂)) ∨
        rel s₁ ((p₂.step s₂).next tr₂)) ∧
    (∀ s₁ s₂, rel s₁ s₂ →
      ∀ tr₂ : (p₂.step s₂).spec.Transcript, ¬ IsSilentStep p₂ s₂ tr₂ →
        ∃ tr₁ : (p₁.step s₁).spec.Transcript, ¬ IsSilentStep p₁ s₁ tr₁ ∧
          rel ((p₁.step s₁).next tr₁) ((p₂.step s₂).next tr₂))

namespace OpenProcessIso

variable {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}

/-- Every open process is weakly bisimilar to itself. -/
protected theorem refl (p : OpenProcess.{u, v, w, w'} m Party Δ) :
    OpenProcessIso p p :=
  ⟨Eq, fun s => ⟨s, rfl⟩, fun s => ⟨s, rfl⟩,
    fun s₁ _ h tr _ => by subst h; exact .inl ⟨tr, rfl⟩,
    fun s₁ _ h tr hv => by subst h; exact ⟨tr, hv, rfl⟩,
    fun s₁ _ h tr _ => by subst h; exact .inl ⟨tr, rfl⟩,
    fun s₁ _ h tr hv => by subst h; exact ⟨tr, hv, rfl⟩⟩

/-- Weak bisimilarity is symmetric. -/
protected theorem symm {p₁ p₂ : OpenProcess.{u, v, w, w'} m Party Δ}
    (h : OpenProcessIso p₁ p₂) :
    OpenProcessIso p₂ p₁ := by
  obtain ⟨rel, htot, hsurj, hfs, hfv, hbs, hbv⟩ := h
  exact ⟨fun s₂ s₁ => rel s₁ s₂, hsurj, htot,
    fun s₂ s₁ hr => hbs s₁ s₂ hr,
    fun s₂ s₁ hr => hbv s₁ s₂ hr,
    fun s₂ s₁ hr => hfs s₁ s₂ hr,
    fun s₂ s₁ hr => hfv s₁ s₂ hr⟩

/-- Weak bisimilarity is transitive. The composite relation witnesses p₂ as
an intermediate: `∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃`. For silent steps, the
intermediate state can advance or stay, using `Classical.em` to case-split
on whether the intermediate step is itself silent. -/
protected theorem trans {p₁ p₂ p₃ : OpenProcess.{u, v, w, w'} m Party Δ}
    (h₁₂ : OpenProcessIso p₁ p₂)
    (h₂₃ : OpenProcessIso p₂ p₃) :
    OpenProcessIso p₁ p₃ := by
  obtain ⟨r₁₂, htot₁₂, hsurj₁₂, hfs₁₂, hfv₁₂, hbs₁₂, hbv₁₂⟩ := h₁₂
  obtain ⟨r₂₃, htot₂₃, hsurj₂₃, hfs₂₃, hfv₂₃, hbs₂₃, hbv₂₃⟩ := h₂₃
  refine ⟨fun s₁ s₃ => ∃ s₂, r₁₂ s₁ s₂ ∧ r₂₃ s₂ s₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s₁
    obtain ⟨s₂, h₂⟩ := htot₁₂ s₁
    obtain ⟨s₃, h₃⟩ := htot₂₃ s₂
    exact ⟨s₃, s₂, h₂, h₃⟩
  · intro s₃
    obtain ⟨s₂, h₂⟩ := hsurj₂₃ s₃
    obtain ⟨s₁, h₁⟩ := hsurj₁₂ s₂
    exact ⟨s₁, s₂, h₁, h₂⟩
  · intro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩ tr₁ hsilent₁
    rcases hfs₁₂ s₁ s₂ hr₁₂ tr₁ hsilent₁ with ⟨tr₂, hn₁₂⟩ | hstay
    · rcases Classical.em (IsSilentStep p₂ s₂ tr₂) with hsilent₂ | hvisible₂
      · rcases hfs₂₃ s₂ s₃ hr₂₃ tr₂ hsilent₂ with ⟨tr₃, hn₂₃⟩ | hstay₂₃
        · exact .inl ⟨tr₃, _, hn₁₂, hn₂₃⟩
        · exact .inr ⟨_, hn₁₂, hstay₂₃⟩
      · obtain ⟨tr₃, _, hn₂₃⟩ := hfv₂₃ s₂ s₃ hr₂₃ tr₂ hvisible₂
        exact .inl ⟨tr₃, _, hn₁₂, hn₂₃⟩
    · exact .inr ⟨s₂, hstay, hr₂₃⟩
  · intro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩ tr₁ hvisible₁
    obtain ⟨tr₂, hv₂, hn₁₂⟩ := hfv₁₂ s₁ s₂ hr₁₂ tr₁ hvisible₁
    obtain ⟨tr₃, hv₃, hn₂₃⟩ := hfv₂₃ s₂ s₃ hr₂₃ tr₂ hv₂
    exact ⟨tr₃, hv₃, _, hn₁₂, hn₂₃⟩
  · intro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩ tr₃ hsilent₃
    rcases hbs₂₃ s₂ s₃ hr₂₃ tr₃ hsilent₃ with ⟨tr₂, hn₂₃⟩ | hstay
    · rcases Classical.em (IsSilentStep p₂ s₂ tr₂) with hsilent₂ | hvisible₂
      · rcases hbs₁₂ s₁ s₂ hr₁₂ tr₂ hsilent₂ with ⟨tr₁, hn₁₂⟩ | hstay₁₂
        · exact .inl ⟨tr₁, _, hn₁₂, hn₂₃⟩
        · exact .inr ⟨_, hstay₁₂, hn₂₃⟩
      · obtain ⟨tr₁, _, hn₁₂⟩ := hbv₁₂ s₁ s₂ hr₁₂ tr₂ hvisible₂
        exact .inl ⟨tr₁, _, hn₁₂, hn₂₃⟩
    · exact .inr ⟨s₂, hr₁₂, hstay⟩
  · intro s₁ s₃ ⟨s₂, hr₁₂, hr₂₃⟩ tr₃ hvisible₃
    obtain ⟨tr₂, hv₂, hn₂₃⟩ := hbv₂₃ s₂ s₃ hr₂₃ tr₃ hvisible₃
    obtain ⟨tr₁, hv₁, hn₁₂⟩ := hbv₁₂ s₁ s₂ hr₁₂ tr₂ hv₂
    exact ⟨tr₁, hv₁, _, hn₁₂, hn₂₃⟩

end OpenProcessIso

end UC
end Interaction
