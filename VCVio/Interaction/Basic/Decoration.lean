/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Node
import Mathlib.Data.Sigma.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Decorations and dependent decorations (`Over`)

`Spec.Decoration Γ spec` is concrete nodewise metadata attached to a fixed
protocol tree `spec`, where `Γ : Spec.Node.Context` is the realized family of
node-local information. If a node of `spec` has move space `X`, then a
decoration provides one value of type `Γ X` at that node, and recursively
decorates every continuation subtree.

This is the basic way to say "the same protocol tree, but with extra data at
each node". Typical examples include:
* `RoleDecoration`, recording who controls a node;
* monad decorations, recording which monad a local action uses at a node;
* oracle decorations, recording what oracle interface is available there.

A context may be written directly, or obtained from a telescope
`Spec.Node.Schema` via `Spec.Node.Schema.toContext`.

`Decoration.Over` is the dependent (displayed) variant:
its fibers may depend on the context value drawn from an existing decoration.

Naming note:
`Decoration.Over` is nested because it is literally a decoration over a fixed
base decoration value. By contrast, `ShapeOver` and `InteractionOver` keep the
suffix form because they are the primary generalized syntax and semantics
layers, not dependent objects over a fixed base `Shape` or `Interaction`.

Functorial `map` / `map_id` / `map_comp` for both layers are in this file.
Composition along `Spec.append` is in `VCVio.Interaction.Basic.Append`.

Because decorations are concrete tree data, they are covariant in node-local
contexts: a context morphism `Γ → Δ` induces a map from decorations by `Γ`
to decorations by `Δ`. The schema-facing API in `Decoration.Schema` packages
that same idea for realized contexts presented by schemas via
`Spec.Node.Schema.SchemaMap`.

This file also contains the bridge between the semantic and staged views of
node metadata: decorating a tree by an extended context `Γ.extend A` is
equivalent to giving a base decoration by `Γ` together with one dependent
`Decoration.Over A` layer on top of it.

In particular, if a schema is built as `(Spec.Node.Schema.singleton Γ).extend A`,
then `Decoration.equivOver A spec` is exactly the statement that a decoration
of that schema's realized context is the same as a base decoration by `Γ`
plus one displayed layer over it.

The file concludes by lifting this one-step bridge recursively to arbitrary
schemas: `Spec.Decoration.Schema.View` is the staged telescope view of a
decoration by `S.toContext`, and `Spec.Decoration.Schema.equivView`
identifies that staged view with an ordinary decoration of the realized
context.
-/

universe u v w w₂

namespace Interaction
namespace Spec

private theorem prod_mk_heq {α : Type u} {β β' : Type v} {a : α} {b : β} {b' : β'}
    (h : b ≍ b') : ((a, b) : α × β) ≍ ((a, b') : α × β') := by
  cases h
  rfl

/-- `Decoration Γ spec` is concrete nodewise metadata on the fixed protocol
tree `spec`, for a realized node context `Γ`.

If a node of `spec` has move space `X`, then the decoration stores one value of
type `Γ X` at that node, and recursively stores decorations on every subtree.

This is different from `Spec.SyntaxOver`:
* a decoration is **data on a tree**;
* syntax is a **specification of local participant objects** that consumes such
  data;
* `Spec.ShapeOver` is the functorial refinement of that syntax layer. -/
def Decoration (Γ : Node.Context.{u, v}) : Spec → Type (max u v)
  | .done => PUnit
  | .node X rest => Γ X × (∀ x, Decoration Γ (rest x))

/-- Natural transformation between per-node decorations, applied recursively. -/
def Decoration.map {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}}
    (f : Interaction.Spec.Node.ContextHom Γ Δ) :
    (spec : Spec) → Decoration Γ spec → Decoration Δ spec
  | .done, _ => ⟨⟩
  | .node X rest, ⟨s, dRest⟩ => ⟨f X s, fun x => Decoration.map f (rest x) (dRest x)⟩

@[simp, grind =]
theorem Decoration.map_id {Γ : Node.Context.{u, v}} :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.map (Node.ContextHom.id Γ) spec d = d
  | .done, ⟨⟩ => rfl
  | .node _ rest, ⟨s, dRest⟩ => by
      simp only [Decoration.map]; congr 1; funext x; exact map_id (rest x) (dRest x)

theorem Decoration.map_comp
    {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}} {Λ : Node.Context.{u, w₂}}
    (g : Node.ContextHom Δ Λ) (f : Node.ContextHom Γ Δ) :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.map g spec (Decoration.map f spec d) =
      Decoration.map (Node.ContextHom.comp g f) spec d
  | .done, ⟨⟩ => rfl
  | .node _ rest, ⟨s, dRest⟩ => by
      simp only [Decoration.map]; congr 1; funext x
      exact map_comp g f (rest x) (dRest x)

/-- Dependent decoration over `d : Decoration Γ spec`: at each node, data in
`F X γ` where `γ` is the context value from `d`, plus recursive decorations on
subtrees. -/
def Decoration.Over {Γ : Node.Context.{u, v}} (F : ∀ X, Γ X → Type w) :
    (spec : Spec) → Decoration Γ spec → Type (max u w)
  | .done, _ => PUnit
  | .node X rest, ⟨γ, dRest⟩ =>
      F X γ × (∀ x, Decoration.Over F (rest x) (dRest x))

/-- Fiberwise map between dependent decoration families over the same base
decoration. -/
def Decoration.Over.map {Γ : Node.Context.{u, v}}
    {F : ∀ X, Γ X → Type w} {G : ∀ X, Γ X → Type w}
    (f : ∀ X γ, F X γ → G X γ) :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.Over F spec d → Decoration.Over G spec d
  | .done, _, _ => ⟨⟩
  | .node X rest, ⟨γ, dRest⟩, ⟨fData, rRest⟩ =>
      ⟨f X γ fData, fun x => Over.map f (rest x) (dRest x) (rRest x)⟩

@[simp, grind =]
theorem Decoration.Over.map_id {Γ : Node.Context.{u, v}} {F : ∀ X, Γ X → Type w} :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over F spec d) →
    Decoration.Over.map (fun _ _ x => x) spec d r = r
  | .done, ⟨⟩, ⟨⟩ => rfl
  | .node _ rest, ⟨γ, dRest⟩, ⟨fd, rr⟩ => by
      simp only [Decoration.Over.map]; congr 1; funext x
      exact map_id (rest x) (dRest x) (rr x)

theorem Decoration.Over.map_comp {Γ : Node.Context.{u, v}}
    {F G H : ∀ X, Γ X → Type w}
    (g : ∀ X γ, G X γ → H X γ) (f : ∀ X γ, F X γ → G X γ) :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over F spec d) →
    Decoration.Over.map g spec d (Decoration.Over.map f spec d r) =
      Decoration.Over.map (fun X γ => g X γ ∘ f X γ) spec d r
  | .done, ⟨⟩, ⟨⟩ => rfl
  | .node _ rest, ⟨γ, dRest⟩, ⟨fd, rr⟩ => by
      simp only [Decoration.Over.map]; congr 1; funext x
      exact map_comp g f (rest x) (dRest x) (rr x)

/--
Transport a dependent decoration across a map of base contexts.

Given:
* a base-context morphism `f : Γ → Δ`, and
* a fiberwise map `g` from `A X γ` to `B X (f X γ)`,

this sends a displayed decoration over `d : Decoration Γ spec` to a displayed
decoration over `Decoration.map f spec d`.
-/
def Decoration.Over.mapBase
    {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}}
    {A : ∀ X, Γ X → Type w₂} {B : ∀ X, Δ X → Type w₂}
    (f : Node.ContextHom Γ Δ)
    (g : ∀ X γ, A X γ → B X (f X γ)) :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.Over A spec d →
    Decoration.Over B spec (Decoration.map f spec d)
  | .done, _, _ => ⟨⟩
  | .node X rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ =>
      ⟨g X γ a, fun x => Over.mapBase f g (rest x) (dRest x) (rRest x)⟩

theorem Decoration.Over.mapBase_id
    {Γ : Node.Context.{u, v}} {A : ∀ X, Γ X → Type w} :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over A spec d) →
    HEq (Decoration.Over.mapBase (Node.ContextHom.id Γ) (fun _ _ x => x) spec d r) r
  | .done, ⟨⟩, ⟨⟩ => HEq.rfl
  | .node _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      simp only [Decoration.Over.mapBase]
      refine prod_mk_heq ?_
      refine Function.hfunext rfl ?_
      intro x y hxy
      cases hxy
      exact mapBase_id (rest x) (dRest x) (rRest x)

theorem Decoration.Over.mapBase_comp
    {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}} {Λ : Node.Context.{u, w₂}}
    {A : ∀ X, Γ X → Type w₂}
    {B : ∀ X, Δ X → Type w₂}
    {C : ∀ X, Λ X → Type w₂}
    (f : Node.ContextHom Γ Δ)
    (g : Node.ContextHom Δ Λ)
    (fOver : ∀ X γ, A X γ → B X (f X γ))
    (gOver : ∀ X δ, B X δ → C X (g X δ)) :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over A spec d) →
    HEq
      (Decoration.Over.mapBase g gOver spec (Decoration.map f spec d)
        (Decoration.Over.mapBase f fOver spec d r))
      (Decoration.Over.mapBase (Node.ContextHom.comp g f)
        (fun X γ => gOver X (f X γ) ∘ fOver X γ) spec d r)
  | .done, ⟨⟩, ⟨⟩ => HEq.rfl
  | .node _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      simp only [Decoration.Over.mapBase]
      refine prod_mk_heq ?_
      refine Function.hfunext rfl ?_
      intro x y hxy
      cases hxy
      exact mapBase_comp f g fOver gOver (rest x) (dRest x) (rRest x)

/--
Pack a base decoration and one dependent `Over` layer into a decoration of the
extended context `Γ.extend A`.

This is the tree-level realization of a single schema extension step.
-/
def Decoration.ofOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → (d : Decoration Γ spec) → Decoration.Over A spec d →
    Decoration (Node.Context.extend Γ A) spec
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ =>
      ⟨⟨γ, a⟩, fun x => ofOver A (rest x) (dRest x) (rRest x)⟩

theorem Decoration.map_ofOver
    {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}}
    {A : ∀ X, Γ X → Type w₂} {B : ∀ X, Δ X → Type w₂}
    (f : Node.ContextHom Γ Δ)
    (g : ∀ X γ, A X γ → B X (f X γ)) :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over A spec d) →
    Decoration.map (Node.Context.extendMap f g) spec (Decoration.ofOver A spec d r) =
      Decoration.ofOver B spec
        (Decoration.map f spec d)
        (Decoration.Over.mapBase f g spec d r)
  | .done, ⟨⟩, ⟨⟩ => rfl
  | .node _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      simp only [Decoration.map, Decoration.ofOver, Decoration.Over.mapBase]
      congr 1
      funext x
      exact map_ofOver f g (rest x) (dRest x) (rRest x)

/--
Unpack a decoration of the extended context `Γ.extend A` into:
* its base decoration by `Γ`, and
* its displayed `Decoration.Over A` layer above that base.

This is the inverse structural view to `Decoration.ofOver`.
-/
def Decoration.toOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → Decoration (Node.Context.extend Γ A) spec →
    Σ d : Decoration Γ spec, Decoration.Over A spec d
  | .done, _ => ⟨⟨⟩, ⟨⟩⟩
  | .node _ rest, ⟨⟨γ, a⟩, dRest⟩ =>
      let ih := fun x => toOver A (rest x) (dRest x)
      ⟨⟨γ, fun x => (ih x).1⟩, ⟨a, fun x => (ih x).2⟩⟩

@[simp]
theorem Decoration.toOver_ofOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over A spec d) →
    Decoration.toOver A spec (Decoration.ofOver A spec d r) = ⟨d, r⟩
  | .done, ⟨⟩, ⟨⟩ => rfl
  | .node _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      rw [Sigma.ext_iff]
      let baseTail :=
        fun x => (Decoration.toOver A (rest x)
          (Decoration.ofOver A (rest x) (dRest x) (rRest x))).1
      let overTail :=
        fun x => (Decoration.toOver A (rest x)
          (Decoration.ofOver A (rest x) (dRest x) (rRest x))).2
      have hbaseTail : baseTail = dRest := by
        funext x
        exact (Sigma.ext_iff.mp (toOver_ofOver A (rest x) (dRest x) (rRest x))).1
      have hoverTail : HEq overTail rRest := by
        refine Function.hfunext rfl ?_
        intro x y hxy
        cases hxy
        exact (Sigma.ext_iff.mp (toOver_ofOver A (rest x) (dRest x) (rRest x))).2
      have hpair : HEq (a, overTail) (a, rRest) := prod_mk_heq hoverTail
      exact ⟨Prod.ext rfl hbaseTail, hpair⟩

@[simp]
theorem Decoration.ofOver_toOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → (d : Decoration (Node.Context.extend Γ A) spec) →
    Decoration.ofOver A spec (Decoration.toOver A spec d).1 (Decoration.toOver A spec d).2 = d
  | .done, ⟨⟩ => rfl
  | .node _ rest, ⟨⟨γ, a⟩, dRest⟩ => by
      simp [Decoration.toOver, Decoration.ofOver, ofOver_toOver A]

/--
Equivalence between:
* decorating a tree by the extended context `Γ.extend A`, and
* decorating it by `Γ` together with one `Decoration.Over A` layer.

This is the main bridge from the semantic "single realized context" view to the
staged schema/dependent-decoration view.

Concrete example:
if a schema is built as `(Spec.Node.Schema.singleton Tag).extend Data`, then
decorations of its realized context `Node.Context.extend Tag Data` are
equivalent to pairs consisting of:
* `tags : Decoration Tag spec`, and
* `datas : Decoration.Over Data spec tags`.
-/
def Decoration.equivOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w)
    (spec : Spec) :
    Equiv (Decoration (Node.Context.extend Γ A) spec)
      (Sigma fun d : Decoration Γ spec => Decoration.Over A spec d) := by
  refine
    { toFun := Decoration.toOver A spec
      invFun := fun ⟨d, r⟩ => Decoration.ofOver A spec d r
      left_inv := Decoration.ofOver_toOver A spec
      right_inv := ?_ }
  intro x
  cases x with
  | mk d r => exact Decoration.toOver_ofOver A spec d r

namespace Decoration
namespace Schema

/--
Map decorations along a schema morphism.

This is just `Decoration.map` viewed through schema-level sources and targets.
-/
abbrev map
    {Γ Δ : Node.Context.{u, v}} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (f : Node.Schema.SchemaMap S T) :
    (spec : Spec) → Decoration S.toContext spec → Decoration T.toContext spec :=
  Decoration.map f

@[simp]
theorem map_id
    {Γ : Node.Context.{u, v}} {S : Node.Schema Γ} :
    (spec : Spec) → (d : Decoration S.toContext spec) →
    Decoration.Schema.map (Node.Schema.SchemaMap.id S) spec d = d :=
  Decoration.map_id

theorem map_comp
    {Γ Δ Λ : Node.Context.{u, v}}
    {S : Node.Schema Γ} {T : Node.Schema Δ} {U : Node.Schema Λ}
    (g : Node.Schema.SchemaMap T U) (f : Node.Schema.SchemaMap S T) :
    (spec : Spec) → (d : Decoration S.toContext spec) →
    Decoration.Schema.map g spec (Decoration.Schema.map f spec d) =
      Decoration.Schema.map (Node.Schema.SchemaMap.comp g f) spec d :=
  Decoration.map_comp g f

theorem map_ofOver
    {Γ Δ : Node.Context.{u, v}}
    {S : Node.Schema Γ} {T : Node.Schema Δ}
    {A : ∀ X, Γ X → Type v} {B : ∀ X, Δ X → Type v}
    (f : Node.Schema.SchemaMap S T)
    (g : ∀ X γ, A X γ → B X (f X γ)) :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over A spec d) →
    Decoration.Schema.map (Node.Schema.SchemaMap.extend (S := S) (T := T) f g) spec
        (Decoration.ofOver A spec d r) =
      Decoration.ofOver B spec
        (Decoration.Schema.map f spec d)
        (Decoration.Over.mapBase f g spec d r)
  | spec, d, r => Decoration.map_ofOver f g spec d r

/--
`Decoration.Schema.telescope S spec` packages the staged telescope view of
decorations for schema `S`, together with an equivalence from ordinary
decorations by the realized context `S.toContext`.

The resulting type is the recursively decomposed form of a decoration:
each `snoc` in the schema contributes one more displayed `Decoration.Over`
layer.
-/
def telescope :
    {Γ : Node.Context.{u, v}} → (S : Node.Schema Γ) → (spec : Spec) →
    Sigma fun T : Type (max u v) => Decoration Γ spec ≃ T
  | _, .nil, spec => ⟨Decoration Node.Context.empty spec, Equiv.refl _⟩
  | _, .singleton A, spec => ⟨Decoration A spec, Equiv.refl _⟩
  | _, .snoc S A, spec =>
      let recView := telescope S spec
      ⟨Sigma fun t : recView.1 => Decoration.Over A spec (recView.2.symm t),
        (Decoration.equivOver A spec).trans recView.2.symm.sigmaCongrLeft.symm⟩

/--
`Decoration.Schema.View S spec` is the staged telescope view carried by the
recursive schema decomposition theorem `Decoration.Schema.telescope`.
-/
abbrev View {Γ : Node.Context.{u, v}} (S : Node.Schema Γ) (spec : Spec) :
    Type (max u v) :=
  (telescope S spec).1

/--
Unpack an ordinary decoration into the staged telescope view determined by a
schema.
-/
abbrev unpack {Γ : Node.Context.{u, v}} (S : Node.Schema Γ) (spec : Spec) :
    Decoration Γ spec → View S spec :=
  (telescope S spec).2.toFun

/--
Pack a staged schema-decoration view back into an ordinary decoration of the
realized context.
-/
abbrev pack {Γ : Node.Context.{u, v}} (S : Node.Schema Γ) (spec : Spec) :
    View S spec → Decoration Γ spec :=
  (telescope S spec).2.invFun

@[simp]
theorem pack_unpack {Γ : Node.Context.{u, v}} (S : Node.Schema Γ) (spec : Spec)
    (d : Decoration Γ spec) :
    pack S spec (unpack S spec d) = d :=
  (telescope S spec).2.left_inv d

@[simp]
theorem unpack_pack {Γ : Node.Context.{u, v}} (S : Node.Schema Γ) (spec : Spec)
    (d : View S spec) :
    unpack S spec (pack S spec d) = d :=
  (telescope S spec).2.right_inv d

/--
Map the staged telescope view of decorations along a schema morphism.

This is the schema-view analogue of `Decoration.Schema.map`: pack the staged
view into an ordinary decoration, map that decoration along the schema
morphism, then unpack it into the staged view for the target schema.
-/
abbrev mapView
    {Γ Δ : Node.Context.{u, v}} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (f : Node.Schema.SchemaMap S T) (spec : Spec) :
    View S spec → View T spec :=
  unpack T spec ∘ Decoration.Schema.map f spec ∘ pack S spec

@[simp]
theorem unpack_map
    {Γ Δ : Node.Context.{u, v}} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (f : Node.Schema.SchemaMap S T) (spec : Spec) (d : Decoration S.toContext spec) :
    unpack T spec (Decoration.Schema.map f spec d) =
      mapView f spec (unpack S spec d) := by
  simp [mapView]

@[simp]
theorem pack_mapView
    {Γ Δ : Node.Context.{u, v}} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (f : Node.Schema.SchemaMap S T) (spec : Spec) (d : View S spec) :
    pack T spec (mapView f spec d) =
      Decoration.Schema.map f spec (pack S spec d) := by
  simp [mapView]

@[simp]
theorem mapView_id
    {Γ : Node.Context.{u, v}} {S : Node.Schema Γ} :
    (spec : Spec) → (d : View S spec) →
    mapView (Node.Schema.SchemaMap.id S) spec d = d := by
  intro spec d
  simp [mapView]

theorem mapView_comp
    {Γ Δ Λ : Node.Context.{u, v}}
    {S : Node.Schema Γ} {T : Node.Schema Δ} {U : Node.Schema Λ}
    (g : Node.Schema.SchemaMap T U) (f : Node.Schema.SchemaMap S T) :
    (spec : Spec) → (d : View S spec) →
    mapView g spec (mapView f spec d) =
      mapView (Node.Schema.SchemaMap.comp g f) spec d := by
  intro spec d
  simp [mapView, Decoration.Schema.map_comp]

namespace Prefix

/--
Project decorations along a syntactic schema prefix.

This is the tree-level forgetting map induced by the schema morphism
`Node.Schema.Prefix.toSchemaMap`.
-/
abbrev map
    {Γ Δ : Node.Context.{u, v}} {S : Node.Schema Γ} {T : Node.Schema Δ}
    (p : Node.Schema.Prefix S T) :
    (spec : Spec) → Decoration T.toContext spec → Decoration S.toContext spec :=
  Decoration.Schema.map p.toSchemaMap

end Prefix

/--
Equivalence between an ordinary decoration by the realized context of `S` and
its staged telescope view.

This is the recursive schema-level form of `Decoration.equivOver`.
-/
abbrev equivView {Γ : Node.Context.{u, v}} (S : Node.Schema Γ) (spec : Spec) :
    Decoration Γ spec ≃ View S spec :=
  (telescope S spec).2

end Schema
end Decoration

end Spec
end Interaction
