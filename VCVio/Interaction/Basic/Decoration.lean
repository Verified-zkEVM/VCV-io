/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Node
import VCVio.Interaction.Basic.Spec
import ToMathlib.PFunctor.Free.Displayed
import ToMathlib.Logic.HEq
import Mathlib.Logic.Equiv.Defs

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

## Polynomial substrate (`DecoratedSpec`)

Just as `Spec` is `PFunctor.FreeM Spec.basePFunctor PUnit`, the bundle
`(spec, Decoration Γ spec)` is `PFunctor.FreeM (Γ.toPFunctor) PUnit`:

```
DecoratedSpec Γ := PFunctor.FreeM (Γ.toPFunctor) PUnit
```

`Γ.toPFunctor` is the polynomial whose positions are `Σ X : Type u, Γ X`
and whose child family is `Sigma.fst`. A free term over this polynomial is
literally a tree where every internal node carries both a move space `X`
and a `Γ`-value, with continuations indexed by the move type.

Forgetting the `Γ`-component on positions yields a polynomial lens
`Γ.toPFunctor → Spec.basePFunctor`, whose lift to free monads is the
shape-forgetful map `DecoratedSpec.shape : DecoratedSpec Γ → Spec`. The
fiber of `shape` over a fixed `spec : Spec` is exactly `Decoration Γ spec`,
formalized as `decoratedSpecEquiv : DecoratedSpec Γ ≃ Σ spec, Decoration Γ spec`.

This makes precise the slogan "a `Γ`-decorated spec is the same data as a
spec together with a `Γ`-decoration on it". Downstream code can use either
view: the `Spec`-indexed `Decoration` family is convenient for talking
about decorations *over a fixed protocol*, while `DecoratedSpec` is the
right object when shape and metadata vary together (e.g. for the polynomial
coalgebraic semantics of `ProcessOver`).
-/

universe u v w w₂ w₃ w₄ w₅

namespace Interaction

open PFunctor

variable {P : PFunctor.{u, v}} {α : Type w}

/-- Displayed-family shape for node-local metadata over a polynomial tree. -/
def Decoration.shape (Γ : P.A → Type w₂) :
    PFunctor.FreeM.Displayed.Shape P α where
  leaf := fun _ => PUnit.{max v w₂ + 1}
  node := fun a child => Γ a × ((b : P.B a) → child b)

/--
Node-local metadata over an arbitrary polynomial free tree.

At a control node `a : P.A`, the decoration stores one value of type `Γ a`
and recursively decorates every abstract control continuation `b : P.B a`.
The plain `Spec.Decoration` below is the specialization to
`Spec.basePFunctor` and terminal payload `PUnit`.
-/
abbrev Decoration (Γ : P.A → Type w₂) : PFunctor.FreeM P α → Type (max v w₂) :=
  PFunctor.FreeM.Displayed (Decoration.shape Γ)

/--
Displayed-family shape for a dependent layer over a polynomial decoration.

At a node with base metadata `γ : Γ a`, the over-layer stores data in
`F a γ` and recursively stores over-data over each decorated child.
-/
def Decoration.overShape (Γ : P.A → Type w₂) (F : (a : P.A) → Γ a → Type w₃) :
    PFunctor.FreeM.Displayed.OverShape (Decoration.shape (P := P) (α := α) Γ) where
  leaf := fun _ _ => PUnit.{max v w₃ + 1}
  node := fun a _ over d => F a d.1 × ((b : P.B a) → over b (d.2 b))

/-- Dependent node-local metadata over an existing polynomial decoration. -/
abbrev Decoration.Over (Γ : P.A → Type w₂) (F : (a : P.A) → Γ a → Type w₃)
    (s : PFunctor.FreeM P α) (d : Decoration Γ s) : Type (max v w₃) :=
  PFunctor.FreeM.Displayed.Over (Decoration.overShape Γ F) s d

namespace Decoration

namespace Context

/-- Extend a node metadata family by one dependent field. -/
def extend (Γ : P.A → Type w₂) (A : (a : P.A) → Γ a → Type w₃) :
    P.A → Type (max w₂ w₃) :=
  fun a => Σ γ : Γ a, A a γ

/-- Map one extended node metadata family to another. -/
def extendMap {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    {A : (a : P.A) → Γ a → Type w₄} {B : (a : P.A) → Δ a → Type w₅}
    (f : ∀ a, Γ a → Δ a)
    (g : ∀ a γ, A a γ → B a (f a γ)) :
    ∀ a, extend Γ A a → extend Δ B a :=
  fun a ⟨γ, x⟩ => ⟨f a γ, g a γ x⟩

end Context

/-- Constructor-local displayed morphism induced by a nodewise metadata map. -/
def mapLocalHom {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a) :
    PFunctor.FreeM.Displayed.LocalHom
      (Decoration.shape (P := P) (α := α) Γ)
      (Decoration.shape (P := P) (α := α) Δ) where
  mapLeaf := fun _ _ => ⟨⟩
  mapChild := fun a _ _ mapChild d =>
    ⟨f a d.1, fun b => mapChild b (d.2 b)⟩

/-- Natural transformation between node-local decorations, applied recursively. -/
def map {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a) :
    (s : PFunctor.FreeM P α) → Decoration Γ s → Decoration Δ s :=
  (mapLocalHom f).toHom

@[simp]
theorem map_pure {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a) (x : α)
    (d : Decoration Γ (PFunctor.FreeM.pure (P := P) x)) :
    map f (PFunctor.FreeM.pure x) d = ⟨⟩ :=
  rfl

@[simp]
theorem map_roll {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a)
    (a : P.A) (rest : P.B a → PFunctor.FreeM P α)
    (d : Decoration Γ (PFunctor.FreeM.roll a rest)) :
    map f (PFunctor.FreeM.roll a rest) d =
      ⟨f a d.1, fun b => map f (rest b) (d.2 b)⟩ :=
  rfl

@[simp]
theorem map_id {Γ : P.A → Type w₂} :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) →
    map (fun _ γ => γ) s d = d
  | .pure _, ⟨⟩ => rfl
  | .roll _ rest, ⟨γ, dRest⟩ => by
      simp only [map_roll]
      congr 1
      funext b
      exact map_id (rest b) (dRest b)

theorem map_comp {Γ : P.A → Type w₂} {Δ : P.A → Type w₃} {Λ : P.A → Type w₄}
    (g : ∀ a, Δ a → Λ a) (f : ∀ a, Γ a → Δ a) :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) →
    map g s (map f s d) = map (fun a => g a ∘ f a) s d
  | .pure _, ⟨⟩ => rfl
  | .roll _ rest, ⟨γ, dRest⟩ => by
      simp only [map_roll]
      congr 1
      funext b
      exact map_comp g f (rest b) (dRest b)

namespace Over

/-- Constructor-local displayed-over morphism induced by a fiberwise map. -/
def mapLocalHom {Γ : P.A → Type w₂}
    {F : (a : P.A) → Γ a → Type w₃}
    {G : (a : P.A) → Γ a → Type w₄}
    (f : ∀ a γ, F a γ → G a γ) :
    PFunctor.FreeM.Displayed.Over.FiberLocalHom
      (Decoration.overShape (P := P) (α := α) Γ F)
      (Decoration.overShape (P := P) (α := α) Γ G) where
  mapLeaf := fun _ _ _ => ⟨⟩
  mapChild := fun a _ _ _ mapChild d r =>
    ⟨f a d.1 r.1, fun b => mapChild b (d.2 b) (r.2 b)⟩

/-- Fiberwise map between dependent decoration families over the same decoration. -/
def map {Γ : P.A → Type w₂}
    {F : (a : P.A) → Γ a → Type w₃}
    {G : (a : P.A) → Γ a → Type w₄}
    (f : ∀ a γ, F a γ → G a γ) :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) →
    Decoration.Over Γ F s d → Decoration.Over Γ G s d :=
  (mapLocalHom f).toHom

@[simp]
theorem map_id {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃} :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ F s d) →
    map (fun _ _ x => x) s d r = r
  | .pure _, ⟨⟩, ⟨⟩ => rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨fd, rRest⟩ => by
      simp only [map, mapLocalHom, PFunctor.FreeM.Displayed.Over.FiberLocalHom.toHom_roll]
      congr 1
      funext b
      exact map_id (rest b) (dRest b) (rRest b)

theorem map_comp {Γ : P.A → Type w₂}
    {F : (a : P.A) → Γ a → Type w₃}
    {G : (a : P.A) → Γ a → Type w₄}
    {H : (a : P.A) → Γ a → Type w₅}
    (g : ∀ a γ, G a γ → H a γ) (f : ∀ a γ, F a γ → G a γ) :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ F s d) →
    map g s d (map f s d r) =
      map (fun a γ => g a γ ∘ f a γ) s d r
  | .pure _, ⟨⟩, ⟨⟩ => rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨fd, rRest⟩ => by
      simp only [map, mapLocalHom, PFunctor.FreeM.Displayed.Over.FiberLocalHom.toHom_roll]
      congr 1
      funext b
      exact map_comp g f (rest b) (dRest b) (rRest b)

/--
Constructor-local displayed-over morphism induced by a map of base metadata and
a compatible map of the dependent over-layer.
-/
def mapBaseLocalHom {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    {A : (a : P.A) → Γ a → Type w₄}
    {B : (a : P.A) → Δ a → Type w₅}
    (f : ∀ a, Γ a → Δ a)
    (g : ∀ a γ, A a γ → B a (f a γ)) :
    PFunctor.FreeM.Displayed.Over.LocalHom
      (Decoration.mapLocalHom (P := P) (α := α) f)
      (Decoration.overShape (P := P) (α := α) Γ A)
      (Decoration.overShape (P := P) (α := α) Δ B) where
  mapLeaf := fun _ _ _ => ⟨⟩
  mapChild := fun a _ _ _ _ _ mapChild d r =>
    ⟨g a d.1 r.1, fun b => mapChild b (d.2 b) (r.2 b)⟩

/--
Transport a dependent decoration across a nodewise map of base decorations.
-/
def mapBase {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    {A : (a : P.A) → Γ a → Type w₄}
    {B : (a : P.A) → Δ a → Type w₅}
    (f : ∀ a, Γ a → Δ a)
    (g : ∀ a γ, A a γ → B a (f a γ)) :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) →
    Decoration.Over Γ A s d →
    Decoration.Over Δ B s (Decoration.map f s d) :=
  (mapBaseLocalHom f g).toHom

theorem mapBase_id {Γ : P.A → Type w₂} {A : (a : P.A) → Γ a → Type w₃} :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ A s d) →
    HEq (mapBase (fun _ γ => γ) (fun _ _ x => x) s d r) r
  | .pure _, ⟨⟩, ⟨⟩ => HEq.rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      simp only [mapBase, mapBaseLocalHom, PFunctor.FreeM.Displayed.Over.LocalHom.toHom_roll]
      refine Prod.mk_heq ?_
      refine Function.hfunext rfl ?_
      intro b y hby
      cases hby
      exact mapBase_id (rest b) (dRest b) (rRest b)

theorem mapBase_comp
    {Γ : P.A → Type w₂} {Δ : P.A → Type w₃} {Λ : P.A → Type w₄}
    {A : (a : P.A) → Γ a → Type w₅}
    {B : (a : P.A) → Δ a → Type w₅}
    {C : (a : P.A) → Λ a → Type w₅}
    (f : ∀ a, Γ a → Δ a)
    (g : ∀ a, Δ a → Λ a)
    (fOver : ∀ a γ, A a γ → B a (f a γ))
    (gOver : ∀ a δ, B a δ → C a (g a δ)) :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ A s d) →
    HEq
      (mapBase g gOver s (Decoration.map f s d)
        (mapBase f fOver s d r))
      (mapBase (fun a => g a ∘ f a)
        (fun a γ => gOver a (f a γ) ∘ fOver a γ) s d r)
  | .pure _, ⟨⟩, ⟨⟩ => HEq.rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      simp only [mapBase, mapBaseLocalHom, PFunctor.FreeM.Displayed.Over.LocalHom.toHom_roll]
      refine Prod.mk_heq ?_
      refine Function.hfunext rfl ?_
      intro b y hby
      cases hby
      exact mapBase_comp f g fOver gOver (rest b) (dRest b) (rRest b)

end Over

/--
Pack a base decoration and one dependent `Over` layer into a decoration of the
extended metadata family.
-/
def ofOver {Γ : P.A → Type w₂} {A : (a : P.A) → Γ a → Type w₃} :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) → Decoration.Over Γ A s d →
    Decoration (Context.extend Γ A) s
  | .pure _, _, _ => ⟨⟩
  | .roll _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ =>
      ⟨⟨γ, a⟩, fun b => ofOver (rest b) (dRest b) (rRest b)⟩

theorem map_ofOver
    {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    {A : (a : P.A) → Γ a → Type w₄}
    {B : (a : P.A) → Δ a → Type w₅}
    (f : ∀ a, Γ a → Δ a)
    (g : ∀ a γ, A a γ → B a (f a γ)) :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ A s d) →
    Decoration.map (Context.extendMap f g) s (ofOver s d r) =
      ofOver s (Decoration.map f s d) (Over.mapBase f g s d r)
  | .pure _, ⟨⟩, ⟨⟩ => rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      simp only [map_roll, ofOver, Over.mapBase,
        Over.mapBaseLocalHom, PFunctor.FreeM.Displayed.Over.LocalHom.toHom_roll]
      congr 1
      funext b
      exact map_ofOver f g (rest b) (dRest b) (rRest b)

/--
Unpack a decoration of an extended metadata family into its base decoration and
dependent over-layer.
-/
def toOver {Γ : P.A → Type w₂} {A : (a : P.A) → Γ a → Type w₃} :
    (s : PFunctor.FreeM P α) → Decoration (Context.extend Γ A) s →
    Σ d : Decoration Γ s, Decoration.Over Γ A s d
  | .pure _, _ => ⟨⟨⟩, ⟨⟩⟩
  | .roll _ rest, ⟨⟨γ, a⟩, dRest⟩ =>
      let ih := fun b => toOver (rest b) (dRest b)
      ⟨⟨γ, fun b => (ih b).1⟩, ⟨a, fun b => (ih b).2⟩⟩

@[simp]
theorem toOver_ofOver {Γ : P.A → Type w₂} {A : (a : P.A) → Γ a → Type w₃} :
    (s : PFunctor.FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ A s d) →
    toOver s (ofOver s d r) = ⟨d, r⟩
  | .pure _, ⟨⟩, ⟨⟩ => rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      rw [Sigma.ext_iff]
      let baseTail :=
        fun b => (toOver (rest b) (ofOver (rest b) (dRest b) (rRest b))).1
      let overTail :=
        fun b => (toOver (rest b) (ofOver (rest b) (dRest b) (rRest b))).2
      have hbaseTail : baseTail = dRest := by
        funext b
        exact (Sigma.ext_iff.mp (toOver_ofOver (rest b) (dRest b) (rRest b))).1
      have hoverTail : HEq overTail rRest := by
        refine Function.hfunext rfl ?_
        intro b y hby
        cases hby
        exact (Sigma.ext_iff.mp (toOver_ofOver (rest b) (dRest b) (rRest b))).2
      have hpair : HEq (a, overTail) (a, rRest) := Prod.mk_heq hoverTail
      exact ⟨Prod.ext rfl hbaseTail, hpair⟩

@[simp]
theorem ofOver_toOver {Γ : P.A → Type w₂} {A : (a : P.A) → Γ a → Type w₃} :
    (s : PFunctor.FreeM P α) →
    (d : Decoration (Context.extend Γ A) s) →
    ofOver s (toOver s d).1 (toOver s d).2 = d
  | .pure _, ⟨⟩ => rfl
  | .roll _ rest, ⟨⟨γ, a⟩, dRest⟩ => by
      simp [toOver, ofOver, ofOver_toOver]

/--
Equivalence between decorating by an extended metadata family and pairing a base
decoration with one dependent over-layer.
-/
def equivOver {Γ : P.A → Type w₂} (A : (a : P.A) → Γ a → Type w₃)
    (s : PFunctor.FreeM P α) :
    Equiv (Decoration (Context.extend Γ A) s)
      (Sigma fun d : Decoration Γ s => Decoration.Over Γ A s d) := by
  refine
    { toFun := toOver s
      invFun := fun ⟨d, r⟩ => ofOver s d r
      left_inv := ofOver_toOver s
      right_inv := ?_ }
  intro x
  cases x with
  | mk d r => exact toOver_ofOver s d r

end Decoration

namespace Spec

/-- Nodewise metadata on a plain `Spec`, specialized from the generic decoration API. -/
abbrev Decoration (Γ : Node.Context.{u, v}) (spec : Spec) : Type (max u v) :=
  _root_.Interaction.Decoration (P := Spec.basePFunctor) (α := PUnit.{u+1}) Γ spec

/-- The unique decoration by the empty node context. -/
def Decoration.empty : (spec : Spec) → Decoration Node.Context.empty spec
  | .done => PUnit.unit
  | .node _ rest => ⟨PUnit.unit, fun x => Decoration.empty (rest x)⟩

/-- Natural transformation between per-node decorations, applied recursively. -/
abbrev Decoration.map {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}}
    (f : Interaction.Spec.Node.ContextHom Γ Δ) :
    (spec : Spec) → Decoration Γ spec → Decoration Δ spec :=
  _root_.Interaction.Decoration.map (P := Spec.basePFunctor) (α := PUnit.{u+1}) f

@[simp, grind =]
theorem Decoration.map_id {Γ : Node.Context.{u, v}} :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.map (Node.ContextHom.id Γ) spec d = d :=
  _root_.Interaction.Decoration.map_id (P := Spec.basePFunctor) (α := PUnit.{u+1})

theorem Decoration.map_comp
    {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}} {Λ : Node.Context.{u, w₂}}
    (g : Node.ContextHom Δ Λ) (f : Node.ContextHom Γ Δ) :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.map g spec (Decoration.map f spec d) =
      Decoration.map (Node.ContextHom.comp g f) spec d :=
  _root_.Interaction.Decoration.map_comp (P := Spec.basePFunctor) (α := PUnit.{u+1}) g f

/-- Dependent decoration over `d : Decoration Γ spec`: at each node, data in
`F X γ` where `γ` is the context value from `d`, plus recursive decorations on
subtrees. -/
abbrev Decoration.Over {Γ : Node.Context.{u, v}} (F : ∀ X, Γ X → Type w)
    (spec : Spec) (d : Decoration Γ spec) : Type (max u w) :=
  _root_.Interaction.Decoration.Over (P := Spec.basePFunctor) (α := PUnit.{u+1}) Γ F spec d

/-- Fiberwise map between dependent decoration families over the same base
decoration. -/
abbrev Decoration.Over.map {Γ : Node.Context.{u, v}}
    {F : ∀ X, Γ X → Type w} {G : ∀ X, Γ X → Type w}
    (f : ∀ X γ, F X γ → G X γ) :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.Over F spec d → Decoration.Over G spec d :=
  _root_.Interaction.Decoration.Over.map (P := Spec.basePFunctor) (α := PUnit.{u+1}) f

@[simp, grind =]
theorem Decoration.Over.map_id {Γ : Node.Context.{u, v}} {F : ∀ X, Γ X → Type w} :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over F spec d) →
    Decoration.Over.map (fun _ _ x => x) spec d r = r :=
  _root_.Interaction.Decoration.Over.map_id (P := Spec.basePFunctor) (α := PUnit.{u+1})

theorem Decoration.Over.map_comp {Γ : Node.Context.{u, v}}
    {F G H : ∀ X, Γ X → Type w}
    (g : ∀ X γ, G X γ → H X γ) (f : ∀ X γ, F X γ → G X γ) :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over F spec d) →
    Decoration.Over.map g spec d (Decoration.Over.map f spec d r) =
      Decoration.Over.map (fun X γ => g X γ ∘ f X γ) spec d r :=
  _root_.Interaction.Decoration.Over.map_comp (P := Spec.basePFunctor) (α := PUnit.{u+1}) g f

/--
Transport a dependent decoration across a map of base contexts.

Given:
* a base-context morphism `f : Γ → Δ`, and
* a fiberwise map `g` from `A X γ` to `B X (f X γ)`,

this sends a displayed decoration over `d : Decoration Γ spec` to a displayed
decoration over `Decoration.map f spec d`.
-/
abbrev Decoration.Over.mapBase
    {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}}
    {A : ∀ X, Γ X → Type w₂} {B : ∀ X, Δ X → Type w₂}
    (f : Node.ContextHom Γ Δ)
    (g : ∀ X γ, A X γ → B X (f X γ)) :
    (spec : Spec) → (d : Decoration Γ spec) →
    Decoration.Over A spec d →
    Decoration.Over B spec (Decoration.map f spec d) :=
  _root_.Interaction.Decoration.Over.mapBase (P := Spec.basePFunctor) (α := PUnit.{u+1}) f g

theorem Decoration.Over.mapBase_id
    {Γ : Node.Context.{u, v}} {A : ∀ X, Γ X → Type w} :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over A spec d) →
    HEq (Decoration.Over.mapBase (Node.ContextHom.id Γ) (fun _ _ x => x) spec d r) r :=
  _root_.Interaction.Decoration.Over.mapBase_id (P := Spec.basePFunctor) (α := PUnit.{u+1})

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
        (fun X γ => gOver X (f X γ) ∘ fOver X γ) spec d r) :=
  _root_.Interaction.Decoration.Over.mapBase_comp
    (P := Spec.basePFunctor) (α := PUnit.{u+1}) f g fOver gOver

/--
Pack a base decoration and one dependent `Over` layer into a decoration of the
extended context `Γ.extend A`.

This is the tree-level realization of a single schema extension step.
-/
abbrev Decoration.ofOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → (d : Decoration Γ spec) → Decoration.Over A spec d →
    Decoration (Node.Context.extend Γ A) spec :=
  _root_.Interaction.Decoration.ofOver (P := Spec.basePFunctor) (α := PUnit.{u+1})

theorem Decoration.map_ofOver
    {Γ : Node.Context.{u, v}} {Δ : Node.Context.{u, w}}
    {A : ∀ X, Γ X → Type w₂} {B : ∀ X, Δ X → Type w₂}
    (f : Node.ContextHom Γ Δ)
    (g : ∀ X γ, A X γ → B X (f X γ)) :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over A spec d) →
    Decoration.map (Node.Context.extendMap f g) spec (Decoration.ofOver A spec d r) =
      Decoration.ofOver B spec
        (Decoration.map f spec d)
        (Decoration.Over.mapBase f g spec d r) :=
  _root_.Interaction.Decoration.map_ofOver (P := Spec.basePFunctor) (α := PUnit.{u+1}) f g

/--
Unpack a decoration of the extended context `Γ.extend A` into:
* its base decoration by `Γ`, and
* its displayed `Decoration.Over A` layer above that base.

This is the inverse structural view to `Decoration.ofOver`.
-/
abbrev Decoration.toOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → Decoration (Node.Context.extend Γ A) spec →
    Σ d : Decoration Γ spec, Decoration.Over A spec d :=
  _root_.Interaction.Decoration.toOver (P := Spec.basePFunctor) (α := PUnit.{u+1})

@[simp]
theorem Decoration.toOver_ofOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → (d : Decoration Γ spec) → (r : Decoration.Over A spec d) →
    Decoration.toOver A spec (Decoration.ofOver A spec d r) = ⟨d, r⟩ :=
  _root_.Interaction.Decoration.toOver_ofOver (P := Spec.basePFunctor) (α := PUnit.{u+1})

@[simp]
theorem Decoration.ofOver_toOver {Γ : Node.Context.{u, v}} (A : ∀ X, Γ X → Type w) :
    (spec : Spec) → (d : Decoration (Node.Context.extend Γ A) spec) →
    Decoration.ofOver A spec (Decoration.toOver A spec d).1 (Decoration.toOver A spec d).2 = d :=
  _root_.Interaction.Decoration.ofOver_toOver (P := Spec.basePFunctor) (α := PUnit.{u+1})

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
      (Sigma fun d : Decoration Γ spec => Decoration.Over A spec d) :=
  _root_.Interaction.Decoration.equivOver (P := Spec.basePFunctor) (α := PUnit.{u+1}) A spec

/-! ## Polynomial substrate `DecoratedSpec`

A `DecoratedSpec Γ` is the free term of the polynomial `Γ.toPFunctor` at the
unit payload: a tree where every internal node carries both its move space
`X` and a `Γ`-value of type `Γ X`, with continuations indexed by `X`.

This is the polynomial substrate that justifies the `Spec`-indexed family
`Decoration Γ spec`: forgetting the `Γ`-component on positions yields a
polynomial lens `Γ.toPFunctor → Spec.basePFunctor` whose lift to free
monads gives `DecoratedSpec.shape`. The fiber of `shape` over a fixed
`spec` is exactly `Decoration Γ spec`, witnessed by `decoratedSpecEquiv`. -/

/-- A `Γ`-decorated interaction spec, viewed polynomially.

This is the free monad on `Γ.toPFunctor` at the unit payload. Equivalently
(by `decoratedSpecEquiv`), it bundles a tree shape `spec : Spec` together
with a `Decoration Γ spec` on it. -/
def DecoratedSpec (Γ : Node.Context.{u, v}) : Type (max (u+1) v) :=
  PFunctor.FreeM Γ.toPFunctor PUnit.{u+1}

namespace DecoratedSpec

variable {Γ : Node.Context.{u, v}}

/-- Forget the `Γ`-component on every position, leaving only the underlying
tree shape. This is the lift to free monads of the polynomial lens
`Γ.toPFunctor → Spec.basePFunctor` whose position map is `Sigma.fst` and
whose child map is the identity. -/
def shape : DecoratedSpec Γ → Spec.{u}
  | .pure _ => Spec.done
  | .roll ⟨X, _⟩ rest => Spec.node X (fun x => DecoratedSpec.shape (rest x))

/-- Read off the per-node `Γ`-decoration of a decorated spec, indexed by
the spec's underlying `shape`. Together with `shape`, this exhibits the
fiberwise structure of `DecoratedSpec Γ` over `Spec`. -/
def decoration : (ds : DecoratedSpec Γ) → Decoration Γ (DecoratedSpec.shape ds)
  | .pure _ => PUnit.unit
  | .roll ⟨_, γ⟩ rest => ⟨γ, fun x => DecoratedSpec.decoration (rest x)⟩

/-- Pack a tree shape together with a `Γ`-decoration on it into a single
decorated spec. Inverse to the pair `(shape, decoration)`. -/
def mk : (spec : Spec.{u}) → Decoration Γ spec → DecoratedSpec Γ
  | .done, _ => PFunctor.FreeM.pure PUnit.unit
  | .node X rest, ⟨γ, dRest⟩ =>
      PFunctor.FreeM.roll ⟨X, γ⟩ (fun x => DecoratedSpec.mk (rest x) (dRest x))

@[simp]
theorem shape_mk : (spec : Spec.{u}) → (d : Decoration Γ spec) →
    DecoratedSpec.shape (DecoratedSpec.mk spec d) = spec
  | .done, _ => rfl
  | .node X rest, ⟨_, dRest⟩ => by
    change Spec.node X (fun x => DecoratedSpec.shape (DecoratedSpec.mk (rest x) (dRest x))) =
      Spec.node X rest
    exact congr_arg (Spec.node X) (funext fun x => shape_mk (rest x) (dRest x))

theorem decoration_mk : (spec : Spec.{u}) → (d : Decoration Γ spec) →
    DecoratedSpec.decoration (DecoratedSpec.mk spec d) ≍ d
  | .done, ⟨⟩ => HEq.rfl
  | .node X rest, ⟨γ, dRest⟩ => by
    change ((γ, fun x => DecoratedSpec.decoration (DecoratedSpec.mk (rest x) (dRest x))) :
        Γ X × (∀ x, Decoration Γ
          (DecoratedSpec.shape (DecoratedSpec.mk (rest x) (dRest x))))) ≍
      ((γ, dRest) : Γ X × (∀ x, Decoration Γ (rest x)))
    refine Prod.mk_heq ?_
    refine Function.hfunext rfl ?_
    intro x y hxy
    cases hxy
    exact decoration_mk (rest x) (dRest x)

@[simp]
theorem mk_shape_decoration : (ds : DecoratedSpec Γ) →
    DecoratedSpec.mk (DecoratedSpec.shape ds) (DecoratedSpec.decoration ds) = ds
  | .pure _ => rfl
  | .roll ⟨X, γ⟩ rest => by
    refine congr_arg (PFunctor.FreeM.roll (P := Γ.toPFunctor) ⟨X, γ⟩) ?_
    funext x
    exact mk_shape_decoration (rest x)

end DecoratedSpec

/-- The polynomial substrate equivalence: a `Γ`-decorated spec is the same
data as a tree shape together with a `Γ`-decoration on it.

This is the `Spec`-indexed fiberwise view of `DecoratedSpec Γ`. The forward
direction takes `(shape, decoration)`; the backward direction is `mk`. -/
def decoratedSpecEquiv {Γ : Node.Context.{u, v}} :
    DecoratedSpec Γ ≃ Σ spec : Spec.{u}, Decoration Γ spec where
  toFun ds := ⟨DecoratedSpec.shape ds, DecoratedSpec.decoration ds⟩
  invFun p := DecoratedSpec.mk p.1 p.2
  left_inv ds := DecoratedSpec.mk_shape_decoration ds
  right_inv p :=
    Sigma.ext (DecoratedSpec.shape_mk p.1 p.2) (DecoratedSpec.decoration_mk p.1 p.2)

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
