/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.PFunctor.Free.Displayed
public import ToMathlib.Logic.HEq
public import Mathlib.Logic.Equiv.Defs

/-!
# Node decorations as displayed families over `PFunctor.FreeM`

A `Decoration Γ s` is the canonical displayed family over a free `P`-tree
`s` whose leaves carry no data and whose internal nodes carry one value of
`Γ a` and recursively decorate every child.

It is the displayed family obtained from the shape

```
leaf  := fun _ => PUnit
node a child := Γ a × ((b : P.B a) → child b)
```

Equivalently, it is `Displayed D s` where `D = Decoration.shape Γ`. Because
`Decoration` is literally a `Displayed` at a chosen `Shape`, every Displayed
operation specializes immediately to `Decoration`: `Displayed.map` becomes
`Decoration.map`, `Displayed.Hom`-actions become decoration morphisms, and so
on. The lemmas in this file are exactly those specializations.

`Decoration.Over` is the dependent (displayed) variant: at each node, an
extra fiber of type `F a γ` over the base decoration's value `γ : Γ a`,
recursively over each child. It is `Displayed.Over` at the corresponding
`OverShape`.

The bridge `equivOver` packages a decoration of an extended context
`Γ.extend A` as a base decoration plus one `Over` layer.

This is the FreeM-generic substrate; protocol-flavored aliases (e.g. for
`Spec`) live downstream.
-/

@[expose] public section

universe u v w w₂ w₃ w₄ w₅

namespace PFunctor
namespace FreeM
namespace Displayed

variable {P : PFunctor.{u, v}} {α : Type w}

/-- Displayed-family shape for node-local metadata over a polynomial tree. -/
def Decoration.shape (Γ : P.A → Type w₂) :
    Shape P α where
  leaf := fun _ => PUnit.{max v w₂ + 1}
  node := fun a child => Γ a × ((b : P.B a) → child b)

/--
Node-local metadata over an arbitrary polynomial free tree.

At a control node `a : P.A`, the decoration stores one value of type `Γ a`
and recursively decorates every abstract control continuation `b : P.B a`.
-/
abbrev Decoration (Γ : P.A → Type w₂) : FreeM P α → Type (max v w₂) :=
  Displayed (Decoration.shape Γ)

/--
Displayed-family shape for a dependent layer over a polynomial decoration.

At a node with base metadata `γ : Γ a`, the over-layer stores data in
`F a γ` and recursively stores over-data over each decorated child.
-/
def Decoration.overShape (Γ : P.A → Type w₂) (F : (a : P.A) → Γ a → Type w₃) :
    OverShape (Decoration.shape (P := P) (α := α) Γ) where
  leaf := fun _ _ => PUnit.{max v w₃ + 1}
  node := fun a _ over d => F a d.1 × ((b : P.B a) → over b (d.2 b))

/-- Dependent node-local metadata over an existing polynomial decoration. -/
abbrev Decoration.Over (Γ : P.A → Type w₂) (F : (a : P.A) → Γ a → Type w₃)
    (s : FreeM P α) (d : Decoration Γ s) : Type (max v w₃) :=
  Displayed.Over (Decoration.overShape Γ F) s d

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

/-- The unique decoration by the everywhere-`PUnit` node metadata family. -/
def empty : (s : FreeM P α) → Decoration (fun _ => PUnit.{max v w₂ + 1}) s
  | .pure _ => ⟨⟩
  | .roll _ rest => ⟨PUnit.unit, fun b => empty (rest b)⟩

/-- Constructor-local displayed morphism induced by a nodewise metadata map. -/
def mapLocalHom {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a) :
    LocalHom
      (Decoration.shape (P := P) (α := α) Γ)
      (Decoration.shape (P := P) (α := α) Δ) where
  mapLeaf := fun _ _ => ⟨⟩
  mapChild := fun a _ _ mapChild d =>
    ⟨f a d.1, fun b => mapChild b (d.2 b)⟩

/-- Natural transformation between node-local decorations, applied recursively. -/
def map {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a) :
    (s : FreeM P α) → Decoration Γ s → Decoration Δ s :=
  (mapLocalHom f).toHom

@[simp]
theorem map_pure {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a) (x : α)
    (d : Decoration Γ (FreeM.pure (P := P) x)) :
    map f (FreeM.pure x) d = ⟨⟩ :=
  rfl

@[simp]
theorem map_roll {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a)
    (a : P.A) (rest : P.B a → FreeM P α)
    (d : Decoration Γ (FreeM.roll a rest)) :
    map f (FreeM.roll a rest) d =
      ⟨f a d.1, fun b => map f (rest b) (d.2 b)⟩ :=
  rfl

@[simp]
theorem map_id {Γ : P.A → Type w₂} :
    (s : FreeM P α) → (d : Decoration Γ s) →
    map (fun _ γ => γ) s d = d
  | .pure _, ⟨⟩ => rfl
  | .roll _ rest, ⟨γ, dRest⟩ => by
      simp only [map_roll]
      congr 1
      funext b
      exact map_id (rest b) (dRest b)

theorem map_comp {Γ : P.A → Type w₂} {Δ : P.A → Type w₃} {Λ : P.A → Type w₄}
    (g : ∀ a, Δ a → Λ a) (f : ∀ a, Γ a → Δ a) :
    (s : FreeM P α) → (d : Decoration Γ s) →
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
    Displayed.Over.FiberLocalHom
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
    (s : FreeM P α) → (d : Decoration Γ s) →
    Decoration.Over Γ F s d → Decoration.Over Γ G s d :=
  (mapLocalHom f).toHom

@[simp]
theorem map_id {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃} :
    (s : FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ F s d) →
    map (fun _ _ x => x) s d r = r
  | .pure _, ⟨⟩, ⟨⟩ => rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨fd, rRest⟩ => by
      simp only [map, mapLocalHom, Displayed.Over.FiberLocalHom.toHom_roll]
      congr 1
      funext b
      exact map_id (rest b) (dRest b) (rRest b)

theorem map_comp {Γ : P.A → Type w₂}
    {F : (a : P.A) → Γ a → Type w₃}
    {G : (a : P.A) → Γ a → Type w₄}
    {H : (a : P.A) → Γ a → Type w₅}
    (g : ∀ a γ, G a γ → H a γ) (f : ∀ a γ, F a γ → G a γ) :
    (s : FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ F s d) →
    map g s d (map f s d r) =
      map (fun a γ => g a γ ∘ f a γ) s d r
  | .pure _, ⟨⟩, ⟨⟩ => rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨fd, rRest⟩ => by
      simp only [map, mapLocalHom, Displayed.Over.FiberLocalHom.toHom_roll]
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
    Displayed.Over.LocalHom
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
    (s : FreeM P α) → (d : Decoration Γ s) →
    Decoration.Over Γ A s d →
    Decoration.Over Δ B s (Decoration.map f s d) :=
  (mapBaseLocalHom f g).toHom

theorem mapBase_id {Γ : P.A → Type w₂} {A : (a : P.A) → Γ a → Type w₃} :
    (s : FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ A s d) →
    HEq (mapBase (fun _ γ => γ) (fun _ _ x => x) s d r) r
  | .pure _, ⟨⟩, ⟨⟩ => HEq.rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      simp only [mapBase, mapBaseLocalHom, Displayed.Over.LocalHom.toHom_roll]
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
    (s : FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ A s d) →
    HEq
      (mapBase g gOver s (Decoration.map f s d)
        (mapBase f fOver s d r))
      (mapBase (fun a => g a ∘ f a)
        (fun a γ => gOver a (f a γ) ∘ fOver a γ) s d r)
  | .pure _, ⟨⟩, ⟨⟩ => HEq.rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      simp only [mapBase, mapBaseLocalHom, Displayed.Over.LocalHom.toHom_roll]
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
    (s : FreeM P α) → (d : Decoration Γ s) → Decoration.Over Γ A s d →
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
    (s : FreeM P α) → (d : Decoration Γ s) →
    (r : Decoration.Over Γ A s d) →
    Decoration.map (Context.extendMap f g) s (ofOver s d r) =
      ofOver s (Decoration.map f s d) (Over.mapBase f g s d r)
  | .pure _, ⟨⟩, ⟨⟩ => rfl
  | .roll _ rest, ⟨γ, dRest⟩, ⟨a, rRest⟩ => by
      simp only [map_roll, ofOver, Over.mapBase,
        Over.mapBaseLocalHom, Displayed.Over.LocalHom.toHom_roll]
      congr 1
      funext b
      exact map_ofOver f g (rest b) (dRest b) (rRest b)

/--
Unpack a decoration of an extended metadata family into its base decoration and
dependent over-layer.
-/
def toOver {Γ : P.A → Type w₂} {A : (a : P.A) → Γ a → Type w₃} :
    (s : FreeM P α) → Decoration (Context.extend Γ A) s →
    Σ d : Decoration Γ s, Decoration.Over Γ A s d
  | .pure _, _ => ⟨⟨⟩, ⟨⟩⟩
  | .roll _ rest, ⟨⟨γ, a⟩, dRest⟩ =>
      let ih := fun b => toOver (rest b) (dRest b)
      ⟨⟨γ, fun b => (ih b).1⟩, ⟨a, fun b => (ih b).2⟩⟩

@[simp]
theorem toOver_ofOver {Γ : P.A → Type w₂} {A : (a : P.A) → Γ a → Type w₃} :
    (s : FreeM P α) → (d : Decoration Γ s) →
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
    (s : FreeM P α) →
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
    (s : FreeM P α) :
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

end Displayed
end FreeM
end PFunctor
