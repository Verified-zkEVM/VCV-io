/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.PFunctor.Free.Basic

/-!
# Displayed families over `PFunctor.FreeM`

This file defines displayed-family shapes over the free monad of a polynomial
functor.

For a polynomial/container `P`, a payload type `α`, and a tree
`s : PFunctor.FreeM P α`, `FreeM.Displayed D s` is the family obtained by
interpreting terminal payloads through `D.leaf` and internal positions through
`D.node`.

This is the common substrate behind several familiar structures:

* decorations, where each node stores metadata and recursively decorates every
  child;
* paths, where each node chooses one child and recursively follows that child;
* compact observations, where some nodes may be skipped or otherwise
  reinterpreted.

Categorically, this is the displayed algebra generated over the initial
`FreeM` algebra. A `Displayed.Section D` is the corresponding displayed
catamorphism: it chooses data in the displayed fiber over every tree.
-/

@[expose] public section

universe uA uB v w w₂ w₃ w₄

namespace PFunctor
namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

namespace Displayed

/--
A displayed-family shape over `FreeM P α`.

The `leaf` argument interprets terminal payloads. The `node` argument
interprets a polynomial position `a : P.A`, given the already-generated
displayed families for each child `b : P.B a`.

Special cases include node decorations, branch paths, and compact transcript
views that suppress uninformative nodes.
-/
structure Shape (P : PFunctor.{uA, uB}) (α : Type v) where
  leaf : α → Sort w
  node : (a : P.A) → ((b : P.B a) → Sort w) → Sort w

end Displayed

/--
Evaluate a displayed-family shape over a concrete `FreeM` tree.

This generates the displayed fiber at every tree by recursion on the free
polynomial structure.
-/
def Displayed (D : Displayed.Shape P α) :
    FreeM P α → Sort w
  | .pure x => D.leaf x
  | .roll a rest => D.node a (fun b => Displayed D (rest b))

namespace Displayed

@[simp]
theorem pure_eq (D : Shape P α) (x : α) :
    Displayed D (FreeM.pure (P := P) x) = D.leaf x :=
  rfl

@[simp]
theorem roll_eq (D : Shape P α) (a : P.A) (rest : P.B a → FreeM P α) :
    Displayed D (FreeM.roll a rest) =
      D.node a (fun b => Displayed D (rest b)) :=
  rfl

variable {D : Shape.{uA, uB, v, w} P α}

/-- A section chooses displayed data over every `FreeM` tree. -/
abbrev Section (D : Shape P α) :=
  (s : FreeM P α) → Displayed D s

namespace Section

/--
Construct a section from constructor-local data.

This is the displayed-family specialization of the dependent recursor for
`FreeM`.
-/
def ofConstruct
    (leafSec : (x : α) → D.leaf x)
    (nodeSec :
      (a : P.A) →
      (child : (b : P.B a) → Sort w) →
      ((b : P.B a) → child b) →
      D.node a child) :
    Section D
  | .pure x => leafSec x
  | .roll a rest => nodeSec a _ (fun b => ofConstruct leafSec nodeSec (rest b))

@[simp]
theorem ofConstruct_pure
    (leafSec : (x : α) → D.leaf x)
    (nodeSec :
      (a : P.A) →
      (child : (b : P.B a) → Sort w) →
      ((b : P.B a) → child b) →
      D.node a child)
    (x : α) :
    ofConstruct leafSec nodeSec (FreeM.pure (P := P) x) = leafSec x :=
  rfl

@[simp]
theorem ofConstruct_roll
    (leafSec : (x : α) → D.leaf x)
    (nodeSec :
      (a : P.A) →
      (child : (b : P.B a) → Sort w) →
      ((b : P.B a) → child b) →
      D.node a child)
    (a : P.A) (rest : P.B a → FreeM P α) :
    ofConstruct leafSec nodeSec (FreeM.roll a rest) =
      nodeSec a (fun b => Displayed D (rest b))
        (fun b => ofConstruct leafSec nodeSec (rest b)) :=
  rfl

end Section

variable
    {E : Shape.{uA, uB, v, w₂} P α}
    {F : Shape.{uA, uB, v, w₃} P α}
    {G : Shape.{uA, uB, v, w₄} P α}

/-- A morphism between two displayed families over the same `FreeM` tree. -/
structure Hom
    (D : Shape.{uA, uB, v, w} P α)
    (E : Shape.{uA, uB, v, w₂} P α) where
  toFun : (s : FreeM P α) → Displayed D s → Displayed E s

instance : CoeFun (Hom D E)
    (fun _ => (s : FreeM P α) → Displayed D s → Displayed E s) where
  coe f := f.toFun

namespace Hom

@[ext]
theorem ext (f g : Hom D E)
    (h : ∀ s d, f s d = g s d) : f = g := by
  cases f
  cases g
  congr
  funext s d
  exact h s d

/-- Identity morphism of a displayed family. -/
protected def id : Hom D D where
  toFun := fun _ d => d

/-- Composition of displayed-family morphisms. -/
def comp (g : Hom E F) (f : Hom D E) :
    Hom D F where
  toFun := fun s d => g s (f s d)

@[simp]
theorem id_apply (s : FreeM P α) (d : Displayed D s) :
    Hom.id s d = d :=
  rfl

@[simp]
theorem comp_apply (g : Hom E F) (f : Hom D E)
    (s : FreeM P α) (d : Displayed D s) :
    comp g f s d = g s (f s d) :=
  rfl

@[simp]
theorem comp_id (f : Hom D E) :
    comp Hom.id f = f := by
  ext s d
  rfl

@[simp]
theorem id_comp (f : Hom D E) :
    comp f Hom.id = f := by
  ext s d
  rfl

theorem comp_assoc (h : Hom F G) (g : Hom E F) (f : Hom D E) :
    comp h (comp g f) = comp (comp h g) f := by
  ext s d
  rfl

end Hom

/--
A constructor-local morphism between displayed-family shapes.

The `mapChild` field maps one node layer, given already-mapped recursive child
data.
-/
structure LocalHom
    (D : Shape.{uA, uB, v, w} P α)
    (E : Shape.{uA, uB, v, w₂} P α) where
  mapLeaf : (x : α) → D.leaf x → E.leaf x
  mapChild :
    (a : P.A) →
    (childD : (b : P.B a) → Sort w) →
    (childE : (b : P.B a) → Sort w₂) →
    ((b : P.B a) → childD b → childE b) →
    D.node a childD → E.node a childE

namespace LocalHom

/-- The recursive function underlying `LocalHom.toHom`. -/
def toHomFun (η : LocalHom D E) :
    (s : FreeM P α) → Displayed D s → Displayed E s
  | .pure x, d => η.mapLeaf x d
  | .roll a rest, d =>
      η.mapChild a _ _ (fun b => toHomFun η (rest b)) d

/-- Interpret a constructor-local morphism as a tree-indexed displayed morphism. -/
def toHom (η : LocalHom D E) : Hom D E where
  toFun := toHomFun η

@[simp]
theorem toHom_pure (η : LocalHom D E) (x : α) (d : D.leaf x) :
    η.toHom (FreeM.pure (P := P) x) d = η.mapLeaf x d :=
  rfl

@[simp]
theorem toHom_roll (η : LocalHom D E)
    (a : P.A) (rest : P.B a → FreeM P α)
    (d : D.node a (fun b => Displayed D (rest b))) :
    η.toHom (FreeM.roll a rest) d =
      η.mapChild a (fun b => Displayed D (rest b))
        (fun b => Displayed E (rest b))
        (fun b => η.toHom (rest b)) d :=
  rfl

end LocalHom

/-- Map displayed data by an interpreted morphism. -/
def map (f : Hom D E) :
    (s : FreeM P α) → Displayed D s → Displayed E s
  | s, d => f s d

@[simp]
theorem map_apply (f : Hom D E) (s : FreeM P α) (d : Displayed D s) :
    map f s d = f s d :=
  rfl

@[simp]
theorem map_id (s : FreeM P α) (d : Displayed D s) :
    map Hom.id s d = d :=
  rfl

@[simp]
theorem map_comp (g : Hom E F) (f : Hom D E)
    (s : FreeM P α) (d : Displayed D s) :
    map (Hom.comp g f) s d = map g s (map f s d) :=
  rfl

end Displayed

end FreeM
end PFunctor
