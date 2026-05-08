/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.PFunctor.Free.Displayed

/-!
# Branch paths and telescopes for `PFunctor.FreeM`

This file contains the path-dependent structure that lives on top of the
basic free monad on a polynomial functor.

For a polynomial/container `P`, `PFunctor.FreeM P α` is the inductive type of
well-founded `P`-branching trees with leaves labelled by `α`. The definitions
below isolate the branch-object pattern of such a tree:

* `FreeM.Path s` records an explicit polynomial direction at every node.
* `FreeM.PathAlong l s` is the canonical path through `s.mapLens l`, i.e. the
  runtime branch through a control tree executed along a polynomial lens.
* `FreeM.output s path` recovers the leaf payload selected by that path.
* `FreeM.append s k` grafts a suffix tree selected by the canonical path of `s`.
* `FreeM.TelescopeWith` is the state-indexed initial algebra obtained by
  iterating such rounds, where the next state is selected by an abstract
  observation of the round.
* `FreeM.Telescope` is the specialization where observations are canonical
  branch paths.

## Terminology and references

The same object appears under several names in the literature. In polynomial
functor language, the free monad on a polynomial is a type of terminating
decision trees. In container and W-type language, these are well-founded trees
and `Path` is the type of paths through such a tree. In dependent-type
presentations of games, these are dependent type trees and paths. In
programming language semantics, the coinductive analogue is an interaction
tree.

Relevant references include:

* Hancock and Setzer, *Interactive Programs in Dependent Type Theory*, for
  dependent I/O-trees over command-response worlds.
* Altenkirch, Ghani, Hancock, McBride, and Morris, *Indexed Containers*, for
  containers, indexed containers, and interaction structures.
* Libkind and Spivak, *Pattern runs on matter*, for free polynomial monads as
  terminating decision trees.
* Escardo and Oliva, *Higher-order games with dependent types*, for dependent
  type trees and paths in history-dependent games.
* Xia, Zakowski, He, Hur, Malecha, Pierce, and Zdancewic, *Interaction Trees*,
  for the coinductive programming-language analogue.
-/

@[expose] public section

universe v w z t uA uB uA₂ uB₂

namespace PFunctor
namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-! ## Canonical paths -/

variable {Q : PFunctor.{uA₂, uB₂}}

/-- Displayed-family shape for canonical root-to-leaf paths. -/
def Path.shape (P : PFunctor.{uA, uB}) (α : Type v) :
    Displayed.Shape.{uA, uB, v, uB+1} P α where
  leaf := fun _ => PUnit.{uB+1}
  node := fun a child => (b : P.B a) × child b

/-- The canonical root-to-leaf path through a `FreeM` tree. -/
abbrev Path {α : Type v} : FreeM P α → Type uB :=
  Displayed (Path.shape P α)

/-! ## Runtime paths along a lens -/

/-- Runtime path through a `P`-tree executed along a lens `l : Lens P Q`.

This is the displayed family over the source control tree whose node directions
come from the runtime polynomial `Q`. A runtime direction
`d : Q.B (l.toFunA a)` selects the source branch `l.toFunB a d`. -/
def PathAlong.shape (l : Lens P Q) :
    Displayed.Shape.{uA, uB, v, uB₂+1} P α where
  leaf := fun _ => PUnit.{uB₂+1}
  node := fun a child => (d : Q.B (l.toFunA a)) × child (l.toFunB a d)

/-- Runtime path through a `P`-tree executed along a lens `l : Lens P Q`. -/
abbrev PathAlong (l : Lens P Q) (s : FreeM P α) : Type uB₂ :=
  Displayed (PathAlong.shape l) s

/-- The leaf payload selected by a path. Although the path itself records only
branch choices, the tree and path together determine the terminal `pure`
payload. -/
def output : (s : FreeM P α) → Path s → α
  | .pure x, _ => x
  | .roll _ rest, ⟨b, path⟩ => output (rest b) path

/-- The leaf payload selected by a runtime path along a lens. -/
def outputAlong (l : Lens P Q) : (s : FreeM P α) → PathAlong l s → α
  | .pure x, _ => x
  | .roll a rest, ⟨d, path⟩ => outputAlong l (rest (l.toFunB a d)) path

@[simp]
theorem outputAlong_pure (l : Lens P Q) (x : α)
    (path : PathAlong l (FreeM.pure x : FreeM P α)) :
    outputAlong l (FreeM.pure x) path = x :=
  rfl

@[simp]
theorem outputAlong_roll (l : Lens P Q) (a : P.A)
    (rest : P.B a → FreeM P α)
    (d : Q.B (l.toFunA a)) (path : PathAlong l (rest (l.toFunB a d))) :
    outputAlong l (FreeM.roll a rest) ⟨d, path⟩ =
      outputAlong l (rest (l.toFunB a d)) path :=
  rfl

@[simp]
theorem output_pure (x : α) (path : Path (FreeM.pure (P := P) x)) :
    output (FreeM.pure x) path = x := rfl

@[simp]
theorem output_roll (a : P.A) (rest : P.B a → FreeM P α)
    (b : P.B a) (path : Path (rest b)) :
    output (FreeM.roll a rest) ⟨b, path⟩ = output (rest b) path := rfl

/-- Constructor-local projection from runtime paths to control paths. -/
def projectPathAlongLocalHom (l : Lens P Q) :
    Displayed.LocalHom (PathAlong.shape (P := P) (Q := Q) (α := α) l) (Path.shape P α) where
  mapLeaf := fun _ _ => ⟨⟩
  mapChild := fun a _ _ mapChild path =>
    ⟨l.toFunB a path.1, mapChild (l.toFunB a path.1) path.2⟩

/-- Project a concrete runtime path along a lens back to the abstract
canonical branch path of the control tree. -/
def projectPathAlong (l : Lens P Q) : (s : FreeM P α) → PathAlong l s → Path s :=
  (projectPathAlongLocalHom l).toHom

@[simp]
theorem projectPathAlong_pure (l : Lens P Q) (x : α)
    (path : PathAlong l (FreeM.pure x : FreeM P α)) :
    projectPathAlong l (FreeM.pure x) path = ⟨⟩ :=
  rfl

@[simp]
theorem projectPathAlong_roll (l : Lens P Q) (a : P.A)
    (rest : P.B a → FreeM P α)
    (path : PathAlong l (FreeM.roll a rest)) :
    projectPathAlong l (FreeM.roll a rest) path =
      ⟨l.toFunB a path.1,
        projectPathAlong l (rest (l.toFunB a path.1)) path.2⟩ :=
  rfl

@[simp]
theorem output_projectPathAlong (l : Lens P Q) :
    (s : FreeM P α) → (path : PathAlong l s) →
      output s (projectPathAlong l s path) = outputAlong l s path
  | .pure _, _ => rfl
  | .roll a rest, ⟨d, path⟩ =>
      output_projectPathAlong l (rest (l.toFunB a d)) path

/-! ## Runtime paths and lens-mapped trees -/

/--
View a runtime path through `s` along `l` as the canonical path through the
lens-mapped runtime tree `s.mapLens l`.

The two types have the same constructor shape, but `PathAlong` is defined over
the source tree while `Path (s.mapLens l)` is defined over the lens-mapped tree.
-/
def pathAlongToMapLensPath (l : Lens P Q) :
    (s : FreeM P α) → PathAlong l s → Path (s.mapLens l)
  | .pure _, _ => ⟨⟩
  | .roll a rest, ⟨d, path⟩ =>
      ⟨d, pathAlongToMapLensPath l (rest (l.toFunB a d)) path⟩

@[simp]
theorem pathAlongToMapLensPath_pure (l : Lens P Q) (x : α)
    (path : PathAlong l (FreeM.pure x : FreeM P α)) :
    pathAlongToMapLensPath l (FreeM.pure x) path = ⟨⟩ :=
  rfl

@[simp]
theorem pathAlongToMapLensPath_roll (l : Lens P Q) (a : P.A)
    (rest : P.B a → FreeM P α)
    (d : Q.B (l.toFunA a)) (path : PathAlong l (rest (l.toFunB a d))) :
    pathAlongToMapLensPath l (FreeM.roll a rest) ⟨d, path⟩ =
      ⟨d, pathAlongToMapLensPath l (rest (l.toFunB a d)) path⟩ :=
  rfl

/--
View a canonical path through the lens-mapped runtime tree `s.mapLens l` as a
runtime path through the original control tree `s` along `l`.

This is the inverse constructor-by-constructor view of
`pathAlongToMapLensPath`.
-/
def mapLensPathToPathAlong (l : Lens P Q) :
    (s : FreeM P α) → Path (s.mapLens l) → PathAlong l s
  | .pure _, _ => ⟨⟩
  | .roll a rest, ⟨d, path⟩ =>
      ⟨d, mapLensPathToPathAlong l (rest (l.toFunB a d)) path⟩

@[simp]
theorem mapLensPathToPathAlong_pure (l : Lens P Q) (x : α)
    (path : Path ((FreeM.pure x : FreeM P α).mapLens l)) :
    mapLensPathToPathAlong l (FreeM.pure x) path = ⟨⟩ :=
  rfl

@[simp]
theorem mapLensPathToPathAlong_roll (l : Lens P Q) (a : P.A)
    (rest : P.B a → FreeM P α)
    (d : Q.B (l.toFunA a))
    (path : Path ((rest (l.toFunB a d)).mapLens l)) :
    mapLensPathToPathAlong l (FreeM.roll a rest) ⟨d, path⟩ =
      ⟨d, mapLensPathToPathAlong l (rest (l.toFunB a d)) path⟩ :=
  rfl

@[simp]
theorem mapLensPathToPathAlong_toMapLensPath (l : Lens P Q) :
    (s : FreeM P α) → (path : PathAlong l s) →
      mapLensPathToPathAlong l s (pathAlongToMapLensPath l s path) = path
  | .pure _, _ => rfl
  | .roll a rest, ⟨d, path⟩ => by
      simp [pathAlongToMapLensPath,
        mapLensPathToPathAlong_toMapLensPath l (rest (l.toFunB a d)) path]

@[simp]
theorem pathAlongToMapLensPath_toPathAlong (l : Lens P Q) :
    (s : FreeM P α) → (path : Path (s.mapLens l)) →
      pathAlongToMapLensPath l s (mapLensPathToPathAlong l s path) = path
  | .pure _, _ => rfl
  | .roll a rest, ⟨d, path⟩ => by
      simp [pathAlongToMapLensPath_toPathAlong l (rest (l.toFunB a d)) path]

@[simp]
theorem output_mapLens_pathAlongToMapLensPath (l : Lens P Q) :
    (s : FreeM P α) → (path : PathAlong l s) →
      output (s.mapLens l) (pathAlongToMapLensPath l s path) =
        outputAlong l s path
  | .pure _, _ => rfl
  | .roll a rest, ⟨d, path⟩ =>
      output_mapLens_pathAlongToMapLensPath l (rest (l.toFunB a d)) path

@[simp]
theorem outputAlong_mapLensPathToPathAlong (l : Lens P Q) :
    (s : FreeM P α) → (path : Path (s.mapLens l)) →
      outputAlong l s (mapLensPathToPathAlong l s path) =
        output (s.mapLens l) path
  | .pure _, _ => rfl
  | .roll a rest, ⟨d, path⟩ =>
      outputAlong_mapLensPathToPathAlong l (rest (l.toFunB a d)) path

/-- Dependent sequential composition for `FreeM` trees using canonical paths. -/
def append {β : Type t} :
    (s₁ : FreeM P α) →
    (Path s₁ → FreeM P β) →
    FreeM P β
  | .pure _, s₂ => s₂ ⟨⟩
  | .roll a rest, s₂ =>
      .roll a fun b => append (rest b) (fun path => s₂ ⟨b, path⟩)

@[simp]
theorem append_pure {β : Type t} (x : α)
    (s₂ : Path (FreeM.pure (P := P) x) → FreeM P β) :
    append (FreeM.pure x) s₂ = s₂ ⟨⟩ := rfl

@[simp]
theorem append_roll {β : Type t} (a : P.A) (rest : P.B a → FreeM P α)
    (s₂ : Path (FreeM.roll a rest) → FreeM P β) :
    append (FreeM.roll a rest) s₂ =
      FreeM.roll a (fun b => append (rest b) (fun path => s₂ ⟨b, path⟩)) := rfl

namespace Path

/-! ## Canonical paths through appended trees -/

/-- Lift a two-argument family indexed by a canonical prefix path and canonical
suffix path to a family on the appended tree. -/
def liftAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    ((path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    Path (FreeM.append s₁ s₂) → Type w
  | .pure _, _, F, path => F ⟨⟩ path
  | .roll _ rest, s₂, F, ⟨b, path⟩ =>
      liftAppend (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path

/-- Combine canonical prefix and suffix paths into a canonical path through the
appended tree. -/
def append {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (path₁ : Path s₁) → Path (s₂ path₁) → Path (FreeM.append s₁ s₂)
  | .pure _, _, _, path₂ => path₂
  | .roll _ rest, s₂, ⟨b, path₁⟩, path₂ =>
      ⟨b, append (rest b) (fun path => s₂ ⟨b, path⟩) path₁ path₂⟩

/-- Split a canonical path through an appended tree into prefix and suffix
canonical paths. -/
def split {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    Path (FreeM.append s₁ s₂) → (path₁ : Path s₁) × Path (s₂ path₁)
  | .pure _, _, path => ⟨⟨⟩, path⟩
  | .roll _ rest, s₂, ⟨b, path⟩ =>
      let splitRest := split (rest b) (fun path₁ => s₂ ⟨b, path₁⟩) path
      ⟨⟨b, splitRest.1⟩, splitRest.2⟩

/-- `liftAppend` on an appended canonical path reduces to the original
two-argument family. -/
@[simp]
theorem liftAppend_append {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) →
    liftAppend s₁ s₂ F (append s₁ s₂ path₁ path₂) = F path₁ path₂
  | .pure _, _, _, ⟨⟩, _ => rfl
  | .roll _ rest, s₂, F, ⟨b, path₁⟩, path₂ => by
      simpa [liftAppend, append] using
        liftAppend_append (rest b) (fun path => s₂ ⟨b, path⟩)
          (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂

/-- Splitting after appending recovers the original canonical prefix and suffix. -/
@[simp]
theorem split_append {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) →
    split s₁ s₂ (append s₁ s₂ path₁ path₂) = ⟨path₁, path₂⟩
  | .pure _, _, ⟨⟩, _ => rfl
  | .roll _ rest, s₂, ⟨b, path₁⟩, path₂ => by
      simp only [append, split]
      rw [split_append]

/-- Appending the components produced by `split` recovers the original
canonical path. -/
@[simp]
theorem append_split {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (path : Path (FreeM.append s₁ s₂)) →
    let splitPath := split s₁ s₂ path
    append s₁ s₂ splitPath.1 splitPath.2 = path
  | .pure _, _, _ => rfl
  | .roll _ rest, s₂, ⟨b, path⟩ => by
      simp only [split, append]
      rw [append_split]

/-- Transport a value of `F path₁ path₂` to the `liftAppend` family at the
combined canonical path. -/
def packAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) →
    F path₁ path₂ → liftAppend s₁ s₂ F (append s₁ s₂ path₁ path₂)
  | .pure _, _, _, ⟨⟩, _, x => x
  | .roll _ rest, s₂, F, ⟨b, path₁⟩, path₂, x =>
      packAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂ x

/-- Transport a value from the `liftAppend` family at an appended canonical path
back to the original two-argument family. -/
def unpackAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) →
    liftAppend s₁ s₂ F (append s₁ s₂ path₁ path₂) → F path₁ path₂
  | .pure _, _, _, ⟨⟩, _, x => x
  | .roll _ rest, s₂, F, ⟨b, path₁⟩, path₂, x =>
      unpackAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂ x

/-- `liftAppend` respects pointwise equality of the pair-indexed family. -/
theorem liftAppend_congr {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F G : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (∀ path₁ path₂, F path₁ path₂ = G path₁ path₂) →
    (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ F path = liftAppend s₁ s₂ G path
  | .pure _, _, _, _, h, path => h ⟨⟩ path
  | .roll _ rest, s₂, _, _, h, ⟨b, path⟩ =>
      liftAppend_congr (rest b) (fun path₁ => s₂ ⟨b, path₁⟩) _ _
        (fun path₁ path₂ => h ⟨b, path₁⟩ path₂) path

/-- A constant family is unaffected by `liftAppend`. -/
@[simp]
theorem liftAppend_const {β : Type t} (γ : Type w) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ (fun _ _ => γ) path = γ
  | .pure _, _, _ => rfl
  | .roll _ rest, s₂, ⟨b, path⟩ =>
      liftAppend_const γ (rest b) (fun path₁ => s₂ ⟨b, path₁⟩) path

/-- `liftAppend` can be reconstructed from the path pieces returned by `split`. -/
theorem liftAppend_split {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path : Path (FreeM.append s₁ s₂)) →
    let splitPath := split s₁ s₂ path
    liftAppend s₁ s₂ F path = F splitPath.1 splitPath.2
  | .pure _, _, _, _ => rfl
  | .roll _ rest, s₂, F, ⟨b, path⟩ => by
      simpa [split, liftAppend] using
        liftAppend_split (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
          (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path

/-- Reinterpret a `liftAppend` value against the path pair recovered by `split`. -/
def unliftAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ F path →
    let splitPath := split s₁ s₂ path
    F splitPath.1 splitPath.2
  | .pure _, _, _, _, x => x
  | .roll _ rest, s₂, F, ⟨b, path⟩, x =>
      unliftAppend (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path x

@[simp]
theorem unpackAppend_packAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) →
    (x : F path₁ path₂) →
    unpackAppend s₁ s₂ F path₁ path₂ (packAppend s₁ s₂ F path₁ path₂ x) = x
  | .pure _, _, _, ⟨⟩, _, _ => rfl
  | .roll _ rest, s₂, F, ⟨b, path₁⟩, path₂, x =>
      unpackAppend_packAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂ x

@[simp]
theorem packAppend_unpackAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) →
    (x : liftAppend s₁ s₂ F (append s₁ s₂ path₁ path₂)) →
    packAppend s₁ s₂ F path₁ path₂ (unpackAppend s₁ s₂ F path₁ path₂ x) = x
  | .pure _, _, _, ⟨⟩, _, _ => rfl
  | .roll _ rest, s₂, F, ⟨b, path₁⟩, path₂, x =>
      packAppend_unpackAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂) path₁ path₂ x

/-- Collapse a `liftAppend` family indexed by `append path₁ path₂` back to the
fused path index. -/
def collapseAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : Path (FreeM.append s₁ s₂) → Type w) →
    (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂
      (fun path₁ path₂ => F (append s₁ s₂ path₁ path₂)) path →
      F path
  | .pure _, _, _, _, x => x
  | .roll _ rest, s₂, F, ⟨b, path⟩, x =>
      collapseAppend (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun tail => F ⟨b, tail⟩) path x

@[simp]
theorem collapseAppend_append {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : Path (FreeM.append s₁ s₂) → Type w) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) →
    (x : liftAppend s₁ s₂
      (fun path₁ path₂ => F (append s₁ s₂ path₁ path₂))
      (append s₁ s₂ path₁ path₂)) →
    collapseAppend s₁ s₂ F (append s₁ s₂ path₁ path₂) x =
      unpackAppend s₁ s₂
        (fun path₁ path₂ => F (append s₁ s₂ path₁ path₂)) path₁ path₂ x
  | .pure _, _, _, ⟨⟩, _, _ => rfl
  | .roll _ rest, s₂, F, ⟨b, path₁⟩, path₂, x => by
      simpa [collapseAppend, append] using
        collapseAppend_append (rest b) (fun path => s₂ ⟨b, path⟩)
          (fun tail => F ⟨b, tail⟩) path₁ path₂ x

/-- Split a fused `liftAppend` product payload into separately lifted payloads. -/
def liftAppendProd {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path →
      liftAppend s₁ s₂ A path × liftAppend s₁ s₂ B path
  | .pure _, _, _, _, _, x => x
  | .roll _ rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProd (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

/-- Fuse separately lifted payloads into a lifted product payload. -/
def liftAppendProdMk {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ A path × liftAppend s₁ s₂ B path →
      liftAppend s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path
  | .pure _, _, _, _, _, x => x
  | .roll _ rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProdMk (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

@[simp]
theorem liftAppendProdMk_liftAppendProd {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path : Path (FreeM.append s₁ s₂)) →
    (x : liftAppend s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path) →
    liftAppendProdMk s₁ s₂ A B path (liftAppendProd s₁ s₂ A B path x) = x
  | .pure _, _, _, _, _, _ => rfl
  | .roll _ rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProdMk_liftAppendProd (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

@[simp]
theorem liftAppendProd_liftAppendProdMk {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path : Path (FreeM.append s₁ s₂)) →
    (x : liftAppend s₁ s₂ A path × liftAppend s₁ s₂ B path) →
    liftAppendProd s₁ s₂ A B path (liftAppendProdMk s₁ s₂ A B path x) = x
  | .pure _, _, _, _, _, _ => rfl
  | .roll _ rest, s₂, A, B, ⟨b, path⟩, x =>
      liftAppendProd_liftAppendProdMk (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path x

@[simp]
theorem liftAppendProd_packAppend {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (A B : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) →
    (x : A path₁ path₂ × B path₁ path₂) →
    liftAppendProd s₁ s₂ A B (append s₁ s₂ path₁ path₂)
      (packAppend s₁ s₂ (fun path₁ path₂ => A path₁ path₂ × B path₁ path₂) path₁ path₂ x) =
        (packAppend s₁ s₂ A path₁ path₂ x.1, packAppend s₁ s₂ B path₁ path₂ x.2)
  | .pure _, _, _, _, ⟨⟩, _, _ => rfl
  | .roll _ rest, s₂, A, B, ⟨b, path₁⟩, path₂, x =>
      liftAppendProd_packAppend (rest b) (fun path => s₂ ⟨b, path⟩)
        (fun path₁ path₂ => A ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => B ⟨b, path₁⟩ path₂) path₁ path₂ x

/-- When `path = append path₁ path₂`, the round-trip (`packAppend` then `unliftAppend`)
recovers the original pair-indexed relation value. -/
theorem rel_unliftAppend_append {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F G : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (R : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)),
      F path₁ path₂ → G path₁ path₂ → Prop) →
    (path₁ : Path s₁) → (path₂ : Path (s₂ path₁)) →
    (x : F path₁ path₂) → (y : G path₁ path₂) →
    let path := append s₁ s₂ path₁ path₂
    R (split s₁ s₂ path).1 (split s₁ s₂ path).2
      (unliftAppend s₁ s₂ F path
        (packAppend s₁ s₂ F path₁ path₂ x))
      (unliftAppend s₁ s₂ G path
        (packAppend s₁ s₂ G path₁ path₂ y))
    = R path₁ path₂ x y
  | .pure _, _, _, _, _, ⟨⟩, _, _, _ => rfl
  | .roll _ rest, s₂, F, G, R, ⟨b, path₁⟩, path₂, x, y => by
      change _ = R ⟨b, path₁⟩ path₂ x y
      simpa [append, split, unliftAppend, liftAppend, packAppend] using
        rel_unliftAppend_append (rest b) (fun path => s₂ ⟨b, path⟩)
          (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
          (fun path₁ path₂ => G ⟨b, path₁⟩ path₂)
          (fun path₁ path₂ => R ⟨b, path₁⟩ path₂) path₁ path₂ x y

/-- Lift a binary relation on pair-indexed families to the fused appended path. -/
def liftAppendRel {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (G : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (R : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)),
      F path₁ path₂ → G path₁ path₂ → Prop) →
    (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ F path →
    liftAppend s₁ s₂ G path → Prop
  | .pure _, _, _, _, R, path, x, y => R ⟨⟩ path x y
  | .roll _ rest, s₂, F, G, R, ⟨b, path⟩, x, y =>
      liftAppendRel (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => G ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => R ⟨b, path₁⟩ path₂) path x y

/-- `liftAppendRel` applies `R` at the path pair recovered by `split`. -/
theorem liftAppendRel_iff {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (G : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (R : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)),
      F path₁ path₂ → G path₁ path₂ → Prop) →
    (path : Path (FreeM.append s₁ s₂)) →
    (x : liftAppend s₁ s₂ F path) →
    (y : liftAppend s₁ s₂ G path) →
    liftAppendRel s₁ s₂ F G R path x y ↔
      R (split s₁ s₂ path).1 (split s₁ s₂ path).2
        (unliftAppend s₁ s₂ F path x)
        (unliftAppend s₁ s₂ G path y)
  | .pure _, _, _, _, _, _, _, _ => Iff.rfl
  | .roll _ rest, s₂, F, G, R, ⟨b, path⟩, x, y =>
      liftAppendRel_iff (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => G ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => R ⟨b, path₁⟩ path₂) path x y

/-- Lift a unary predicate on a pair-indexed family to the fused appended path. -/
def liftAppendPred {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (Pred : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)), F path₁ path₂ → Prop) →
    (path : Path (FreeM.append s₁ s₂)) →
    liftAppend s₁ s₂ F path → Prop
  | .pure _, _, _, Pred, path, x => Pred ⟨⟩ path x
  | .roll _ rest, s₂, F, Pred, ⟨b, path⟩, x =>
      liftAppendPred (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => Pred ⟨b, path₁⟩ path₂) path x

/-- `liftAppendPred` applies the predicate at the path pair recovered by `split`. -/
theorem liftAppendPred_iff {β : Type t} :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : Path s₁) → Path (s₂ path₁) → Type w) →
    (Pred : ∀ (path₁ : Path s₁) (path₂ : Path (s₂ path₁)), F path₁ path₂ → Prop) →
    (path : Path (FreeM.append s₁ s₂)) →
    (x : liftAppend s₁ s₂ F path) →
    liftAppendPred s₁ s₂ F Pred path x ↔
      Pred (split s₁ s₂ path).1 (split s₁ s₂ path).2
        (unliftAppend s₁ s₂ F path x)
  | .pure _, _, _, _, _, _ => Iff.rfl
  | .roll _ rest, s₂, F, Pred, ⟨b, path⟩, x =>
      liftAppendPred_iff (rest b) (fun path₁ => s₂ ⟨b, path₁⟩)
        (fun path₁ path₂ => F ⟨b, path₁⟩ path₂)
        (fun path₁ path₂ => Pred ⟨b, path₁⟩ path₂) path x

end Path

namespace PathAlong

/-! ## Lens-executed paths through appended trees -/

/-- Lift a two-argument family indexed by a runtime prefix path and a runtime
suffix path to a family on the appended tree.

The suffix is selected by the control projection of the runtime prefix. -/
def liftAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    ((path₁ : PathAlong l s₁) →
      PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    PathAlong l (FreeM.append s₁ s₂) → Type w
  | .pure _, _, F, path => F ⟨⟩ path
  | .roll a rest, s₂, F, ⟨d, path⟩ =>
      liftAppend l (rest (l.toFunB a d))
        (fun path₁ => s₂ ⟨l.toFunB a d, path₁⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂)
        path

/-- Combine a runtime prefix path and a runtime suffix path into a runtime path
through the appended tree. -/
def append {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (path₁ : PathAlong l s₁) →
    PathAlong l (s₂ (projectPathAlong l s₁ path₁)) →
    PathAlong l (FreeM.append s₁ s₂)
  | .pure _, _, _, path₂ => path₂
  | .roll a rest, s₂, ⟨d, path₁⟩, path₂ =>
      ⟨d, append l (rest (l.toFunB a d))
        (fun path => s₂ ⟨l.toFunB a d, path⟩)
        path₁ path₂⟩

/-- Split a runtime path through an appended tree into its prefix runtime path
and suffix runtime path. -/
def split {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    PathAlong l (FreeM.append s₁ s₂) →
    (path₁ : PathAlong l s₁) ×
      PathAlong l (s₂ (projectPathAlong l s₁ path₁))
  | .pure _, _, path => ⟨⟨⟩, path⟩
  | .roll a rest, s₂, ⟨d, path⟩ =>
      let splitRest :=
        split l (rest (l.toFunB a d))
          (fun path₁ => s₂ ⟨l.toFunB a d, path₁⟩)
          path
      ⟨⟨d, splitRest.1⟩, splitRest.2⟩

/-- `liftAppend` on an appended runtime path reduces to the original
two-argument family. -/
@[simp]
theorem liftAppend_append {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) →
      PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) →
    (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    liftAppend l s₁ s₂ F (append l s₁ s₂ path₁ path₂) = F path₁ path₂
  | .pure _, _, _, ⟨⟩, _ => rfl
  | .roll a rest, s₂, F, ⟨d, path₁⟩, path₂ => by
      simpa [liftAppend, append] using
        liftAppend_append l (rest (l.toFunB a d))
          (fun path => s₂ ⟨l.toFunB a d, path⟩)
          (fun path₁ path₂ => F ⟨d, path₁⟩ path₂)
          path₁ path₂

/-- Splitting after appending recovers the original runtime prefix and suffix. -/
@[simp]
theorem split_append {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (path₁ : PathAlong l s₁) →
    (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    split l s₁ s₂ (append l s₁ s₂ path₁ path₂) = ⟨path₁, path₂⟩
  | .pure _, _, ⟨⟩, _ => rfl
  | .roll a rest, s₂, ⟨d, path₁⟩, path₂ => by
      simp only [append, split]
      rw [split_append]

/-- Appending the components produced by `split` recovers the original runtime path. -/
@[simp]
theorem append_split {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (path : PathAlong l (FreeM.append s₁ s₂)) →
    let splitPath := split l s₁ s₂ path
    append l s₁ s₂ splitPath.1 splitPath.2 = path
  | .pure _, _, _ => rfl
  | .roll a rest, s₂, ⟨d, path⟩ => by
      simp only [split, append]
      rw [append_split]

/-- Transport a value of `F path₁ path₂` to the `liftAppend` family at the
combined runtime path. The definition follows the same recursion as
`liftAppend`, so it avoids explicit equality transports. -/
def packAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) →
      PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) →
    (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    F path₁ path₂ → liftAppend l s₁ s₂ F (append l s₁ s₂ path₁ path₂)
  | .pure _, _, _, ⟨⟩, _, x => x
  | .roll a rest, s₂, F, ⟨d, path₁⟩, path₂, x =>
      packAppend l (rest (l.toFunB a d))
        (fun path => s₂ ⟨l.toFunB a d, path⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂)
        path₁ path₂ x

/-- Transport a value from the `liftAppend` family at an appended runtime path
back to the original two-argument family. -/
def unpackAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) →
      PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) →
    (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    liftAppend l s₁ s₂ F (append l s₁ s₂ path₁ path₂) → F path₁ path₂
  | .pure _, _, _, ⟨⟩, _, x => x
  | .roll a rest, s₂, F, ⟨d, path₁⟩, path₂, x =>
      unpackAppend l (rest (l.toFunB a d))
        (fun path => s₂ ⟨l.toFunB a d, path⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂)
        path₁ path₂ x

/-- `liftAppend` can be reconstructed from the runtime path pieces returned by `split`. -/
theorem liftAppend_split {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) →
      PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path : PathAlong l (FreeM.append s₁ s₂)) →
    let splitPath := split l s₁ s₂ path
    liftAppend l s₁ s₂ F path = F splitPath.1 splitPath.2
  | .pure _, _, _, _ => rfl
  | .roll a rest, s₂, F, ⟨d, path⟩ => by
      simpa [split, liftAppend] using
        liftAppend_split l (rest (l.toFunB a d))
          (fun path₁ => s₂ ⟨l.toFunB a d, path₁⟩)
          (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path

/-- Reinterpret a runtime `liftAppend` value against the path pair recovered by `split`. -/
def unliftAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) →
      PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path : PathAlong l (FreeM.append s₁ s₂)) →
    liftAppend l s₁ s₂ F path →
    let splitPath := split l s₁ s₂ path
    F splitPath.1 splitPath.2
  | .pure _, _, _, _, x => x
  | .roll a rest, s₂, F, ⟨d, path⟩, x =>
      unliftAppend l (rest (l.toFunB a d))
        (fun path₁ => s₂ ⟨l.toFunB a d, path₁⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path x

@[simp]
theorem unpackAppend_packAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) →
      PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) →
    (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    (x : F path₁ path₂) →
    unpackAppend l s₁ s₂ F path₁ path₂ (packAppend l s₁ s₂ F path₁ path₂ x) = x
  | .pure _, _, _, ⟨⟩, _, _ => rfl
  | .roll a rest, s₂, F, ⟨d, path₁⟩, path₂, x =>
      unpackAppend_packAppend l (rest (l.toFunB a d))
        (fun path => s₂ ⟨l.toFunB a d, path⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path₁ path₂ x

@[simp]
theorem packAppend_unpackAppend {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (F : (path₁ : PathAlong l s₁) →
      PathAlong l (s₂ (projectPathAlong l s₁ path₁)) → Type w) →
    (path₁ : PathAlong l s₁) →
    (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    (x : liftAppend l s₁ s₂ F (append l s₁ s₂ path₁ path₂)) →
    packAppend l s₁ s₂ F path₁ path₂ (unpackAppend l s₁ s₂ F path₁ path₂ x) = x
  | .pure _, _, _, ⟨⟩, _, _ => rfl
  | .roll a rest, s₂, F, ⟨d, path₁⟩, path₂, x =>
      packAppend_unpackAppend l (rest (l.toFunB a d))
        (fun path => s₂ ⟨l.toFunB a d, path⟩)
        (fun path₁ path₂ => F ⟨d, path₁⟩ path₂) path₁ path₂ x

/-- Projecting an appended runtime path gives the appended projected paths. -/
@[simp]
theorem projectPathAlong_append {β : Type t} (l : Lens P Q) :
    (s₁ : FreeM P α) → (s₂ : Path s₁ → FreeM P β) →
    (path₁ : PathAlong l s₁) →
    (path₂ : PathAlong l (s₂ (projectPathAlong l s₁ path₁))) →
    projectPathAlong l (FreeM.append s₁ s₂) (append l s₁ s₂ path₁ path₂) =
      Path.append s₁ s₂ (projectPathAlong l s₁ path₁)
        (projectPathAlong l (s₂ (projectPathAlong l s₁ path₁)) path₂)
  | .pure _, _, ⟨⟩, _ => rfl
  | .roll a rest, s₂, ⟨d, path₁⟩, path₂ => by
      change
        (⟨l.toFunB a d,
          projectPathAlong l (FreeM.append (rest (l.toFunB a d))
            (fun path => s₂ ⟨l.toFunB a d, path⟩))
            (append l (rest (l.toFunB a d))
              (fun path => s₂ ⟨l.toFunB a d, path⟩) path₁ path₂)⟩ :
          Path (FreeM.append (FreeM.roll a rest) s₂)) =
        (⟨l.toFunB a d,
          Path.append (rest (l.toFunB a d))
            (fun path => s₂ ⟨l.toFunB a d, path⟩)
            (projectPathAlong l (rest (l.toFunB a d)) path₁)
            (projectPathAlong l
              (s₂ ⟨l.toFunB a d, projectPathAlong l (rest (l.toFunB a d)) path₁⟩)
              path₂)⟩ :
          Path (FreeM.append (FreeM.roll a rest) s₂))
      exact congrArg
        (fun path : Path (FreeM.append (rest (l.toFunB a d))
            (fun path => s₂ ⟨l.toFunB a d, path⟩)) =>
          (⟨l.toFunB a d, path⟩ :
            Path (FreeM.append (FreeM.roll a rest) s₂)))
        (projectPathAlong_append l (rest (l.toFunB a d))
          (fun path => s₂ ⟨l.toFunB a d, path⟩) path₁ path₂)

end PathAlong

/-! ## Telescopes -/

/-- Initial-algebra presentation of a state-machine telescope of `FreeM`
rounds observed through an arbitrary observation family `Obs`.

At each state `s`, an inhabitant either terminates or extends by running
`round s` and recursing into the next state selected by an observation
`obs : Obs s`. The observation family is intentionally abstract: canonical
`FreeM` branch paths use `Obs s = Path (round s)`, while quotiented or compact
views can erase uninformative singleton choices. -/
inductive TelescopeWith {St : Type z} {Out : St → Type v}
    (round : (s : St) → FreeM P (Out s))
    (Obs : St → Type w)
    (step : (s : St) → Obs s → St) : St → Type (max w z)
  | done (s : St) : TelescopeWith round Obs step s
  | extend (s : St)
      (cont : (obs : Obs s) → TelescopeWith round Obs step (step s obs)) :
      TelescopeWith round Obs step s

namespace TelescopeWith

variable {St : Type z} {Out : St → Type v} {round : (s : St) → FreeM P (Out s)}
    {Obs : St → Type w} {step : (s : St) → Obs s → St}

/-- Flatten a telescope into a single `FreeM` tree by iterated dependent
append, using `appendRound` to graft each observed round and `finish` at
terminal states. -/
def toFreeM {β : Type t}
    (appendRound : (s : St) → (Obs s → FreeM P β) → FreeM P β)
    (finish : St → FreeM P β) :
    {s : St} → TelescopeWith round Obs step s → FreeM P β
  | _, .done s => finish s
  | _, .extend s cont => appendRound s fun obs => (cont obs).toFreeM appendRound finish

@[simp]
theorem toFreeM_done {β : Type t}
    (appendRound : (s : St) → (Obs s → FreeM P β) → FreeM P β)
    (finish : St → FreeM P β) (s : St) :
    (TelescopeWith.done (round := round) (Obs := Obs) (step := step) s).toFreeM
      appendRound finish =
      finish s := rfl

@[simp]
theorem toFreeM_extend {β : Type t}
    (appendRound : (s : St) → (Obs s → FreeM P β) → FreeM P β)
    (finish : St → FreeM P β) (s : St)
    (cont : (obs : Obs s) → TelescopeWith round Obs step (step s obs)) :
    (TelescopeWith.extend s cont).toFreeM appendRound finish =
      appendRound s (fun obs => (cont obs).toFreeM appendRound finish) := rfl

end TelescopeWith

/-- State-machine telescopes whose observations are canonical `FreeM` branch
paths. This is the default specialization of `TelescopeWith`; users with a
more compact observation type should use `TelescopeWith` directly. -/
abbrev Telescope {St : Type z} {Out : St → Type v}
    (round : (s : St) → FreeM P (Out s))
    (step : (s : St) → Path (round s) → St) : St → Type (max uB z) :=
  TelescopeWith round (fun s => Path (round s)) step

namespace Telescope

variable {St : Type z} {Out : St → Type v} {round : (s : St) → FreeM P (Out s)}
    {step : (s : St) → Path (round s) → St}

/-- Constructor wrapper for terminating a canonical-path telescope. -/
abbrev done (s : St) : Telescope round step s :=
  TelescopeWith.done s

/-- Constructor wrapper for extending a canonical-path telescope. -/
abbrev extend (s : St)
    (cont : (path : Path (round s)) → Telescope round step (step s path)) :
    Telescope round step s :=
  TelescopeWith.extend s cont

/-- Flatten a canonical-path telescope into a single `FreeM` tree by iterated
dependent append, using `finish` at terminal states. -/
def toFreeM {β : Type t} (finish : St → FreeM P β) :
    {s : St} → Telescope round step s → FreeM P β :=
  TelescopeWith.toFreeM (fun s => append (round s)) finish

@[simp]
theorem toFreeM_done {β : Type t} (finish : St → FreeM P β) (s : St) :
    (Telescope.done (round := round) (step := step) s).toFreeM finish =
      finish s := rfl

@[simp]
theorem toFreeM_extend {β : Type t} (finish : St → FreeM P β) (s : St)
    (cont : (path : Path (round s)) → Telescope round step (step s path)) :
    (Telescope.extend s cont).toFreeM finish =
      append (round s) (fun path => (cont path).toFreeM finish) := rfl

end Telescope


end FreeM
end PFunctor
