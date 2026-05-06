/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.PFunctor.Free.Basic

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

/-- The canonical root-to-leaf path through a `FreeM` tree. -/
def Path {α : Type v} : FreeM P α → Type uB
  | .pure _ => PUnit
  | .roll a rest => (b : P.B a) × Path (rest b)

/-! ## Runtime paths along a lens -/

/-- Runtime path through a `P`-tree executed along a lens `l : Lens P Q`.

This is definitionally the canonical path through the lens-mapped runtime tree
`s.mapLens l`. The source tree's control flow is still governed by `P`, while
the mapped tree exposes each node through `Q`; a runtime direction
`d : Q.B (l.toFunA a)` selects the source branch `l.toFunB a d`. -/
abbrev PathAlong (l : Lens P Q) (s : FreeM P α) : Type uB₂ :=
  Path (s.mapLens l)

/-- The leaf payload selected by a path. Although the path itself records only
branch choices, the tree and path together determine the terminal `pure`
payload. -/
def output : (s : FreeM P α) → Path s → α
  | .pure x, _ => x
  | .roll _ rest, ⟨b, path⟩ => output (rest b) path

/-- The leaf payload selected by a runtime path along a lens. -/
def outputAlong (l : Lens P Q) (s : FreeM P α) (path : PathAlong l s) : α :=
  output (s.mapLens l) path

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

/-- Project a concrete runtime path along a lens back to the abstract
canonical branch path of the control tree. -/
def projectPathAlong (l : Lens P Q) :
    (s : FreeM P α) → PathAlong l s → Path s
  | .pure _, _ => ⟨⟩
  | .roll a rest, ⟨d, path⟩ =>
      ⟨l.toFunB a d, projectPathAlong l (rest (l.toFunB a d)) path⟩

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

Since `PathAlong l s` is definitionally `Path (s.mapLens l)`, this map is the
identity. It remains named so downstream code can state intent explicitly.
-/
def pathAlongToMapLensPath (l : Lens P Q)
    (s : FreeM P α) (path : PathAlong l s) : Path (s.mapLens l) :=
  path

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

Since `PathAlong l s` is definitionally `Path (s.mapLens l)`, this map is the
identity. It remains named so downstream code can state intent explicitly.
-/
def mapLensPathToPathAlong (l : Lens P Q)
    (s : FreeM P α) (path : Path (s.mapLens l)) : PathAlong l s :=
  path

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
  | _, _ => rfl

@[simp]
theorem pathAlongToMapLensPath_toPathAlong (l : Lens P Q) :
    (s : FreeM P α) → (path : Path (s.mapLens l)) →
      pathAlongToMapLensPath l s (mapLensPathToPathAlong l s path) = path
  | _, _ => rfl

@[simp]
theorem output_mapLens_pathAlongToMapLensPath (l : Lens P Q) :
    (s : FreeM P α) → (path : PathAlong l s) →
      output (s.mapLens l) (pathAlongToMapLensPath l s path) =
        outputAlong l s path
  | _, _ => rfl

@[simp]
theorem outputAlong_mapLensPathToPathAlong (l : Lens P Q) :
    (s : FreeM P α) → (path : Path (s.mapLens l)) →
      outputAlong l s (mapLensPathToPathAlong l s path) =
        output (s.mapLens l) path
  | _, _ => rfl

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
