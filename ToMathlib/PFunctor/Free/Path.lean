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

* `FreeM.PathView` describes how to present one observed node step.
* `FreeM.PathWith view s` records a complete root-to-leaf branch through `s`
  using that presentation.
* `FreeM.Path s` is the canonical path view, recording an explicit polynomial
  direction at every node.
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

/-- Presentation of one observed path step at a `FreeM` node.

For a node `roll a rest`, a recursive path algebra first supplies a family
`K : P.B a → Type w` of path tails for each child. A `PathView` chooses a
presentation of the one-step path data over that family. The `pack` and
`unpack` maps connect that presentation to the canonical sigma view. -/
structure PathView (P : PFunctor.{uA, uB}) where
  Step : (a : P.A) → (P.B a → Type w) → Type w
  pack : {a : P.A} → {K : P.B a → Type w} → ((b : P.B a) × K b) → Step a K
  unpack : {a : P.A} → {K : P.B a → Type w} → Step a K → (b : P.B a) × K b

namespace PathView

/-- The canonical path view records the chosen polynomial direction together
with the recursive path tail. -/
def canonical (P : PFunctor.{uA, uB}) : PathView.{uB} P where
  Step _ K := (b : _) × K b
  pack x := x
  unpack x := x

end PathView

/-- A complete branch through a `FreeM` tree, presented through a chosen
`PathView`. For a terminal `pure` leaf the path is trivial; for a `roll` node,
the path is one observed step whose tails are recursive paths through the
children. -/
def PathWith (view : PathView.{w} P) {α : Type v} : FreeM P α → Type w
  | .pure _ => PUnit
  | .roll a rest => view.Step a (fun b => PathWith view (rest b))

/-- The canonical root-to-leaf path through a `FreeM` tree. This records an
explicit polynomial direction at every `roll` node. -/
abbrev Path {α : Type v} (s : FreeM P α) : Type uB :=
  PathWith (PathView.canonical P) s

/-- The leaf payload selected by a path. Although the path itself records only
branch choices, the tree and path together determine the terminal `pure`
payload. -/
def outputWith (view : PathView.{w} P) : (s : FreeM P α) → PathWith view s → α
  | .pure x, _ => x
  | .roll _ rest, path =>
      let ⟨b, tail⟩ := view.unpack path
      outputWith view (rest b) tail

/-- The leaf payload selected by a canonical path. -/
def output : (s : FreeM P α) → Path s → α :=
  outputWith (PathView.canonical P)

@[simp]
theorem output_pure (x : α) (path : Path (FreeM.pure (P := P) x)) :
    output (FreeM.pure x) path = x := rfl

@[simp]
theorem output_roll (a : P.A) (rest : P.B a → FreeM P α)
    (b : P.B a) (path : Path (rest b)) :
    output (FreeM.roll a rest) ⟨b, path⟩ = output (rest b) path := rfl

/-! ## Runtime paths along a lens -/

variable {Q : PFunctor.{uA₂, uB₂}}

/-- Runtime path through a `P`-tree executed along a lens `l : Lens P Q`.

The tree's control flow is still governed by `P`, but each node is exposed
through the concrete/runtime polynomial `Q`: at control position `a`, runtime
chooses a direction of `Q.B (l.toFunA a)`, which the lens maps back to the
abstract control branch `P.B a`.

This is defined directly by recursion on the control tree, rather than as
`Path (s.mapLens l)`, so the constructor equations are the definitional core
used by interaction semantics. -/
def PathAlong (l : Lens P Q) : FreeM P α → Type uB₂
  | .pure _ => PUnit
  | .roll a rest => (d : Q.B (l.toFunA a)) × PathAlong l (rest (l.toFunB a d))

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

/-- Dependent sequential composition for `FreeM` trees using an arbitrary path
view. Run `s₁`, then continue with a suffix selected by the observed path of
`s₁`; the suffix may change the leaf payload from `α` to `β`.

The payload produced by `s₁` is still available to the suffix as
`FreeM.outputWith view s₁ path`, since it is determined by the tree and path. -/
def appendWith (view : PathView.{w} P) {β : Type t} :
    (s₁ : FreeM P α) →
    (PathWith view s₁ → FreeM P β) →
    FreeM P β
  | .pure _, s₂ => s₂ ⟨⟩
  | .roll a rest, s₂ =>
      .roll a fun b => appendWith view (rest b) (fun path => s₂ (view.pack ⟨b, path⟩))

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
