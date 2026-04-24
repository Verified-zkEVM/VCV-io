/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.PFunctor.MFacts
public import ToMathlib.Control.Monad.Iter

/-! # Interaction Trees

Interaction Trees (ITrees) are a coinductive datatype for representing
recursive and impure programs that interact with an environment through a
fixed set of events. We follow the construction of Xia, Zakowski, He, Hur,
Malecha, Pierce, and Zdancewic, *Interaction Trees: Representing Recursive
and Impure Programs in Coq* (POPL 2020), and adapt it to Lean 4 / Mathlib.

The Coq presentation defines

```coq
CoInductive itree (E : Type → Type) (R : Type) :=
| Ret (r : R) | Tau (t : itree E R) | Vis {X : Type} (e : E X) (k : X → itree E R).
```

In Lean we model the event signature as a *polynomial functor*
`F : PFunctor.{u, u}` (shapes are event names, positions are answer types) so
that the resulting tree lives at a single universe `u`. ITrees themselves are
the M-type (final coalgebra) of the one-step polynomial functor `Poly F α`
whose shapes are pure leaves, silent steps, or visible queries.

## Naming conventions

| Coq                | Lean                                    |
| ------------------ | --------------------------------------- |
| `itree E R`        | `ITree F α`                             |
| `itreeF E R T`     | `ITree.Shape F α`                       |
| `RetF` / `Ret`     | `ITree.Shape.pure` / `ITree.pure`       |
| `TauF` / `Tau`     | `ITree.Shape.step` / `ITree.step`       |
| `VisF` / `Vis`     | `ITree.Shape.query` / `ITree.query`     |
| `observe`          | `ITree.shape`                           |
| `ITree.bind`       | `ITree.bind` (also `>>=`)               |
| `ITree.iter`       | `ITree.iter`                            |
| `ITree.trigger e`  | `ITree.lift`                            |

## Main definitions

* `ITree.Shape F α` — one-step view of an ITree node.
* `ITree.Poly F α` — the polynomial functor whose M-type is `ITree F α`.
* `ITree F α` — interaction trees over events `F` with leaves of type `α`.
* `ITree.pure`, `ITree.step`, `ITree.query` — smart constructors.
* `ITree.shape` — one-step destructor, the analogue of Coq's `observe`.
* `ITree.bind` — monadic bind, defined via `PFunctor.M.corec`.
* `ITree.iter` — iteration combinator turning `β → ITree F (β ⊕ α)` into
  `β → ITree F α`, the canonical `MonadIter` operator.
* `ITree.lift` — lift a single event into an ITree: `lift a = query a pure`.
* `Monad (ITree F)`, `MonadIter (ITree F)` — instances built from `bind`,
  `pure`, and `iter`.

## Implementation notes

Lean 4's `coinductive` keyword (v4.25) only builds coinductive *predicates*;
there is no built-in coinductive `Type`. We therefore use `PFunctor.M`, which
is the standard Mathlib coinductive-type construction. The `partial_fixpoint`
machinery is *also* not a substitute, because it requires a `CCPO` on the
return type, which `M F` does not have. Corecursive functions producing
ITrees go through `PFunctor.M.corec`. All of this is empirically validated in
the project's `ITreePilot.lean` (no longer needed once this file is in place).
-/

@[expose] public section

universe u v

namespace ITree

/-! ### One-step polynomial functor -/

/-- One-step view of an ITree node: a pure leaf, a silent step, or a visible
query. Mirrors Coq's `itreeF` (`Core/ITreeDefinition.v`). -/
inductive Shape (F : PFunctor.{u, u}) (α : Type u) : Type u where
  /-- A leaf carrying a result of type `α`. (Coq `RetF`.) -/
  | pure (r : α) : Shape F α
  /-- A silent (`τ`) step. (Coq `TauF`.) -/
  | step : Shape F α
  /-- A visible event named by `a : F.A`; the continuation will be indexed by
  `F.B a`. (Coq `VisF`.) -/
  | query (a : F.A) : Shape F α

/-- One-step polynomial functor whose M-type is the type of ITrees over events
`F` returning a value of type `α`.

* `A := Shape F α`: which kind of node we are at.
* `B`: the position type encoding the *arity* of each kind of node.
  - `.pure r` has no children (`PEmpty`).
  - `.step` has exactly one child (`PUnit`).
  - `.query a` has children indexed by the answer type `F.B a`. -/
@[reducible]
def Poly (F : PFunctor.{u, u}) (α : Type u) : PFunctor.{u, u} where
  A := Shape F α
  B
    | .pure _r => PEmpty.{u + 1}
    | .step    => PUnit.{u + 1}
    | .query a => F.B a

end ITree

/-- Interaction trees over events `F : PFunctor.{u, u}` with leaves of type
`α : Type u`, defined as the final coalgebra (M-type) of `ITree.Poly F α`.

This is the Lean / Mathlib analogue of Coq's `itree E R`
(`InteractionTrees/theories/Core/ITreeDefinition.v`). -/
def ITree (F : PFunctor.{u, u}) (α : Type u) : Type u :=
  PFunctor.M (ITree.Poly F α)

namespace ITree

variable {F : PFunctor.{u, u}} {α β γ : Type u}

/-! ### Smart constructors -/

/-- Build the `.pure` ITree node carrying a result `r : α`. (Coq `Ret`.) -/
def pure (r : α) : ITree F α :=
  PFunctor.M.mk (F := Poly F α) ⟨.pure r, PEmpty.elim⟩

/-- Build the `.step` ITree node — a silent step in front of `t`. (Coq `Tau`.) -/
def step (t : ITree F α) : ITree F α :=
  PFunctor.M.mk (F := Poly F α) ⟨.step, fun _ => t⟩

/-- Build the `.query` ITree node — a visible event `a : F.A` together with a
continuation `k : F.B a → ITree F α`. (Coq `Vis`.) -/
def query (a : F.A) (k : F.B a → ITree F α) : ITree F α :=
  PFunctor.M.mk (F := Poly F α) ⟨.query a, k⟩

/-! ### One-step destructor (`observe`) -/

/-- One-step observation of an ITree as a `Shape F α` constructor packed with
its continuation. Concretely a synonym for `PFunctor.M.dest` instantiated at
`Poly F α`. (Coq `observe`.) -/
@[reducible]
def shape' (t : ITree F α) : (Poly F α).Obj (ITree F α) :=
  PFunctor.M.dest t

/-- One-step shape view of an ITree, dropping the continuation. The full data
remains accessible via `shape'`. -/
def shape (t : ITree F α) : Shape F α :=
  (shape' t).1

@[simp] theorem shape'_pure (r : α) :
    shape' (pure (F := F) r) = ⟨.pure r, PEmpty.elim⟩ :=
  PFunctor.M.dest_mk _

@[simp] theorem shape'_step (t : ITree F α) :
    shape' (step t) = ⟨.step, fun _ => t⟩ :=
  PFunctor.M.dest_mk _

@[simp] theorem shape'_query (a : F.A) (k : F.B a → ITree F α) :
    shape' (query a k) = ⟨.query a, k⟩ :=
  PFunctor.M.dest_mk _

@[simp] theorem shape_pure (r : α) :
    shape (pure (F := F) r) = .pure r := by
  unfold shape; rw [shape'_pure]

@[simp] theorem shape_step (t : ITree F α) :
    shape (step t) = .step := by
  unfold shape; rw [shape'_step]

@[simp] theorem shape_query (a : F.A) (k : F.B a → ITree F α) :
    shape (query a k) = .query a := by
  unfold shape; rw [shape'_query]

/-- Recover an ITree from its one-step shape together with the continuation
data. The composition `ofShape ∘ shape' = id` and `shape' ∘ ofShape = id`
hold definitionally (see `ofShape_shape'` and `shape'_ofShape`). -/
def ofShape (sh : (Poly F α).Obj (ITree F α)) : ITree F α :=
  PFunctor.M.mk sh

@[simp] theorem shape'_ofShape (sh : (Poly F α).Obj (ITree F α)) :
    shape' (ofShape sh) = sh := PFunctor.M.dest_mk sh

@[simp] theorem ofShape_shape' (t : ITree F α) :
    ofShape (shape' t) = t := PFunctor.M.mk_dest t

/-! ### Monadic bind via `M.corec`

The Coq `bind` (`Core/ITreeDefinition.v:157-168`) is a `cofix` over `subst`.
We translate it to `M.corec` by carrying a sum state: `Sum.inl t` means "we
are still consuming the original tree `t`", `Sum.inr u` means "we have spliced
in `k r` for some leaf `r` and are now propagating `u`'s structure". -/

/-- Step transformer used by `bind`: peel off one node from the current state
and emit the corresponding output node together with the next state. -/
def bindStep (k : α → ITree F β) :
    ITree F α ⊕ ITree F β → (Poly F β).Obj (ITree F α ⊕ ITree F β)
  | .inl t =>
      match PFunctor.M.dest t with
      | ⟨.pure r, _⟩ =>
          match PFunctor.M.dest (k r) with
          | ⟨s, c⟩ => ⟨s, fun b => .inr (c b)⟩
      | ⟨.step, c⟩ => ⟨.step, fun _ => .inl (c PUnit.unit)⟩
      | ⟨.query a, c⟩ => ⟨.query a, fun b => .inl (c b)⟩
  | .inr u =>
      match PFunctor.M.dest u with
      | ⟨s, c⟩ => ⟨s, fun b => .inr (c b)⟩

/-- Monadic bind on ITrees. `t.bind k` runs `t` until it reaches a `.pure r`
leaf and then continues with `k r`. (Coq `ITree.bind`.) -/
def bind (t : ITree F α) (k : α → ITree F β) : ITree F β :=
  PFunctor.M.corec (bindStep k) (.inl t)

/-! ### Iteration via `M.corec`

The Coq `iter` (`Core/ITreeDefinition.v:192-194`) is

```coq
CoFixpoint iter body i :=
  Tau (body i >>= fun rj => match rj with
                            | inl j => iter body j
                            | inr r => Ret r end).
```

Lean has no native guardedness checker, so the natural recursive form is
rejected by both `structural_recursion` and `partial_fixpoint`. We therefore
push the recursion into `M.corec` with state `ITree F (β ⊕ α)`: at each step
we peel off one node and convert leaves of the form `.pure (.inl j)` into a
silent step followed by a fresh `body j` call. -/

/-- Step transformer used by `iter`. -/
def iterStep (body : β → ITree F (β ⊕ α)) :
    ITree F (β ⊕ α) → (Poly F α).Obj (ITree F (β ⊕ α))
  | t =>
      match PFunctor.M.dest t with
      | ⟨.pure (.inl j), _⟩ => ⟨.step, fun _ => body j⟩
      | ⟨.pure (.inr r), _⟩ => ⟨.pure r, PEmpty.elim⟩
      | ⟨.step, c⟩ => ⟨.step, fun u => c u⟩
      | ⟨.query a, c⟩ => ⟨.query a, fun b => c b⟩

/-- Iteration combinator. `iter body init` repeatedly invokes
`body : β → ITree F (β ⊕ α)`; intermediate `Sum.inl j` results restart the
loop on `j`, intermediate `Sum.inr r` results terminate with `r`.

Each loop iteration is silent-step-guarded so the corecursive definition is
productive. (Coq `ITree.iter`.) -/
def iter (body : β → ITree F (β ⊕ α)) (init : β) : ITree F α :=
  PFunctor.M.corec (iterStep body) (body init)

/-! ### Lifting events -/

/-- Lift a single event `a : F.A` into an ITree, returning the answer
unchanged. (Coq `ITree.trigger`.) -/
def lift (a : F.A) : ITree F (F.B a) :=
  query a pure

/-! ### Monad and `MonadIter` instances -/

instance instMonad : Monad (ITree F) where
  pure := pure
  bind := bind

instance instMonadIter : MonadIter (ITree F) where
  iterM := iter

/-! ### Definitional unfoldings

These match Coq's `Core/ITreeDefinition.v:208-217` (`unfold_bind`,
`unfold_iter`) but as one-step `simp` lemmas on `shape'`. The full equational
theory (`bind_pure_left`, `bind_assoc`, `iter_unfold`, …) requires
bisimulation reasoning and lives in `ToMathlib.ITree.Bisim.*`. -/

@[simp] theorem shape'_bind (t : ITree F α) (k : α → ITree F β) :
    shape' (bind t k) =
      PFunctor.M.dest (PFunctor.M.corec (bindStep k) (.inl t)) := rfl

@[simp] theorem shape'_iter (body : β → ITree F (β ⊕ α)) (init : β) :
    shape' (iter body init) =
      PFunctor.M.dest (PFunctor.M.corec (iterStep body) (body init)) := rfl

@[simp] theorem shape_lift (a : F.A) :
    shape (lift (F := F) a) = .query a := by
  unfold lift; rw [shape_query]

end ITree
