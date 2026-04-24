/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.ITree.Construct

/-! # Bisimulation for Interaction Trees

This module defines the two equivalences on `ITree F α` used throughout the
algebraic theory:

* `ITree.Bisim t s` — *strong* (a.k.a. structural) bisimulation. Two ITrees
  are strongly bisimilar iff their one-step shapes match and the
  continuations are pointwise bisimilar. By the universal property of
  `PFunctor.M`, strong bisimulation coincides with definitional equality;
  for that reason we set `Bisim = (· = ·)`.

* `ITree.WeakBisim t s` — *weak* bisimulation (Coq `eutt`). Two ITrees are
  weakly bisimilar iff they reach matching one-step shapes after stripping
  any number of leading `step` (silent τ) nodes from either side. This
  collapses the `step`-equivalence class and is the *intended* notion of
  ITree equivalence for reasoning about programs.

The `WeakBisimF` Shape-level functor packaged here exposes the one-step
"bisimulation up to step" relation underlying `WeakBisim`. Definitions of the
algebraic laws (reflexivity, symmetry, transitivity, and the bind/iter
unfoldings) live in the sibling files
`ToMathlib.ITree.Bisim.Equiv` and `ToMathlib.ITree.Bisim.Bind`.

## Implementation notes

Lean 4.29 supports `coinductive` *predicates* via the `coinductive` keyword,
producing the greatest fixpoint of a monotone Prop-valued functor. We use
that for `WeakBisim`. For `Bisim`, the situation is degenerate: `M.bisim`
already proves that any one-step bisimulation between two `M`-values
implies definitional equality, so we expose `Bisim` as `=` plus a
convenience destructor `Bisim.dest` matching the Coq presentation.

The algebraic laws are scaffolded with `sorry` and will be filled in as
the project's bisimulation tooling matures. The intent is that *clients*
can write program-logic proofs against the API now; the proofs will be
discharged later.
-/

@[expose] public section

universe u

namespace ITree

variable {F : PFunctor.{u, u}} {α : Type u}

/-! ### Strong bisimulation -/

/-- Strong bisimulation on interaction trees. Two ITrees are strongly
bisimilar iff they are equal as elements of the M-type `PFunctor.M (Poly F α)`,
which by `PFunctor.M.bisim` is the same as having matching one-step shapes
with pointwise-bisimilar continuations. -/
@[reducible]
def Bisim (t s : ITree F α) : Prop := t = s

@[inherit_doc] scoped infix:50 " ≅ " => ITree.Bisim

namespace Bisim

variable {t s u : ITree F α}

@[refl] theorem refl' (t : ITree F α) : t ≅ t := rfl

@[symm] theorem symm' (h : t ≅ s) : s ≅ t := Eq.symm h

@[trans] theorem trans' (h₁ : t ≅ s) (h₂ : s ≅ u) : t ≅ u := Eq.trans h₁ h₂

/-- One-step characterisation: two ITrees are strongly bisimilar iff their
`shape'` agrees on the head shape and on each child up to bisimilarity.

This is the explicit destructor matching the Coq `eqit`/`bisim` constructor
shape; it is provable by `PFunctor.M.bisim`. -/
theorem dest (h : t ≅ s) : shape' t = shape' s := by
  cases h; rfl

end Bisim

/-! ### Weak bisimulation -/

/-- Weak bisimulation (a.k.a. equivalence up to taus, Coq `eutt`). Two ITrees
are weakly bisimilar iff after stripping leading `step` nodes from each side
their one-step shapes agree and continuations are pointwise weakly bisimilar.

This is the intended notion of equivalence for ITrees: it identifies all
silent-step-padded variants of the same observable program. -/
coinductive WeakBisim {F : PFunctor.{u, u}} {α : Type u} :
    ITree F α → ITree F α → Prop where
  /-- Both heads are pure leaves carrying the same value. -/
  | pure (t s : ITree F α) (r : α)
      (ht : shape' t = ⟨.pure r, PEmpty.elim⟩)
      (hs : shape' s = ⟨.pure r, PEmpty.elim⟩) :
      WeakBisim t s
  /-- Both heads are visible queries on the same event with pointwise
  weakly-bisimilar continuations. -/
  | query (t s : ITree F α) (a : F.A) (c c' : F.B a → ITree F α)
      (ht : shape' t = ⟨.query a, c⟩) (hs : shape' s = ⟨.query a, c'⟩)
      (h : ∀ b, WeakBisim (c b) (c' b)) :
      WeakBisim t s
  /-- Strip a `step` from the left. -/
  | tauL (t s t' : ITree F α) (ht : shape' t = ⟨.step, fun _ => t'⟩)
      (h : WeakBisim t' s) : WeakBisim t s
  /-- Strip a `step` from the right. -/
  | tauR (t s s' : ITree F α) (hs : shape' s = ⟨.step, fun _ => s'⟩)
      (h : WeakBisim t s') : WeakBisim t s

@[inherit_doc] scoped infix:50 " ≈ " => ITree.WeakBisim

/-- One-step "bisimulation up to silent steps" functor on shapes. Given a
relation `R` on `ITree F α`, `WeakBisimF R sh sh'` says that the
shapes `sh, sh' : (Poly F α).Obj (ITree F α)` agree on a non-`step` constructor
and the corresponding continuations are pointwise in `R`.

This Shape-level functor is used by `ToMathlib.ITree.Bisim.Equiv` to phrase
the `WeakBisim` "destructor" lemma after silent-step stripping. -/
inductive WeakBisimF (R : ITree F α → ITree F α → Prop) :
    (Poly F α).Obj (ITree F α) → (Poly F α).Obj (ITree F α) → Prop where
  /-- Pure leaves agree. -/
  | pure (r : α) (h h' : (Poly F α).B (.pure r) → ITree F α) :
      WeakBisimF R ⟨.pure r, h⟩ ⟨.pure r, h'⟩
  /-- Visible queries agree on the event name and pointwise on continuations. -/
  | query (a : F.A) (c c' : F.B a → ITree F α) (hcc : ∀ b, R (c b) (c' b)) :
      WeakBisimF R ⟨.query a, c⟩ ⟨.query a, c'⟩

end ITree
