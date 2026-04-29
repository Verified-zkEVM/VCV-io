/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import ToMathlib.PFunctor.Lens.Basic

/-!
# Lawful State Lenses

This file specializes polynomial-functor lenses to **state lenses**. In Poly,
following Spivak and Niu's *Polynomial Functors: A Mathematical Theory of
Interaction*, a dependent lens `p → q` is a natural transformation between
polynomial functors, represented by a forward map on positions and a backward
map on directions. For the self-monomial polynomial `PFunctor.selfMonomial σ`,
both positions and directions are states of type `σ`. Thus a lens
`selfMonomial σ → selfMonomial τ` has exactly the shape of a classical state
lens:

* `get : σ → τ`, reading a view/component state;
* `put : τ → σ → σ`, writing an updated view/component back into the source.

The law classes below use the standard bidirectional-programming names from
Foster, Greenwald, Moore, Pierce, and Schmitt's lens work: `PutGet`, `GetPut`,
and the stronger `PutPut` law, often called *very well-behavedness*. We keep
these laws on `selfMonomial` lenses rather than on arbitrary polynomial lenses:
for a general `PFunctor.Lens p q`, the backward map returns a direction of `p`,
not a new position of `p`, so the usual get/put round-trip equations are not
well-typed without this state-polynomial specialization.

The binary relation `IsSeparated` captures the non-interference condition for
two lenses with the same source. This is the condition used by Pacheco and
Cunha's point-free lens calculus to justify splitting a source into two
independently updatable views: updating the left and right views should not
change the other view, and the two updates should commute. It is also the
state-lens analogue of the separation-logic intuition behind separation lenses:
two views describe spatially separated portions of a state.

References:

* David I. Spivak and Nelson Niu, *Polynomial Functors: A Mathematical Theory
  of Interaction*, Cambridge University Press, 2025.
* J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore, Benjamin C. Pierce,
  and Alan Schmitt, *Combinators for Bidirectional Tree Transformations: A
  Linguistic Approach to the View-Update Problem*, POPL 2005.
* Hugo Pacheco and Alcino Cunha, *Generic Point-free Lenses*, MPC 2010.
-/

@[expose] public section

universe u

namespace PFunctor

namespace Lens

/-- A state lens from source state `σ` to view state `τ`.

This is not a new kind of optic. It is the existing polynomial-functor lens
between the self-monomial polynomials `selfMonomial σ` and `selfMonomial τ`.
Its position map is the state `get`, and its direction map is the state `put`.
-/
abbrev State (σ τ : Type u) : Type u :=
  Lens (selfMonomial σ) (selfMonomial τ)

namespace State

variable {σ τ υ σ₁ σ₂ : Type u}

/-! ## Basic operations -/

/-- Construct a state lens from a getter and a putter. -/
def mk (get : σ → τ) (put : τ → σ → σ) : State σ τ :=
  get ⇆ fun s t => put t s

/-- Read the view/component state selected by a state lens. -/
def get (L : State σ τ) : σ → τ :=
  L.toFunA

/-- Write an updated view/component state back into the source state.

The argument order follows the usual bidirectional-programming convention:
`L.put t s` updates source `s` with new view `t`.
-/
def put (L : State σ τ) (t : τ) (s : σ) : σ :=
  L.toFunB s t

@[simp]
theorem mk_get (get : σ → τ) (put : τ → σ → σ) :
    (mk get put).get = get :=
  rfl

@[simp]
theorem mk_put (get : σ → τ) (put : τ → σ → σ) (t : τ) (s : σ) :
    (mk get put).put t s = put t s :=
  rfl

/-- The identity state lens. -/
protected def id (σ : Type u) : State σ σ :=
  Lens.id (selfMonomial σ)

@[simp]
theorem id_get (s : σ) :
    (State.id σ).get s = s :=
  rfl

@[simp]
theorem id_put (t s : σ) :
    (State.id σ).put t s = t :=
  rfl

/-- Compose state lenses. -/
def comp (L₂ : State τ υ) (L₁ : State σ τ) : State σ υ :=
  L₂ ∘ₗ L₁

@[inherit_doc] scoped infixl:75 " ∘ₛ " => comp

@[simp]
theorem comp_get (L₂ : State τ υ) (L₁ : State σ τ) (s : σ) :
    (L₂.comp L₁).get s = L₂.get (L₁.get s) :=
  rfl

@[simp]
theorem comp_put (L₂ : State τ υ) (L₁ : State σ τ) (u : υ) (s : σ) :
    (L₂.comp L₁).put u s = L₁.put (L₂.put u (L₁.get s)) s :=
  rfl

/-- The first projection state lens from a product state. -/
def fst (σ τ : Type u) : State (σ × τ) σ :=
  mk Prod.fst fun x s => (x, s.2)

/-- The second projection state lens from a product state. -/
def snd (σ τ : Type u) : State (σ × τ) τ :=
  mk Prod.snd fun x s => (s.1, x)

@[simp]
theorem fst_get (s : σ × τ) :
    (fst σ τ).get s = s.1 :=
  rfl

@[simp]
theorem fst_put (x : σ) (s : σ × τ) :
    (fst σ τ).put x s = (x, s.2) :=
  rfl

@[simp]
theorem snd_get (s : σ × τ) :
    (snd σ τ).get s = s.2 :=
  rfl

@[simp]
theorem snd_put (x : τ) (s : σ × τ) :
    (snd σ τ).put x s = (s.1, x) :=
  rfl

/-! ## Lens laws -/

/-- The `PutGet` law for a state lens.

In the bidirectional-programming literature this is the consistency law:
after writing an updated view `t` into a source `s`, reading the view back
returns exactly `t`.
-/
class IsPutGet (L : State σ τ) : Prop where
  /-- Reading immediately after writing returns the written view. -/
  get_put : ∀ s t, L.get (L.put t s) = t

/-- The `GetPut` law for a state lens.

In the bidirectional-programming literature this is the stability law:
writing back the view already present in a source leaves the source unchanged.
-/
class IsGetPut (L : State σ τ) : Prop where
  /-- Writing the current view back into the source is a no-op. -/
  put_get : ∀ s, L.put (L.get s) s = s

/-- The `PutPut` law for a state lens.

This is the constant-complement law used in the classical view-update
literature: two consecutive writes are observationally the same as the second
write alone. Lenses satisfying `PutGet`, `GetPut`, and `PutPut` are commonly
called *very well-behaved*.
-/
class IsPutPut (L : State σ τ) : Prop where
  /-- Consecutive writes collapse to the last write. -/
  put_put : ∀ s t₁ t₂, L.put t₂ (L.put t₁ s) = L.put t₂ s

/-- A well-behaved state lens.

This bundles the two basic round-trip laws, `PutGet` and `GetPut`, following
the standard terminology for asymmetric lenses in bidirectional programming.
-/
class IsWellBehaved (L : State σ τ) : Prop extends IsPutGet L, IsGetPut L

/-- A very well-behaved state lens.

This extends well-behavedness with `PutPut`, the law saying that repeated
updates keep a constant complement and collapse to the last update.
-/
class IsVeryWellBehaved (L : State σ τ) : Prop
    extends IsWellBehaved L, IsPutPut L

export IsPutGet (get_put)
export IsGetPut (put_get)
export IsPutPut (put_put)

instance id_isVeryWellBehaved : IsVeryWellBehaved (State.id σ) where
  get_put := by intro _ _; rfl
  put_get := by intro _; rfl
  put_put := by intro _ _ _; rfl

instance fst_isVeryWellBehaved : IsVeryWellBehaved (fst σ τ) where
  get_put := by intro _ _; rfl
  put_get := by intro _; rfl
  put_put := by intro _ _ _; rfl

instance snd_isVeryWellBehaved : IsVeryWellBehaved (snd σ τ) where
  get_put := by intro _ _; rfl
  put_get := by intro _; rfl
  put_put := by intro _ _ _; rfl

instance comp_isPutGet (L₂ : State τ υ) (L₁ : State σ τ)
    [IsPutGet L₂] [IsPutGet L₁] :
    IsPutGet (L₂.comp L₁) where
  get_put := by
    intro s u
    simp only [comp_get, comp_put]
    rw [get_put, get_put]

instance comp_isGetPut (L₂ : State τ υ) (L₁ : State σ τ)
    [IsGetPut L₂] [IsGetPut L₁] :
    IsGetPut (L₂.comp L₁) where
  put_get := by
    intro s
    simp only [comp_get, comp_put]
    rw [put_get, put_get]

instance comp_isWellBehaved (L₂ : State τ υ) (L₁ : State σ τ)
    [IsWellBehaved L₂] [IsWellBehaved L₁] :
    IsWellBehaved (L₂.comp L₁) where

/-!
`PutPut` is intentionally not given as a generic composition instance here.
Very well-behaved asymmetric lenses are closed under the classical lens
composition operation, but the proof is more naturally developed alongside the
larger bidirectional-lens algebra if and when it is needed.
-/

/-! ## Separation / non-interference -/

/-- Non-interference for two well-behaved state lenses with a common source.

This relation says that the left and right lenses describe separated portions
of the same source state. Updating either view leaves the other view unchanged,
and left and right updates commute. Pacheco and Cunha use this commutation
condition to justify a split combinator for two lenses with a shared concrete
domain; in program-logical terminology, it is the lens-level analogue of two
spatially separated state views.
-/
class IsSeparated (L : State σ σ₁) (R : State σ σ₂) : Prop where
  /-- Updating the right view does not change the left view. -/
  left_get_put_right : ∀ s r, L.get (R.put r s) = L.get s
  /-- Updating the left view does not change the right view. -/
  right_get_put_left : ∀ s l, R.get (L.put l s) = R.get s
  /-- Left and right updates commute. -/
  put_comm : ∀ s l r, L.put l (R.put r s) = R.put r (L.put l s)

export IsSeparated (left_get_put_right right_get_put_left put_comm)

theorem IsSeparated.symm {L : State σ σ₁} {R : State σ σ₂}
    [h : IsSeparated L R] : IsSeparated R L where
  left_get_put_right := h.right_get_put_left
  right_get_put_left := h.left_get_put_right
  put_comm := by
    intro s r l
    exact (h.put_comm s l r).symm

instance fst_snd_isSeparated : IsSeparated (fst σ τ) (snd σ τ) where
  left_get_put_right := by intro _ _; rfl
  right_get_put_left := by intro _ _; rfl
  put_comm := by intro _ _ _; rfl

instance snd_fst_isSeparated : IsSeparated (snd σ τ) (fst σ τ) :=
  IsSeparated.symm

end State

end Lens

end PFunctor
