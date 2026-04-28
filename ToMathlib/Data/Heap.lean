/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Logic.Equiv.Sum

/-!
# Typed heaps over identifier sets

`Heap Ident` (with `[CellSpec Ident]`) is a dependent function
`(i : Ident) → CellSpec.type i`. It models package state as a collection of
named, typed cells indexed by an identifier set `Ident`.

Composition uses disjoint sums of identifier sets. A heap over `α ⊕ β` splits
canonically into a heap over `α` and a heap over `β`, and cell framing follows
from ordinary function update: reading cell `j` after writing cell `i ≠ j`
returns the old value.

## Usage

```
inductive MyCells
  | counter
  | flag
  deriving DecidableEq

instance : CellSpec MyCells where
  type    | .counter => Nat | .flag => Bool
  default | .counter => 0   | .flag => false

def initial : Heap MyCells := Heap.empty
def stepped : Heap MyCells := initial.update .counter 5
example : stepped.get .counter = 5 := by simp [stepped]
example : stepped.get .flag    = false := by simp [stepped]
```

Stateful handlers can use this layer as a typed cell-keyed state convention:
`Heap Ident` stores one value of the cell-specific type at every identifier. -/

universe u v

/-! ## `CellSpec` : a typed cell directory

A `CellSpec Ident` says: each identifier `i : Ident` carries a value type
`CellSpec.type i : Type v`, with a designated `CellSpec.default i`. The
default is what the heap holds before any cell is written.

`Ident` lives in `Type u`, value types in `Type v`; both universes are
independent. Sum composition (`Sum.instCellSpec` below) requires both
operands' universes to match. -/
class CellSpec (Ident : Type u) where
  /-- Value type carried by the cell at identifier `i`. -/
  type : Ident → Type v
  /-- Default value of the cell at identifier `i`, used to initialize a fresh
  heap (`Heap.empty`). -/
  default : (i : Ident) → type i

-- Mark the projections reducible so that the cell-type and cell-default
-- projections unfold during typeclass synthesis, elaboration, and `simp`.
-- Without this, an expression like `Heap.update h .counter 5` would fail
-- to elaborate because Lean could not see that `CellSpec.type .counter`
-- reduces to `Nat`; and `simp` could not reduce `Heap.empty.get .counter`
-- to the user-supplied default.
attribute [reducible] CellSpec.type CellSpec.default

/-! ## `Heap` : the dependent-function heap

`Heap Ident` is the type of states: one cell-value per identifier. Lives in
`Type max u v`. -/
abbrev Heap (Ident : Type u) [CellSpec.{u, v} Ident] : Type max u v :=
  (i : Ident) → CellSpec.type i

namespace Heap

variable {Ident : Type u} [CellSpec.{u, v} Ident]

/-- The default heap: every cell holds its `CellSpec`-prescribed default. -/
def empty : Heap Ident := fun i => CellSpec.default i

instance : Inhabited (Heap Ident) where
  default := empty

/-- Read the cell at identifier `i`. -/
@[reducible]
def get (h : Heap Ident) (i : Ident) : CellSpec.type i := h i

/-- Write `v : CellSpec.type i` to cell `i`, leaving all other cells
unchanged. -/
def update [DecidableEq Ident] (h : Heap Ident) (i : Ident) (v : CellSpec.type i) :
    Heap Ident := Function.update h i v

@[simp]
theorem get_empty (i : Ident) : (empty : Heap Ident).get i = CellSpec.default i :=
  rfl

@[simp]
theorem get_update_self [DecidableEq Ident] (h : Heap Ident) (i : Ident)
    (v : CellSpec.type i) : (h.update i v).get i = v :=
  Function.update_self ..

@[simp]
theorem get_update_of_ne [DecidableEq Ident] {h : Heap Ident} {i j : Ident}
    (hij : j ≠ i) (v : CellSpec.type i) : (h.update i v).get j = h.get j :=
  Function.update_of_ne hij ..

@[simp]
theorem update_eq_self [DecidableEq Ident] (h : Heap Ident) (i : Ident) :
    h.update i (h.get i) = h :=
  Function.update_eq_self ..

@[simp]
theorem update_idem [DecidableEq Ident] (h : Heap Ident) (i : Ident)
    (v w : CellSpec.type i) : (h.update i v).update i w = h.update i w :=
  Function.update_idem ..

end Heap

/-! ## `Sum` of identifier sets : `CellSpec` instance

Composing two packages with identifier sets `α` and `β` yields one with
identifier set `α ⊕ β`. The cell directory is the disjoint union of the two,
defaults too. -/
instance Sum.instCellSpec {α β : Type u}
    [CellSpec.{u, v} α] [CellSpec.{u, v} β] : CellSpec.{u, v} (α ⊕ β) where
  type
    | .inl a => CellSpec.type a
    | .inr b => CellSpec.type b
  default
    | .inl a => CellSpec.default a
    | .inr b => CellSpec.default b

/-! ## `PEmpty` : `CellSpec` instance for the empty identifier set

The trivial heap `Heap PEmpty` has a unique inhabitant (the empty function).
It is useful whenever a typed-heap construction needs a stateless identifier
set. -/
instance PEmpty.instCellSpec : CellSpec.{u, v} PEmpty where
  type i := i.elim
  default i := i.elim

namespace Heap

/-! ## `Heap.split` : the canonical decomposition

`Heap (α ⊕ β) ≃ Heap α × Heap β`, the lynchpin of state-separating
composition in this layer. The forward direction restricts to `inl` / `inr`
cells; the inverse is `Sum.rec` on the identifier. Both directions reduce by
case-analysis on the identifier and are `rfl`-definitional after `cases`.
-/
def split (α β : Type u) [CellSpec.{u, v} α] [CellSpec.{u, v} β] :
    Heap (α ⊕ β) ≃ Heap α × Heap β where
  toFun h := (fun a => h (.inl a), fun b => h (.inr b))
  invFun p := fun i => match i with
    | .inl a => p.1 a
    | .inr b => p.2 b
  left_inv h := funext fun i => by cases i <;> rfl
  right_inv := fun ⟨_, _⟩ => rfl

@[simp]
theorem split_apply_inl {α β : Type u} [CellSpec.{u, v} α] [CellSpec.{u, v} β]
    (h : Heap (α ⊕ β)) (a : α) : (split α β h).1 a = h (.inl a) := rfl

@[simp]
theorem split_apply_inr {α β : Type u} [CellSpec.{u, v} α] [CellSpec.{u, v} β]
    (h : Heap (α ⊕ β)) (b : β) : (split α β h).2 b = h (.inr b) := rfl

@[simp]
theorem split_symm_apply_inl {α β : Type u} [CellSpec.{u, v} α] [CellSpec.{u, v} β]
    (p : Heap α × Heap β) (a : α) : (split α β).symm p (.inl a) = p.1 a := rfl

@[simp]
theorem split_symm_apply_inr {α β : Type u} [CellSpec.{u, v} α] [CellSpec.{u, v} β]
    (p : Heap α × Heap β) (b : β) : (split α β).symm p (.inr b) = p.2 b := rfl

@[simp]
theorem split_empty (α β : Type u) [CellSpec.{u, v} α] [CellSpec.{u, v} β] :
    split α β (empty : Heap (α ⊕ β)) = (empty, empty) := by
  ext i <;> rfl

/-- Splitting after an update on the left identifier set updates only the
left split component. -/
@[simp]
theorem split_update_inl {α β : Type u}
    [CellSpec.{u, v} α] [CellSpec.{u, v} β] [DecidableEq α] [DecidableEq β]
    (h : Heap (α ⊕ β)) (a : α) (v : CellSpec.type a) :
    split α β (h.update (.inl a) v) =
      ((split α β h).1.update a v, (split α β h).2) := by
  apply Prod.ext
  · funext i
    by_cases hi : i = a
    · subst hi
      simp [split, Heap.update]
    · simp [split, Heap.update, hi]
  · funext i
    simp [split, Heap.update]

/-- Splitting after an update on the right identifier set updates only the
right split component. -/
@[simp]
theorem split_update_inr {α β : Type u}
    [CellSpec.{u, v} α] [CellSpec.{u, v} β] [DecidableEq α] [DecidableEq β]
    (h : Heap (α ⊕ β)) (b : β) (v : CellSpec.type b) :
    split α β (h.update (.inr b) v) =
      ((split α β h).1, (split α β h).2.update b v) := by
  apply Prod.ext
  · funext i
    simp [split, Heap.update]
  · funext i
    by_cases hi : i = b
    · subst hi
      simp [split, Heap.update]
    · simp [split, Heap.update, hi]

/-- Rebuilding a split heap after updating the left component is the same as
updating the composite heap at the corresponding `Sum.inl` cell. -/
@[simp]
theorem split_symm_update_inl {α β : Type u}
    [CellSpec.{u, v} α] [CellSpec.{u, v} β] [DecidableEq α] [DecidableEq β]
    (p : Heap α × Heap β) (a : α) (v : CellSpec.type a) :
    (split α β).symm (p.1.update a v, p.2) =
      ((split α β).symm p).update (.inl a) v := by
  funext i
  cases i with
  | inl a' =>
      by_cases ha' : a' = a
      · subst ha'
        simp [split, Heap.update]
      · simp [split, Heap.update, ha']
  | inr b =>
      simp [split, Heap.update]

/-- Rebuilding a split heap after updating the right component is the same as
updating the composite heap at the corresponding `Sum.inr` cell. -/
@[simp]
theorem split_symm_update_inr {α β : Type u}
    [CellSpec.{u, v} α] [CellSpec.{u, v} β] [DecidableEq α] [DecidableEq β]
    (p : Heap α × Heap β) (b : β) (v : CellSpec.type b) :
    (split α β).symm (p.1, p.2.update b v) =
      ((split α β).symm p).update (.inr b) v := by
  funext i
  cases i with
  | inl a =>
      simp [split, Heap.update]
  | inr b' =>
      by_cases hb' : b' = b
      · subst hb'
        simp [split, Heap.update]
      · simp [split, Heap.update, hb']

end Heap

/-! ## Sanity check: a two-cell heap

A small example demonstrating cell access, frame, and the canonical
`Sum`-split. If you're reading this to learn the API, this is the right
starting point. -/

namespace HeapExample

inductive Id
  | counter
  | flag
  deriving DecidableEq

instance : CellSpec Id where
  type
    | .counter => Nat
    | .flag    => Bool
  default
    | .counter => 0
    | .flag    => false

example : (Heap.empty : Heap Id).get .counter = 0 := rfl

example : ((Heap.empty : Heap Id).update .counter 5).get .counter = 5 := by
  simp

example : ((Heap.empty : Heap Id).update .counter 5).get .flag = false := by
  rw [Heap.get_update_of_ne (by decide : (Id.flag : Id) ≠ .counter)]
  rfl

example : (Heap.split Id Id (Heap.empty : Heap (Id ⊕ Id))).1.get .counter = 0 :=
  rfl

example :
    let h0 : Heap Id := Heap.empty
    let h1 : Heap Id := h0.update .counter 7
    (Heap.split Id Id).symm (h1, h0) (.inl .counter) = 7 := by
  simp

example :
    let h0 : Heap Id := Heap.empty
    let h1 : Heap Id := h0.update .counter 7
    (Heap.split Id Id).symm (h1, h0) (.inr .counter) = 0 := by
  simp

end HeapExample
