/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Composition

/-!
# HeapSSP Examples

This file contains small heap-package examples. A counter package and a log
package are composed in parallel, producing a composite heap indexed by the
disjoint sum of their cell directories. -/

open OracleSpec OracleComp

/-! ## Interface specs

`OracleSpec ι := ι → Type v` is a function: it sends each query index
(possibly carrying input data in its constructor) to the response type. -/

namespace VCVio.HeapSSP.Example

/-- Counter operations: `incr` increments and returns nothing; `read`
returns the current count. -/
inductive CounterOp
  | incr
  | read

/-- Counter exports: `incr ↦ Unit`, `read ↦ Nat`. -/
@[reducible] def counterSpec : OracleSpec CounterOp
  | .incr => Unit
  | .read => Nat

/-- Log operations: `push x` pushes `x` and returns nothing; `top` returns
the most recent entry if any. The input to `push` is encoded in the
constructor, in the standard `OracleSpec` idiom. -/
inductive LogOp
  | push (x : Nat)
  | top

/-- Log exports: `push _ ↦ Unit`, `top ↦ Option Nat`. -/
@[reducible] def logSpec : OracleSpec LogOp
  | .push _ => Unit
  | .top    => Option Nat

/-! ## Packages -/

/-- Cell directory for the counter side: a single cell `count : Nat`. -/
inductive CounterCell
  | count
  deriving DecidableEq

instance : VCVio.HeapSSP.CellSpec CounterCell where
  type    | .count => Nat
  default | .count => 0

/-- Cell directory for the log side: a single cell `entries : List Nat`. -/
inductive LogCell
  | entries
  deriving DecidableEq

instance : VCVio.HeapSSP.CellSpec LogCell where
  type    | .entries => List Nat
  default | .entries => []

open VCVio.HeapSSP

/-- Counter package: state is `Heap CounterCell`. -/
def counterPkg : Package unifSpec counterSpec CounterCell where
  init := pure Heap.empty
  impl
    | .incr => StateT.mk fun (h : Heap CounterCell) =>
        pure ((), h.update .count (h .count + 1))
    | .read => StateT.mk fun (h : Heap CounterCell) =>
        pure (h .count, h)

/-- Log package: state is `Heap LogCell`. -/
def logPkg : Package unifSpec logSpec LogCell where
  init := pure Heap.empty
  impl
    | .push x => StateT.mk fun (h : Heap LogCell) =>
        pure ((), h.update .entries (x :: h .entries))
    | .top    => StateT.mk fun (h : Heap LogCell) =>
        pure ((h .entries).head?, h)

/-- Parallel composition: state is `Heap (CounterCell ⊕ LogCell)`.

The `Sum`-shaped identifier is the canonical disjoint union of the two cell
directories. To talk about the counter cell we use `Sum.inl .count`, and
`Heap.split CounterCell LogCell` projects the composite heap into the two
factor heaps. -/
def composed : Package (unifSpec + unifSpec) (counterSpec + logSpec)
    (CounterCell ⊕ LogCell) :=
  Package.par counterPkg logPkg

/-- The composite state has shape `Heap (CounterCell ⊕ LogCell)`. The
identifier set is the canonical disjoint sum of the two cell directories;
each cell carries its declared type from the appropriate `CellSpec`. -/
example : Package (unifSpec + unifSpec) (counterSpec + logSpec)
    (CounterCell ⊕ LogCell) := composed

/-- Per-cell access on the composite heap goes through the `Sum`-tagged
identifier. -/
example
    (h : Heap (CounterCell ⊕ LogCell)) (n : Nat) :
    (h.update (.inl .count) n) (.inl .count) = n := by
  simp [Heap.update]

/-- Per-cell **frame** : writing the counter cell does not perturb the log
cell. Holds definitionally via `Heap.get_update_of_ne` plus the standard
discriminator for `Sum`. -/
example
    (h : Heap (CounterCell ⊕ LogCell)) (n : Nat) :
    (h.update (.inl .count) n) (.inr .entries) = h (.inr .entries) :=
  Heap.get_update_of_ne (by decide) _

/-- The composite heap *splits* canonically into the two factor heaps via
`Heap.split`. The splitter is an `Equiv`, so it provides both directions and
`simp` lemmas for reshaping composed heaps. -/
example
    (h : Heap (CounterCell ⊕ LogCell)) (n : Nat) :
    (Heap.split CounterCell LogCell (h.update (.inl .count) n)).1 .count = n := by
  simp [Heap.update]

end VCVio.HeapSSP.Example
