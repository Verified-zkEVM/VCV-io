/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Composition
import VCVio.SSP.Composition

/-!
# HeapSSP vs SSP : a side-by-side comparison

This file defines the *same* small set of packages in both frameworks and
runs the same composition both ways. Reading the two halves side-by-side
makes the design difference concrete:

* `VCVio.SSP.Package` carries a free state type `σ : Type v`. Composition
  via `par` gives state `σ₁ × σ₂` — a structural product, no naming.
* `VCVio.HeapSSP.Package` carries a heap `Heap Ident` over an identifier
  set `Ident : Type` with a `[CellSpec Ident]` directory. Composition via
  `par` (or `link`) gives state `Heap (α ⊕ β)`, with `Heap.split` as the
  canonical reshape. Each cell has a name and a type fixed by `CellSpec`.

The example is deliberately tiny: a `Counter` package exporting `incr` and
`read`, and a `Log` package exporting `push (x : Nat)` and `top`. The two
are parallel-composed. In both versions, the composite exposes the
disjoint sum of export interfaces; the only thing that changes is the
*shape* of the composite's state.

The point of the pilot is to surface this shape difference at the type
level so we can compare proof ergonomics on the same structural shape (and
not just at the level of toy examples). Real comparisons happen further up
the stack, e.g. on the Fiat-Shamir EUF-CMA chain. -/

open OracleSpec OracleComp

/-! ## Shared interface specs

The two packages export operations of types that don't depend on whether
we're in SSP or HeapSSP, so we can share them across both halves.

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

end VCVio.HeapSSP.Example

/-! ## SSP version (free product state) -/

namespace VCVio.HeapSSP.Example.SSPSide

open VCVio.HeapSSP.Example

/-- SSP-style counter: state is `Nat`. -/
def counterPkg : VCVio.SSP.Package unifSpec counterSpec Nat where
  init := pure 0
  impl
    | .incr => StateT.mk fun n => pure ((), n + 1)
    | .read => StateT.mk fun n => pure (n, n)

/-- SSP-style log: state is `List Nat`. -/
def logPkg : VCVio.SSP.Package unifSpec logSpec (List Nat) where
  init := pure []
  impl
    | .push x => StateT.mk fun xs => pure ((), x :: xs)
    | .top    => StateT.mk fun xs => pure (xs.head?, xs)

/-- Parallel composition: state is the structural product `Nat × List Nat`.

Notice the state type: it's a bare `Prod`. There is no name for either
component. To talk about "the counter cell" we have to project on the
left; "the log cell" is on the right. -/
def composed : VCVio.SSP.Package (unifSpec + unifSpec) (counterSpec + logSpec)
    (Nat × List Nat) :=
  VCVio.SSP.Package.par counterPkg logPkg

/-- The composite state has shape `Nat × List Nat`. There's no symbolic
handle for either cell; access is by `.1` / `.2` projection. -/
example : VCVio.SSP.Package (unifSpec + unifSpec) (counterSpec + logSpec)
    (Nat × List Nat) := composed

end VCVio.HeapSSP.Example.SSPSide

/-! ## HeapSSP version (named-cell heap state) -/

namespace VCVio.HeapSSP.Example.HeapSide

open VCVio.HeapSSP.Example

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

/-- HeapSSP-style counter: state is `Heap CounterCell`. -/
def counterPkg : Package unifSpec counterSpec CounterCell where
  init := pure Heap.empty
  impl
    | .incr => StateT.mk fun (h : Heap CounterCell) =>
        pure ((), h.update .count (h .count + 1))
    | .read => StateT.mk fun (h : Heap CounterCell) =>
        pure (h .count, h)

/-- HeapSSP-style log: state is `Heap LogCell`. -/
def logPkg : Package unifSpec logSpec LogCell where
  init := pure Heap.empty
  impl
    | .push x => StateT.mk fun (h : Heap LogCell) =>
        pure ((), h.update .entries (x :: h .entries))
    | .top    => StateT.mk fun (h : Heap LogCell) =>
        pure ((h .entries).head?, h)

/-- Parallel composition: state is `Heap (CounterCell ⊕ LogCell)`.

Now both components have *names*. To talk about "the counter cell" we say
`h (Sum.inl .count)`, and `Heap.split CounterCell LogCell` projects the
composite heap into the two factor heaps. The `Sum`-shaped identifier is
the canonical disjoint-union of the two cell directories. -/
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
discriminator for `Sum`. The same disjointness in the SSP version is a
type-level fact about which `Prod` projection a handler touches; the
HeapSSP version makes it a per-cell property of the underlying function. -/
example
    (h : Heap (CounterCell ⊕ LogCell)) (n : Nat) :
    (h.update (.inl .count) n) (.inr .entries) = h (.inr .entries) :=
  Heap.get_update_of_ne (by decide) _

/-- The composite heap *splits* canonically into the two factor heaps via
`Heap.split`. This is the heap-side analogue of `Prod.fst` / `Prod.snd` on
the SSP side, but it lives in `Equiv` (so we get a free inverse, free
`simp` lemmas, and free composition with `Equiv.sumComm` / `Equiv.sumAssoc`
for reshaping more complex compositions). -/
example
    (h : Heap (CounterCell ⊕ LogCell)) (n : Nat) :
    (Heap.split CounterCell LogCell (h.update (.inl .count) n)).1 .count = n := by
  simp [Heap.update]

end VCVio.HeapSSP.Example.HeapSide

/-! ## Observations

Compare the two `composed` definitions:

* `SSPSide.composed : Package _ _ (Nat × List Nat)`
* `HeapSide.composed : Package _ _ (CounterCell ⊕ LogCell)`

In SSP, three-way composition `(A.par B).par C` has state
`(σ_A × σ_B) × σ_C`, while `A.par (B.par C)` has state
`σ_A × (σ_B × σ_C)`. These are equal up to `Equiv.prodAssoc` but not
definitionally — and any cross-tree reshuffling needs a bespoke
state-bijection lemma.

In HeapSSP, the analogous state types are `Heap ((α ⊕ β) ⊕ γ)` and
`Heap (α ⊕ (β ⊕ γ))`. These are equivalent via `Equiv.sumAssoc` lifted
through `Heap`'s functoriality on the identifier set, and the
`Heap.split` lemmas reduce all such reshapes to a single canonical
combinator. The disjointness of cells is read off the `Sum` tag; per-cell
frame holds definitionally for any two distinct identifiers. -/
