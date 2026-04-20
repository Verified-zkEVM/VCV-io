/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import Mathlib.Data.Fintype.Basic

/-!
# Finite-branching ornament on interaction specs

`Interaction.Spec.Fintype spec` is the recursive typeclass-level ornament
asserting that every move space appearing in `spec : Spec.{0}` carries
`Fintype` and `Nonempty` instances.

This is the tree-shaped analog of `OracleSpec.Fintype extends PFunctor.Fintype`:
`OracleSpec` has one layer of positions (a single polynomial functor), so a
single `PFunctor.Fintype` witness suffices. `Spec` is a tree of nodes, so the
ornament recurses into every subtree.

A `Spec.Fintype spec` instance is the data needed to derive a canonical
uniform sampler `Spec.Sampler.uniform : Sampler ProbComp spec` built by
uniform selection at each node (see `VCVio.Interaction.UC.Runtime`).
-/

namespace Interaction

/-- Recursive finite-branching ornament on an interaction spec.

The `.done` case holds vacuously. At a `.node X rest` the ornament
bundles `Fintype` and `Nonempty` witnesses for the move space `X`
together with a per-branch ornament on every continuation `rest x`.
Typeclass synthesis builds these up structurally from concrete `spec`
trees via the companion instances below, the same way
`OracleSpec.Fintype` synthesizes from `PFunctor.Fintype`. -/
protected class inductive Spec.Fintype : Spec.{0} → Type 1 where
  | done : Spec.Fintype Spec.done
  | node {X : Type} (hFin : Fintype X) (hNon : Nonempty X)
      {rest : X → Spec.{0}} (hRec : ∀ x, Spec.Fintype (rest x)) :
      Spec.Fintype (Spec.node X rest)

namespace Spec.Fintype

/-- Canonical `Spec.Fintype` instance for the terminal spec. -/
instance instDone : Spec.Fintype Spec.done := .done

/-- Canonical `Spec.Fintype` instance for a node: synthesizes from
`Fintype X`, `Nonempty X`, and a per-branch ornament. -/
instance instNode {X : Type} [hFin : Fintype X] [hNon : Nonempty X]
    {rest : X → Spec.{0}} [hRec : ∀ x, Spec.Fintype (rest x)] :
    Spec.Fintype (Spec.node X rest) :=
  .node hFin hNon hRec

/-- Extract the `Fintype` instance for the move space of the root node. -/
@[reducible]
def rootFintype {X : Type} {rest : X → Spec.{0}}
    (h : Spec.Fintype (Spec.node X rest)) : Fintype X :=
  match h with
  | .node hFin _ _ => hFin

/-- Extract the `Nonempty` instance for the move space of the root node. -/
@[reducible]
def rootNonempty {X : Type} {rest : X → Spec.{0}}
    (h : Spec.Fintype (Spec.node X rest)) : Nonempty X :=
  match h with
  | .node _ hNon _ => hNon

/-- Extract the ornament for every continuation of the root node. -/
@[reducible]
def tail {X : Type} {rest : X → Spec.{0}}
    (h : Spec.Fintype (Spec.node X rest)) : ∀ x, Spec.Fintype (rest x) :=
  match h with
  | .node _ _ hRec => hRec

end Spec.Fintype

end Interaction
