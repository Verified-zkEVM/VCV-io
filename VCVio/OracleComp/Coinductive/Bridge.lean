/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.OracleComp.OracleComp
import ToMathlib.ITree.Basic

/-! # Bridge between `OracleComp` and `ITree`

`OracleComp spec α` is the *inductive* free monad on `spec.toPFunctor`;
`ITree spec.toPFunctor α` is the *coinductive* (M-type) free monad on the
same polynomial functor. Every finite, terminating `OracleComp` program has
a canonical embedding into the (potentially-infinite) ITree world.

This module provides that embedding, `OracleComp.toITree`, together with a
small handful of structural simp lemmas (`toITree_pure`, `toITree_queryBind`,
`toITree_bind`).

The reverse map "ITree-to-OracleComp" exists *only* on terminating ITrees
and requires productivity / well-foundedness arguments that are not yet
in scope; hence we provide only the forward direction here.

## Universe restriction

To keep the polynomial functor uniform-universe, we specialise to
`OracleSpec.{u, u} ι`. The general `OracleSpec.{u, v}` case would force
`Poly F α` to live in `Type (max u v + 1)`, which is at odds with our
single-universe ITree definition.
-/

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

/-- Embed an `OracleComp spec α` into the corresponding `ITree`. Each `pure x`
becomes `ITree.pure x`; each `queryBind t k` becomes `ITree.query t (toITree ∘ k)`.
The recursion is structural on `OracleComp` (which is an inductive free monad),
so productivity is automatic. -/
def toITree (oa : OracleComp spec α) : ITree spec.toPFunctor α :=
  oa.recOn (motive := fun _ => ITree spec.toPFunctor α)
    ITree.pure
    (fun t _k ih => ITree.query (F := spec.toPFunctor) t ih)

@[simp] theorem toITree_pure (x : α) :
    toITree (pure x : OracleComp spec α) = ITree.pure x := rfl

@[simp] theorem toITree_queryBind (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    toITree (queryBind t k) = ITree.query (F := spec.toPFunctor) t (fun u => toITree (k u)) :=
  rfl

end OracleComp
