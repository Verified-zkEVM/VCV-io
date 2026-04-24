/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.ITree.Bisim.Equiv

/-! # Algebraic laws for `bind` and `iter`

The classical equational theory of interaction trees, lifted to Lean. All
laws are stated either as strong bisimulations (`Bisim`, i.e. definitional
equality of M-types) or weak bisimulations (`WeakBisim`).

## Main statements

* `bind_pure_left`, `bind_pure_right`, `bind_assoc` — monad laws on
  `ITree.bind`. The first two are strong bisimulations via `M.bisim`; the
  third likewise.
* `iter_unfold` — the canonical fixed-point equation for `ITree.iter`,
  matching the Coq `unfold_iter` (`Core/ITreeDefinition.v`).
* `iter_bind` — left-distributive interaction between `iter` and `bind`.
* `step_weakBisim` — silent steps are absorbed by weak bisimulation
  (`step t ≈ t`); the defining feature of `eutt`.

The proofs are scaffolded with `sorry`. The strong-bisimulation laws
(`bind_pure_left`, `bind_pure_right`, `bind_assoc`) reduce to constructing
explicit `PFunctor.M`-bisimulations and discharging them with
`PFunctor.M.bisim`. The weak-bisimulation laws (`iter_unfold`, `iter_bind`,
`step_weakBisim`) require the project's coinductive proof tooling, which is
under active development.
-/

@[expose] public section

universe u

namespace ITree

variable {F : PFunctor.{u, u}} {α β γ : Type u}

/-! ### Monad laws -/

theorem bind_pure_left (r : α) (k : α → ITree F β) :
    bind (pure r) k = k r := by
  sorry

theorem bind_pure_right (t : ITree F α) :
    bind t pure = t := by
  sorry

theorem bind_assoc (t : ITree F α) (k : α → ITree F β) (k' : β → ITree F γ) :
    bind (bind t k) k' = bind t (fun a => bind (k a) k') := by
  sorry

/-! ### `iter` unfolding and interaction with `bind` -/

theorem iter_unfold (body : β → ITree F (β ⊕ α)) (init : β) :
    iter body init =
      bind (body init)
        (fun rj => match rj with
          | .inl j => step (iter body j)
          | .inr r => pure r) := by
  sorry

theorem iter_bind (body : β → ITree F (β ⊕ α)) (k : α → ITree F γ) (init : β) :
    bind (iter body init) k =
      iter (fun b => bind (body b) (fun rj => match rj with
        | .inl j => pure (.inl j)
        | .inr r => bind (k r) (fun c => pure (.inr c)))) init := by
  sorry

/-! ### Step is weakly absorbed -/

theorem step_weakBisim (t : ITree F α) : WeakBisim (step t) t := by
  sorry

end ITree
