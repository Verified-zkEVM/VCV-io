/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.ITree.Sim.Defs
public import ToMathlib.ITree.Bisim.Bind

/-! # Naturality lemmas for `ITree.simulate` and `ITree.mapSpec`

The standard equational theory for the simulation operators:

* `simulate_pure`, `simulate_step`, `simulate_query` — one-step unfoldings
  recording the action of `simulate` on each `Shape` constructor.
* `simulate_bind` — `simulate` distributes over `bind`.
* `simulate_id` — interpreting via the trivial handler is (weakly) the
  identity.
* `mapSpec_pure`, `mapSpec_step`, `mapSpec_query` — one-step unfoldings of
  `mapSpec`.
* `mapSpec_id`, `mapSpec_comp` — functoriality of `mapSpec`.
* `simulate_mapSpec` — relating `simulate` and `mapSpec` on a renaming.

The proofs are scaffolded with `sorry`; they reduce to one-step `M.corec`
unfoldings combined with the (sorry-blocked) bisimulation laws of
`ToMathlib.ITree.Bisim.Bind`.
-/

@[expose] public section

universe u

namespace ITree

variable {E F G : PFunctor.{u, u}} {α β : Type u}

/-! ### One-step unfoldings of `simulate` -/

theorem simulate_pure (h : Handler E F) (r : α) :
    simulate h (pure (F := E) r) = pure r := by
  sorry

theorem simulate_step (h : Handler E F) (t : ITree E α) :
    WeakBisim (simulate h (step t)) (simulate h t) := by
  sorry

theorem simulate_query (h : Handler E F) (a : E.A) (k : E.B a → ITree E α) :
    WeakBisim (simulate h (query a k))
      (bind (h a) (fun b => simulate h (k b))) := by
  sorry

/-! ### `simulate` is monadic and identity-preserving -/

theorem simulate_bind (h : Handler E F) (t : ITree E α) (k : α → ITree E β) :
    WeakBisim (simulate h (bind t k)) (bind (simulate h t) (fun a => simulate h (k a))) := by
  sorry

theorem simulate_id (t : ITree E α) :
    WeakBisim (simulate (Handler.id E) t) t := by
  sorry

/-! ### One-step unfoldings of `mapSpec` -/

theorem mapSpec_pure (φ : PFunctor.Hom E F) (r : α) :
    mapSpec φ (pure (F := E) r) = pure r := by
  sorry

theorem mapSpec_step (φ : PFunctor.Hom E F) (t : ITree E α) :
    mapSpec φ (step t) = step (mapSpec φ t) := by
  sorry

theorem mapSpec_query (φ : PFunctor.Hom E F) (a : E.A) (k : E.B a → ITree E α) :
    mapSpec φ (query a k) =
      query (φ.shape a) (fun b => mapSpec φ (k ((φ.arity a).mp b))) := by
  sorry

/-! ### Functoriality of `mapSpec` -/

theorem mapSpec_id (t : ITree E α) :
    mapSpec (PFunctor.Hom.id E) t = t := by
  sorry

theorem mapSpec_comp (φ : PFunctor.Hom E F) (ψ : PFunctor.Hom F G) (t : ITree E α) :
    mapSpec (ψ.comp φ) t = mapSpec ψ (mapSpec φ t) := by
  sorry

/-! ### Relating `simulate` and `mapSpec` -/

theorem simulate_ofHom (φ : PFunctor.Hom E F) (t : ITree E α) :
    WeakBisim (simulate (Handler.ofHom φ) t) (mapSpec φ t) := by
  sorry

end ITree
