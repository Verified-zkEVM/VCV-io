/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.PFunctor.Univariate.M

/-! # Auxiliary lemmas for `PFunctor.M`

Small extensions to `Mathlib.Data.PFunctor.Univariate.M` used by the
`ToMathlib.ITree` port of the Coq `InteractionTrees` library.

The Mathlib file already supplies `M.mk`, `M.dest`, `M.corec`, `M.dest_mk`,
`M.mk_dest`, `M.dest_corec`, `M.corec_unique`, and the bisimulation principle
`M.bisim`. We add a few rewriting helpers that come up repeatedly when
defining and reasoning about ITrees:

* `M.dest_corec_apply` — destructured form of `M.dest_corec` whose RHS unpacks
  the `Sigma` so that nested pattern matches reduce by `rfl`.
* `M.dest_corec_eq` — reformulation of `M.dest_corec` that lets `simp` see the
  result as an explicit `Sigma`.
* `M.corec_dest` — corecursive characterization of the identity, useful for
  proving `corec`-style uniqueness equations.
* `M.bisim_corec` — convenience bisimulation up to two `corec`s, the workhorse
  for `bind`/`iter` rewriting.
-/

@[expose] public section

universe u uA uB v

namespace PFunctor

namespace M

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- `M.dest_corec` with the result `Sigma` unpacked. The shape of `M.dest`'s
output is `(g x).1`; the children component, after applying the `PFunctor.map`
on the RHS of `M.dest_corec`, is `M.corec g ∘ (g x).2`. -/
theorem dest_corec_apply (g : α → P α) (x : α) :
    M.dest (M.corec g x) = ⟨(g x).1, fun b => M.corec g ((g x).2 b)⟩ := by
  rw [M.dest_corec]
  rcases h : g x with ⟨a, f⟩
  rfl

/-- Pointwise version of `dest_corec_apply` written in `Sigma`-eta form,
convenient when the right-hand side of a `corec` step is already known
explicitly. -/
theorem dest_corec_eq {a : P.A} {h : P.B a → α} (g : α → P α) (x : α) (heq : g x = ⟨a, h⟩) :
    M.dest (M.corec g x) = ⟨a, fun b => M.corec g (h b)⟩ := by
  rw [dest_corec_apply, heq]

/-- Bisimulation principle specialized to two `corec`s built from the same
shape transformer. If at every reachable state the two seed transitions agree
on shapes and yield bisimilar children, the two `corec`s are equal. -/
theorem corec_eq_corec {α β : Type v} (g : α → P α) (h : β → P β)
    (R : α → β → Prop) (x₀ : α) (y₀ : β)
    (hR : R x₀ y₀)
    (step : ∀ x y, R x y → ∃ a f f',
      g x = ⟨a, f⟩ ∧ h y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    M.corec g x₀ = M.corec h y₀ := by
  let S : M P → M P → Prop :=
    fun u v => ∃ x y, R x y ∧ u = M.corec g x ∧ v = M.corec h y
  refine M.bisim S ?_ _ _ ⟨x₀, y₀, hR, rfl, rfl⟩
  rintro u v ⟨x, y, hxy, rfl, rfl⟩
  obtain ⟨a, f, f', hf, hf', hR'⟩ := step x y hxy
  refine ⟨a, M.corec g ∘ f, M.corec h ∘ f', ?_, ?_, ?_⟩
  · rw [dest_corec, hf]; rfl
  · rw [dest_corec, hf']; rfl
  · intro i; exact ⟨f i, f' i, hR' i, rfl, rfl⟩

end M

end PFunctor
