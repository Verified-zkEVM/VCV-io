/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Control.Basic

/-!
# Monadic folds and `Fin`-indexed sequencing

`Fin.mOfFn`, the unfolding of `List.mapM`'s loop, `forIn` over a product accumulator as a
`foldlM`, and `bind_eq_of_map_eq` for binds whose first steps agree up to a projection.
-/

public section

universe u v w

/-- Monadic analog of `Fin.ofFn`: given `f : Fin n → m α`, runs each computation
in order and collects the results as a function `Fin n → α`. This is the
`Fin n → α` counterpart of Mathlib's `Vector.mOfFn`. -/
@[expose]
def Fin.mOfFn {m : Type u → Type v} [Monad m] {α : Type u} :
    (n : ℕ) → (Fin n → m α) → m (Fin n → α)
  | 0, _ => return Fin.elim0
  | n + 1, f => do
    let a ← f 0
    let rest ← Fin.mOfFn n (fun i => f i.succ)
    return Fin.cons a rest

lemma list_mapM_loop_eq {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α : Type w} {β : Type u} (xs : List α) (f : α → m β) (ys : List β) :
    List.mapM.loop f xs ys = (ys.reverse ++ ·) <$> List.mapM.loop f xs [] := by
  revert ys
  induction xs with
  | nil => simp [List.mapM.loop]
  | cons x xs h =>
      intro ys
      simp only [List.mapM.loop, map_bind]
      refine congr_arg (f x >>= ·) (funext fun x ↦ ?_)
      simp [h (x :: ys), h [x]]

/-! ### `forIn` / `foldlM` bridge for imperative-style loops

Lean's `for`/`let mut` syntax desugars to `List.forIn` with `MProd` state and
`ForInStep.yield` continuations, while functional-style code uses `List.foldlM`
with `Prod` state. The lemmas below bridge these two representations.

For a single mutable variable (no `MProd` wrapper), use Mathlib's
`List.forIn_yield_eq_foldlM` directly. -/

/-- A `for`/`let mut` loop with two mutable variables (desugared to `forIn` over
`MProd` state with `ForInStep.yield` in every branch) is equivalent to `foldlM`
with `Prod` state. This bridges two impedance mismatches at once:

1. `forIn` with yield-only body ↔ `foldlM`
2. `MProd` state from `let mut` desugaring ↔ `Prod` state -/
theorem List.forIn_mprod_yield_eq_foldlM
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α : Type w} {β γ : Type u} (l : List α) (b₀ : β) (c₀ : γ)
    (f : α → MProd β γ → m (ForInStep (MProd β γ)))
    (g : β × γ → α → m (β × γ))
    (hfg : ∀ a b c, f a ⟨b, c⟩ = do
      let r ← g (b, c) a; pure (.yield ⟨r.1, r.2⟩)) :
    (do let r ← forIn l ⟨b₀, c₀⟩ f; pure (r.fst, r.snd)) =
    l.foldlM g (b₀, c₀) := by
  suffices ∀ (b : β) (c : γ),
    (do let r ← forIn l ⟨b, c⟩ f; pure (r.fst, r.snd)) = l.foldlM g (b, c) from
    this b₀ c₀
  intro b c
  induction l generalizing b c with
  | nil => simp [List.forIn_nil, List.foldlM_nil]
  | cons x xs ih =>
    rw [List.forIn_cons, List.foldlM_cons, hfg]
    simp only [monad_norm]
    congr 1; funext ⟨b', c'⟩
    exact ih b' c'

section CrossTypeBind

/-- If the first steps agree after projection, and continuations agree on matching inputs,
    then the full bind computations agree. Generalizes `bind_congr` to different source types. -/
theorem bind_eq_of_map_eq {m : Type → Type*} [Monad m] [LawfulMonad m]
    {α₁ α₂ β : Type} {m₁ : m α₁} {m₂ : m α₂}
    {f₁ : α₁ → m β} {f₂ : α₂ → m β}
    (proj : α₁ → α₂)
    (h_first : proj <$> m₁ = m₂)
    (h_cont : ∀ a₁, f₁ a₁ = f₂ (proj a₁)) :
    m₁ >>= f₁ = m₂ >>= f₂ := by
  simp only [← h_first, monad_norm, funext h_cont, Function.comp_apply]

end CrossTypeBind
