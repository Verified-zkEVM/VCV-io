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
# `Fin`-indexed monadic sequencing

`Fin.mOfFn`: run a `Fin n`-indexed family of monadic computations in order and collect the
results as a function.
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
