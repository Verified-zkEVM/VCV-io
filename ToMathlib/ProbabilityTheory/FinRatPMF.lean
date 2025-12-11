/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.DFinsupp.BigOperators

/-!
# Probability mass functions with finite support and non-negative rational weights

This is a special case of `PMF` that suffices for denotational semantics of `OracleComp` with finite
oracle specifications.

We define this separately to ease computational behavior.
-/

universe u

open DFinsupp

-- def FinRatPMF (α : Type u) : Type u :=
--   {f : α → ℚ≥0 // ∃ s : Finset α, f.support ⊆ s ∧ ∑ x ∈ s, f x = 1}

/-- Probability mass function with finite support and non-negative rational weights.

Defined using a list-based representation, storing a list of tuples `(a, p)` where `a` is an outcome
and `p` is its probability. This representation is _not_ unique; many different `FinRatPMF`s can
represent the same probability distribution. When we want to find out whether two `FinRatPMF`s are
equal as distributions, we need to perform a normalization step. -/
structure FinRatPMF (α : Type u) : Type u where
  toList : List (α × ℚ≥0)
  sum_eq_one : (toList.map Prod.snd).sum = 1

namespace FinRatPMF

variable {α β : Type u}

def support [DecidableEq α] (p : FinRatPMF α) : Finset α := p.toList.map Prod.fst |>.toFinset

def pure (a : α) : FinRatPMF α := ⟨[(a, 1)], by simp⟩

def bind (f : FinRatPMF α) (g : α → FinRatPMF β) : FinRatPMF β :=
  ⟨f.toList >>= (fun a => (g a.1).toList), by
    simp [List.flatMap]
    unfold Function.comp
    sorry⟩

instance : Monad FinRatPMF where
  pure := pure
  bind := bind

-- instance : LawfulMonad FinRatPMF where

/-- Assuming decidable equality on `α`, we can convert a `FinRatPMF` to a `PMF`. -/
def toPMF [DecidableEq α] (p : FinRatPMF α) : PMF α :=
  ⟨fun x => (p.toList.filter (fun a => a.1 = x)).map Prod.snd |>.sum, by
    sorry⟩

end FinRatPMF
