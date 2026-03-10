/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# Asymptotic Security Experiments

This file defines asymptotic security experiments, which are families of security experiments
indexed by a security parameter `n : ℕ`. An asymptotic experiment is **secure** if its
advantage is a negligible function of the security parameter.

## Main Definitions

- `AsymSecExp m`: A family of security experiments `(n : ℕ) → SecExp (m n)`, together with
  an `ExecutionMethod` for each `n`.
- `AsymSecExp.advantage`: The advantage as a function of the security parameter.
- `AsymSecExp.secure`: The advantage is negligible.

## Main Results

- `AsymSecExp.secure_of_pointwise_bound`: If the advantage at each `n` is bounded by `f n`,
  and `f` is negligible, then the experiment is secure.
-/

open OracleComp OracleSpec ENNReal Filter

/-- An asymptotic security experiment: a family of `SecExp` indexed by security parameter `n : ℕ`.
The monad `m n` at each security parameter may vary (e.g., different oracle specs). -/
structure AsymSecExp (m : ℕ → Type → Type*) where
  exp : (n : ℕ) → SecExp (m n)

namespace AsymSecExp

variable {m : ℕ → Type → Type*}

/-- The advantage of the asymptotic experiment as a function of the security parameter. -/
noncomputable def advantage [∀ n, Monad (m n)] [∀ n, HasEvalSPMF (m n)]
    (ase : AsymSecExp m) (n : ℕ) : ℝ≥0∞ :=
  (ase.exp n).advantage

/-- An asymptotic security experiment is **secure** if its advantage is negligible. -/
def secure [∀ n, Monad (m n)] [∀ n, HasEvalSPMF (m n)]
    (ase : AsymSecExp m) : Prop :=
  negligible ase.advantage

/-- If the advantage at each `n` is bounded by `f n`, and `f` is negligible,
then the experiment is secure. -/
theorem secure_of_pointwise_bound [∀ n, Monad (m n)] [∀ n, HasEvalSPMF (m n)]
    (ase : AsymSecExp m) (f : ℕ → ℝ≥0∞) (hf : negligible f)
    (hbound : ∀ n, ase.advantage n ≤ f n) : ase.secure := by
  intro p
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hf p)
  · intro n; exact zero_le _
  · intro n; exact mul_le_mul_of_nonneg_left (hbound n) (zero_le _)

end AsymSecExp
