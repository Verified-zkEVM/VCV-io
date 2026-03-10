/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# Asymptotic Security Experiments and Games

This file defines asymptotic security experiments (families of experiments indexed by
a security parameter `n : ℕ`) and security games (experiments parameterized by an adversary).

An asymptotic experiment is **secure** if its advantage is a negligible function.
A security game is **secure against a class of adversaries** if every adversary in the class
has negligible advantage.

## Main Definitions

- `AsymSecExp m`: A family of `SecExp` indexed by `n : ℕ`.
- `AsymSecExp.secure`: The advantage is negligible.
- `AsymSecGame Adv m`: A game mapping adversary + security parameter to an experiment.
- `AsymSecGame.secureAgainst`: For all adversaries satisfying a predicate, advantage is negligible.

## Main Results

- `AsymSecExp.secure_of_pointwise_bound`: Pointwise ≤ negligible ⟹ secure.
- `negligible_of_le`: Monotonicity of negligibility.
- `AsymSecGame.secureAgainst_of_reduction`: Basic security reduction (tight).
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

/-! ## Negligibility helpers -/

/-- Negligibility is monotone: if `f ≤ g` pointwise and `g` is negligible, then `f` is. -/
theorem negligible_of_le {f g : ℕ → ℝ≥0∞} (hfg : ∀ n, f n ≤ g n) (hg : negligible g) :
    negligible f := by
  intro p
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg p)
  · intro n; exact zero_le _
  · intro n; exact mul_le_mul_of_nonneg_left (hfg n) (zero_le _)

/-! ## Asymptotic Security Games

A security game is parameterized by an adversary type. Each adversary + security parameter
yields a concrete `SecExp`. The standard security statement is:
"for all adversaries satisfying `isPPT`, the advantage is negligible."

The predicate `isPPT` is left abstract; users specialize it to `PolyQueries` or other
efficiency notions as appropriate. -/

/-- An asymptotic security game: maps each adversary and security parameter to a
concrete security experiment. -/
structure AsymSecGame (Adv : Type*) (m : ℕ → Type → Type*) where
  game : Adv → (n : ℕ) → SecExp (m n)

namespace AsymSecGame

variable {Adv : Type*} {m : ℕ → Type → Type*}
variable [∀ n, Monad (m n)] [∀ n, HasEvalSPMF (m n)]

/-- The advantage of adversary `A` at security parameter `n`. -/
noncomputable def advantage (g : AsymSecGame Adv m) (A : Adv) (n : ℕ) : ℝ≥0∞ :=
  (g.game A n).advantage

/-- A game is **secure against a class of adversaries** (specified by `isPPT`)
if every adversary in that class has negligible advantage. -/
def secureAgainst (g : AsymSecGame Adv m) (isPPT : Adv → Prop) : Prop :=
  ∀ A, isPPT A → negligible (g.advantage A)

/-- Fixing an adversary in a game produces an asymptotic security experiment. -/
def toAsymSecExp (g : AsymSecGame Adv m) (A : Adv) : AsymSecExp m where
  exp n := g.game A n

@[simp]
theorem advantage_eq_toAsymSecExp_advantage (g : AsymSecGame Adv m) (A : Adv) :
    g.advantage A = (g.toAsymSecExp A).advantage := rfl

/-- Basic security reduction (tight): if there is a map `reduce : Adv → Adv'` that
preserves efficiency and the advantage of `g` is pointwise ≤ the advantage of `g'`
on the reduced adversary, then security of `g'` implies security of `g`. -/
theorem secureAgainst_of_reduction {Adv' : Type*} {m' : ℕ → Type → Type*}
    [∀ n, Monad (m' n)] [∀ n, HasEvalSPMF (m' n)]
    {g : AsymSecGame Adv m} {g' : AsymSecGame Adv' m'}
    {isPPT : Adv → Prop} {isPPT' : Adv' → Prop}
    {reduce : Adv → Adv'}
    (hreduce : ∀ A, isPPT A → isPPT' (reduce A))
    (hbound : ∀ A n, g.advantage A n ≤ g'.advantage (reduce A) n)
    (hsecure : g'.secureAgainst isPPT') :
    g.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hbound A) (hsecure (reduce A) (hreduce A hA))

end AsymSecGame
