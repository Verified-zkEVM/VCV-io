/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# Asymptotic Security Experiments and Games

This file defines asymptotic security experiments and games where the advantage function
is abstract — not tied to any specific game formulation. This allows the same meta-theorems
(reductions, game-hopping, hybrid arguments) to work for failure-based games (`SecExp`),
distinguishing games (`ProbComp.distAdvantage`), and any other advantage metric.

## Main Definitions

- `SecurityExp`: An advantage function `ℕ → ℝ≥0∞` with security = negligibility.
- `SecurityGame Adv`: An advantage function `Adv → ℕ → ℝ≥0∞` with quantified security.
- Smart constructors: `ofSecExp`, `ofDistGame`, `ofGuessGame`.

## Main Results

- `SecurityExp.secure_of_pointwise_bound`: Pointwise ≤ negligible ⟹ secure.
- `SecurityGame.secureAgainst_of_reduction`: Basic security reduction (tight).
- `SecurityGame.secureAgainst_of_poly_reduction`: Polynomial-loss security reduction.
- `SecurityGame.secureAgainst_of_close`: Game-hopping step.
- `SecurityGame.secureAgainst_of_hybrid`: Hybrid argument over a chain of games.
-/

open OracleComp OracleSpec ENNReal Filter

/-- An asymptotic security experiment: an advantage function of the security parameter.
Secure means the advantage is negligible. -/
structure SecurityExp where
  advantage : ℕ → ℝ≥0∞

namespace SecurityExp

/-- An asymptotic security experiment is **secure** if its advantage is negligible. -/
def secure (ase : SecurityExp) : Prop :=
  negligible ase.advantage

/-- If the advantage at each `n` is bounded by `f n`, and `f` is negligible,
then the experiment is secure. -/
theorem secure_of_pointwise_bound
    (ase : SecurityExp) (f : ℕ → ℝ≥0∞) (hf : negligible f)
    (hbound : ∀ n, ase.advantage n ≤ f n) : ase.secure :=
  negligible_of_le hbound hf

/-! ### Smart constructors -/

/-- Build from a family of failure-based `SecExp`. -/
noncomputable def ofSecExp {m : ℕ → Type → Type*}
    [∀ n, Monad (m n)] [∀ n, HasEvalSPMF (m n)]
    (exp : (n : ℕ) → SecExp (m n)) : SecurityExp where
  advantage n := (exp n).advantage

/-- Build from a two-game distinguishing experiment.
Advantage = `|Pr[= () | game₀ n] - Pr[= () | game₁ n]|`. -/
noncomputable def ofDistExp
    (game₀ game₁ : ℕ → ProbComp Unit) : SecurityExp where
  advantage n := ENNReal.ofReal ((game₀ n).distAdvantage (game₁ n))

/-- Build from a single-game guessing experiment.
Advantage = `|1/2 - Pr[= () | game n]|`. -/
noncomputable def ofGuessExp
    (game : ℕ → ProbComp Unit) : SecurityExp where
  advantage n := ENNReal.ofReal ((game n).guessAdvantage)

end SecurityExp

/-! ## Asymptotic Security Games

A security game is parameterized by an adversary type. The advantage function maps
each adversary and security parameter to a non-negative extended real.

The predicate `isPPT` is left abstract; users specialize it to `PolyQueries` or other
efficiency notions as appropriate. -/

/-- An asymptotic security game: maps each adversary and security parameter to an
advantage value. Decoupled from any specific game formulation — the same meta-theorems
work for failure-based, distinguishing, and other game styles. -/
structure SecurityGame (Adv : Type*) where
  advantage : Adv → ℕ → ℝ≥0∞

namespace SecurityGame

variable {Adv : Type*}

/-- A game is **secure against a class of adversaries** (specified by `isPPT`)
if every adversary in that class has negligible advantage. -/
def secureAgainst (g : SecurityGame Adv) (isPPT : Adv → Prop) : Prop :=
  ∀ A, isPPT A → negligible (g.advantage A)

/-- Fixing an adversary in a game produces an asymptotic security experiment. -/
def toSecurityExp (g : SecurityGame Adv) (A : Adv) : SecurityExp where
  advantage := g.advantage A

@[simp]
theorem toSecurityExp_advantage (g : SecurityGame Adv) (A : Adv) :
    (g.toSecurityExp A).advantage = g.advantage A := rfl

/-! ### Smart constructors -/

/-- Build from a family of failure-based `SecExp`. -/
noncomputable def ofSecExp {m : ℕ → Type → Type*}
    [∀ n, Monad (m n)] [∀ n, HasEvalSPMF (m n)]
    (game : Adv → (n : ℕ) → SecExp (m n)) : SecurityGame Adv where
  advantage A n := (game A n).advantage

/-- Build from a two-game distinguishing experiment.
Advantage = `|Pr[= () | game₀ A n] - Pr[= () | game₁ A n]|`. -/
noncomputable def ofDistGame
    (game₀ game₁ : Adv → ℕ → ProbComp Unit) : SecurityGame Adv where
  advantage A n := ENNReal.ofReal ((game₀ A n).distAdvantage (game₁ A n))

/-- Build from a single-game guessing experiment.
Advantage = `|1/2 - Pr[= () | game A n]|`. -/
noncomputable def ofGuessGame
    (game : Adv → ℕ → ProbComp Unit) : SecurityGame Adv where
  advantage A n := ENNReal.ofReal ((game A n).guessAdvantage)

/-! ### Security reductions -/

/-- Basic security reduction: if there is a map `reduce : Adv → Adv'` that
preserves efficiency and the advantage of `g` is pointwise ≤ the advantage of `g'`
on the reduced adversary, then security of `g'` implies security of `g`. -/
theorem secureAgainst_of_reduction {Adv' : Type*}
    {g : SecurityGame Adv} {g' : SecurityGame Adv'}
    {isPPT : Adv → Prop} {isPPT' : Adv' → Prop}
    {reduce : Adv → Adv'}
    (hreduce : ∀ A, isPPT A → isPPT' (reduce A))
    (hbound : ∀ A n, g.advantage A n ≤ g'.advantage (reduce A) n)
    (hsecure : g'.secureAgainst isPPT') :
    g.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hbound A) (hsecure (reduce A) (hreduce A hA))

/-! ### Game hopping -/

/-- **Game-hopping step**: if the advantage of `g₁` at every security parameter is at most the
advantage of `g₂` plus some negligible `ε`, and `g₂` is secure, then `g₁` is secure.

This is the fundamental lemma for game-hopping proofs: each "hop" from `g₁` to `g₂`
introduces at most `ε(n)` advantage loss, and `ε` is absorbed because negligible functions
are closed under addition. -/
theorem secureAgainst_of_close
    {g₁ g₂ : SecurityGame Adv} {isPPT : Adv → Prop}
    {ε : ℕ → ℝ≥0∞} (hε : negligible ε)
    (hclose : ∀ A, isPPT A → ∀ n, g₁.advantage A n ≤ g₂.advantage A n + ε n)
    (hsecure : g₂.secureAgainst isPPT) :
    g₁.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hclose A hA) (negligible_add (hsecure A hA) hε)

/-- Game-hopping step with a reduction: if the advantage of `g₁` with adversary `A` is at most
the advantage of `g₂` with reduced adversary plus `ε`, then security of `g₂` (against the
target class) implies security of `g₁`. Combines reduction and game hop. -/
theorem secureAgainst_of_close_reduction {Adv' : Type*}
    {g₁ : SecurityGame Adv} {g₂ : SecurityGame Adv'}
    {isPPT : Adv → Prop} {isPPT' : Adv' → Prop}
    {reduce : Adv → Adv'}
    {ε : ℕ → ℝ≥0∞} (hε : negligible ε)
    (hreduce : ∀ A, isPPT A → isPPT' (reduce A))
    (hclose : ∀ A, isPPT A → ∀ n,
      g₁.advantage A n ≤ g₂.advantage (reduce A) n + ε n)
    (hsecure : g₂.secureAgainst isPPT') :
    g₁.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hclose A hA)
    (negligible_add (hsecure (reduce A) (hreduce A hA)) hε)

/-! ### Polynomial-loss reductions -/

/-- **Polynomial-loss security reduction**: if there is a reduction `reduce : Adv → Adv'`
that preserves efficiency and the advantage of `g` is at most `loss(n)` times the
advantage of `g'` on the reduced adversary, then security of `g'` implies security of `g`.

This handles reductions where the adversary's advantage is amplified by a polynomial factor,
e.g., from a hybrid argument guessing which of `poly(n)` steps to exploit. -/
theorem secureAgainst_of_poly_reduction {Adv' : Type*}
    {g : SecurityGame Adv} {g' : SecurityGame Adv'}
    {isPPT : Adv → Prop} {isPPT' : Adv' → Prop}
    {reduce : Adv → Adv'}
    {loss : Polynomial ℕ}
    (hreduce : ∀ A, isPPT A → isPPT' (reduce A))
    (hbound : ∀ A n, g.advantage A n ≤ ↑(loss.eval n) * g'.advantage (reduce A) n)
    (hsecure : g'.secureAgainst isPPT') :
    g.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hbound A)
    (negligible_polynomial_mul (hsecure (reduce A) (hreduce A hA)) loss)

/-- Combined game-hopping step with polynomial advantage loss and reduction. -/
theorem secureAgainst_of_close_poly_reduction {Adv' : Type*}
    {g₁ : SecurityGame Adv} {g₂ : SecurityGame Adv'}
    {isPPT : Adv → Prop} {isPPT' : Adv' → Prop}
    {reduce : Adv → Adv'}
    {loss : Polynomial ℕ}
    {ε : ℕ → ℝ≥0∞} (hε : negligible ε)
    (hreduce : ∀ A, isPPT A → isPPT' (reduce A))
    (hclose : ∀ A, isPPT A → ∀ n,
      g₁.advantage A n ≤ ↑(loss.eval n) * g₂.advantage (reduce A) n + ε n)
    (hsecure : g₂.secureAgainst isPPT') :
    g₁.secureAgainst isPPT := fun A hA =>
  negligible_of_le (hclose A hA)
    (negligible_add (negligible_polynomial_mul (hsecure (reduce A) (hreduce A hA)) loss) hε)

/-! ### Hybrid argument -/

/-- **Hybrid argument**: given `k + 1` games indexed by `0, 1, ..., k`, if consecutive
games differ by at most `ε(n)` in advantage and the final game is secure, then the
first game is also secure.

The total advantage loss is at most `k · ε(n)`, which is negligible since `ε` is
negligible and `k` is constant. -/
theorem secureAgainst_of_hybrid
    {games : ℕ → SecurityGame Adv}
    {isPPT : Adv → Prop}
    {ε : ℕ → ℝ≥0∞} (hε : negligible ε)
    {k : ℕ}
    (hconsec : ∀ j < k, ∀ A, isPPT A → ∀ n,
      (games j).advantage A n ≤ (games (j + 1)).advantage A n + ε n)
    (hsecure : (games k).secureAgainst isPPT) :
    (games 0).secureAgainst isPPT := by
  induction k with
  | zero => exact hsecure
  | succ k ih =>
    exact ih (fun j hj => hconsec j (by omega))
      (secureAgainst_of_close hε (hconsec k (by omega)) hsecure)

end SecurityGame
