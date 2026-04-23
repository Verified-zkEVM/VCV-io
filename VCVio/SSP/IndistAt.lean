/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.SSP.DistEquiv
import VCVio.SSP.Hybrid
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# State-Separating Proofs: ε-bounded Indistinguishability

`Package.IndistAt G₀ G₁ ε` (notation `G₀ ≈ᵈ[ε] G₁`) says that the Boolean distinguishing
advantage between two probability-only packages is bounded by `ε` against *every* Boolean
adversary. This is the standard ε-indistinguishability of state-separating proofs, suitable for
chained game-hopping where the cumulative bound is the sum of per-hop bounds.

## API surface

* **Quasi-relation laws**: `refl` (at ε = 0), `refl_le` (at any non-negative ε), `symm`
  (preserves ε), `trans` (sums ε's), plus a `Trans` instance keyed on the per-step bounds.
* **ε-monotonicity**: `mono`. Increasing the slack only weakens the relation.
* **Bridge from `DistEquiv`**: `of_distEquiv` upgrades a perfect equivalence to ε = 0
  indistinguishability; `distEquiv_left`/`distEquiv_right` transport an indistinguishability
  hop along a `≡ᵈ`-hop on either side. The `Trans` instances on the *mixed* relations
  `(· ≡ᵈ ·) (· ≈ᵈ[ε] ·)` (and the symmetric pair) let `Trans.trans` fuse perfect and
  bounded hops directly without an explicit `distEquiv_left/right` invocation.
* **Bridge to `Package.advantage`**: `advantage_le`, the literal definition.
* **Hybrid argument**: `hybrid` lifts a chain of per-hop `≈ᵈ[ε i]` bounds to a single
  cumulative bound `∑ i ∈ Finset.range n, ε i` between the chain's endpoints.

## Calc and chained hops

The ternary notation `G₀ ≈ᵈ[ε] G₁` is not a binary relation, so Lean's `calc` cannot parse
calc steps written with it. Use `Trans.trans` (which respects all of the registered `Trans`
instances) or the dedicated combinators `IndistAt.trans` / `IndistAt.distEquiv_left` /
`IndistAt.distEquiv_right` to chain hops; `IndistAt.hybrid` is the right tool for chains of
length ≥ 3.

## Note on the `ε = 0` case

In the Bool-adversary world, `IndistAt G₀ G₁ 0` is a strictly weaker statement than `G₀ ≡ᵈ G₁`
out of the box: the latter equates the full output distribution against arbitrary-typed
adversaries, while the former only constrains the Bool-valued probabilities. The two notions
do coincide in the discrete case once one quantifies over post-processing functions, but that
equivalence is not unfolded here; downstream proofs that need full distributional equivalence
should reach for `DistEquiv`.

## Composition

* **`link` congruence in the inner argument**: `link_inner_congr` swaps the inner game of a
  linked composition along an `≈ᵈ[ε]`-hop, leveraging
  `Package.advantage_link_left_eq_advantage_shiftLeft`. The bound is preserved exactly: the
  outer reduction `P` is absorbed into the shifted adversary.
* `par_congr` and outer-side congruences live in follow-up files once parallel-composition
  structural reductions and a notion of equivalence for *open* packages stabilise.
-/

universe uₘ uₑ

open OracleSpec OracleComp ProbComp

namespace VCVio.SSP

namespace Package

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}

/-- Two probability-only packages are *ε-indistinguishable* if every Boolean-valued adversary's
distinguishing advantage is bounded by `ε`.

Equivalent characterisations:
* The Boolean distinguishing advantage `G₀.advantage G₁ A ≤ ε` for every adversary `A`
  (the literal definition).
* When `ε = 0`, this asserts zero distinguishing advantage; cf. `DistEquiv` for the strictly
  stronger "perfect equivalence" against arbitrary-typed adversaries.

The state types `σ₀, σ₁` of the two games are independent: only the export interface and the
distinguishing advantage matter from an adversary's point of view. -/
def IndistAt {σ₀ σ₁ : Type}
    (G₀ : Package unifSpec E σ₀) (G₁ : Package unifSpec E σ₁) (ε : ℝ) : Prop :=
  ∀ (A : OracleComp E Bool), G₀.advantage G₁ A ≤ ε

@[inherit_doc IndistAt]
scoped notation:50 G₀ " ≈ᵈ[" ε "] " G₁ => Package.IndistAt G₀ G₁ ε

namespace IndistAt

variable {σ σ₀ σ₁ σ₂ : Type}

/-! ### Quasi-relation laws -/

/-- Every package is `0`-indistinguishable from itself. -/
@[simp]
protected theorem refl (G : Package unifSpec E σ) : G ≈ᵈ[0] G := by
  intro A
  rw [advantage_self]

protected theorem symm {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁} {ε : ℝ}
    (h : G₀ ≈ᵈ[ε] G₁) : G₁ ≈ᵈ[ε] G₀ := fun A => by
  rw [advantage_symm]; exact h A

/-- ε-indistinguishability composes by adding bounds: a chain of two hops with bounds `ε₀`
and `ε₁` yields a hop with bound `ε₀ + ε₁`. This is the SSP triangle inequality, packaged
for game-hopping. -/
@[trans]
protected theorem trans {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁}
    {G₂ : Package unifSpec E σ₂} {ε₀ ε₁ : ℝ}
    (h₀₁ : G₀ ≈ᵈ[ε₀] G₁) (h₁₂ : G₁ ≈ᵈ[ε₁] G₂) : G₀ ≈ᵈ[ε₀ + ε₁] G₂ :=
  fun A => (advantage_triangle G₀ G₁ G₂ A).trans (add_le_add (h₀₁ A) (h₁₂ A))

instance trans_instance {ε₀ ε₁ : ℝ} :
    @Trans (Package unifSpec E σ₀) (Package unifSpec E σ₁) (Package unifSpec E σ₂)
      (· ≈ᵈ[ε₀] ·) (· ≈ᵈ[ε₁] ·) (· ≈ᵈ[ε₀ + ε₁] ·) where
  trans := IndistAt.trans

/-! ### ε-monotonicity -/

/-- Weakening the bound preserves ε-indistinguishability. -/
theorem mono {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁} {ε ε' : ℝ}
    (h_le : ε ≤ ε') (h : G₀ ≈ᵈ[ε] G₁) : G₀ ≈ᵈ[ε'] G₁ := fun A => (h A).trans h_le

/-- Every package is ε-indistinguishable from itself for any non-negative ε. The dedicated
non-negative-ε form is convenient when chaining: for example, `IndistAt.refl_le G hε` closes
`G ≈ᵈ[ε] G` without an explicit `mono` invocation. -/
theorem refl_le {ε : ℝ} (G : Package unifSpec E σ) (h : 0 ≤ ε) : G ≈ᵈ[ε] G :=
  IndistAt.mono h (IndistAt.refl G)

/-! ### Bridge from `DistEquiv` -/

/-- A perfect distributional equivalence implies `0`-indistinguishability.

The reverse direction (`IndistAt 0` implies `DistEquiv`) is *not* proved here; see the file
header for discussion. -/
theorem of_distEquiv {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁}
    (h : G₀ ≡ᵈ G₁) : G₀ ≈ᵈ[0] G₁ := fun A => by
  rw [DistEquiv.advantage_zero h]

/-- Transport ε-indistinguishability along a `DistEquiv` on the LEFT side. The bound is
unchanged: a perfect hop costs zero. -/
theorem distEquiv_left {G₀ : Package unifSpec E σ₀} {G₀' : Package unifSpec E σ}
    {G₁ : Package unifSpec E σ₁} {ε : ℝ}
    (h : G₀ ≡ᵈ G₀') (hi : G₀' ≈ᵈ[ε] G₁) : G₀ ≈ᵈ[ε] G₁ := fun A => by
  rw [DistEquiv.advantage_left h]; exact hi A

/-- Transport ε-indistinguishability along a `DistEquiv` on the RIGHT side. The bound is
unchanged: a perfect hop costs zero. -/
theorem distEquiv_right {G₀ : Package unifSpec E σ₀}
    {G₁ : Package unifSpec E σ₁} {G₁' : Package unifSpec E σ} {ε : ℝ}
    (h : G₁ ≡ᵈ G₁') (hi : G₀ ≈ᵈ[ε] G₁) : G₀ ≈ᵈ[ε] G₁' := fun A => by
  rw [← DistEquiv.advantage_right G₀ h]; exact hi A

/-- `Trans` instance enabling `calc` chains that start with a `≡ᵈ`-hop and continue with an
`≈ᵈ[ε]`-hop. The cumulative bound is unchanged: a perfect hop costs zero. -/
instance trans_distEquiv_indistAt {ε : ℝ} :
    @Trans (Package unifSpec E σ₀) (Package unifSpec E σ) (Package unifSpec E σ₁)
      (· ≡ᵈ ·) (· ≈ᵈ[ε] ·) (· ≈ᵈ[ε] ·) where
  trans h hi := IndistAt.distEquiv_left h hi

/-- `Trans` instance enabling `calc` chains that start with an `≈ᵈ[ε]`-hop and continue with a
`≡ᵈ`-hop. The cumulative bound is unchanged: a perfect hop costs zero. -/
instance trans_indistAt_distEquiv {ε : ℝ} :
    @Trans (Package unifSpec E σ₀) (Package unifSpec E σ₁) (Package unifSpec E σ)
      (· ≈ᵈ[ε] ·) (· ≡ᵈ ·) (· ≈ᵈ[ε] ·) where
  trans hi h := IndistAt.distEquiv_right h hi

/-! ### Bridge to `Package.advantage` -/

/-- The literal definition: an `IndistAt` witness yields the per-adversary bound. -/
theorem advantage_le {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁} {ε : ℝ}
    (h : G₀ ≈ᵈ[ε] G₁) (A : OracleComp E Bool) : G₀.advantage G₁ A ≤ ε := h A

/-- Build an `IndistAt` witness from a per-adversary bound. -/
theorem of_advantage_le {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁} {ε : ℝ}
    (h : ∀ (A : OracleComp E Bool), G₀.advantage G₁ A ≤ ε) : G₀ ≈ᵈ[ε] G₁ := h

/-! ### Hybrid argument -/

/-- **Hybrid argument.** A chain of per-hop ε-indistinguishabilities through a sequence of
games with potentially different state types collapses to a single endpoint bound, with the
cumulative ε given by the sum of the per-hop bounds.

This is the standard SSP/SSProve hybrid argument: chain `n` per-hop bounds and read off the
overall bound from the sum. The state types `σ i` are allowed to differ across the chain, so
this scales to chains that interleave structural (state-bijection) and quantitative hops. -/
theorem hybrid {n : ℕ} {σ : ℕ → Type} {ε : ℕ → ℝ}
    (G : (i : ℕ) → Package unifSpec E (σ i))
    (h : ∀ i ∈ Finset.range n, G i ≈ᵈ[ε i] G (i + 1)) :
    G 0 ≈ᵈ[∑ i ∈ Finset.range n, ε i] G n := fun A =>
  (advantage_hybrid G A n).trans (Finset.sum_le_sum (fun i hi => h i hi A))

/-! ### Compositional bounds (`link`) -/

section LinkCongr

variable {ιₘ : Type uₘ} {M : OracleSpec.{uₘ, 0} ιₘ}
variable {σ_P : Type}

/-- **Inner-game congruence for `link`.** Swapping the inner game of a linked composition along
an `≈ᵈ[ε]`-hop preserves the bound exactly: the outer reduction `P` is absorbed into the
shifted adversary `P.shiftLeft A` via
`Package.advantage_link_left_eq_advantage_shiftLeft`. -/
theorem link_inner_congr (P : Package M E σ_P)
    {Q₀ : Package unifSpec M σ₀} {Q₁ : Package unifSpec M σ₁} {ε : ℝ}
    (h : Q₀ ≈ᵈ[ε] Q₁) :
    P.link Q₀ ≈ᵈ[ε] P.link Q₁ := by
  intro A
  rw [advantage_link_left_eq_advantage_shiftLeft]
  exact h (P.shiftLeft A)

end LinkCongr

end IndistAt

end Package

/-! ### Sanity tests for the mixed `Trans` instances and `hybrid` -/

section SanityTests

open Package

variable {ιₑ : Type} {E : OracleSpec.{0, 0} ιₑ}
variable {σ₀ σ σ₁ : Type}
variable {G₀ : Package unifSpec E σ₀} {G₀' G₁' : Package unifSpec E σ}
variable {G₁ : Package unifSpec E σ₁}

/-- A perfect hop on the left chains into an ε-bounded hop without changing the bound (uses
the `trans_distEquiv_indistAt` instance under the hood). -/
example {ε : ℝ} (h : G₀ ≡ᵈ G₀') (hi : G₀' ≈ᵈ[ε] G₁) : G₀ ≈ᵈ[ε] G₁ :=
  Trans.trans (r := (· ≡ᵈ ·)) (s := (· ≈ᵈ[ε] ·)) h hi

/-- A perfect hop on the right chains into an ε-bounded hop without changing the bound (uses
the `trans_indistAt_distEquiv` instance under the hood). -/
example {ε : ℝ} (hi : G₀ ≈ᵈ[ε] G₁') (h : G₁' ≡ᵈ G₁) : G₀ ≈ᵈ[ε] G₁ :=
  Trans.trans (r := (· ≈ᵈ[ε] ·)) (s := (· ≡ᵈ ·)) hi h

/-- The hybrid bound collapses a chain of ε-hops to a single sum bound. -/
example {n : ℕ} {state : ℕ → Type} {ε : ℕ → ℝ}
    (G : (i : ℕ) → Package unifSpec E (state i))
    (h : ∀ i ∈ Finset.range n, G i ≈ᵈ[ε i] G (i + 1)) :
    G 0 ≈ᵈ[∑ i ∈ Finset.range n, ε i] G n :=
  IndistAt.hybrid G h

end SanityTests

end VCVio.SSP
