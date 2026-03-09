/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append

/-!
# Discrete Logarithm Assumptions (DLog / CDH / DDH)

Standard hardness assumptions for cryptographic groups, formalized using Mathlib's
`Module F G` for scalar multiplication.

## Mathematical setup

We model a cyclic group as:
- `F` : the scalar field (exponents), e.g. `ZMod p` for a prime-order group
- `G` : the group of elements (e.g. elliptic curve points), with `[AddCommGroup G]`
- `Module F G` : scalar multiplication `a • g` (corresponds to `g^a` in multiplicative notation)
- `g : G` : a fixed generator (public system parameter)

## Notation correspondence

| Textbook (multiplicative) | This file (additive / EC-style) |
|---|---|
| `g^a`                     | `a • g`                         |
| `g^a · g^b = g^{a+b}`    | `a • g + b • g = (a + b) • g`  |
| `(g^a)^b = g^{ab}`       | `b • (a • g) = (b * a) • g`    |

## Assumptions

- **DLog**: given `(g, x • g)`, find `x`
- **CDH**: given `(g, a • g, b • g)`, find `(a * b) • g`
- **DDH**: distinguish `(g, a • g, b • g, (a * b) • g)` from `(g, a • g, b • g, c • g)`
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace DiffieHellman

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

/-! ## DLog (Discrete Logarithm) -/

/-- A DLog adversary receives a generator and a group element, and tries to find the
discrete logarithm (scalar). -/
def DLogAdversary (F G : Type) := G → G → ProbComp F

/-- DLog experiment: sample a random scalar `x`, give the adversary `(g, x • g)`,
and check whether the adversary's guess equals `x`. -/
def dlogExp (g : G) (adversary : DLogAdversary F G) : ProbComp Bool := do
  let x ← $ᵗ F
  let x' ← adversary g (x • g)
  return decide (x' = x)

/-! ## CDH (Computational Diffie-Hellman) -/

/-- A CDH adversary receives `(g, a • g, b • g)` and tries to compute `(a * b) • g`. -/
def CDHAdversary (F G : Type) := G → G → G → ProbComp G

/-- CDH experiment: sample random scalars `a, b`, give the adversary `(g, a • g, b • g)`,
and check whether the adversary's output equals `(a * b) • g`. -/
def cdhExp (g : G) (adversary : CDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F
  let h ← adversary g (a • g) (b • g)
  return decide (h = (a * b) • g)

/-! ## DDH (Decisional Diffie-Hellman) -/

/-- A DDH adversary receives `(g, A, B, T)` and guesses whether `T = (a * b) • g`
(real) or `T` is a random group element (random). -/
def DDHAdversary (F G : Type) := G → G → G → G → ProbComp Bool

/-- DDH experiment: sample random scalars `a, b` and a bit. If the bit is `true`, set
`T = (a * b) • g`; otherwise sample `T` uniformly from `G`. The adversary wins by
guessing the bit correctly. -/
def ddhExp (g : G) (adversary : DDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F
  let bit ← $ᵗ Bool
  let T ← if bit then pure ((a * b) • g) else $ᵗ G
  let b' ← adversary g (a • g) (b • g) T
  return (bit == b')

/-- DDH advantage: how much better than random guessing the adversary does. -/
noncomputable def ddhAdvantage (g : G) (adversary : DDHAdversary F G) : ℝ≥0∞ :=
  Pr[= true | ddhExp g adversary] - 1 / 2

/-! ## Cyclic group instantiation helpers -/

section CyclicInstantiation

variable {G : Type} [CommGroup G] [Fintype G]

/-- In a cyclic-group style instantiation (multiplicative), this rules out degenerate
generator choices by requiring that `fun a => g ^ a` is surjective. -/
def NondegenerateGenerator (g : G) : Prop :=
  Function.Surjective fun a : Fin (Fintype.card G) => g ^ a.1

lemma NondegenerateGenerator.ne_one [Nontrivial G] {g : G}
    (hg : NondegenerateGenerator (G := G) g) : g ≠ 1 := by
  intro hg1
  rcases exists_ne (1 : G) with ⟨x, hx⟩
  rcases hg x with ⟨a, ha⟩
  have h1x : (1 : G) = x := by simpa [hg1] using ha
  exact hx h1x.symm

end CyclicInstantiation

end DiffieHellman
