/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
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
def CDHAdversary (G : Type) := G → G → G → ProbComp G

/-- CDH experiment: sample random scalars `a, b`, give the adversary `(g, a • g, b • g)`,
and check whether the adversary's output equals `(a * b) • g`. -/
def cdhExp (g : G) (adversary : CDHAdversary G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F
  let h ← adversary g (a • g) (b • g)
  return decide (h = (a * b) • g)

/-! ## DDH (Decisional Diffie-Hellman) -/

/-- A DDH adversary receives `(g, A, B, T)` and guesses whether `T = (a * b) • g`
(real) or `T` is a random group element (random). -/
def DDHAdversary (G : Type) := G → G → G → G → ProbComp Bool

/-- DDH experiment: sample random scalars `a, b` and a bit. If the bit is `true`, set
`T = (a * b) • g`; otherwise sample `T` uniformly from `G`. The adversary wins by
guessing the bit correctly.

**Design assumption**: this definition is well-formed only when `g` generates `G`
(i.e., `Function.Surjective (· • g : F → G)`), ensuring that the real case
`(a * b) • g` and the random case `T ← $ᵗ G` are sampled from the same set.
Without this, a degenerate instantiation could trivially distinguish by testing
subgroup membership.  For a span-correct formulation without the surjectivity
assumption, replace `$ᵗ G` with `(· • g) <$> $ᵗ F`. -/
def ddhExp (g : G) (adversary : DDHAdversary G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F
  let bit ← $ᵗ Bool
  let T ← if bit then pure ((a * b) • g) else $ᵗ G
  let b' ← adversary g (a • g) (b • g) T
  return (bit == b')

/-- DDH advantage: absolute distance from random guessing (1/2).
Uses `ℝ` with absolute value rather than `ℝ≥0∞` subtraction, which would silently
saturate at zero for adversaries that guess the wrong bit more often than not. -/
noncomputable def ddhAdvantage (g : G) (adversary : DDHAdversary G) : ℝ :=
  |(Pr[= true | ddhExp (F := F) g adversary]).toReal - 1 / 2|

/-! ## Generable relation for discrete log -/

section DLogGenerable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [Fintype G] [SampleableType G] [DecidableEq G]
variable (g : G)

private lemma probOutput_map_bijective_uniform_cross
    {α β : Type} [SampleableType α] [SampleableType β] [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Bijective f) (y : β) :
    Pr[= y | f <$> ($ᵗ α : ProbComp α)] = Pr[= y | ($ᵗ β : ProbComp β)] := by
  obtain ⟨x, rfl⟩ := hf.surjective y
  rw [probOutput_map_injective ($ᵗ α) hf.injective x,
      probOutput_uniformSample, probOutput_uniformSample,
      Fintype.card_of_bijective hf]

/-- The discrete log relation is generable when `· • g` is bijective:
sample `sk ← $ᵗ F` and return `(sk • g, sk)`. -/
def dlogGenerable (hg : Function.Bijective (· • g : F → G)) :
    GenerableRelation G F (fun pk sk => decide (sk • g = pk)) where
  gen := do let sk ← $ᵗ F; return (sk • g, sk)
  gen_sound := fun pk sk hmem => by
    rw [decide_eq_true_eq]
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
               Prod.mk.injEq] at hmem
    obtain ⟨_, -, rfl, rfl⟩ := hmem; rfl
  gen_uniform_right := fun pk => by
    simp only [map_eq_bind_pure_comp, Function.comp, bind_assoc, pure_bind]
    exact probOutput_map_bijective_uniform_cross (· • g) hg pk
  gen_uniform_left := fun sk => by
    simp only [map_eq_bind_pure_comp, Function.comp, bind_assoc, pure_bind, bind_pure]

end DLogGenerable

/-! ## Cyclic group instantiation helpers -/

section CyclicInstantiation

variable {G : Type} [AddCommGroup G] [Fintype G]

/-- A generator `g` is nondegenerate if `fun a => a.val • g` surjects onto `G`,
ruling out the trivial case. Uses additive notation consistent with `Module F G`. -/
def NondegenerateGenerator (g : G) : Prop :=
  Function.Surjective fun a : Fin (Fintype.card G) => a.val • g

lemma NondegenerateGenerator.ne_zero [Nontrivial G] {g : G}
    (hg : NondegenerateGenerator (G := G) g) : g ≠ 0 := by
  intro hg0
  rcases exists_ne (0 : G) with ⟨x, hx⟩
  rcases hg x with ⟨a, ha⟩
  have h0x : (0 : G) = x := by simpa [hg0] using ha
  exact hx h0x.symm

end CyclicInstantiation

end DiffieHellman
