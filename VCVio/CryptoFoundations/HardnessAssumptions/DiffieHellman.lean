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
import VCVio.EvalDist.Bool
import VCVio.ProgramLogic.Tactics

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

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic

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

/-- A CDH adversary receives `(g, a • g, b • g)` and tries to compute `(a * b) • g`.
`_F` is a phantom type parameter for the scalar field, enabling Lean to infer `F`
at call sites of `cdhExp`. -/
def CDHAdversary (_F G : Type) := G → G → G → ProbComp G

/-- CDH experiment: sample random scalars `a, b`, give the adversary `(g, a • g, b • g)`,
and check whether the adversary's output equals `(a * b) • g`. -/
def cdhExp (g : G) (adversary : CDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F
  let h ← adversary g (a • g) (b • g)
  return decide (h = (a * b) • g)

/-! ## DDH (Decisional Diffie-Hellman) -/

/-- A DDH adversary receives `(g, A, B, T)` and guesses whether `T = (a * b) • g`
(real) or `T` is a random group element (random).
`_F` is a phantom type parameter for the scalar field, enabling Lean to infer `F`
at call sites of `ddhExp` and related definitions. -/
def DDHAdversary (_F G : Type) := G → G → G → G → ProbComp Bool

/-- DDH experiment: sample random scalars `a, b` and a bit. If the bit is `true`, set
`c = a * b` (the real DH scalar); otherwise sample `c ← $ᵗ F` independently. The adversary
receives `(g, a • g, b • g, c • g)` and wins by guessing the bit.

All sampling is from the scalar field `F`, so the experiment is well-defined for any
`Module F G` without requiring that `g` generates all of `G`. -/
def ddhExp (g : G) (adversary : DDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F
  let bit ← $ᵗ Bool
  let c ← if bit then pure (a * b) else $ᵗ F
  let b' ← adversary g (a • g) (b • g) (c • g)
  return (bit == b')

/-- DDH advantage: absolute distance from random guessing (1/2).
Uses `ℝ` with absolute value rather than `ℝ≥0∞` subtraction, which would silently
saturate at zero for adversaries that guess the wrong bit more often than not. -/
noncomputable def ddhGuessAdvantage (g : G) (adversary : DDHAdversary F G) : ℝ :=
  |(Pr[= true | ddhExp g adversary]).toReal - 1 / 2|

/-! ## DDH: Two-game formulation -/

/-- DDH real game: the adversary receives a genuine DH triple `(g, a • g, b • g, (a * b) • g)`. -/
def ddhExpReal (g : G) (adversary : DDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F
  adversary g (a • g) (b • g) ((a * b) • g)

/-- DDH random game: the adversary receives `(g, a • g, b • g, c • g)` with independent
`c ← $ᵗ F`. -/
def ddhExpRand (g : G) (adversary : DDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F; let c ← $ᵗ F
  adversary g (a • g) (b • g) (c • g)

/-- Two-game DDH advantage: `|Pr[output 1 | real] - Pr[output 1 | random]|`. -/
noncomputable def ddhDistAdvantage (g : G) (adversary : DDHAdversary F G) : ℝ :=
  |(Pr[= true | ddhExpReal g adversary]).toReal -
    (Pr[= true | ddhExpRand g adversary]).toReal|

omit [Fintype F] [DecidableEq F] [DecidableEq G] [SampleableType G] in
/-- The single-game DDH experiment can be decomposed as a uniform-bit branch over
the real and random DDH games. -/
private lemma ddhExp_probOutput_eq_branch (g : G) (adversary : DDHAdversary F G) :
    Pr[= true | ddhExp g adversary] =
    Pr[= true | do
      let bit ← ($ᵗ Bool : ProbComp Bool)
      let z ← if bit then ddhExpReal g adversary
               else ddhExpRand g adversary
      pure (bit == z)] := by
  unfold ddhExp
  simp only [← probEvent_eq_eq_probOutput]
  rw [probEvent_bind_congr fun a _ => probEvent_bind_bind_swap _ _ _ _,
      probEvent_bind_bind_swap]
  simp only [probEvent_eq_eq_probOutput]
  refine probOutput_bind_congr' ($ᵗ Bool) true ?_
  intro bit
  cases bit <;> simp [ddhExpReal, ddhExpRand]

omit [Fintype F] [DecidableEq F] [DecidableEq G] [SampleableType G] in
/-- The single-game DDH decomposes: `Pr[win] - 1/2 = (Pr[real=1] - Pr[rand=1]) / 2`. -/
lemma ddhExp_probOutput_sub_half (g : G) (adversary : DDHAdversary F G) :
    (Pr[= true | ddhExp g adversary]).toReal - 1 / 2 =
    ((Pr[= true | ddhExpReal g adversary]).toReal -
      (Pr[= true | ddhExpRand g adversary]).toReal) / 2 := by
  rw [show (Pr[= true | ddhExp g adversary]).toReal =
      (Pr[= true | do
        let bit ← ($ᵗ Bool : ProbComp Bool)
        let z ← if bit then ddhExpReal g adversary
                 else ddhExpRand g adversary
        pure (bit == z)]).toReal from by
    congr 1; exact ddhExp_probOutput_eq_branch (F := F) g adversary]
  exact probOutput_uniformBool_branch_toReal_sub_half
    (ddhExpReal g adversary)
    (ddhExpRand g adversary)

omit [Fintype F] [DecidableEq F] [DecidableEq G] [SampleableType G] in
/-- The two DDH advantage formulations are related by a factor of 2:
`ddhDistAdvantage = 2 * ddhGuessAdvantage`. -/
theorem ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage (g : G) (adversary : DDHAdversary F G) :
    ddhDistAdvantage g adversary = 2 * ddhGuessAdvantage g adversary := by
  unfold ddhDistAdvantage ddhGuessAdvantage
  have h := ddhExp_probOutput_sub_half (F := F) g adversary
  have h2 : (Pr[= true | ddhExpReal g adversary]).toReal -
      (Pr[= true | ddhExpRand g adversary]).toReal =
      2 * ((Pr[= true | ddhExp g adversary]).toReal - 1 / 2) := by linarith
  rw [h2, abs_mul, abs_of_nonneg (by positivity)]

/-! ## Generable relation for discrete log -/

section DLogGenerable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [Fintype G] [SampleableType G] [DecidableEq G]
variable (g : G)

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
    exact probOutput_map_bijective_uniform_cross (α := F) (β := G) (· • g) hg pk
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
