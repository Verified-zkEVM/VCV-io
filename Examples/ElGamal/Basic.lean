/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import Examples.ElGamal.Common
import VCVio.CryptoFoundations.AsymmEncAlg.IND_CPA
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# ElGamal Encryption: IND-CPA via the generic one-time lift

This file defines ElGamal encryption over a module `Module F G` and treats the security proof as
a one-time DDH client of the generic IND-CPA lift in `AsymmEncAlg`.

## Mathematical notation

We use additive / EC-style notation throughout:

| Textbook (multiplicative) | This file (additive)             |
|---------------------------|----------------------------------|
| `g^a`                     | `a • gen`                        |
| `g^a · g^b = g^{a+b}`     | `a • gen + b • gen`              |
| `(g^a)^b = g^{ab}`        | `b • (a • gen) = (b * a) • gen` |
| `m · g^{ab}`              | `m + (a * b) • gen`              |

Here `F` is the scalar field (for example `ZMod p`), `G` is the additive group of ciphertext
payloads (for example elliptic-curve points), and `gen : G` is a fixed public generator.

## Proof structure

1. ElGamal definition and correctness.
2. One-time DDH bridge:
   `IND_CPA_OneTime_DDHReduction`,
   `IND_CPA_OneTime_game_evalDist_eq_ddhExpReal`,
   `IND_CPA_OneTime_DDHReduction_rand_half`, and
   `elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage`.
3. Final theorem:
   `elGamal_IND_CPA_le_q_mul_ddh` is a direct instantiation of
   `AsymmEncAlg.IND_CPA_advantage_toReal_le_q_mul_of_oneTime_signedAdvantageReal_bound`
   with one-time loss `2 * ε`.
-/

open OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

/-- ElGamal encryption over a module `Module F G` with generator `gen : G`.

Key generation samples a scalar `sk ← $ᵗ F` and returns `(sk • gen, sk)`.
Encryption of `msg` under public key `pk` samples `r ← $ᵗ F` and returns
`(r • gen, msg + r • pk)`. Decryption recovers `msg` as `c₂ - sk • c₁`. -/
@[simps!] def elgamalAsymmEnc (F G : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G]
    (gen : G) : AsymmEncAlg ProbComp
    (M := G) (PK := G) (SK := F) (C := G × G) where
  keygen := do
    let sk ← $ᵗ F
    return (sk • gen, sk)
  encrypt := fun pk msg => do
    let r ← $ᵗ F
    return (r • gen, msg + r • pk)
  decrypt := fun sk (c₁, c₂) =>
    return (some (c₂ - sk • c₁))
  __ := ExecutionMethod.default

namespace elgamalAsymmEnc

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

/-- ElGamal decryption perfectly inverts encryption: `Dec(sk, Enc(pk, msg)) = msg`. -/
theorem correct [DecidableEq G] : (elgamalAsymmEnc F G gen).PerfectlyCorrect := by
  have hcancel : ∀ (msg : G) (sk r : F),
      msg + r • (sk • gen) - sk • (r • gen) = msg := by
    intro msg sk r
    have : r • (sk • gen) = sk • (r • gen) := by
      rw [← mul_smul, ← mul_smul, mul_comm]
    rw [this, add_sub_cancel_right]
  simp [AsymmEncAlg.PerfectlyCorrect, AsymmEncAlg.CorrectExp, elgamalAsymmEnc, hcancel]

section IND_CPA

variable [DecidableEq G]

local instance : Inhabited G := ⟨0⟩

/-- One-time DDH reduction for ElGamal. On input `(gen, A, B, T)`, use `A` as the ElGamal public
key, form the challenge ciphertext `(B, T + m_b)`, and return whether the one-time adversary
guessed the hidden bit `b`. -/
def IND_CPA_OneTime_DDHReduction
    (adv : AsymmEncAlg.IND_CPA_Adv (elgamalAsymmEnc F G gen)) :
    DiffieHellman.DDHAdversary F G := fun _ A B T => do
  let (m₁, m₂, st) ← adv.chooseMessages A
  let bit ← ($ᵗ Bool : ProbComp Bool)
  let c : G × G := (B, T + if bit then m₁ else m₂)
  let bit' ← adv.distinguish st c
  pure (bit == bit')

/-- Real-branch identification for the one-time ElGamal reduction. After unfolding
`IND_CPA_OneTime_Game_ProbComp`, `elgamalAsymmEnc`, `DiffieHellman.ddhExpReal`, and
`IND_CPA_OneTime_DDHReduction`, both sides normalize to the same sample space. -/
private lemma IND_CPA_OneTime_game_evalDist_eq_ddhExpReal
    (adv : AsymmEncAlg.IND_CPA_Adv (elgamalAsymmEnc F G gen)) :
    evalDist
      (AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
        (encAlg := elgamalAsymmEnc F G gen) adv) =
      evalDist
        (DiffieHellman.ddhExpReal (F := F) gen
          (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)) := by
  -- Proof plan:
  -- 1. unfold `IND_CPA_OneTime_Game_ProbComp`, `elgamalAsymmEnc`, `DiffieHellman.ddhExpReal`,
  --    and `IND_CPA_OneTime_DDHReduction`
  -- 2. align the bind order on both sides
  -- 3. rewrite `((r * sk) • gen)` as `r • (sk • gen)`
  -- 4. conclude by reflexivity after normalization
  sorry

/-- Random-branch half lemma for the one-time ElGamal reduction. Under bijectivity of `(· • gen)`,
the DDH-random branch gives a uniform additive mask independent of the challenge bit, so the
adversary can do no better than random guessing. -/
private lemma IND_CPA_OneTime_DDHReduction_rand_half
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_Adv (elgamalAsymmEnc F G gen)) :
    Pr[= true | DiffieHellman.ddhExpRand (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] = 1 / 2 := by
  -- Proof plan:
  -- 1. unfold the random DDH branch and the reduction
  -- 2. use bijectivity of `(· • gen)` to rewrite the first component as a uniform header and the
  --    second component as a uniformly masked payload
  -- 3. apply `ElGamalExamples.uniformMaskedCipher_dist_indep`
  -- 4. close with `probOutput_decide_eq_uniformBool_half`
  sorry

/-- The absolute one-time signed IND-CPA advantage of ElGamal is exactly twice the DDH guess
advantage of the reduction above. The factor `2` is essential because the DDH guess advantage is
defined from the mixed experiment, while the one-time IND-CPA game compares the real and random
branches directly. -/
theorem elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_Adv (elgamalAsymmEnc F G gen)) :
    |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (encAlg := elgamalAsymmEnc F G gen) adv| =
      2 * DiffieHellman.ddhGuessAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) := by
  -- Proof plan:
  -- 1. rewrite the one-time game using `IND_CPA_OneTime_game_evalDist_eq_ddhExpReal`
  -- 2. rewrite the DDH-random branch to `1 / 2` via `IND_CPA_OneTime_DDHReduction_rand_half`
  -- 3. identify the resulting absolute real/random gap with `ddhDistAdvantage`
  -- 4. conclude via
  --    `DiffieHellman.ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage`
  sorry

/-- **Main theorem.** If an adversary makes at most `q` LR queries and every extracted one-time
ElGamal DDH reduction has guess advantage at most `ε`, then ElGamal has IND-CPA advantage at most
`q * (2 * ε)`. -/
theorem elGamal_IND_CPA_le_q_mul_ddh
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elgamalAsymmEnc F G gen).IND_CPA_adversary)
    (q : ℕ) (ε : ℝ)
    (hq : adversary.MakesAtMostQueries q)
    (hε : 0 ≤ ε)
    (hddh : ∀ adv : AsymmEncAlg.IND_CPA_Adv (elgamalAsymmEnc F G gen),
      DiffieHellman.ddhGuessAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) ≤ ε) :
    ((elgamalAsymmEnc F G gen).IND_CPA_advantage adversary).toReal ≤ q * (2 * ε) := by
  refine AsymmEncAlg.IND_CPA_advantage_toReal_le_q_mul_of_oneTime_signedAdvantageReal_bound
    (encAlg' := elgamalAsymmEnc F G gen) adversary q (2 * ε) hq ?_ ?_
  · nlinarith
  · intro adv
    calc
      |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
          (encAlg := elgamalAsymmEnc F G gen) adv|
        = 2 * DiffieHellman.ddhGuessAdvantage gen
            (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) := by
              exact elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage
                (F := F) (G := G) (gen := gen) hg adv
      _ ≤ 2 * ε := by
          nlinarith [hddh adv]

end IND_CPA

end elgamalAsymmEnc
